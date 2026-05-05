import Lean
import Mathlib.Logic.ExistsUnique
import Mathlib.Data.Fin.Tuple.Basic
import Pullback.Shallow.Fix

open Lean

/-- `BasedType α` means each element of α maps to a runtime Type -/
class BasedType (α : Type) where
  valueType : α → Type

/-- `Typed α A` means each element of α can be assigned a type in A -/
class Typed (α A : Type) where
  type : α → A

inductive PType (BaseType : Type) where
| ofBase : BaseType → PType BaseType
| fun : PType BaseType → PType BaseType → PType BaseType
| prod : PType BaseType → PType BaseType → PType BaseType
deriving DecidableEq

namespace PType

/-- Interpret a PType as a runtime Type, given a mapping on base types -/
def type {BaseType : Type} [BasedType BaseType] : PType BaseType → Type
| .ofBase baseTy => BasedType.valueType baseTy
| .fun α β => α.type → β.type
| .prod α β => α.type × β.type

end PType

/-- `Interp BaseType Const` gives a runtime value for each typed constant. -/
class Interp (BaseType : Type) (Const : Type) [BasedType BaseType] [Typed Const (PType BaseType)] where
  interp : ∀ c : Const, PType.type (BaseType := BaseType) (Typed.type (α := Const) (A := PType BaseType) c)

inductive PExpr (Const BaseType : Type) [Typed Const (PType BaseType)] : List (PType BaseType) → PType BaseType → Type where
/-
  add unused context variables to the outside. Eg if `0 ⊢ f 0` is valid then `1 0 ⊢ f 0` is certainly valid.
  Note that the inner most context variable is the left most element of the context list
-/
| lift {ty} {ctx ctx'} (e : PExpr Const BaseType ctx ty) : PExpr Const BaseType (ctx ++ ctx') ty
| const {ctx} (c : Const): PExpr Const BaseType ctx (Typed.type c)
| letE {ctx} {valT} {ty} (val : PExpr Const BaseType ctx valT) (body : PExpr Const BaseType (valT::ctx) ty) : PExpr Const BaseType ctx ty
| var {ctx} (name : Fin ctx.length) (ty : PType BaseType := ctx.get name) (hty : ctx.get name = ty := by rfl) : PExpr Const BaseType ctx ty
| app {ctx} {argT} {ty} (f : PExpr Const BaseType ctx (.fun argT ty)) (arg : PExpr Const BaseType ctx argT) : PExpr Const BaseType ctx ty
| lam {bodyT} {ctx} (varType : PType BaseType) (body : PExpr Const BaseType (varType::ctx) bodyT) : PExpr Const BaseType ctx (.fun varType bodyT)

/-- DVector is a heterogeneous tuple indexed by a list of types -/
def DVector : List Type → Type
| [] => Unit
| α::l => α × DVector l

namespace DVector

def cons {L: List Type} {α : Type} : α → DVector L → DVector (α::L)
| a, dv => (a, dv)

def cons' {BaseType : Type} [BasedType BaseType] {ctx : List (PType BaseType)} {alpha : PType BaseType} : alpha.type → DVector (ctx.map (·.type)) → DVector ((alpha::ctx).map (·.type))
| a, dv => (a, dv)

def push {L: Array Type} {α : Type} (dv : DVector L.toList) (a : α) : DVector (L.push α).toList :=
  match L with
  | ⟨[]⟩ => (a, ())
  | ⟨l::ls⟩ =>
      let (x, xs) := dv
      (x, push xs a)

def take {BaseType : Type} [BasedType BaseType] {ctx : List (PType BaseType)} : (n : Nat) → DVector (ctx.map (·.type)) → DVector ((ctx.take n).map (·.type))
| 0, _ => ()
| n+1, v =>
  match ctx with
  | [] => ()
  | (_ :: _) =>
      let (x, xs) := v
      let xs' := take n xs
      (x, xs')

def get : {L : List Type} → (v : DVector L) → (i : Fin L.length) → L.get i
| _::_, (va, _), ⟨0, _⟩ => va
| _::_, (_, dv), ⟨i+1, h⟩ => get dv ⟨i, Nat.lt_of_succ_lt_succ h⟩

end DVector

def PExpr.interp {Const BaseType : Type} [BasedType BaseType] [Typed Const (PType BaseType)] [Interp BaseType Const] {ctx} {ty} (args : DVector (ctx.map (·.type))) : (e : PExpr Const BaseType ctx ty) → ty.type
| lift (ctx := ctx) e => e.interp (ctx := ctx) (cast (by simp) (args.take ctx.length))
| const c => Interp.interp c
| letE val body =>
  body.interp (DVector.cons' (val.interp args) args)
| var name ty hty => cast (by grind) <| args.get (Fin.cast (by simp) name)
| app f arg =>
  (f.interp args) (arg.interp args)
| lam varType body =>
  fun x : varType.type => body.interp (DVector.cons' x args)

namespace PExpr

inductive RawPExpr (Const BaseType : Type)
where
| var   (x : Name)
| app   (f a : RawPExpr Const BaseType)
| lam   (x : Name) (ty : PType BaseType)
        (body : RawPExpr Const BaseType)
| letE  (x : Name)
        (v body : RawPExpr Const BaseType)
| const (c : Const)

def RawPExpr.inferType {Const BaseType} [DecidableEq BaseType] [Typed Const (PType BaseType)] (ctxRaw : List (Name × PType BaseType)) : RawPExpr Const BaseType → Option (PType BaseType)
| var (x : Name) => do return (ctxRaw.map (·.2)).get (Fin.cast (by grind) (← ctxRaw.findFinIdx? (·.1 == x)))
| app f a => do
  match ← f.inferType ctxRaw, ← a.inferType ctxRaw with
  | .fun dom codom, ta =>
    if ta = dom then
      return codom
    none
  | _, _ => none
| lam x ty body =>
  (body.inferType ((x, ty)::ctxRaw)).map (fun bodyT => .fun ty bodyT)
| letE x v body =>
  (v.inferType ctxRaw).bind
    fun vT =>
      body.inferType ((x, vT)::ctxRaw)
| const c => some (Typed.type c)

def RawPExpr.toPExpr {BaseType Const} [DecidableEq BaseType] [Typed Const (PType BaseType)] (ctxRaw : List (Name × PType BaseType)) :
  (e : RawPExpr Const BaseType) → (he : (e.inferType ctxRaw).isSome) →
    (PExpr Const BaseType (ctxRaw.map (·.2)) ((e.inferType ctxRaw).get he))
| var x, he =>
  let xi := (ctxRaw.findFinIdx? (·.1 == x)).get (by grind [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff])
  let ctx := ctxRaw.map (·.2)
  have hctx : ctxRaw.length = ctx.length := by simp [ctx]
  let varTy : PType BaseType := ctx.get (Fin.cast hctx xi)
  let e : PExpr Const BaseType ctx (ctx.get (Fin.cast hctx xi)) :=
    PExpr.var (Fin.cast hctx xi)
  cast (by {
    congr
    simp [ctx, inferType, List.find?_eq_map_findFinIdx?_getElem, xi]
  }) e
| app f a, he =>
  have hfT := by
    grind [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff]
  have : (inferType ctxRaw f) = (f.inferType ctxRaw).get hfT := by grind
  match hf : (f.inferType ctxRaw).get hfT with
  | .fun dom codom =>
    let ctx := ctxRaw.map (·.2)
    have ha : (a.inferType ctxRaw).isSome := by
      simp only [inferType, Option.pure_def, Option.bind_eq_bind, Option.bind_fun_none] at he
      rw [this, hf] at he
      grind [Option.isSome_iff_exists, Option.bind_eq_some_iff]
    let aT := (a.inferType ctxRaw).get ha
    let a' : PExpr Const BaseType ctx aT := a.toPExpr ctxRaw ha
    have hdom : dom = aT := by
      simp only [inferType, Option.pure_def, Option.bind_eq_bind, Option.bind_fun_none] at he
      rw [this, hf] at he
      grind [Option.isSome_iff_exists, Option.bind_eq_some_iff]
    have hf : (f.inferType ctxRaw).isSome := by
      simp only [inferType, Option.pure_def, Option.bind_eq_bind, Option.bind_fun_none] at he
      rw [this, hf] at he
      grind [Option.isSome_iff_exists, Option.bind_eq_some_iff]
    let f' : PExpr Const BaseType ctx (.fun aT codom) := cast (by grind) (f.toPExpr ctxRaw hf)
    let e : PExpr Const BaseType ctx codom := .app f' a'
    cast (by grind [inferType]) e
  | .prod _ _ | .ofBase _ => by
    simp [inferType] at he
    rw [this, hf] at he
    simp at he
| lam varname vartype body, he =>
  cast (by grind [inferType]) <|
    PExpr.lam vartype (body.toPExpr ((varname, vartype)::ctxRaw) (by grind [inferType]))
| letE x v body, he =>
  have hv : (v.inferType ctxRaw).isSome := by
    grind [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff]
  let vT := (v.inferType ctxRaw).get hv
  let v' := v.toPExpr ctxRaw hv
  have hbody : (inferType ((x, vT) :: ctxRaw) body).isSome := by
    grind [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff]
  cast (by grind [inferType]) <|
    PExpr.letE v' (body.toPExpr ((x, vT)::ctxRaw) hbody)
| const c, he => .const c

class HasType {Const BaseType} [DecidableEq BaseType] [Typed Const (PType BaseType)] (ctxRaw : List (Name × PType BaseType)) (e : RawPExpr (Const := Const) (BaseType := BaseType)) (ty : outParam (PType BaseType)) where
  hasType : e.inferType ctxRaw = ty

class HasVar {BaseType} (ctxRaw : List (Name × PType BaseType)) (name : Name) (ty : outParam (PType BaseType)) where
  hasVar : ctxRaw.find? (·.1 == name) = some (name, ty)

def RawPExpr.toPExpr' {BaseType Const} [DecidableEq BaseType] [Typed Const (PType BaseType)] (ctxRaw : List (Name × PType BaseType)) (ty : PType BaseType) :
  (e : RawPExpr Const BaseType) → [HasType ctxRaw e ty] →
    (PExpr Const BaseType (ctxRaw.map (·.2)) ty) :=
  fun e he =>
    cast (by grind [HasType]) (e.toPExpr ctxRaw (by grind [HasType]))

namespace RawPExpr

variable {BaseType Const} [DecidableEq BaseType] [Typed Const (PType BaseType)]


instance instHasType_const (ctxRaw : List (Name × PType BaseType)) (c : Const) :
  HasType ctxRaw (RawPExpr.const c : RawPExpr Const BaseType) (Typed.type c) :=
  ⟨by simp [inferType]⟩

instance instHasType_lam (ctxRaw : List (Name × PType BaseType)) (x : Name) (argT bodyT : PType BaseType)
    (body : RawPExpr Const BaseType) [HasType ((x, argT)::ctxRaw) body bodyT] :
  HasType ctxRaw (RawPExpr.lam x argT body : RawPExpr Const BaseType) (PType.fun argT bodyT) :=
  ⟨by
    have hbody : inferType ((x, argT) :: ctxRaw) body = some bodyT :=
      HasType.hasType (ctxRaw := ((x, argT) :: ctxRaw)) (e := body) (ty := bodyT)
    simp [inferType, hbody]
  ⟩

instance instHasType_letE (ctxRaw : List (Name × PType BaseType)) (x : Name)
    (v body : RawPExpr Const BaseType) (vT bodyT : PType BaseType)
    [HasType ctxRaw v vT] [HasType ((x, vT)::ctxRaw) body bodyT] :
  HasType ctxRaw (RawPExpr.letE x v body : RawPExpr Const BaseType) bodyT :=
  ⟨by
    have hv : inferType ctxRaw v = some vT :=
      HasType.hasType (ctxRaw := ctxRaw) (e := v) (ty := vT)
    have hbody : inferType ((x, vT) :: ctxRaw) body = some bodyT :=
      HasType.hasType (ctxRaw := ((x, vT) :: ctxRaw)) (e := body) (ty := bodyT)
    simp [inferType, hv, hbody]
  ⟩

instance instHasType_app (ctxRaw : List (Name × PType BaseType)) (dom codom : PType BaseType) (f x : RawPExpr Const BaseType) [HasType ctxRaw f (PType.fun dom codom)] [HasType ctxRaw x dom] :
  HasType ctxRaw (RawPExpr.app f x) codom :=
  ⟨by simp [inferType]; grind [HasType]⟩

instance instHasVar_head {ctx : List (Name × PType BaseType)} {name : Name} {ty : PType BaseType} :
    HasVar ((name, ty) :: ctx) name ty :=
  ⟨by grind⟩

theorem hasVar_cons {ctx : List (Name × PType BaseType)} {name name' : Name} {ty ty' : PType BaseType}
    {idx : Fin ctx.length}
    (h : HasVar ctx name ty) (hne : name' ≠ name) :
    HasVar ((name', ty') :: ctx) name ty :=
  ⟨by grind [h.1]⟩

instance instHasType_var {ctx : List (Name × PType BaseType)} {name : Name}
  {ty : PType BaseType} [hv : HasVar ctx name ty] :
    HasType ctx (RawPExpr.var name : RawPExpr Const BaseType) ty :=
  ⟨by
    {
      have := hv.1
      rw [List.find?_eq_some_iff_getElem] at this
      simp [List.findFinIdx?_eq_some_iff, inferType, Option.bind_eq_some_iff]
      obtain ⟨i, hi, H⟩ := this.2
      use ⟨i, hi⟩
      grind
    }⟩

macro "inferHasType" : tactic =>
  `(tactic| (apply HasType.mk; simp [RawPExpr.inferType, List.findFinIdx?, List.findFinIdx?.go]))

macro "inferHasVar" : tactic =>
  `(tactic| (apply HasVar.mk; rfl))


open Lean Meta Expr Elab Term Tactic Core IO LibrarySuggestions
#check Simp.Context.ofArgs
#check Lean.Meta.mkSimpTheoremFromExpr
open Lean Meta Elab Tactic Simp in
open Lean Meta
/-- Simplify an expression using the given lemmas -/
def simpExpr (e : Expr) (defns : List Name) : MetaM Expr := do
  let cfg : Lean.Meta.Simp.Config := {
    zeta := true
    beta := true
    eta := true
    iota := true
    proj := true
    decide := false
    contextual := false
    arith := false
  }
  let ctx ← Meta.mkSimpContext (simpOnly := false) cfg

  let mut simpTheorems := ctx.simpTheorems
  if simpTheorems.isEmpty then
    simpTheorems := #[]

  -- 🔥 KEY CHANGE HERE
  for name in defns do
    simpTheorems ← simpTheorems.modifyM 0 fun thms0 =>
      thms0.addDeclToUnfold name

  let ctx := ctx.setSimpTheorems simpTheorems
  let result ← Meta.simp e ctx
  return result.1.expr

open Lean Meta Elab Tactic Simp
/-- Term elaborator that returns `RawPExpr.inferType vars e` unevaluated (no simplification). -/
elab "exprTypeOf" e:term "in" vars:term : term => do
  let stx ← `(RawPExpr.inferType $vars $e)
  let e ← Lean.Elab.Term.elabTerm stx none
  simpExpr e [`PExpr.RawPExpr.inferType, `List.findFinIdx?, `List.findFinIdx?.go, `Typed.type]

end RawPExpr

variable {Const Const' BaseType BaseType'} [DecidableEq BaseType] [BasedType BaseType] [BasedType BaseType'] [DecidableEq BaseType'] [Typed Const (PType BaseType)] [Typed Const' (PType BaseType')]
variable [Interp BaseType Const] [Interp BaseType' Const']


@[simp]
theorem toPExpr'_app
    {ctx : List (Name × PType BaseType)}
    {f a : RawPExpr Const BaseType}
    {A B : PType BaseType}
    (hf : HasType ctx f (A.fun B) := by inferHasType) (ha : HasType ctx a A := by inferHasType) :
  (RawPExpr.app f a).toPExpr' ctx B
  =
  PExpr.app
    (f.toPExpr' ctx (A.fun B))
    (a.toPExpr' ctx A) := by
simp [RawPExpr.toPExpr', RawPExpr.toPExpr]
rw! (castMode := .all) [hf.1]
simp [ha.1]

@[simp]
theorem toPExpr'_const
    {ctx : List (Name × PType BaseType)}
    (c : Const) :
  (RawPExpr.const c : RawPExpr Const BaseType).toPExpr' ctx (Typed.type c)
  = PExpr.const c := by
rfl

@[simp]
theorem toPExpr'_lam
    {ctx : List (Name × PType BaseType)}
    {x : Name} {argT bodyT : PType BaseType}
    {body : RawPExpr Const BaseType}
    (hbody : HasType ((x, argT) :: ctx) body bodyT := by inferHasType) :
  (RawPExpr.lam x argT body : RawPExpr Const BaseType).toPExpr' ctx (.fun argT bodyT)
  = PExpr.lam argT (body.toPExpr' ((x, argT) :: ctx) bodyT) := by
simp [RawPExpr.toPExpr', RawPExpr.toPExpr]
rw! (castMode := .all) [hbody.1]
simp

@[simp]
theorem toPExpr'_letE
    {ctx : List (Name × PType BaseType)}
    {x : Name} {v body : RawPExpr Const BaseType}
    {vT bodyT : PType BaseType}
    (hv : HasType ctx v vT := by inferHasType) (hbody : HasType ((x, vT) :: ctx) body bodyT := by inferHasType) :
  (RawPExpr.letE x v body : RawPExpr Const BaseType).toPExpr' ctx bodyT
  = PExpr.letE (v.toPExpr' ctx vT) (body.toPExpr' ((x, vT) :: ctx) bodyT) := by
simp [RawPExpr.toPExpr', RawPExpr.toPExpr]
rw! (castMode := .all) [hv.1, hbody.1]
grind

@[simp]
theorem toPExpr'_var
    {ctx : List (Name × PType BaseType)}
    {name : Name} {ty : PType BaseType}
    (hv : HasVar ctx name ty := by inferHasVar) :
  (RawPExpr.var name : RawPExpr Const BaseType).toPExpr' ctx ty
  = PExpr.var (Fin.cast (by grind) ((ctx.findFinIdx? (·.1 == name)).get (by grind [HasVar]))) ty (by {
    have := hv.1
    sorry
  }) := by
  simp [RawPExpr.toPExpr', RawPExpr.toPExpr]
  grind [HasVar]

example
  {ctx : List (Name × PType BaseType)} {ty : PType BaseType} (args : DVector (ctx.map (·.2.type)))
  {e : RawPExpr Const BaseType} {e' : RawPExpr Const' BaseType'}
  (f : PType BaseType → PType BaseType') (hf : ∀ ty : PType BaseType, ty.type = (f ty).type)
  (he : HasType ctx e ty := by inferHasType) (he' : HasType (ctx.map (fun (x, v) => (x, f v))) e' (f ty) := by inferHasType)
  (E : ty.type) (E' : (f ty).type)
  (He : (e.toPExpr' ctx ty).interp (cast (by grind) args) = E)
  (He' : (e'.toPExpr' (ctx.map (fun (x, t) => (x, f t))) (f ty)).interp (cast sorry args) = E')
  (H : E ≍ E') :
    let harg := by
      apply congrArg
      simp
      grind
    (e.toPExpr ctx (by grind [HasType])).interp (cast (by grind) args) = cast (by simp [he.1, he'.1, hf]) ((e'.toPExpr (ctx.map (fun (x, t) => (x, f t))) (by grind [HasType])).interp (cast harg args)) := sorry

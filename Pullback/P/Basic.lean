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
| var {ctx} (name : Fin ctx.length) : PExpr Const BaseType ctx (ctx.get name)
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
| var name => cast (by simp) <| args.get (Fin.cast (by simp) name)
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
| var (x : Name) => (ctxRaw.find? (·.1 == x)).map (·.2)
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
  let xi := (ctxRaw.findFinIdx? (·.1 == x)).get (by grind [inferType])
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

def RawPExpr.toPExpr' {BaseType Const} [DecidableEq BaseType] [Typed Const (PType BaseType)] (ctxRaw : List (Name × PType BaseType)) (ty : PType BaseType) :
  (e : RawPExpr Const BaseType) → [HasType ctxRaw e ty] →
    (PExpr Const BaseType (ctxRaw.map (·.2)) ty) :=
  fun e he =>
    cast (by grind [HasType]) (e.toPExpr ctxRaw (by grind [HasType]))

namespace RawPExpr

variable {BaseType Const} [DecidableEq BaseType] [Typed Const (PType BaseType)]

theorem hasType_var (ty : PType BaseType) (ctxRaw : List (Name × PType BaseType)) (name : Name)
    (hname : (ctxRaw.find? (·.1 == name)) = some (name, ty)) :
  HasType ctxRaw (RawPExpr.var name : RawPExpr Const BaseType) ty :=
  ⟨by simpa [inferType] using congrArg (Option.map Prod.snd) hname⟩

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
end RawPExpr

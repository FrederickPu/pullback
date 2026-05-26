import Lean
import Mathlib.Logic.ExistsUnique
import Mathlib.Data.Fin.Tuple.Basic
import Pullback.Shallow.Fix

open Lean

/-- `BasedType α` means each element of α maps to a runtime Type -/
class BasedType (α : Type) where
  valueType : α → Type

/-- `Typed α A` means each element of α can be assigned a type in A -/
class Typed (α : Type) (A : outParam Type) where
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
| const {ctx} (c : Const) (ty : PType BaseType := Typed.type c) (hty : Typed.type c = ty := by rfl) : PExpr Const BaseType ctx ty
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

open Lean Meta in
private partial def getDVectorElem (dv : Expr) : Nat → MetaM (Option Expr)
  | 0 => do
    let dv' ← whnf dv
    if dv'.getAppFn.isConstOf ``Prod.mk then
      let args := dv'.getAppArgs
      return if args.size >= 4 then some args[args.size - 2]! else none
    else if dv'.getAppFn.isConstOf ``DVector.cons' then
      let args := dv'.getAppArgs
      return if args.size >= 2 then some args[args.size - 2]! else none
    else return none
  | n + 1 => do
    let dv' ← whnf dv
    if dv'.getAppFn.isConstOf ``Prod.mk then
      let args := dv'.getAppArgs
      if args.size >= 4 then return ← getDVectorElem args[args.size - 1]! n
      else return none
    else if dv'.getAppFn.isConstOf ``DVector.cons' then
      let args := dv'.getAppArgs
      if args.size >= 2 then return ← getDVectorElem args[args.size - 1]! n
      else return none
    else return none

open Lean Meta Simp in
simproc ↓ [simp] DVector.reduceGet (_) := fun e => do
  unless e.getAppFn.isConstOf ``DVector.get do return .continue
  let eArgs := e.getAppArgs
  unless eArgs.size >= 3 do return .continue
  let dv    := eArgs[1]!
  let finI  := eArgs[2]!
  let extra := eArgs.extract 3 eArgs.size
  let finI' ← withTransparency .default (whnf finI)
  let valExpr ← withTransparency .default (whnf (← mkAppM ``Fin.val #[finI']))
  let .lit (.natVal n) := valExpr | return .continue
  let some result ← withTransparency .default (getDVectorElem dv n) | return .continue
  return .visit { expr := mkAppN result extra, proof? := none }

def PExpr.interp {Const BaseType : Type} [BasedType BaseType] [Typed Const (PType BaseType)] [Interp BaseType Const] {ctx} {ty} (args : DVector (ctx.map (·.type))) : (e : PExpr Const BaseType ctx ty) → ty.type
| lift (ctx := ctx) e => e.interp (ctx := ctx) (cast (by simp) (args.take ctx.length))
| const c ty hty => cast (by simp [hty]) (Interp.interp c)
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

/-- The canonical elaboration result for a raw expression: its inferred type paired with
the intrinsically typed expression at that type. -/
abbrev RawPExpr.ElabResult {Const BaseType : Type} [Typed Const (PType BaseType)]
    (ctxRaw : List (Name × PType BaseType)) : Type :=
  Σ ty : PType BaseType, PExpr Const BaseType (ctxRaw.map (·.2)) ty

/-- Canonical syntax-directed elaboration from raw syntax to intrinsically typed syntax.

This is the computational path intended to replace proof-reconstructing reductions of
`toPExpr'`: typing failures return `none`, while successful branches compute the type and
the `PExpr` together. -/
def RawPExpr.elab? {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) :
    RawPExpr Const BaseType → Option (RawPExpr.ElabResult (Const := Const) (BaseType := BaseType) ctxRaw)
| var x => do
  let i ← ctxRaw.findFinIdx? (·.1 == x)
  let j : Fin (ctxRaw.map (·.2)).length := Fin.cast (by simp) i
  return ⟨(ctxRaw.map (·.2)).get j, PExpr.var j⟩
| app f a => do
  let ⟨fty, f'⟩ ← RawPExpr.elab? ctxRaw f
  let ⟨aty, a'⟩ ← RawPExpr.elab? ctxRaw a
  match fty with
  | .fun dom codom =>
      if h : aty = dom then
        return ⟨codom, PExpr.app f' (h ▸ a')⟩
      else
        none
  | .ofBase _ | .prod _ _ => none
| lam x ty body => do
  let ⟨bodyT, body'⟩ ← RawPExpr.elab? ((x, ty)::ctxRaw) body
  return ⟨PType.fun ty bodyT, PExpr.lam ty body'⟩
| letE x v body => do
  let ⟨vT, v'⟩ ← RawPExpr.elab? ctxRaw v
  let ⟨bodyT, body'⟩ ← RawPExpr.elab? ((x, vT)::ctxRaw) body
  return ⟨bodyT, PExpr.letE v' body'⟩
| const c =>
  some ⟨Typed.type c, PExpr.const c⟩

/-- `elab?` computes exactly the same type as `inferType` when it succeeds. -/
theorem RawPExpr.elab?_type {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) (e : RawPExpr Const BaseType) :
    (RawPExpr.elab? ctxRaw e).map Sigma.fst = e.inferType ctxRaw := by
  induction e generalizing ctxRaw with
  | var x =>
      simp [RawPExpr.elab?, RawPExpr.inferType]
  | app f a ihf iha =>
      cases hf : RawPExpr.elab? ctxRaw f with
      | none =>
          have hfinfer : RawPExpr.inferType ctxRaw f = none := by
            simpa [hf] using (ihf ctxRaw).symm
          simp [RawPExpr.elab?, RawPExpr.inferType, hf, hfinfer]
      | some fr =>
          cases fr with
          | mk fty f' =>
              have hfinfer : RawPExpr.inferType ctxRaw f = some fty := by
                simpa [hf] using (ihf ctxRaw).symm
              cases ha : RawPExpr.elab? ctxRaw a with
              | none =>
                  have hainfer : RawPExpr.inferType ctxRaw a = none := by
                    simpa [ha] using (iha ctxRaw).symm
                  simp [RawPExpr.elab?, RawPExpr.inferType, hf, hfinfer, ha, hainfer]
              | some ar =>
                  cases ar with
                  | mk aty a' =>
                      have hainfer : RawPExpr.inferType ctxRaw a = some aty := by
                        simpa [ha] using (iha ctxRaw).symm
                      cases fty <;> simp [RawPExpr.elab?, RawPExpr.inferType, hf, hfinfer, ha, hainfer]
  | lam x ty body ih =>
      cases hbody : RawPExpr.elab? ((x, ty)::ctxRaw) body with
      | none =>
          have hinfer : RawPExpr.inferType ((x, ty)::ctxRaw) body = none := by
            simpa [hbody] using (ih ((x, ty)::ctxRaw)).symm
          simp [RawPExpr.elab?, RawPExpr.inferType, hbody, hinfer]
      | some r =>
          cases r with
          | mk bodyT body' =>
              have hinfer : RawPExpr.inferType ((x, ty)::ctxRaw) body = some bodyT := by
                simpa [hbody] using (ih ((x, ty)::ctxRaw)).symm
              simp [RawPExpr.elab?, RawPExpr.inferType, hbody, hinfer]
  | letE x v body ihv ihbody =>
      cases hv : RawPExpr.elab? ctxRaw v with
      | none =>
          have hvinfer : RawPExpr.inferType ctxRaw v = none := by
            simpa [hv] using (ihv ctxRaw).symm
          simp [RawPExpr.elab?, RawPExpr.inferType, hv, hvinfer]
      | some vr =>
          cases vr with
          | mk vT v' =>
              have hvinfer : RawPExpr.inferType ctxRaw v = some vT := by
                simpa [hv] using (ihv ctxRaw).symm
              cases hbody : RawPExpr.elab? ((x, vT)::ctxRaw) body with
              | none =>
                  have hbodyinfer : RawPExpr.inferType ((x, vT)::ctxRaw) body = none := by
                    simpa [hbody] using (ihbody ((x, vT)::ctxRaw)).symm
                  simp [RawPExpr.elab?, RawPExpr.inferType, hv, hvinfer, hbody, hbodyinfer]
              | some br =>
                  cases br with
                  | mk bodyT body' =>
                      have hbodyinfer : RawPExpr.inferType ((x, vT)::ctxRaw) body = some bodyT := by
                        simpa [hbody] using (ihbody ((x, vT)::ctxRaw)).symm
                      simp [RawPExpr.elab?, RawPExpr.inferType, hv, hvinfer, hbody, hbodyinfer]
  | const c =>
      simp [RawPExpr.elab?, RawPExpr.inferType]

/-- Total elaboration guarded by a proof that the raw expression is inferable.

The proof is used only to reject the impossible `none` branch; the successful branch is
the canonical result of `elab?`. -/
def RawPExpr.elab {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) (e : RawPExpr Const BaseType)
    (h : (e.inferType ctxRaw).isSome) :
    RawPExpr.ElabResult (Const := Const) (BaseType := BaseType) ctxRaw :=
  match hc : RawPExpr.elab? ctxRaw e with
  | some r => r
  | none =>
      False.elim <| by
        have ht := RawPExpr.elab?_type ctxRaw e
        rw [hc] at ht
        simp at ht
        rw [← ht] at h
        simp at h

class HasType {Const BaseType} [Typed Const (PType BaseType)] [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType))
    (e : RawPExpr (Const := Const) (BaseType := BaseType))
    (ty : outParam (PType BaseType)) : Prop where
  hasType : e.inferType ctxRaw = ty

class HasVar {BaseType} (ctxRaw : List (Name × PType BaseType)) (name : Name)
    (ty : outParam (PType BaseType)) : Prop where
  hasVar : ctxRaw.find? (·.1 == name) = some (name, ty)

namespace HasType

lemma const_inv {Const BaseType} [Typed Const (PType BaseType)] [DecidableEq BaseType]
    {ctx : List (Name × PType BaseType)} {c : Const} {ty : PType BaseType}
    [h : HasType ctx (RawPExpr.const c) ty] : Typed.type c = ty := by
  have hi := h.hasType
  simp [RawPExpr.inferType] at hi
  exact hi

end HasType

/-- Structural elaboration of raw syntax to typed syntax.
Delegates directly to `inferType` evidence carried by `HasType`. -/
def RawPExpr.toPExprElab {BaseType Const : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) (ty : PType BaseType) :
    (e : RawPExpr Const BaseType) → [HasType ctxRaw e ty] →
      PExpr Const BaseType (ctxRaw.map (·.2)) ty :=
  fun e inst => by
    cases e with
    | const c =>
        have hty_eq : Typed.type c = ty := HasType.const_inv (ctx := ctxRaw) (c := c) (ty := ty)
        exact hty_eq ▸ .const c
    | var name =>
        have hi := inst.hasType
        simp [RawPExpr.inferType] at hi
        generalize hfind : ctxRaw.findFinIdx? (·.1 == name) = idx at hi
        cases idx with
        | none => simp at hi
        | some i =>
            simp at hi
            exact .var (Fin.cast (by simp) i) ty (by simpa using hi)
    | app f a =>
        have hi := inst.hasType
        simp [RawPExpr.inferType] at hi
        generalize hf_opt : f.inferType ctxRaw = hf_val at hi
        cases hf_val with
        | none => simp at hi
        | some fty =>
            generalize ha_opt : a.inferType ctxRaw = ha_val at hi
            cases ha_val with
            | none => simp at hi
            | some aty =>
                cases fty with
                | ofBase _ => simp at hi
                | prod _ _ => simp at hi
                | «fun» dom codom =>
                    by_cases h_aty_eq_dom : aty = dom
                    · simp [h_aty_eq_dom] at hi
                      have h_codom_eq_ty : codom = ty := by simpa using hi
                      subst ty
                      have hf_ht : HasType ctxRaw f (PType.fun dom codom) :=
                        ⟨by simpa using hf_opt⟩
                      have ha_ht : HasType ctxRaw a dom :=
                        ⟨by simpa [h_aty_eq_dom] using ha_opt⟩
                      letI := hf_ht
                      letI := ha_ht
                      exact .app (RawPExpr.toPExprElab ctxRaw (PType.fun dom codom) f)
                        (RawPExpr.toPExprElab ctxRaw dom a)
                    · simp [h_aty_eq_dom] at hi
    | lam x tyLam body =>
        have hi := inst.hasType
        simp [RawPExpr.inferType] at hi
        generalize hb_opt : body.inferType ((x, tyLam) :: ctxRaw) = hb_val at hi
        cases hb_val with
        | none => simp at hi
        | some bodyT =>
            simp at hi
            subst ty
            have hb_ht : HasType ((x, tyLam) :: ctxRaw) body bodyT := ⟨by simpa using hb_opt⟩
            letI := hb_ht
            exact .lam tyLam (RawPExpr.toPExprElab ((x, tyLam) :: ctxRaw) bodyT body)
    | letE x v body =>
        have hi := inst.hasType
        simp [RawPExpr.inferType] at hi
        generalize hv_opt : v.inferType ctxRaw = hv_val at hi
        cases hv_val with
        | none => simp at hi
        | some vT =>
            simp at hi
            have hv_ht : HasType ctxRaw v vT := ⟨by simpa using hv_opt⟩
            have hb_ht : HasType ((x, vT) :: ctxRaw) body ty := ⟨by simpa using hi⟩
            letI := hv_ht
            letI := hb_ht
            exact .letE (RawPExpr.toPExprElab ctxRaw vT v)
              (RawPExpr.toPExprElab ((x, vT) :: ctxRaw) ty body)

/-- Elaborate raw syntax at its inferred type.

This is the surface API for callers that want the type computed by `inferType`. It is a
thin wrapper around `toPExprElab`; the only proof work is packaging the successful
`inferType` result as a `HasType` instance. -/
def RawPExpr.toPExpr {BaseType Const} [Typed Const (PType BaseType)] [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) :
    (e : RawPExpr Const BaseType) → (he : (e.inferType ctxRaw).isSome) →
      PExpr Const BaseType (ctxRaw.map (·.2)) ((e.inferType ctxRaw).get he) :=
  fun e he =>
    let ty := (e.inferType ctxRaw).get he
    have hty : e.inferType ctxRaw = some ty := by
      cases h : e.inferType ctxRaw with
      | none => simp [h] at he
      | some _ => simp [ty, h]
    letI : HasType ctxRaw e ty := ⟨hty⟩
    RawPExpr.toPExprElab ctxRaw ty e

theorem RawPExpr.toPExpr_heq_toPExprElab {BaseType Const}
    [Typed Const (PType BaseType)] [DecidableEq BaseType]
    {ctxRaw : List (Name × PType BaseType)} {e : RawPExpr Const BaseType}
    {ty : PType BaseType} [h : HasType ctxRaw e ty]
    (he : (e.inferType ctxRaw).isSome) :
    RawPExpr.toPExpr ctxRaw e he ≍ RawPExpr.toPExprElab ctxRaw ty e := by
  have hget : (e.inferType ctxRaw).get he = ty := by
    generalize hopt : e.inferType ctxRaw = opt at he ⊢
    cases opt with
    | none => simp at he
    | some ty' =>
        have hty' : ty' = ty := by
          exact Option.some.inj (by simpa [hopt] using h.hasType)
        simp [hty']
  cases hget
  rw [heq_iff_eq]
  simp [RawPExpr.toPExpr]

/-- A typed `PExpr`-like expression that may contain opaque raw holes.

Ordinary constructors elaborate structurally. A `hole` embeds a raw expression guarded by
typing evidence, so conversion to `PExpr` can leave opaque subexpressions at known types. -/
inductive PExprWithHoles {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType] :
    List (Name × PType BaseType) → PType BaseType → Type where
| hole {ctxRaw ty} (e : RawPExpr Const BaseType) (h : HasType ctxRaw e ty) :
    PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw ty
| const {ctxRaw} (c : Const) :
    PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw (Typed.type c)
| var {ctxRaw} (i : Fin (ctxRaw.map (·.2)).length)
    (ty : PType BaseType := (ctxRaw.map (·.2)).get i)
    (hty : (ctxRaw.map (·.2)).get i = ty := by rfl) :
    PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw ty
| app {ctxRaw argT ty}
    (f : PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw (.fun argT ty))
    (arg : PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw argT) :
    PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw ty
| lam {ctxRaw bodyT} (x : Name) (varType : PType BaseType)
    (body : PExprWithHoles (Const := Const) (BaseType := BaseType) ((x, varType)::ctxRaw) bodyT) :
    PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw (.fun varType bodyT)
| letE {ctxRaw valT ty} (x : Name)
    (val : PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw valT)
    (body : PExprWithHoles (Const := Const) (BaseType := BaseType) ((x, valT)::ctxRaw) ty) :
    PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw ty

namespace PExprWithHoles

/-- Result of pure partial elaboration: an inferred type paired with a typed partial
expression at that type. -/
abbrev Result {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType] (ctxRaw : List (Name × PType BaseType)) : Type :=
  Σ ty : PType BaseType, PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw ty

/-- Resolve a variable in a split context, checking locally bound variables before the
ambient context. This keeps generated partial skeletons from carrying an unknown context
through every lookup introduced by visible lambdas. -/
def findVarWithLocals? {BaseType : Type}
    (ctxRaw localCtx : List (Name × PType BaseType)) (x : Name) :
    Option (Fin ((localCtx ++ ctxRaw).map (·.2)).length) :=
  match localCtx.findFinIdx? (·.1 == x) with
  | some i =>
      some ⟨i.val, by
        have hi : i.val < (localCtx ++ ctxRaw).length :=
          Nat.lt_of_lt_of_le i.isLt (by simp [List.length_append])
        simpa using hi⟩
  | none => do
      let i ← ctxRaw.findFinIdx? (·.1 == x)
      some ⟨localCtx.length + i.val, by
        have hi : localCtx.length + i.val < (localCtx ++ ctxRaw).length := by
          simp [List.length_append, Nat.add_lt_add_left i.isLt localCtx.length]
        simp at hi ⊢⟩

/-- Pure partial elaboration with a split local/ambient context. The resulting partial
expression lives in `localCtx ++ ctxRaw`, but variables introduced by visible lambdas are
looked up in `localCtx` first. -/
def ofRawWithLocals? {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw localCtx : List (Name × PType BaseType)) :
    RawPExpr Const BaseType →
      Option (Result (Const := Const) (BaseType := BaseType) (localCtx ++ ctxRaw))
| RawPExpr.var x => do
  let i ← findVarWithLocals? ctxRaw localCtx x
  return ⟨((localCtx ++ ctxRaw).map (·.2)).get i, PExprWithHoles.var i⟩
| RawPExpr.app f a => do
  let ⟨fty, f'⟩ ← ofRawWithLocals? ctxRaw localCtx f
  let ⟨aty, a'⟩ ← ofRawWithLocals? ctxRaw localCtx a
  match fty with
  | .fun dom codom =>
      if h : aty = dom then
        return ⟨codom, PExprWithHoles.app f' (h ▸ a')⟩
      else
        none
  | .ofBase _ | .prod _ _ => none
| RawPExpr.lam x ty body => do
  let ⟨bodyT, body'⟩ ← ofRawWithLocals? ctxRaw ((x, ty)::localCtx) body
  return ⟨PType.fun ty bodyT, PExprWithHoles.lam x ty body'⟩
| RawPExpr.letE x v body => do
  let ⟨vT, v'⟩ ← ofRawWithLocals? ctxRaw localCtx v
  let ⟨bodyT, body'⟩ ← ofRawWithLocals? ctxRaw ((x, vT)::localCtx) body
  return ⟨bodyT, PExprWithHoles.letE x v' body'⟩
| RawPExpr.const c =>
  some ⟨Typed.type c, PExprWithHoles.const c⟩

/-- Pure syntax-directed generation of a typed partial expression from fully visible raw
syntax. This is the partial-expression analogue of `RawPExpr.elab?`. -/
def ofRaw? {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) :
    RawPExpr Const BaseType → Option (Result (Const := Const) (BaseType := BaseType) ctxRaw)
| RawPExpr.var x => do
  let i ← ctxRaw.findFinIdx? (·.1 == x)
  let j : Fin (ctxRaw.map (·.2)).length := Fin.cast (by simp) i
  return ⟨(ctxRaw.map (·.2)).get j, PExprWithHoles.var j⟩
| RawPExpr.app f a => do
  let ⟨fty, f'⟩ ← ofRaw? ctxRaw f
  let ⟨aty, a'⟩ ← ofRaw? ctxRaw a
  match fty with
  | .fun dom codom =>
      if h : aty = dom then
        return ⟨codom, PExprWithHoles.app f' (h ▸ a')⟩
      else
        none
  | .ofBase _ | .prod _ _ => none
| RawPExpr.lam x ty body => do
  let ⟨bodyT, body'⟩ ← ofRaw? ((x, ty)::ctxRaw) body
  return ⟨PType.fun ty bodyT, PExprWithHoles.lam x ty body'⟩
| RawPExpr.letE x v body => do
  let ⟨vT, v'⟩ ← ofRaw? ctxRaw v
  let ⟨bodyT, body'⟩ ← ofRaw? ((x, vT)::ctxRaw) body
  return ⟨bodyT, PExprWithHoles.letE x v' body'⟩
| RawPExpr.const c =>
  some ⟨Typed.type c, PExprWithHoles.const c⟩

/-- `ofRaw?` agrees with `inferType` on the inferred type. -/
theorem ofRaw?_type {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) (e : RawPExpr Const BaseType) :
    (ofRaw? ctxRaw e).map Sigma.fst = e.inferType ctxRaw := by
  induction e generalizing ctxRaw with
  | var x =>
      simp [ofRaw?, RawPExpr.inferType]
  | app f a ihf iha =>
      cases hf : ofRaw? ctxRaw f with
      | none =>
          have hfinfer : RawPExpr.inferType ctxRaw f = none := by
            simpa [hf] using (ihf ctxRaw).symm
          simp [ofRaw?, RawPExpr.inferType, hf, hfinfer]
      | some fr =>
          cases fr with
          | mk fty f' =>
              have hfinfer : RawPExpr.inferType ctxRaw f = some fty := by
                simpa [hf] using (ihf ctxRaw).symm
              cases ha : ofRaw? ctxRaw a with
              | none =>
                  have hainfer : RawPExpr.inferType ctxRaw a = none := by
                    simpa [ha] using (iha ctxRaw).symm
                  simp [ofRaw?, RawPExpr.inferType, hf, hfinfer, ha, hainfer]
              | some ar =>
                  cases ar with
                  | mk aty a' =>
                      have hainfer : RawPExpr.inferType ctxRaw a = some aty := by
                        simpa [ha] using (iha ctxRaw).symm
                      cases fty <;> simp [ofRaw?, RawPExpr.inferType, hf, hfinfer, ha, hainfer]
  | lam x ty body ih =>
      cases hbody : ofRaw? ((x, ty)::ctxRaw) body with
      | none =>
          have hinfer : RawPExpr.inferType ((x, ty)::ctxRaw) body = none := by
            simpa [hbody] using (ih ((x, ty)::ctxRaw)).symm
          simp [ofRaw?, RawPExpr.inferType, hbody, hinfer]
      | some r =>
          cases r with
          | mk bodyT body' =>
              have hinfer : RawPExpr.inferType ((x, ty)::ctxRaw) body = some bodyT := by
                simpa [hbody] using (ih ((x, ty)::ctxRaw)).symm
              simp [ofRaw?, RawPExpr.inferType, hbody, hinfer]
  | letE x v body ihv ihbody =>
      cases hv : ofRaw? ctxRaw v with
      | none =>
          have hvinfer : RawPExpr.inferType ctxRaw v = none := by
            simpa [hv] using (ihv ctxRaw).symm
          simp [ofRaw?, RawPExpr.inferType, hv, hvinfer]
      | some vr =>
          cases vr with
          | mk vT v' =>
              have hvinfer : RawPExpr.inferType ctxRaw v = some vT := by
                simpa [hv] using (ihv ctxRaw).symm
              cases hbody : ofRaw? ((x, vT)::ctxRaw) body with
              | none =>
                  have hbodyinfer : RawPExpr.inferType ((x, vT)::ctxRaw) body = none := by
                    simpa [hbody] using (ihbody ((x, vT)::ctxRaw)).symm
                  simp [ofRaw?, RawPExpr.inferType, hv, hvinfer, hbody, hbodyinfer]
              | some br =>
                  cases br with
                  | mk bodyT body' =>
                      have hbodyinfer : RawPExpr.inferType ((x, vT)::ctxRaw) body = some bodyT := by
                        simpa [hbody] using (ihbody ((x, vT)::ctxRaw)).symm
                      simp [ofRaw?, RawPExpr.inferType, hv, hvinfer, hbody, hbodyinfer]
  | const c =>
      simp [ofRaw?, RawPExpr.inferType]

/-- Pure expected-type partial elaboration. Unlike `ofRaw?`, this returns a partial
expression exactly at the requested type, avoiding a sigma result at the call site. -/
def ofRawDirectAs? {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) (ty : PType BaseType) :
    RawPExpr Const BaseType →
      Option (PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw ty)
| RawPExpr.var x => do
  let i ← ctxRaw.findFinIdx? (·.1 == x)
  let j : Fin (ctxRaw.map (·.2)).length := Fin.cast (by simp) i
  if h : (ctxRaw.map (·.2)).get j = ty then
    some (PExprWithHoles.var j ty h)
  else
    none
| RawPExpr.app f a => do
  let ⟨fty, f'⟩ ← ofRaw? ctxRaw f
  match fty with
  | .fun argT codom =>
      if hcodom : codom = ty then
        let a' ← ofRawDirectAs? ctxRaw argT a
        some (hcodom ▸ PExprWithHoles.app f' a')
      else
        none
  | .ofBase _ | .prod _ _ => none
| RawPExpr.lam x argT body =>
  match ty with
  | .fun dom codom =>
      if hdom : argT = dom then
        (ofRawDirectAs? ((x, argT)::ctxRaw) codom body).map fun body' =>
          cast (by cases hdom; rfl) (PExprWithHoles.lam x argT body')
      else
        none
  | .ofBase _ | .prod _ _ => none
| RawPExpr.letE x v body => do
  let ⟨vT, v'⟩ ← ofRaw? ctxRaw v
  let body' ← ofRawDirectAs? ((x, vT)::ctxRaw) ty body
  some (PExprWithHoles.letE x v' body')
| RawPExpr.const c =>
  if h : Typed.type c = ty then
    some (h ▸ PExprWithHoles.const c)
  else
    none

/-- Pure partial elaboration with an externally requested type. The proof only rules out
the impossible failed branch and justifies the final cast. -/
def ofRawDirectAs {BaseType Const : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) (ty : PType BaseType)
    (e : RawPExpr Const BaseType) [h : HasType ctxRaw e ty] :
    PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw ty :=
  match hc : ofRaw? ctxRaw e with
  | some ⟨ty', pe⟩ =>
      have hty : ty' = ty := by
        have ht := ofRaw?_type ctxRaw e
        have hHas : e.inferType ctxRaw = some ty := h.hasType
        rw [hc, hHas] at ht
        simpa using ht
      cast (by rw [hty]) pe
  | none =>
      False.elim <| by
        have ht := ofRaw?_type ctxRaw e
        have hHas : e.inferType ctxRaw = some ty := h.hasType
        rw [hc, hHas] at ht
        simp at ht

/-- Expected-type partial elaboration with an `isSome` surface driven by `inferType`.

This keeps call-site proofs like `.get (by simp)` on the cheap type-inference path, even
when the ambient context is generalized. The successful branch still returns a generated
`PExprWithHoles`, not a handwritten expression. -/
def ofRawDirectAsSplit? {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) (ty : PType BaseType) :
    RawPExpr Const BaseType →
      Option (PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw ty) := fun e =>
  if h : e.inferType ctxRaw = some ty then
    letI : HasType ctxRaw e ty := HasType.mk h
    some (ofRawDirectAs ctxRaw ty e)
  else
    none

@[simp]
theorem ofRawDirectAsSplit?_isSome {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) (ty : PType BaseType)
    (e : RawPExpr Const BaseType) [h : HasType ctxRaw e ty] :
    (ofRawDirectAsSplit? ctxRaw ty e).isSome = true := by
  simp [ofRawDirectAsSplit?, h.hasType]

/-- Expected-type wrapper around `ofRawWithLocals?` starting with no local binders.

This keeps the generated skeleton from carrying ambient context variables through visible
lambdas, while still returning an expression at the expected type. -/
@[reducible]
def ofRawWithLocalsAs? {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) (ty : PType BaseType)
    (e : RawPExpr Const BaseType) :
    Option (PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw ty) :=
  match PExprWithHoles.ofRawWithLocals? ctxRaw [] e with
  | some ⟨ty', pe⟩ =>
      if h : ty' = ty then
        some (h ▸ pe)
      else
        none
  | none => none

@[reducible]
def ofRawAs? {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) (ty : PType BaseType)
    (e : RawPExpr Const BaseType) :
    Option (PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw ty) :=
  ofRawWithLocalsAs? ctxRaw ty e

@[reducible]
def ofRawAs {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) (ty : PType BaseType)
    (e : RawPExpr Const BaseType) (h : (ofRawAs? ctxRaw ty e).isSome) :
    PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw ty :=
  (ofRawAs? ctxRaw ty e).get h

@[reducible]
def app2WithRawArgs {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    {ctxRaw : List (Name × PType BaseType)} {arg₁ arg₂ out : PType BaseType}
    (fRaw : RawPExpr Const BaseType)
    (hf : (ofRawAs? ctxRaw (arg₁.fun (arg₂.fun out)) fRaw).isSome)
    {a b : RawPExpr Const BaseType}
    (ha : HasType ctxRaw a arg₁) (hb : HasType ctxRaw b arg₂) :
    PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw out :=
  PExprWithHoles.app
    (PExprWithHoles.app
      (ofRawAs ctxRaw (arg₁.fun (arg₂.fun out)) fRaw hf)
      (PExprWithHoles.hole a ha))
    (PExprWithHoles.hole b hb)

def toPExpr {BaseType Const : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    {ctxRaw : List (Name × PType BaseType)} {ty : PType BaseType} :
    PExprWithHoles (Const := Const) (BaseType := BaseType) ctxRaw ty →
      PExpr Const BaseType (ctxRaw.map (·.2)) ty
| .hole e h =>
    letI := h
    RawPExpr.toPExprElab ctxRaw ty e
| .const c => PExpr.const c
| .var i ty hty => PExpr.var i ty hty
| .app f arg => PExpr.app f.toPExpr arg.toPExpr
| .lam x varType body => PExpr.lam varType body.toPExpr
| .letE x val body => PExpr.letE val.toPExpr body.toPExpr

end PExprWithHoles

def RawPExpr.toPExpr' {BaseType Const} [Typed Const (PType BaseType)] [DecidableEq BaseType]  (ctxRaw : List (Name × PType BaseType)) (ty : PType BaseType) :
  (e : RawPExpr Const BaseType) → [HasType ctxRaw e ty] →
    (PExpr Const BaseType (ctxRaw.map (·.2)) ty) :=
  fun e _ => RawPExpr.toPExprElab ctxRaw ty e

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

inductive PType (BaseType : Type) (n : Nat) where
| tyVar : Fin n → PType BaseType n
| ofBase : BaseType → PType BaseType n
| fun : PType BaseType n → PType BaseType n → PType BaseType n
| prod : PType BaseType n → PType BaseType n → PType BaseType n
deriving DecidableEq

/- PPType: a PType with an associated number of parametric type variables -/
abbrev PPType (BaseType : Type) := Sigma (PType BaseType)

namespace PType

/-- Interpret a PType as a runtime Type, given a mapping on base types -/
def type {BaseType : Type} [BasedType BaseType] {n : Nat} : PType BaseType n → (ctxTy : List Type) → ctxTy.length = n → Type
| .ofBase baseTy, _, _ => BasedType.valueType baseTy
| .fun α β, ctx, hctx => α.type ctx hctx → β.type ctx hctx
| .prod α β, ctx, hctx => α.type ctx hctx × β.type ctx hctx
| .tyVar i, ctx, hctx => ctx.get (Fin.cast (by grind) i)

def weaken
  {BaseType : Type}
  {m n : Nat}
  (h : m ≤ n) :
  PType BaseType m → PType BaseType n
| .tyVar i =>
    .tyVar ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩
| .ofBase b =>
    .ofBase b
| .fun a b =>
    .fun (weaken h a) (weaken h b)
| .prod a b =>
    .prod (weaken h a) (weaken h b)

lemma weaken_comp
    {BaseType : Type}
    {a b c : Nat}
    (hab : a ≤ b)
    (hbc : b ≤ c)
    (ty : PType BaseType a) :
    PType.weaken hbc (PType.weaken hab ty)
    =
    PType.weaken (Nat.le_trans hab hbc) ty := by
  induction ty <;> simp [PType.weaken, *]

lemma type_weaken
    {BaseType : Type} [BasedType BaseType]
    {m n : Nat} (h : m ≤ n)
    (ty : PType BaseType m)
    (ctxTy : List Type)
    (hctxTy : ctxTy.length = n) :
    (PType.weaken h ty).type ctxTy hctxTy =
      ty.type (ctxTy.take m) (by
        rw [List.length_take]
        omega) := by
  induction ty generalizing ctxTy <;> simp [PType.weaken, PType.type, *]

end PType


namespace PPType

def weakenTo
  {BaseType : Type}
  (N : Nat)
  (ty : PPType BaseType)
  (h : ty.1 ≤ N) :
  PType BaseType N :=
  PType.weaken h ty.2

def «fun»
  {BaseType : Type}
  (a b : PPType BaseType) :
  PPType BaseType :=
  let ⟨na, ta⟩ := a
  let ⟨nb, tb⟩ := b
  let N := max na nb
  ⟨N,
    PType.fun
      (PType.weaken (Nat.le_max_left na nb) ta)
      (PType.weaken (Nat.le_max_right na nb) tb)⟩

def beq
  {BaseType : Type}
  [DecidableEq BaseType]
  (a b : PPType BaseType) :
  Bool :=
  let ⟨na, ta⟩ := a
  let ⟨nb, tb⟩ := b
  let N := max na nb
  let ta' := PType.weaken (Nat.le_max_left na nb) ta
  let tb' := PType.weaken (Nat.le_max_right na nb) tb
  ta' == tb'

end PPType

/-- `Interp BaseType Const` gives a runtime value for each typed constant. -/
class Interp (BaseType : Type) (Const : Type) [BasedType BaseType] [Typed Const (PPType BaseType)] where
  interp : ∀ c : Const,
    let ⟨_, ty⟩ := (Typed.type (α := Const) (A := PPType BaseType) c);
    ∀ ctxTy : List Type, ∀ hctxTy,
    PType.type ty ctxTy hctxTy

inductive PExpr (Const BaseType : Type) [Typed Const (PPType BaseType)] : (n : Nat) → List (PType BaseType n) → PType BaseType n → Type where
| const (c : Const) (hc : (Typed.type c).1 ≤ n) {ctx} : PExpr Const BaseType n ctx (PType.weaken hc (Typed.type c).2)
| letE {ctx} {valT} {ty} (val : PExpr Const BaseType n ctx valT) (body : PExpr Const BaseType n (valT::ctx) ty) : PExpr Const BaseType n ctx ty
| var {ctx} (name : Fin ctx.length) : PExpr Const BaseType n ctx (ctx.get name)
| app {ctx} {argT} {ty} (f : PExpr Const BaseType n ctx (PType.fun argT ty)) (arg : PExpr Const BaseType n ctx argT) : PExpr Const BaseType n ctx ty
| lam {bodyT} {ctx} (varType : PType BaseType _) (body : PExpr Const BaseType n (varType::ctx) bodyT) : PExpr Const BaseType n ctx (.fun varType bodyT)

namespace Fin

def weaken {α : Type} {ctx ctx' : List α}
    (i : Fin ctx.length) : Fin (ctx ++ ctx').length :=
  ⟨i.val, by
    rw [List.length_append]
    exact Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)⟩

end Fin
namespace PExpr

def weaken
  {Const BaseType : Type}
  [Typed Const (PPType BaseType)] :
  {n : Nat} →
  {ctx ctx' : List (PType BaseType n)} →
  {ty : PType BaseType n} →
  PExpr Const BaseType n ctx ty →
  PExpr Const BaseType n (ctx ++ ctx') ty
| _, _, _, _, .const c hc =>
    .const c hc
| _, ctx, ctx', _, .var name =>
    cast
      (by simp [Fin.weaken])
      (PExpr.var (Const := Const) (ctx := ctx ++ ctx') (Fin.weaken (ctx' := ctx') name))
| _, _, ctx', _, .app f arg =>
    .app
      (weaken (ctx' := ctx') f)
      (weaken (ctx' := ctx') arg)
| _, _, ctx', _, .lam varType body =>
    .lam varType <|
      cast
        (by simp)
        (weaken (ctx' := ctx') body)
| _, _, ctx', _, .letE val body =>
    .letE
      (weaken (ctx' := ctx') val)
      (cast
        (by simp)
        (weaken (ctx' := ctx') body))

def weakenT
  {Const BaseType : Type}
  [Typed Const (PPType BaseType)] :
  {m n : Nat} →
  (h : m ≤ n) →
  {ctx : List (PType BaseType m)} →
  {ty : PType BaseType m} →
  PExpr Const BaseType m ctx ty →
  PExpr Const BaseType n
    (ctx.map (PType.weaken h))
    (PType.weaken h ty)
| _, _, h, ctx, _, .const c hc =>
    cast
      (by simp [PType.weaken_comp])
      (PExpr.const
        (ctx := ctx.map (PType.weaken h))
        c
        (Nat.le_trans hc h))
| m, n, h, ctx, _, .var name =>
    cast
      (by simp)
      (PExpr.var
        (Const := Const)
        (ctx := ctx.map (PType.weaken h))
        (Fin.cast (by simp) name))
| _, _, h, _, _, .app f arg =>
    .app
      (weakenT h f)
      (weakenT h arg)
| _, _, h, _, _, .lam varType body =>
    .lam (PType.weaken h varType) <|
      cast (by simp)
        (weakenT h body)
| _, _, h, _, _, .letE val body =>
    .letE
      (weakenT h val)
      (cast (by simp)
        (weakenT h body))

end PExpr

/-- DVector is a heterogeneous tuple indexed by a list of types -/
def DVector : List Type → Type
| [] => Unit
| α::l => α × DVector l

namespace DVector

def cons {L: List Type} {α : Type} : α → DVector L → DVector (α::L)
| a, dv => (a, dv)

def cons' {BaseType : Type} [BasedType BaseType] {n} {ctx : List (PType BaseType n)} {alpha : PType BaseType n} {ctxTy hctxTy} : alpha.type ctxTy hctxTy → DVector (ctx.map (·.type ctxTy hctxTy)) → DVector ((alpha::ctx).map (·.type ctxTy hctxTy))
| a, dv => (a, dv)

def push {L: Array Type} {α : Type} (dv : DVector L.toList) (a : α) : DVector (L.push α).toList :=
  match L with
  | ⟨[]⟩ => (a, ())
  | ⟨l::ls⟩ =>
      let (x, xs) := dv
      (x, push xs a)

def take {BaseType : Type} [BasedType BaseType] {m} {ctx : List (PType BaseType m)} {ctxTy hctxTy} : (n : Nat) → DVector (ctx.map (·.type ctxTy hctxTy)) → DVector ((ctx.take n).map (·.type ctxTy hctxTy))
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

def PExpr.interp
  {Const BaseType : Type}
  [BasedType BaseType]
  [Typed Const (PPType BaseType)]
  [Interp BaseType Const]
  {n : Nat}
  {ty : PType BaseType n}
  {ctxTy : List Type}
  {hctxTy : ctxTy.length = n}
  : {ctx : List (PType BaseType n)} →
    (e : PExpr Const BaseType n ctx ty) →
    DVector (ctx.map (·.type ctxTy hctxTy)) →
    ty.type ctxTy hctxTy
| _, .const c hc, _args =>
    let tyc : PPType BaseType := Typed.type c
    have hlen : (ctxTy.take (Typed.type c).1).length = (Typed.type c).1 := by
      simpa [List.length_take, hctxTy] using hc
    have hweaken : (PType.weaken hc tyc.2).type ctxTy hctxTy =
        tyc.2.type (ctxTy.take tyc.1) hlen := by
      simpa using
        (PType.type_weaken (m := tyc.1) (n := n) (h := hc)
          (ty := tyc.2) (ctxTy := ctxTy) (hctxTy := hctxTy))
    cast hweaken.symm
      (Interp.interp c (ctxTy.take tyc.1) hlen)
| _, .letE val body, args =>
    PExpr.interp body <|
      DVector.cons' (PExpr.interp val args) args
| _, .var name, args =>
    cast (by simp) <|
      DVector.get args (Fin.cast (by simp [List.length_map]) name)
| _, .app f arg, args =>
    (PExpr.interp f args) (PExpr.interp arg args)
| _, .lam varType body, args =>
    fun x =>
      PExpr.interp body <|
        DVector.cons' x args

inductive RawPExpr (Const BaseType : Type)
where
| var   (x : Name)
| app   (f a : RawPExpr Const BaseType)
| lam   (x : Name) (ty : PPType BaseType)
        (body : RawPExpr Const BaseType)
| letE  (x : Name)
        (v body : RawPExpr Const BaseType)
| const (c : Const)

namespace RawPExpr

def inferType
  {Const BaseType : Type}
  [DecidableEq BaseType]
  [Typed Const (PPType BaseType)]
  (ctxRaw : List (Name × PPType BaseType)) :
  RawPExpr Const BaseType → Option (PPType BaseType)
| .var x => do
    let i ← ctxRaw.findFinIdx? (fun y => y.1 == x)
    return (ctxRaw.map (·.2)).get (Fin.cast (by simp) i)
| .app f a => do
    let tf ← inferType ctxRaw f
    let ta ← inferType ctxRaw a
    match tf with
    | ⟨nf, .fun dom codom⟩ =>
        if PPType.beq ⟨nf, dom⟩ ta then
          return ⟨nf, codom⟩
        else
          none
    | _ =>
        none
| .lam x ty body => do
    let bodyT ← inferType ((x, ty) :: ctxRaw) body
    return PPType.fun ty bodyT
| .letE x v body => do
    let vT ← inferType ctxRaw v
    inferType ((x, vT) :: ctxRaw) body
| .const c =>
    some (Typed.type c)

end RawPExpr

abbrev PPExpr (Const BaseType : Type) [Typed Const (PPType BaseType)] :=
  Sigma fun n =>
  Sigma fun ctx : List (PType BaseType n) =>
  Sigma fun ty : PType BaseType n =>
    PExpr Const BaseType n ctx ty

namespace RawPExpr

def ctxN {BaseType : Type} : List (Name × PPType BaseType) → Nat
| [] => 0
| (_, ty) :: xs => max ty.1 (ctxN xs)

lemma le_ctxN
    {BaseType : Type}
    {ctxRaw : List (Name × PPType BaseType)}
    {y : Name × PPType BaseType}
    (hy : y ∈ ctxRaw) :
    y.2.1 ≤ ctxN ctxRaw := by
  induction ctxRaw with
  | nil =>
      cases hy
  | cons head tail ih =>
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hy) (Nat.le_max_right _ _)

def ctxTypes
  {BaseType : Type}
  (ctxRaw : List (Name × PPType BaseType)) :
  List (PType BaseType (ctxN ctxRaw)) :=
  ctxRaw.attach.map fun y =>
    PType.weaken
      (le_ctxN (ctxRaw := ctxRaw) (y := y.val) y.property)
      y.val.2.2

def ctxTypesAt
  {BaseType : Type}
  (ctxRaw : List (Name × PPType BaseType))
  (N : Nat)
  (hN : ctxN ctxRaw ≤ N) :
  List (PType BaseType N) :=
  ctxRaw.attach.map fun y =>
    PType.weaken
      (Nat.le_trans
        (le_ctxN (ctxRaw := ctxRaw) (y := y.val) y.property)
        hN)
      y.val.2.2

lemma ctxTypesAt_map_weaken
    {BaseType : Type}
    (ctxRaw : List (Name × PPType BaseType))
    {N M : Nat}
    (hN : ctxN ctxRaw ≤ N)
    (hNM : N ≤ M) :
    (ctxTypesAt ctxRaw N hN).map (PType.weaken hNM) =
      ctxTypesAt ctxRaw M (Nat.le_trans hN hNM) := by
  simp [ctxTypesAt, PType.weaken_comp]

lemma ctxTypesAt_proof_irrel
    {BaseType : Type}
    (ctxRaw : List (Name × PPType BaseType))
    {N : Nat}
    (h1 h2 : ctxN ctxRaw ≤ N) :
    ctxTypesAt ctxRaw N h1 = ctxTypesAt ctxRaw N h2 := by
  cases Subsingleton.elim h1 h2
  rfl

lemma ctxTypesAt_cons
    {BaseType : Type}
    (ctxRaw : List (Name × PPType BaseType))
    (x : Name) (ty : PPType BaseType)
    {N : Nat}
    (hN : ctxN ((x, ty) :: ctxRaw) ≤ N) :
    ctxTypesAt ((x, ty) :: ctxRaw) N hN =
      PType.weaken (Nat.le_trans (Nat.le_max_left _ _) hN) ty.2 ::
        ctxTypesAt ctxRaw N (Nat.le_trans (Nat.le_max_right _ _) hN) := by
  simp [ctxTypesAt]

/- `toPExprAux` returns a typed term at one global type-variable bound.
   `ctxOk` says the raw context fits in that bound. -/
private structure ElabResult
    (Const BaseType : Type)
    [Typed Const (PPType BaseType)]
    (ctxRaw : List (Name × PPType BaseType)) where
  bound : Nat
  ctxOk : ctxN ctxRaw ≤ bound
  outTy : PType BaseType bound
  term : PExpr Const BaseType bound (ctxTypesAt ctxRaw bound ctxOk) outTy

private def toPExprAux
  {Const BaseType : Type}
  [DecidableEq BaseType]
  [Typed Const (PPType BaseType)] :
  (ctxRaw : List (Name × PPType BaseType)) →
  RawPExpr Const BaseType →
  Option (ElabResult (Const := Const) (BaseType := BaseType) ctxRaw)
| ctxRaw, .const c =>
    let bound := max (Typed.type c).1 (ctxN ctxRaw)
    let ctxOk : ctxN ctxRaw ≤ bound := Nat.le_max_right _ _
    let ctx := ctxTypesAt ctxRaw bound ctxOk
    let tyOk : (Typed.type c).1 ≤ bound := Nat.le_max_left _ _
    some ⟨bound, ctxOk, PType.weaken tyOk (Typed.type c).2,
      PExpr.const (ctx := ctx) c tyOk⟩
| ctxRaw, .var x => do
    let i ← ctxRaw.findFinIdx? (fun y => y.1 == x)
    let bound := ctxN ctxRaw
    let ctx := ctxTypesAt ctxRaw bound (Nat.le_refl _)
    let idx : Fin ctx.length := Fin.cast (by simp [ctx, ctxTypesAt]) i
    some ⟨bound, Nat.le_refl _, ctx.get idx, .var idx⟩
| ctxRaw, .lam x ty body =>
    match toPExprAux ((x, ty) :: ctxRaw) body with
    | none => none
    | some bodyRes =>
        match bodyRes with
            | ⟨bodyBound, bodyCtxOk, bodyTy, bodyTerm⟩ =>
                match ty with
                | ⟨nArg, argT⟩ =>
                let bound := max (max nArg bodyBound) (ctxN ctxRaw)
                let argOk : nArg ≤ bound := le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
                let bodyOk : bodyBound ≤ bound := le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
                let ctxOk : ctxN ctxRaw ≤ bound := by omega
                let outerCtx := ctxTypesAt ctxRaw bound ctxOk
                let bodyCtxOk : ctxN ((x, ⟨nArg, argT⟩) :: ctxRaw) ≤ bound := by
                  dsimp [ctxN]
                  exact Nat.max_le.mpr ⟨argOk, ctxOk⟩
                let bodyTerm' : PExpr Const BaseType bound (PType.weaken argOk argT :: outerCtx) (PType.weaken bodyOk bodyTy) := by
                  simpa [outerCtx, ctxTypesAt_map_weaken, ctxTypesAt_cons, ctxTypesAt_proof_irrel, PType.weaken_comp]
                    using (PExpr.weakenT bodyOk bodyTerm)
                some ⟨bound, ctxOk, PType.fun (PType.weaken argOk argT) (PType.weaken bodyOk bodyTy),
                  PExpr.lam (PType.weaken argOk argT) bodyTerm'⟩
| ctxRaw, .app f a =>
    match toPExprAux ctxRaw f, toPExprAux ctxRaw a with
    | none, _ => none
    | _, none => none
    | some funRes, some argRes =>
        match funRes, argRes with
        | ⟨funBound, funCtxOk, funTy, funTerm⟩, ⟨argBound, argCtxOk, argTy, argTerm⟩ =>
            let bound := max funBound argBound
            let funOk : funBound ≤ bound := Nat.le_max_left _ _
            let argOk : argBound ≤ bound := Nat.le_max_right _ _
            let ctxOk : ctxN ctxRaw ≤ bound := by omega
            match funTy with
            | .fun dom codom =>
                let funTerm' : PExpr Const BaseType bound (ctxTypesAt ctxRaw bound ctxOk)
                    (PType.fun (PType.weaken funOk dom) (PType.weaken funOk codom)) := by
                  simpa [ctxTypesAt_map_weaken, ctxTypesAt_proof_irrel, PType.weaken_comp]
                    using (PExpr.weakenT funOk funTerm)
                let argTerm' : PExpr Const BaseType bound (ctxTypesAt ctxRaw bound ctxOk)
                    (PType.weaken argOk argTy) := by
                  simpa [ctxTypesAt_map_weaken, ctxTypesAt_proof_irrel, PType.weaken_comp]
                    using (PExpr.weakenT argOk argTerm)
                if argMatches : PType.weaken argOk argTy = PType.weaken funOk dom then
                  let argTerm'' : PExpr Const BaseType bound (ctxTypesAt ctxRaw bound ctxOk) (PType.weaken funOk dom) := by
                    simpa [argMatches] using argTerm'
                  some ⟨bound, ctxOk, PType.weaken funOk codom,
                    PExpr.app funTerm' argTerm''⟩
                else
                  none
            | _ => none
| ctxRaw, .letE x v body =>
    match toPExprAux ctxRaw v with
    | none => none
    | some valRes =>
        match valRes with
        | ⟨valBound, valCtxOk, valTy, valTerm⟩ =>
            let bodyRawCtx := (x, ⟨valBound, valTy⟩) :: ctxRaw
            match toPExprAux bodyRawCtx body with
            | none => none
            | some bodyRes =>
                match bodyRes with
                | ⟨bodyBound, bodyCtxOk, bodyTy, bodyTerm⟩ =>
                    let bound := max valBound bodyBound
                    let valOk : valBound ≤ bound := Nat.le_max_left _ _
                    let bodyOk : bodyBound ≤ bound := Nat.le_max_right _ _
                    let ctxOk : ctxN ctxRaw ≤ bound := by omega
                    let valTerm' : PExpr Const BaseType bound (ctxTypesAt ctxRaw bound ctxOk) (PType.weaken valOk valTy) := by
                      simpa [ctxTypesAt_map_weaken, ctxTypesAt_proof_irrel, PType.weaken_comp]
                        using (PExpr.weakenT valOk valTerm)
                    let bodyRawCtxOk : ctxN bodyRawCtx ≤ bound := by omega
                    have bodyCtxEq : ctxTypesAt bodyRawCtx bound bodyRawCtxOk = PType.weaken valOk valTy :: ctxTypesAt ctxRaw bound ctxOk := by
                      simpa [bodyRawCtx, ctxTypesAt_proof_irrel] using
                        (ctxTypesAt_cons (ctxRaw := ctxRaw) (x := x) (ty := ⟨valBound, valTy⟩) (N := bound) bodyRawCtxOk)
                    let bodyTerm' : PExpr Const BaseType bound (PType.weaken valOk valTy :: ctxTypesAt ctxRaw bound ctxOk) (PType.weaken bodyOk bodyTy) := by
                      simpa [ctxTypesAt_map_weaken, ctxTypesAt_proof_irrel, PType.weaken_comp, bodyCtxEq]
                        using (PExpr.weakenT bodyOk bodyTerm)
                    some ⟨bound, ctxOk, PType.weaken bodyOk bodyTy, PExpr.letE valTerm' bodyTerm'⟩

def toPExpr
  {Const BaseType : Type}
  [DecidableEq BaseType]
  [Typed Const (PPType BaseType)] :
  (ctxRaw : List (Name × PPType BaseType)) →
  RawPExpr Const BaseType →
  Option (PPExpr Const BaseType)
| ctxRaw, e => do
    let result ← toPExprAux (Const := Const) (BaseType := BaseType) ctxRaw e
    pure ⟨result.bound, ctxTypesAt ctxRaw result.bound result.ctxOk, result.outTy, result.term⟩

end RawPExpr

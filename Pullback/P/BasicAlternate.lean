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
    Interp.interp c ctxTy hctxTy
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

def toPExpr
  {Const BaseType : Type}
  [DecidableEq BaseType]
  [Typed Const (PPType BaseType)] :
  (ctxRaw : List (Name × PPType BaseType)) →
  RawPExpr Const BaseType →
  Option (PPExpr Const BaseType)
| ctxRaw, .const c =>
    some ⟨(Typed.type c).1, [], (Typed.type c).2, .const c⟩
| ctxRaw, .var x => do
    let i ← ctxRaw.findFinIdx? (fun y => y.1 == x)
    let ctx := ctxTypes ctxRaw
    let i' : Fin ctx.length := Fin.cast (by simp [ctx, ctxTypes]) i
    some ⟨ctxN ctxRaw, ctx, ctx.get i', .var i'⟩
| ctxRaw, .lam x ty body => do
    let ⟨nBody, ctxBody, bodyT, bodyE⟩ ←
      toPExpr ((x, ty) :: ctxRaw) body
    let ⟨nArg, argT⟩ := ty
    -- Need both argT and bodyT in same n.
    let N := max nArg nBody
    let argT' := PType.weaken (Nat.le_max_left nArg nBody) argT
    let bodyT' := PType.weaken (Nat.le_max_right nArg nBody) bodyT
    -- Also need expression/type-variable weakening on bodyE from nBody to N.
    none
| ctxRaw, .app f a => do
    let ⟨nf, ctxf, tf, ef⟩ ← toPExpr ctxRaw f
    let ⟨na, ctxa, ta, ea⟩ ← toPExpr ctxRaw a
    -- Need both expressions weakened to common N and same ctx.
    none
| ctxRaw, .letE x v body => do
    let ⟨nv, ctxv, vT, vE⟩ ← toPExpr ctxRaw v
    -- Need vT repackaged as PPType to extend raw ctx,
    -- then elaborate body under the extended context.
    let bodyRawCtx := (x, ⟨nv, vT⟩) :: ctxRaw
    let ⟨nb, ctxb, bodyT, bodyE⟩ ← toPExpr bodyRawCtx body
    -- Need vE and bodyE weakened/aligned to same n/context.
    none

end RawPExpr

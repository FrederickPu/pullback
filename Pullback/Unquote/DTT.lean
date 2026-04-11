import Lean
import Pullback.SSA.VarMap

open Lean

inductive PExpr where
| var (n : Name) : PExpr
| lam (binderName : Name) (binderType : PExpr) (body : PExpr) : PExpr
| forallE (binderName : Name) (binderType : PExpr) (body : PExpr) : PExpr
| app (f x : PExpr) : PExpr
| sort : PExpr
deriving DecidableEq

def PExpr.subst (name : Name) : PExpr → (replacement : PExpr) → PExpr
  | .var n, replacement => if n == name then replacement else .var n
  | .lam bn bt body, replacement =>
    if bn == name then .lam bn (bt.subst name replacement) body
    else .lam bn (bt.subst name replacement) (body.subst name replacement)
  | .forallE bn bt body, replacement =>
    if bn == name then .forallE bn (bt.subst name replacement) body
    else .forallE bn (bt.subst name replacement) (body.subst name replacement)
  | .app f x, replacement => .app (f.subst name replacement) (x.subst name replacement)
  | .sort, _ => .sort

partial def PExpr.betaReduce : PExpr → PExpr
  | .app (.lam name _ body) x => (body.subst name x).betaReduce
  | .app f x => .app f.betaReduce x.betaReduce
  | .forallE n t b => .forallE n t.betaReduce b.betaReduce
  | .lam n t b => .lam n t.betaReduce b.betaReduce
  | e => e

def PExpr.inferType (vars : Map Name PExpr) : PExpr → Option PExpr
| .var name => vars.get name
| .sort => some .sort
| .lam name type body => do
  let bodyType ← body.inferType (vars.push (name, type))
  return .forallE name type bodyType
| .forallE name type body => do
  let .sort ← type.inferType vars | none
  let .sort ← body.inferType (vars.push (name, type)) | none
  return .sort
| .app f x => do
  let .forallE name binderType bodyType ← f.inferType vars | none
  let xType ← x.inferType vars
  guard (xType == binderType)
  return bodyType.subst name x

/-! ## TypeWhnf -/

universe uu

inductive TypeWhnf : Type (uu + 1) where
  | ret : Type uu → TypeWhnf
  | ext : (dom : Type uu) → (dom → TypeWhnf) → TypeWhnf

namespace TypeWhnf
def toType : TypeWhnf.{uu} → Type uu
  | .ret T => T
  | .ext dom rest => (x : dom) → (rest x).toType
end TypeWhnf

/-! ## TypedVal: a value paired with its type -/

structure TypedVal where
  whnf : TypeWhnf.{uu}
  val : whnf.toType

/-! ## Contexts -/

def TyCtx := Map Name TypeWhnf.{uu}
def ICtx := Array (Name × TypedVal.{uu})

namespace ICtx
def empty : ICtx.{uu} := #[]
def push (ctx : ICtx.{uu}) (name : Name) (e : TypedVal.{uu}) : ICtx.{uu} :=
  Array.push ctx (name, e)
def get (ctx : ICtx.{uu}) (name : Name) : Option (TypedVal.{uu}) :=
  (ctx.reverse.find? (·.1 == name)).map (·.2)
end ICtx

/-! ## interp

Returns Sum:
- inl whnf : type mode result (a TypeWhnf)
- inr tv   : value mode result (a TypedVal)

isType flag determines which branch.
-/

partial def PExpr.interp (isType : Bool) (vars : Map Name PExpr)
    (tyCtx : TyCtx.{uu}) (ictx : ICtx.{uu})
    : PExpr → Option (TypeWhnf.{uu} ⊕ TypedVal.{uu})

  | .sort =>
    match isType with
    | true => none
    | false => none

  | .var name =>
    match isType with
    | true => (tyCtx.get name).map Sum.inl
    | false => (ictx.get name).map Sum.inr

  | .forallE name binderType body =>
    match isType with
    | true => do
      let .inl domWhnf ← PExpr.interp true vars tyCtx ictx binderType | none
      match domWhnf with
      | TypeWhnf.ret dom =>
        return Sum.inl (TypeWhnf.ext dom (fun v =>
          let vars' := vars.push (name, binderType)
          let tyCtx' := tyCtx.push (name, TypeWhnf.ret dom)
          let ictx' := ictx.push name ⟨TypeWhnf.ret dom, v⟩
          match PExpr.interp true vars' tyCtx' ictx' body with
          | some (.inl w) => w
          | _ => TypeWhnf.ret PUnit))
      | _ => none
    | false => none

  | .lam name binderType body =>
    match isType with
    | true => none
    | false => do
      let .inl domWhnf ← PExpr.interp true vars tyCtx ictx binderType | none
      match domWhnf with
      | TypeWhnf.ret dom =>
        let vars' := vars.push (name, binderType)
        let tyCtx' := tyCtx.push (name, TypeWhnf.ret dom)
        let whnf := TypeWhnf.ext dom (fun v =>
          let ictx' := ictx.push name ⟨TypeWhnf.ret dom, v⟩
          let bodyTy := match PExpr.inferType vars' body with
            | some te => te
            | none => PExpr.sort
          match PExpr.interp true vars' tyCtx' ictx' bodyTy with
          | some (.inl w) => w
          | _ => TypeWhnf.ret PUnit)
        let val : whnf.toType := fun v =>
          let ictx' := ictx.push name ⟨TypeWhnf.ret dom, v⟩
          match PExpr.interp false vars' tyCtx' ictx' body with
          | some (.inr tv) => cast sorry tv.val
          | _ => sorry
        return Sum.inr ⟨whnf, val⟩
      | _ => none

  | .app f x =>
    match isType with
    | true => do
      let .inl fWhnf ← PExpr.interp true vars tyCtx ictx f | none
      match fWhnf with
      | TypeWhnf.ext dom rest =>
        let .inr xTv ← PExpr.interp false vars tyCtx ictx x | none
        let xVal : dom := cast sorry xTv.val
        return Sum.inl (rest xVal)
      | _ => none
    | false => do
      let .inr fTv ← PExpr.interp false vars tyCtx ictx f | none
      match fTv.whnf with
      | TypeWhnf.ext dom rest =>
        let .inr xTv ← PExpr.interp false vars tyCtx ictx x | none
        let xVal : dom := cast sorry xTv.val
        let fVal : (v : dom) → (rest v).toType := cast sorry fTv.val
        return Sum.inr ⟨rest xVal, fVal xVal⟩
      | _ => none

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

/-! ## TypeTelescope

A telescope represents a dependent chain of types:
  (a : A) → (b : B a) → (c : C a b) → RetType a b c

Each entry's type can depend on the values of all previous entries.
The last entry is the return type.

This is used to represent types in the interpretation context,
since a constant like `Vector` has type `Type → Nat → Type`,
which is a telescope: [Type, (fun α => Nat), (fun α n => Type)].
-/

universe uu

inductive TypeWhnf : Type (uu + 1) where
  | ret : Type uu → TypeWhnf
  | ext : (dom : Type uu) → (dom → TypeWhnf) → TypeWhnf

def TypeWhnf.isFun : TypeWhnf.{uu} → Bool
| ret _ => false
| ext _ _ => true

def TypeWhnf.dom : (T : TypeWhnf.{uu}) → (hfun : T.isFun) → Type uu
| ret _, hfun => by simp [isFun] at hfun
| ext dom _, hfun => dom

def TypeWhnf.codom : (T : TypeWhnf.{uu}) → (hfun : T.isFun) → (T.dom hfun → TypeWhnf.{uu})
| ret _, hfun => by simp [isFun] at hfun
| ext _ rest, hfun => rest

def TypeWhnf.apply : (T : TypeWhnf.{uu}) → (hfun : T.isFun) → T.dom hfun → TypeWhnf.{uu} :=
  fun T hfun t => (T.codom hfun) t

def TyCtx := Map Name TypeWhnf.{uu}

/-! ## interpType

Interprets a PExpr type expression into a TypeTelescope.
The telescope captures dependency: for a forallE chain,
each codomain can depend on previous values.

For fully-applied types, the result is `.ret T` and
`.toType` gives the actual `Type uu`.
-/

partial def PExpr.interpType (vars : Map Name PExpr) (tyCtx : TyCtx.{uu})
    : PExpr → Option (TypeWhnf.{uu})
  | .sort => none
  | .var name => tyCtx.get name
  | .forallE _name binderType body => do
    let .ret dom ← binderType.interpType vars tyCtx | none
    some (.ext dom (fun _v =>
      -- For dependent types, v would be used to extend tyCtx
      -- For now, non-dependent: ignore v
      match body.interpType vars tyCtx with
      | some tel => tel
      | none => .ret PUnit))
  | .app f x => do
    let fTel ← f.interpType vars tyCtx
    let .ret xTy ← x.interpType vars tyCtx | none
    -- Apply x to f's telescope
    fTel.apply sorry (cast sorry xTy)
  | .lam _ _ _ => none

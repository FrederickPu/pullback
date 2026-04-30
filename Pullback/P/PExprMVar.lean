import Pullback.P.Basic
/-
PExprMvar: a variant of PExpr where opaque subterms are replaced by metavariables
that carry their already-known PType. Together with the `Aligns` predicate and the
`Aligns.inferType_eq` transport theorem, this lets you reduce
`(PExpr.app f a).inferType vars` by `rfl` to `some β` whenever you have
hypotheses establishing the types of `f` and `a`.

This file contains only the core definitions and theorems — no tactics.
The companion file `ReplaceMvarsTactic.lean` provides the `replace_mvars` tactic.
-/
import Lean

open Lean

-- ============================================================================
-- 1. PExprMvar: PExpr + an mvar constructor that carries a known type.
-- ============================================================================

inductive PExprMvar (Const BaseType : Type) [Typed Const (PType BaseType)] where
  | const : Const → PExprMvar Const BaseType
  | letE  (var : Name)
          (val : PExprMvar Const BaseType)
          (body : PExprMvar Const BaseType) : PExprMvar Const BaseType
  | var   (name : Name) : PExprMvar Const BaseType
  | app   (f : PExprMvar Const BaseType) (arg : PExprMvar Const BaseType) :
          PExprMvar Const BaseType
  | lam   (varName : Name) (varType : PType BaseType)
          (body : PExprMvar Const BaseType) : PExprMvar Const BaseType
  | mvar  (idx : Nat) (ty : PType BaseType) : PExprMvar Const BaseType
deriving DecidableEq

-- ============================================================================
-- 2. PExprMvar.inferType — identical to PExpr.inferType except the mvar case
--    returns its carried type. This is what makes things reduce by `rfl`.
-- ============================================================================

def PExprMvar.inferType {Const : Type} {BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType] [DecidableEq (PType BaseType)]
    (vars : VarMap BaseType) : PExprMvar Const BaseType → Option (PType BaseType)
  | .const c => some (Typed.type c)
  | .letE name val body =>
      (val.inferType vars).bind fun valType =>
        body.inferType (vars.push ⟨name, valType⟩)
  | .var name => Map.get vars name
  | .app f arg =>
      f.inferType vars |>.bind fun fType =>
      arg.inferType vars |>.bind fun argType =>
      fType.funDom? |>.bind fun dom =>
        if dom = argType then fType.funCodom? else none
  | .lam name varType body =>
      body.inferType (vars.push (name, varType)) |>.bind fun bodyType =>
        some (.fun varType bodyType)
  | .mvar _ ty => some ty

-- ============================================================================
-- 3. Aligns: structural correspondence between a PExpr and a PExprMvar
--    relative to a fixed top-level VarMap. The mvar leaf case requires a proof
--    that the original PExpr's inferred type matches the carried type.
-- ============================================================================

inductive Aligns {Const : Type} {BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType] [DecidableEq (PType BaseType)] :
    PExpr Const BaseType → PExprMvar Const BaseType → VarMap BaseType → Prop where
  | const   {c : Const} {vars} :
      Aligns (.const c) (.const c) vars
  | var     {n : Name} {vars} :
      Aligns (.var n) (.var n) vars
  | app     {f f' a a'} {vars} :
      Aligns f f' vars →
      Aligns a a' vars →
      Aligns (.app f a) (.app f' a') vars
  | lam     {n : Name} {τ : PType BaseType} {b b'} {vars} :
      Aligns b b' (vars.push (n, τ)) →
      Aligns (.lam n τ b) (.lam n τ b') vars
  | letE    {n : Name} {v v' body body'} {vars} {valType : PType BaseType}
            (hv : v.inferType vars = some valType) :
      Aligns v v' vars →
      Aligns body body' (vars.push (n, valType)) →
      Aligns (.letE n v body) (.letE n v' body') vars
  | mvar    {e : PExpr Const BaseType} {idx : Nat} {τ : PType BaseType} {vars}
            (hτ : e.inferType vars = some τ) :
      Aligns e (.mvar idx τ) vars

-- ============================================================================
-- 4. Transport theorem.
-- ============================================================================

theorem Aligns.inferType_eq
    {Const : Type} {BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType] [DecidableEq (PType BaseType)]
    {e : PExpr Const BaseType} {em : PExprMvar Const BaseType} {vars : VarMap BaseType} :
    Aligns e em vars → em.inferType vars = e.inferType vars := by
  intro h
  induction h with
  | const => rfl
  | var   => rfl
  | app _ _ ihf iha =>
      simp [PExpr.inferType, PExprMvar.inferType, ihf, iha]
  | lam _ ih =>
      simp [PExpr.inferType, PExprMvar.inferType, ih]
  | letE hv _ _ ihv ihbody =>
      simp [PExpr.inferType, PExprMvar.inferType, ihv, hv, ihbody]
  | mvar hτ =>
      simp [PExprMvar.inferType, hτ]

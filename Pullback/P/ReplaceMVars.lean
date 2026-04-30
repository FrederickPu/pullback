import Lean
import Pullback.P.PExprMVar

open Lean Elab Tactic Meta

namespace ReplaceMvars

/-- A collected hypothesis of the form `e.inferType vars = some τ`. -/
structure InferHyp where
  fvar  : FVarId
  pexpr : Expr  -- the `e` in `e.inferType vars = some τ`
  vars  : Expr  -- the `vars`
  ptype : Expr  -- the `τ`

/--
Try to interpret `ty` as `@PExpr.inferType _ _ _ vars e = @Option.some _ τ`.
On success returns `(e, vars, τ)`.
-/
def matchInferTypeEq? (ty : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let some (_, lhs, rhs) := ty.eq? | return none
  -- lhs should be an application of `PExpr.inferType`.
  let (lhsFn, lhsArgs) := lhs.getAppFnArgs
  unless lhsFn == ``PExpr.inferType do return none
  -- PExpr.inferType has signature
  --   (Const BaseType : Type) [Typed _ _] [DecidableEq _] [DecidableEq _] (vars : VarMap _) (e : PExpr _ _)
  -- so after full elaboration lhsArgs has 6 entries; vars is at index 4, e at index 5.
  -- But to be robust we just take the last two explicit args by position.
  if lhsArgs.size < 2 then return none
  let varsExpr := lhsArgs[lhsArgs.size - 2]!
  let pexprExpr := lhsArgs[lhsArgs.size - 1]!
  -- rhs should be `@Option.some α τ` with α = Option (PType BaseType).
  let (rhsFn, rhsArgs) := rhs.getAppFnArgs
  unless rhsFn == ``Option.some do return none
  if rhsArgs.size < 2 then return none
  let τ := rhsArgs[1]!  -- index 0 is the type, index 1 is the value
  return some (pexprExpr, varsExpr, τ)

/-- Collect every hypothesis `_.inferType vars = some _` whose `vars` is defeq to `targetVars`. -/
def collectInferHyps (targetVars : Expr) : TacticM (Array InferHyp) := do
  let mut out : Array InferHyp := #[]
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let some (e, v, τ) ← matchInferTypeEq? ty | continue
    unless ← isDefEq v targetVars do continue
    out := out.push { fvar := ldecl.fvarId, pexpr := e, vars := v, ptype := τ }
  return out

/--
A leaf record: a subterm of the original PExpr that got replaced by a mvar,
together with the hypothesis FVar that justifies it.
-/
structure MvarLeaf where
  origPExpr : Expr  -- subterm of the original PExpr
  hyp       : FVarId
  vars      : Expr
  ptype     : Expr
  idx       : Nat

/--
Walk a Lean-level Expr `e` representing a `PExpr Const BaseType` and produce a
PExprMvar Lean Expr where each subterm matching some collected hypothesis is
replaced by `PExprMvar.mvar idx τ`. Records the (subterm, hyp) pairs.
-/
partial def buildPExprMvar (hyps : Array InferHyp) (e : Expr) :
    StateRefT (Array MvarLeaf) MetaM Expr := do
  -- Try to match against any collected hypothesis.
  for h in hyps do
    if ← isDefEq e h.pexpr then
      let st ← get
      let idx := st.size
      let leaf : MvarLeaf := { origPExpr := e, hyp := h.fvar, vars := h.vars, ptype := h.ptype, idx := idx }
      set (st.push leaf)
      -- Build `PExprMvar.mvar idx τ` with the concrete `Const`/`BaseType`
      -- parameters from the source expression so typeclass synthesis stays local.
      let eType ← inferType e
      let (eTypeFn, eTypeArgs) := eType.getAppFnArgs
      unless eTypeFn == ``PExpr do
        throwError "replace_mvars: expected a PExpr-typed subterm{indentExpr e}"
      unless eTypeArgs.size ≥ 2 do
        throwError "replace_mvars: malformed PExpr type{indentExpr eType}"
      let constTy := eTypeArgs[0]!
      let baseTy := eTypeArgs[1]!
      return ← mkAppOptM ``PExprMvar.mvar
        #[some constTy, some baseTy, none, some (mkNatLit idx), some h.ptype]
  -- Otherwise recurse on the head constructor.
  let (fn, args) := e.getAppFnArgs
  match fn with
  | ``PExpr.const =>
      -- args = #[Const, BaseType, _typedInst, c]
      if h : args.size = 4 then
        mkAppM ``PExprMvar.const #[args[3]]
      else
        throwError "replace_mvars: PExpr.const has unexpected arg count{indentExpr e}"
  | ``PExpr.var =>
      -- args = #[Const, BaseType, _typedInst, name]
      if h : args.size = 4 then
        mkAppM ``PExprMvar.var #[args[3]]
      else
        throwError "replace_mvars: PExpr.var has unexpected arg count{indentExpr e}"
  | ``PExpr.app =>
      -- args = #[Const, BaseType, _typedInst, f, a]
      if h : args.size = 5 then
        let f' ← buildPExprMvar hyps args[3]
        let a' ← buildPExprMvar hyps args[4]
        mkAppM ``PExprMvar.app #[f', a']
      else
        throwError "replace_mvars: PExpr.app has unexpected arg count{indentExpr e}"
  | ``PExpr.lam =>
      -- args = #[Const, BaseType, _typedInst, name, ptype, body]
      if h : args.size = 6 then
        let body' ← buildPExprMvar hyps args[5]
        mkAppM ``PExprMvar.lam #[args[3], args[4], body']
      else
        throwError "replace_mvars: PExpr.lam has unexpected arg count{indentExpr e}"
  | ``PExpr.letE =>
      -- args = #[Const, BaseType, _typedInst, name, val, body]
      if h : args.size = 6 then
        let val' ← buildPExprMvar hyps args[4]
        let body' ← buildPExprMvar hyps args[5]
        mkAppM ``PExprMvar.letE #[args[3], val', body']
      else
        throwError "replace_mvars: PExpr.letE has unexpected arg count{indentExpr e}"
  | _ =>
      throwError "replace_mvars: don't know how to translate{indentExpr e}\nto a PExprMvar"

/--
Build a term-mode proof of `Aligns origPExpr em vars`.
Recurses on origPExpr and em together, using the leaves table to discharge
mvar slots and the appropriate `Aligns` constructor for structural slots.
-/
partial def buildAlignsProof (origPExpr em : Expr) (leaves : Array MvarLeaf) :
    MetaM Expr := do
  -- mvar leaf?
  for leaf in leaves do
    if ← isDefEq origPExpr leaf.origPExpr then
      let (emFn, _) := em.getAppFnArgs
      if emFn == ``PExprMvar.mvar then
        let origTy ← inferType origPExpr
        let (origTyFn, origTyArgs) := origTy.getAppFnArgs
        unless origTyFn == ``PExpr do
          throwError "replace_mvars: expected a PExpr-typed subterm{indentExpr origPExpr}"
        unless origTyArgs.size ≥ 2 do
          throwError "replace_mvars: malformed PExpr type{indentExpr origTy}"
        let constTy := origTyArgs[0]!
        let baseTy := origTyArgs[1]!
        return ← mkAppOptM ``Aligns.mvar
          #[some constTy, some baseTy, none, none, none,
            some origPExpr, some (mkNatLit leaf.idx), some leaf.ptype, some leaf.vars,
            some (mkFVar leaf.hyp)]
  -- Structural recursion.
  let (peFn, peArgs) := origPExpr.getAppFnArgs
  let (emFn, emArgs) := em.getAppFnArgs
  match peFn, emFn with
  | ``PExpr.const, ``PExprMvar.const =>
      mkAppM ``Aligns.const #[]
  | ``PExpr.var, ``PExprMvar.var =>
      mkAppM ``Aligns.var #[]
  | ``PExpr.app, ``PExprMvar.app =>
      if hp : peArgs.size = 5 then
        if hm : emArgs.size = 5 then
          let pf ← buildAlignsProof peArgs[3] emArgs[3] leaves
          let pa ← buildAlignsProof peArgs[4] emArgs[4] leaves
          mkAppM ``Aligns.app #[pf, pa]
        else throwError "replace_mvars: bad PExprMvar.app shape"
      else throwError "replace_mvars: bad PExpr.app shape"
  | ``PExpr.lam, ``PExprMvar.lam =>
      if hp : peArgs.size = 6 then
        if hm : emArgs.size = 6 then
          let pb ← buildAlignsProof peArgs[5] emArgs[5] leaves
          mkAppM ``Aligns.lam #[pb]
        else throwError "replace_mvars: bad PExprMvar.lam shape"
      else throwError "replace_mvars: bad PExpr.lam shape"
  | ``PExpr.letE, ``PExprMvar.letE =>
      if hp : peArgs.size = 6 then
        if hm : emArgs.size = 6 then
          let pv ← buildAlignsProof peArgs[4] emArgs[4] leaves
          let pb ← buildAlignsProof peArgs[5] emArgs[5] leaves
          -- find an `hv : peArgs[4].inferType vars = some _` in context.
          let mut hvOpt : Option Expr := none
          for ldecl in (← getLCtx) do
            if ldecl.isImplementationDetail then continue
            let ty ← instantiateMVars ldecl.type
            let some (e, _, _) ← matchInferTypeEq? ty | continue
            if ← isDefEq e peArgs[4] then
              hvOpt := some (mkFVar ldecl.fvarId)
              break
          match hvOpt with
          | some hv => mkAppM ``Aligns.letE #[hv, pv, pb]
          | none    =>
              throwError "replace_mvars: no `inferType` hypothesis for letE val{indentExpr peArgs[4]}"
        else throwError "replace_mvars: bad PExprMvar.letE shape"
      else throwError "replace_mvars: bad PExpr.letE shape"
  | _, _ =>
      throwError "replace_mvars: structural mismatch between{indentExpr origPExpr}\nand{indentExpr em}"

/--
Find the first occurrence of `PExpr.inferType _ _ _ vars e` in the goal,
returning `(vars, e)`.
-/
def findInferTypeInGoal (goal : Expr) : Option (Expr × Expr) := do
  let sub ← goal.find? fun sub =>
    let (fn, args) := sub.getAppFnArgs
    fn == ``PExpr.inferType && args.size ≥ 2
  let args := sub.getAppArgs
  some (args[args.size - 2]!, args[args.size - 1]!)

elab "replace_mvars" : tactic => do
  let goalType ← getMainTarget
  let some (targetVars, targetPExpr) := findInferTypeInGoal goalType
    | throwError "replace_mvars: could not find a `PExpr.inferType _ _` subterm in the goal"
  let hyps ← collectInferHyps targetVars
  if hyps.isEmpty then
    throwError "replace_mvars: no hypotheses of the form `_.inferType <vars> = some _` found"
  let (em, leaves) ← (buildPExprMvar hyps targetPExpr).run #[]
  let alignsProof ← buildAlignsProof targetPExpr em leaves
  -- Aligns.inferType_eq alignsProof : PExprMvar.inferType vars em = PExpr.inferType vars targetPExpr
  -- We rewrite right-to-left: replace `PExpr.inferType vars targetPExpr` with `PExprMvar.inferType vars em`.
  let eqProof ← mkAppM ``Aligns.inferType_eq #[alignsProof]
  let symmEq ← mkAppM ``Eq.symm #[eqProof]
  let rwResult ← (← getMainGoal).rewrite goalType symmEq
  let newGoal ← (← getMainGoal).replaceTargetEq rwResult.eNew rwResult.eqProof
  replaceMainGoal (newGoal :: rwResult.mvarIds)
  -- Try rfl.
  try
    let g ← getMainGoal
    g.refl
    replaceMainGoal []
  catch _ => pure ()

end ReplaceMvars

-- ============================================================================
-- Tests for the replace_mvars tactic
-- ============================================================================

section ReplaceMvarsTests

inductive TBT | A | B | C deriving DecidableEq

instance : BasedType TBT where
  valueType | .A => Unit | .B => Bool | .C => Nat

inductive TConst | dummy

instance : Typed TConst (PType TBT) where
  type | .dummy => .ofBase .A

abbrev TVMT := VarMap TBT

-- Test 1: simple app
-- replace_mvars proves (f a).inferType vars = some β
-- from hf : f.inferType vars = some (α → β) and ha : a.inferType vars = some α.
-- Without the tactic, rfl fails because f and a are opaque.
theorem test_replace_mvars_app
    (vars : TVMT)
    (f a : PExpr TConst TBT)
    (α β : PType TBT)
    (hf : f.inferType vars = some (.fun α β))
    (ha : a.inferType vars = some α) :
    (f.app a).inferType vars = some β := by
  replace_mvars
  simp [PExprMvar.inferType, PType.funDom?, PType.funCodom?]

-- Test 2: nested app  f a b : γ  from individual types of f, a, b
theorem test_replace_mvars_nested_app
    (vars : TVMT)
    (f a b : PExpr TConst TBT)
    (α β γ : PType TBT)
    (hf : f.inferType vars = some (.fun α (.fun β γ)))
    (ha : a.inferType vars = some α)
    (hb : b.inferType vars = some β) :
    ((f.app a).app b).inferType vars = some γ := by
  replace_mvars
  simp [PExprMvar.inferType, PType.funDom?, PType.funCodom?]

-- Test 3: hypothesis about an intermediate subterm
-- replace_mvars uses hfa directly, replacing the whole (f a) with one mvar
theorem test_replace_mvars_intermediate_hyp
    (vars : TVMT)
    (f a b : PExpr TConst TBT)
    (β γ : PType TBT)
    (hfa : (f.app a).inferType vars = some (.fun β γ))
    (hb  : b.inferType vars = some β) :
    ((f.app a).app b).inferType vars = some γ := by
  replace_mvars
  simp [PExprMvar.inferType, PType.funDom?, PType.funCodom?]

end ReplaceMvarsTests

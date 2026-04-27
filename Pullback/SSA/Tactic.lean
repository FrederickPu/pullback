import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Simp
import Lean.Meta.Tactic.Replace
import Lean.Meta.Tactic.Rewrite

open Lean Lean.Elab.Tactic Lean.Meta

def applyToAllHyps (goal : MVarId) (f : MVarId → FVarId → MetaM (MVarId × Bool)) : MetaM (MVarId × Bool) := do
  let mut goal := goal
  let mut progress := false
  let hypNames ← goal.withContext do
    return (← getLCtx).decls.toArray.filterMap (fun d => d.map (·.userName))
  for hypName in hypNames do
    let lctx ← goal.withContext getLCtx
    let some decl := lctx.findFromUserName? hypName | continue
    if decl.isImplementationDetail then continue
    let (newGoal, p) ← f goal decl.fvarId
    goal := newGoal
    progress := progress || p
  return (goal, progress)

syntax (name := bindSomeElim) "bind_some_elim" : tactic

def matchBindSome (goal : MVarId) (fvarId : FVarId) : MetaM (Option Name) :=
  goal.withContext do
    let decl ← fvarId.getDecl
    let ty ← inferType decl.toExpr
    let some (_, lhs, rhs) := ty.eq? | return none
    unless lhs.getAppFn.isConstOf ``Option.bind do return none
    unless rhs.isAppOf ``Option.some do return none
    let args := lhs.getAppArgs
    let n := args.size
    let rawName := match args[n - 1]! with
      | .lam name _ _ _ => name
      | _ => `val
    let binderName :=
      if rawName.isInternal || rawName.hasMacroScopes then `dolift else rawName
    return some binderName

def applyBindSomeIff (goal : MVarId) (hypId : FVarId) : MetaM (MVarId × FVarId) :=
  goal.withContext do
    let hypExpr := .fvar hypId
    let hypTy   ← inferType hypExpr
    let some (_, lhs, rhs) := hypTy.eq? | throwError "not an eq"
    let args := lhs.getAppArgs
    let α_1  := args[0]!
    let α    := args[1]!
    let x    := args[2]!
    let f    := args[3]!
    let b    := rhs.getAppArgs[1]!
    let iffConst ← mkAppOptM ``Option.bind_eq_some_iff
      #[some α, some b, some α_1, some x, some f]
    let newVal  ← mkAppM ``Iff.mp #[iffConst, hypExpr]
    let newTy   ← inferType newVal
    let hypName := (← goal.getDecl).lctx.get! hypId |>.userName
    let newGoal ← goal.assert hypName newTy newVal
    let (newHypId, newGoal) ← newGoal.intro1P
    let newGoal ← newGoal.tryClear hypId
    return (newGoal, newHypId)

def destructBindSome (goal : MVarId) (hypId : FVarId) (witName : Name) (hWitName : Name) (hypName : Name) : MetaM MVarId :=
  goal.withContext do
    let hypExpr := .fvar hypId
    let wit     ← mkAppM ``Exists.choose #[hypExpr]
    let spec    ← mkAppM ``Exists.choose_spec #[hypExpr]
    let hWit    ← mkAppM ``And.left #[spec]
    let hyp'    ← mkAppM ``And.right #[spec]
    let witTy   ← inferType wit
    let hWitTy  ← inferType hWit
    let hypTy'  ← inferType hyp'
    let g ← goal.define witName witTy wit
    let (witFVar, g) ← g.intro1P
    let witExpr := .fvar witFVar
    let hWit'   := hWit.replace  (fun e => if e == wit then some witExpr else none)
    let hWitTy' := hWitTy.replace (fun e => if e == wit then some witExpr else none)
    let hyp''   := hyp'.replace  (fun e => if e == wit then some witExpr else none)
    let hypTy'' := hypTy'.replace (fun e => if e == wit then some witExpr else none)
    let g ← g.assert hWitName hWitTy' hWit'
    let (_, g) ← g.intro1P
    let g ← g.assert hypName hypTy'' hyp''
    let (_, g) ← g.intro1P
    let g ← g.clearValue witFVar
    let g ← g.tryClear hypId
    return g

def bindSomeElimHyp (goal : MVarId) (fvarId : FVarId) : MetaM (MVarId × Bool) := do
  let hypName := (← goal.withContext fvarId.getDecl).userName
  let mut goal := goal
  let mut fvarId := fvarId
  let mut progress := false
  while true do
    let some binderName ← matchBindSome goal fvarId | break
    let (newGoal, newHypId) ← applyBindSomeIff goal fvarId
    let hWitName := Name.mkSimple s!"h{binderName}"
    goal ← destructBindSome newGoal newHypId binderName hWitName hypName
    let lctx ← goal.withContext getLCtx
    let some decl := lctx.findFromUserName? hypName | break
    fvarId := decl.fvarId
    progress := true
  return (goal, progress)

@[tactic bindSomeElim]
def evalBindSomeElim : Tactic := fun _ => do
  let goal ← getMainGoal
  let (newGoal, progress) ← applyToAllHyps goal bindSomeElimHyp
  replaceMainGoal [newGoal]
  unless progress do
    logWarning "bind_some_elim: no hypothesis of the form `f >>= g = some _` found"

syntax (name := isSomeElim) "is_some_elim" : tactic

def matchIsSome (goal : MVarId) (fvarId : FVarId) : MetaM (Option Name) :=
  goal.withContext do
    let decl ← fvarId.getDecl
    let ty ← inferType decl.toExpr
    let some (_, lhs, rhs) := ty.eq? | return none
    unless rhs.isConstOf ``Bool.true do return none
    unless lhs.getAppFn.isConstOf ``Option.isSome do return none
    let optArg := lhs.getAppArgs[1]!
    match optArg with
      | .fvar id => do
        let lctx ← getLCtx
        return some (lctx.get! id).userName
      | _ => return some `a

def applyIsSomeIff (goal : MVarId) (hypId : FVarId) : MetaM (MVarId × FVarId) := do
  goal.withContext do
    let hypExpr := .fvar hypId
    let hypTy   ← inferType hypExpr
    let some (_, lhs, _) := hypTy.eq? | throwError "not an eq"
    let optArg  := lhs.getAppArgs[1]!
    let iffConst ← mkAppOptM ``Option.isSome_iff_exists #[none, some optArg]
    let newVal  ← mkAppM ``Iff.mp #[iffConst, hypExpr]
    let newTy   ← inferType newVal
    let hypName := (← goal.withContext getLCtx).get! hypId |>.userName
    let newGoal ← goal.assert hypName newTy newVal
    let (newHypId, newGoal) ← newGoal.intro1P
    let newGoal ← newGoal.tryClear hypId
    return (newGoal, newHypId)

def destructIsSome (goal : MVarId) (hypId : FVarId) (witName : Name) (hypName : Name) : MetaM MVarId :=
  goal.withContext do
    let hypExpr := .fvar hypId
    let wit     ← mkAppM ``Exists.choose #[hypExpr]
    let spec    ← mkAppM ``Exists.choose_spec #[hypExpr]
    let witTy   ← inferType wit
    let specTy  ← inferType spec
    let g ← goal.define witName witTy wit
    let (witFVar, g) ← g.intro1P
    let witExpr := .fvar witFVar
    let spec'   := spec.replace  (fun e => if e == wit then some witExpr else none)
    let specTy' := specTy.replace (fun e => if e == wit then some witExpr else none)
    let g ← g.assert hypName specTy' spec'
    let (_, g) ← g.intro1P
    let g ← g.clearValue witFVar
    let g ← g.tryClear hypId
    return g

def isSomeElimHyp (goal : MVarId) (fvarId : FVarId) : MetaM (MVarId × Bool) := do
  let some witName ← matchIsSome goal fvarId | return (goal, false)
  let hypName := (← goal.withContext fvarId.getDecl).userName
  let (newGoal, newHypId) ← applyIsSomeIff goal fvarId
  let witName' := Name.mkSimple s!"{witName}'"
  let goal ← destructIsSome newGoal newHypId witName' hypName
  return (goal, true)

@[tactic isSomeElim]
def evalIsSomeElim : Tactic := fun _ => do
  let goal ← getMainGoal
  let (newGoal, progress) ← applyToAllHyps goal isSomeElimHyp
  replaceMainGoal [newGoal]
  unless progress do
    logWarning "is_some_elim: no hypothesis of the form `x.isSome = true` found"

syntax (name := optionElim) "option_elim" : tactic

def rewriteBindEqBindHyp (goal : MVarId) (fvarId : FVarId) : MetaM MVarId := do
  let bindEqBind ← mkConstWithFreshMVarLevels ``Option.bind_eq_bind
  let ty ← goal.withContext (inferType (.fvar fvarId))
  let some result ← observing? (goal.rewrite ty bindEqBind) | return goal
  let replaceResult ← goal.withContext (goal.replaceLocalDecl fvarId result.eNew result.eqProof)
  return replaceResult.mvarId

-- Split a hypothesis `h : A ∧ B` into `h : A` and a fresh `h_right : B`.
-- Returns the new goal and true if progress was made.
def splitAndHyp (goal : MVarId) (fvarId : FVarId) : MetaM (MVarId × Bool) :=
  goal.withContext do
    let decl ← fvarId.getDecl
    let ty   ← inferType decl.toExpr
    let some (_, _) := ty.and? | return (goal, false)
    let hypExpr := .fvar fvarId
    let lhs ← mkAppM ``And.left  #[hypExpr]
    let rhs ← mkAppM ``And.right #[hypExpr]
    let lhsTy ← inferType lhs
    let rhsTy ← inferType rhs
    -- replace the original hyp with its left component under the same name
    let g ← goal.assert decl.userName lhsTy lhs
    let (_, g) ← g.intro1P
    let g ← g.tryClear fvarId
    -- add the right component as a fresh name
    let rhsName := Name.mkSimple s!"{decl.userName}_right"
    let g ← g.assert rhsName rhsTy rhs
    let (_, g) ← g.intro1P
    return (g, true)

def optionElimHyp (goal : MVarId) (fvarId : FVarId) : MetaM (MVarId × Bool) := do
  let hypName := (← goal.withContext fvarId.getDecl).userName
  let goal ← rewriteBindEqBindHyp goal fvarId
  -- re-lookup fresh fvarId by name after rewrite
  let lctx ← goal.withContext getLCtx
  let some decl := lctx.findFromUserName? hypName | return (goal, false)
  let (goal, p1) ← isSomeElimHyp goal decl.fvarId
  let lctx ← goal.withContext getLCtx
  let some decl := lctx.findFromUserName? hypName | return (goal, p1)
  let (goal, p2) ← bindSomeElimHyp goal decl.fvarId
  return (goal, p1 || p2)

@[tactic optionElim]
def evalOptionElim : Tactic := fun _ => do
  let mut progress := true
  while progress do
    evalTactic (← `(tactic| try simp only [reduceIte, Option.ite_none_right_eq_some, Option.ite_none_left_eq_some] at *))
    let goal ← getMainGoal
    let (newGoal, p1) ← applyToAllHyps goal splitAndHyp
    replaceMainGoal [newGoal]
    let goal ← getMainGoal
    let (newGoal, p2) ← applyToAllHyps goal optionElimHyp
    replaceMainGoal [newGoal]
    progress := p1 || p2

theorem womp (a c : Option Nat) (b : Nat → Option Nat) (p : Nat → Prop) :
    (do let x ← a; some <| p (← b x)) = some True →
    c.isSome →
    (do let x ← a; let y ← c; some <| p (← b x)) = some True := by
  intro h h1
  option_elim
  grind

theorem test_ite_symbolic_cond
    (cond : Prop) [Decidable cond] (x t : Nat)
    (f : Nat → Option Nat)
    (h : (do let v ← (if cond then some x else none); f v) = some t) :
    cond := by
  option_elim
  grind

theorem test_ite_then_bind
    (cond : Prop) [Decidable cond] (a : Option Nat) (f : Nat → Option Nat)
    (t : Nat)
    (h : (do let x ← (if cond then a else none); f x) = some t) :
    cond ∧ ∃ x, a = some x ∧ f x = some t := by
  option_elim
  grind

theorem test_real_shape
    (vars : List (String × Nat)) (var : String) (val : Nat)
    (lookup : String → List (String × Nat) → Option Nat)
    (compute : Nat → Option Nat) (t : Nat)
    (h : (do
      let a ← lookup var vars
      if a = val then compute a else none) = some t) :
    ∃ a, lookup var vars = some a ∧ a = val ∧ compute a = some t := by
  option_elim
  grind

-- Test: the ite is inside the bind body, and the true branch contains another bind.
-- Pipeline:
--   outer bind destructs    →  hx : a = some x,  h : (if cond x then b x >>= c else none) = some t
--   ite_none_right_eq_some  →  h : cond x ∧ (b x >>= c) = some t
--   splitAndHyp             →  h : cond x,  h_right : (b x >>= c) = some t
--   inner bind destructs    →  hy : b x = some y,  h_right : c y = some t
theorem test_bind_ite_bind
    (a : Option Nat) (b : Nat → Option Nat) (c : Nat → Option Nat)
    (cond : Nat → Prop) [DecidablePred cond] (t : Nat)
    (h : (do
      let x ← a
      if cond x then do let y ← b x; c y else none) = some t) :
    ∃ x, a = some x ∧ cond x ∧ ∃ y, b x = some y ∧ c y = some t := by
  option_elim
  grind

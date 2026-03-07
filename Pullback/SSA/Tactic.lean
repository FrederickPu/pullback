import Mathlib

open Lean Lean.Elab.Tactic Lean.Meta

syntax (name := bindSomeElim) "bind_some_elim" : tactic

/-- Check if a local decl is of the form `Option.bind _ _ = some _` and return binder name -/
def matchBindSome (decl : LocalDecl) : MetaM (Option Name) := do
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
    let s := rawName.toString
    if s.startsWith "__" || s.startsWith "_@" then `dolift else rawName
  return some binderName

def applyBindSomeIff (goal : MVarId) (hypId : FVarId) : MetaM (MVarId × FVarId) := do
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
    let (newHypId, newGoal) ← newGoal.intro1
    let newGoal ← newGoal.clear hypId
    return (newGoal, newHypId)  -- return the new FVarId

def destructBindSome (goal : MVarId) (hypId : FVarId) (witName : Name) (hWitName : Name) (hypName : Name) : MetaM MVarId := do
  goal.withContext do
    let hypExpr := .fvar hypId
    let wit     ← mkAppM ``Exists.choose #[hypExpr]
    let spec    ← mkAppM ``Exists.choose_spec #[hypExpr]
    let hWit    ← mkAppM ``And.left #[spec]
    let hyp'    ← mkAppM ``And.right #[spec]
    let witTy   ← inferType wit
    let hWitTy  ← inferType hWit
    let hypTy'  ← inferType hyp'
    -- use define (let binding) so witFVar is opaque to subsequent terms
    let g ← goal.define witName witTy wit
    let (witFVar, g) ← g.intro1P
    let witExpr := .fvar witFVar
    -- now replace all Exists.choose references with the let-bound witFVar
    let hWit'  := hWit.replace  (fun e => if e == wit then some witExpr else none)
    let hWitTy' := hWitTy.replace (fun e => if e == wit then some witExpr else none)
    let hyp''  := hyp'.replace  (fun e => if e == wit then some witExpr else none)
    let hypTy'' := hypTy'.replace (fun e => if e == wit then some witExpr else none)
    let g ← g.assert hWitName hWitTy' hWit'
    let (_, g) ← g.intro1P
    let g ← g.assert hypName hypTy'' hyp''
    let (_, g) ← g.intro1P
    -- clearbody witFVar makes x opaque (removes := h✝.choose)
    let g ← g.clearValue witFVar
    -- now h✝ has no dependents, can clear it
    let g ← g.tryClear hypId
    return g

/-- Process all hypotheses in the goal, peeling one bind layer each. Returns (newGoal, progress) -/
def bindSomeElimStep (goal : MVarId) : MetaM (MVarId × Bool) := do
  goal.withContext do
    let lctx ← getLCtx
    let mut goal := goal
    let mut progress := false
    for decl in lctx do
      if decl.isImplementationDetail then continue
      let mut hypName := decl.userName
      while true do
        let lctx ← goal.withContext getLCtx
        let some decl := lctx.findFromUserName? hypName | break
        let some binderName ← goal.withContext (matchBindSome decl) | break
        let (newGoal, newHypId) ← applyBindSomeIff goal decl.fvarId
        let hWitName := Name.mkSimple s!"h{binderName}"
        goal ← destructBindSome newGoal newHypId binderName hWitName hypName
        progress := true
    return (goal, progress)

@[tactic bindSomeElim]
def evalBindSomeElim : Tactic := fun _ => do
  let goal ← getMainGoal
  let (newGoal, progress) ← bindSomeElimStep goal
  replaceMainGoal [newGoal]
  unless progress do
    logWarning "bind_some_elim: no hypothesis of the form `f >>= g = some _` found"


syntax (name := isSomeElim) "is_some_elim" : tactic

def matchIsSome (goal : MVarId) (decl : LocalDecl) : MetaM (Option Name) := do
  goal.withContext do
    let ty ← inferType decl.toExpr
    let some (_, lhs, rhs) := ty.eq? | return none
    unless rhs.isConstOf ``Bool.true do return none
    unless lhs.getAppFn.isConstOf ``Option.isSome do return none
    let optArg := lhs.getAppArgs[1]!
    match optArg with
      | .fvar id => do
        let lctx ← getLCtx
        return lctx.get! id |>.userName
      | _ => pure `a

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
    let newGoal ← newGoal.clear hypId
    return (newGoal, newHypId)

def destructIsSome (goal : MVarId) (hypId : FVarId) (witName : Name) (hypName : Name) : MetaM MVarId := do
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

def isSomeElimStep (goal : MVarId) : MetaM (MVarId × Bool) := do
  goal.withContext do
    let lctx ← getLCtx
    let mut goal := goal
    let mut progress := false
    for decl in lctx do
      if decl.isImplementationDetail then continue
      let some witName ← matchIsSome goal decl | continue
      let (newGoal, newHypId) ← applyIsSomeIff goal decl.fvarId
      let witName' := Name.mkSimple s!"{witName}'"
      goal ← destructIsSome newGoal newHypId witName' decl.userName
      progress := true
    return (goal, progress)

@[tactic isSomeElim]
def evalIsSomeElim : Tactic := fun _ => do
  let goal ← getMainGoal
  let (newGoal, progress) ← isSomeElimStep goal
  replaceMainGoal [newGoal]
  unless progress do
    logWarning "is_some_elim: no hypothesis of the form `x.isSome = true` found"

theorem womp (a c : Option Nat) (b : Nat → Option Nat) (p : Nat → Prop) :
    (do let x ← a; some <| p (← b x)) = some True →
    c.isSome →
    (do let x ← a; let y ← c; some <| p (← b x)) = some True := by
  intro h h1
  rewrite [Option.bind_eq_bind] at *
  is_some_elim
  bind_some_elim
  -- bind_some_elim
  grind

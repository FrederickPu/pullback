import Mathlib

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
      let s := rawName.toString
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
    let (newHypId, newGoal) ← newGoal.intro1
    let newGoal ← newGoal.clear hypId
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
    let newGoal ← newGoal.clear hypId
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
  let goal ← getMainGoal
  let (newGoal, progress) ← applyToAllHyps goal optionElimHyp
  replaceMainGoal [newGoal]
  unless progress do
    logWarning "option_elim: no progress made"

theorem womp (a c : Option Nat) (b : Nat → Option Nat) (p : Nat → Prop) :
    (do let x ← a; some <| p (← b x)) = some True →
    c.isSome →
    (do let x ← a; let y ← c; some <| p (← b x)) = some True := by
  intro h h1
  option_elim
  grind

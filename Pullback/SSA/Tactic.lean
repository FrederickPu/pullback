import Mathlib

open Lean Lean.Elab.Tactic Lean.Meta

syntax (name := bindSomeElim) "bind_some_elim" : tactic

@[tactic bindSomeElim]
def evalBindSomeElim : Tactic := fun _ =>
  withMainContext do
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue
      let ty ← inferType decl.toExpr
      let some (_, lhs, rhs) := ty.eq? | continue
      unless lhs.getAppFn.isConstOf ``Option.bind do continue
      unless rhs.isAppOf ``Option.some do continue
      let args := lhs.getAppArgs
      let n := args.size
      let rawName := match args[n - 1]! with
        | .lam name _ _ _ => name
        | _ => `val
      let binderName :=
        let s := rawName.toString
        if s.startsWith "__" || s.startsWith "_@" then `dolift else rawName
      let hyp  := mkIdent decl.userName
      let wit  := mkIdent binderName
      let hWit := mkIdent (Name.mkSimple s!"h{binderName}")
      evalTactic (← `(tactic| apply Option.bind_eq_some_iff.mp at $hyp:ident))
      evalTactic (← `(tactic| obtain ⟨$wit, $hWit, $hyp⟩ := $hyp:ident))
      return
    throwTacticEx `bind_some_elim (← getMainGoal)
      "no hypothesis of the form `f >>= g = some _` found"

syntax (name := isSomeElim) "is_some_elim" : tactic

@[tactic isSomeElim]
def evalIsSomeElim : Tactic := fun _ =>
  withMainContext do
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue
      let ty ← inferType decl.toExpr
      -- match h : x.isSome = true
      let some (_, lhs, rhs) := ty.eq? | continue
      unless rhs.isConstOf ``Bool.true do continue
      unless lhs.getAppFn.isConstOf ``Option.isSome do continue
      -- extract the name of the Option variable
      let optArg := lhs.getAppArgs[1]!  -- the Option value
      let witName := match optArg with
        | .fvar id => (lctx.get! id).userName
        | _ => `a
      let hyp  := mkIdent decl.userName
      let wit  := mkIdent (Name.mkSimple s!"{witName}'")
      evalTactic (← `(tactic| apply Option.isSome_iff_exists.mp at $hyp:ident))
      evalTactic (← `(tactic| obtain ⟨$wit, $hyp⟩ := $hyp:ident))
      return
    throwTacticEx `is_some_elim (← getMainGoal)
      "no hypothesis of the form `x.isSome = true` found"

theorem womp (a c : Option Nat) (b : Nat → Option Nat) (p : Nat → Prop) :
    (do let x ← a; some <| p (← b x)) = some True →
    c.isSome →
    (do let x ← a; let y ← c; some <| p (← b x)) = some True := by
  intro h h1
  rewrite [Option.bind_eq_bind] at *
  is_some_elim
  bind_some_elim
  bind_some_elim
  grind

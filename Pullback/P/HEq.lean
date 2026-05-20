import Lean
import Mathlib.Lean.Expr.Basic

open Lean

/-- `ext_heq x` applies `Function.hfunext` to a `f ≍ g` goal, closes the domain
    type equality with `rfl`, introduces `x x' hx` where `hx : x ≍ x'`, converts
    the HEq to Eq, and rewrites to collapse `x'` to `x`.

    Chain multiple layers with `ext_heq i; ext_heq j`.

    Uses `evalTactic` per step so each tactic sees the updated goal state — avoiding
    the focused-scope issue that `·` bullets or `(...)` blocks would introduce. -/
elab "ext_heq" x:ident : tactic => do
  let xp := Lean.mkIdentFrom x (x.getId.appendAfter "'")
  let hx := Lean.mkIdentFrom x (.mkSimple s!"h{x.getId.lastComponentAsString}")
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply Function.hfunext))
  Lean.Elab.Tactic.evalTactic (← `(tactic| rfl))
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro $x $xp $hx))
  Lean.Elab.Tactic.evalTactic (← `(tactic| have : $x = $xp := by rw [← heq_iff_eq]; exact $hx))
  Lean.Elab.Tactic.evalTactic (← `(tactic| rw [← this]))
  Lean.Elab.Tactic.evalTactic (← `(tactic| clear this $hx $xp))

set_option maxHeartbeats 2000000

theorem cast_fun_apply_heq
    {α α' : Sort u} {β : Sort v}
    (h : (α → β) = (α' → β)) (f : α → β)
    {a : α} {a' : α'} (ha : a ≍ a') :
    cast h f a' = f a := by
  have : α = α' := type_eq_of_heq ha
  subst this; cases ha; rw [cast_eq]

-- -- Step 1: push cast through a lambda
-- @[simp] theorem cast_lam_eq {α α' : Sort u} {β : Sort v}
--     (h : (α → β) = (α' → β)) (hα : α = α') (body : α → β) :
--     cast h (fun a => body a) = (fun a' => body (cast hα.symm a')) := by
--   cases hα; rfl

-- Step 2: kill cast of an HEq-related value
@[simp] theorem cast_eq_of_heq {α α' : Sort u} (h : α' = α)
    {a : α} {a' : α'} (ha : a ≍ a') :
    cast h a' = a := by
  cases h; cases ha; rfl

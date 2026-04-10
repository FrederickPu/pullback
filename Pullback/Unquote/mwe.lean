import Qq

open Qq

theorem womp (a c : Option Nat) (b : Nat → Option Nat) (p : Nat → Prop) : (do let x ← a; some <| p (← b x)) = some True → c.isSome → (do let x ← a; let y ← c; some <| p (← b x)) = some True := by
  intro h h1
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h



  /-
    a c : Option Nat
    b : Nat → Option Nat
    p : Nat → Prop
    h : (do
        let x ← a
        let __do_lift ← b x
        some (p __do_lift)) =
      some True
    ⊢ (wp⟦a⟧
        (fun a =>
          wp⟦do
              let _ ← c
              let __do_lift ← b a
              some (p __do_lift)⟧
            (fun a => ⌜some a = some True⌝, fun x => ⌜none = some True⌝, ()),
          fun x => ⌜none = some True⌝, ())).down
  -/

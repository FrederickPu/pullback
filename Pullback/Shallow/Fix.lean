import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Ordinal.Family

universe u v
namespace Function
open Classical

variable {α : Type u} {C : α → Sort v}

def calls (F : (x : α) → ((y : α) → C y) → C x) (x y : α) : Prop :=
  ∃ k1 k2, (∀ z, z ≠ y → k1 z = k2 z) ∧ F x k1 ≠ F x k2

def Terminates (F : (x : α) → ((y : α) → C y) → C x) : Prop :=
  WellFounded (fun y x => calls F x y)

/-- Opaque iteration: just runs `F` against itself. Terminates iff `F` does. -/
@[specialize]
partial def opaqueFix [∀ y, Nonempty (C y)]
    (F : (x : α) → ((y : α) → C y) → C x) (x : α) : C x :=
  F x (fun y => opaqueFix F y)

/-- Fixpoint of `F` with extrinsic termination: when `F` terminates, this equals
    the well-founded fixpoint; otherwise it's opaque. -/
@[cbv_opaque, implemented_by opaqueFix]
def extrinsicFix [∀ y, Nonempty (C y)]
    (F : (x : α) → ((y : α) → C y) → C x) (x : α) : C x :=
  if h : Terminates F then
    h.fix (fun x ih =>
      F x (fun y => if hc : calls F x y then ih y hc else Classical.arbitrary _)) x
  else
    opaqueFix F x

end Function

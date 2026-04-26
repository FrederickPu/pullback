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

/-- Extends a partial oracle (defined only on called positions) to a total oracle
    by filling uncalled positions with `Classical.arbitrary`. -/
noncomputable def extendOracle [∀ y, Nonempty (C y)]
    (F : (x : α) → ((y : α) → C y) → C x) (x : α)
    (ih : (y : α) → calls F x y → C y) (y : α) : C y :=
  if h : calls F x y then ih y h else Classical.arbitrary _

/-- Fixpoint of `F` with extrinsic termination: when `F` terminates, this equals
    the well-founded fixpoint; otherwise it's opaque. -/
@[cbv_opaque, implemented_by opaqueFix]
def extrinsicFix [∀ y, Nonempty (C y)]
    (F : (x : α) → ((y : α) → C y) → C x) (x : α) : C x :=
  if h : Terminates F then
    h.fix (fun x ih => F x (extendOracle F x ih)) x
  else
    opaqueFix F x

theorem extrinsicFix_eq_of_relation
    [∀ y, Nonempty (C y)]
    (F : (x : α) → ((y : α) → C y) → C x) (hF : Terminates F)
    (r' : α → α → Prop) (hr' : WellFounded r')
    (hcontains : ∀ x y, calls F x y → r' y x)
    (F' : (x : α) → ((y : α) → r' y x → C y) → C x)
    (hF' : ∀ x (ih : (y : α) → r' y x → C y),
      F' x ih = F x (extendOracle F x (fun y h => ih y (hcontains x y h))))
    (x : α) :
    WellFounded.extrinsicFix r' F' x = extrinsicFix F x := by
  rw [show WellFounded.extrinsicFix r' F' x = hr'.fix F' x from by
    unfold WellFounded.extrinsicFix; rw [dif_pos hr']]
  rw [show extrinsicFix F x = hF.fix (fun x ih => F x (extendOracle F x ih)) x from by
    unfold extrinsicFix; rw [dif_pos hF]]
  induction x using hF.induction with
  | _ x ih =>
    rw [WellFounded.fix_eq, WellFounded.fix_eq, hF']
    apply congrArg (F x)
    funext y
    unfold extendOracle
    split_ifs with h
    · exact ih y h
    · rfl

end Function

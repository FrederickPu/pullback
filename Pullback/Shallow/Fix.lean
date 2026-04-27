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

namespace extendOracle

variable [∀ y, Nonempty (C y)]
  (F : (x : α) → ((y : α) → C y) → C x) (x : α)

/-- At called positions, `extendOracle` returns the partial oracle's value. -/
@[simp] theorem of_calls
    (ih : (y : α) → calls F x y → C y) {y : α} (h : calls F x y) :
    extendOracle F x ih y = ih y h := by
  unfold extendOracle; rw [dif_pos h]

/-- At uncalled positions, `extendOracle` returns `Classical.arbitrary`. -/
@[simp] theorem of_not_calls
    (ih : (y : α) → calls F x y → C y) {y : α} (h : ¬ calls F x y) :
    extendOracle F x ih y = Classical.arbitrary _ := by
  unfold extendOracle; rw [dif_neg h]

/-- `extendOracle` agrees with `ih` on the called set: a clean form for `hF'`-style hypotheses. -/
theorem agrees_on_calls
    (ih : (y : α) → calls F x y → C y) :
    ∀ y (h : calls F x y), extendOracle F x ih y = ih y h := fun _ h => of_calls F x ih h

/-- Two `extendOracle`s with `ih`s agreeing on called positions are pointwise equal. -/
theorem ext_of_calls_agree
    (ih1 ih2 : (y : α) → calls F x y → C y)
    (h : ∀ y (hc : calls F x y), ih1 y hc = ih2 y hc) :
    extendOracle F x ih1 = extendOracle F x ih2 := by
  funext y
  unfold extendOracle
  split_ifs with hc
  · exact h y hc
  · rfl

/-- `F` applied to two `extendOracle`s with calls-agreeing `ih`s gives the same result. -/
theorem F_extendOracle_eq_of_calls_agree
    (ih1 ih2 : (y : α) → calls F x y → C y)
    (h : ∀ y (hc : calls F x y), ih1 y hc = ih2 y hc) :
    F x (extendOracle F x ih1) = F x (extendOracle F x ih2) := by
  rw [ext_of_calls_agree F x ih1 ih2 h]

end extendOracle

theorem extrinsicFix_eq_of_relation
    [∀ y, Nonempty (C y)]
    (F : (x : α) → ((y : α) → C y) → C x) (hF : Terminates F)
    (r' : α → α → Prop) (hr' : WellFounded r')
    (hcontains : ∀ x y, calls F x y → r' y x)
    (F' : (x : α) → ((y : α) → r' y x → C y) → C x)
    (hF' : ∀ x (ih : (y : α) → r' y x → C y) (k : (y : α) → C y),
      (∀ y (h : calls F x y), k y = ih y (hcontains x y h)) →
      F x k = F' x ih)
    (x : α) :
    WellFounded.extrinsicFix r' F' x = extrinsicFix F x := by
  rw [show WellFounded.extrinsicFix r' F' x = hr'.fix F' x from by
    unfold WellFounded.extrinsicFix; rw [dif_pos hr']]
  rw [show extrinsicFix F x = hF.fix (fun x ih => F x (extendOracle F x ih)) x from by
    unfold extrinsicFix; rw [dif_pos hF]]
  induction x using hF.induction with
  | _ x ih =>
    rw [WellFounded.fix_eq, WellFounded.fix_eq]
    rw [← hF' x (fun y _ => hr'.fix F' y)
              (extendOracle F x (fun y h => hr'.fix F' y))
              (extendOracle.agrees_on_calls F x _)]
    exact extendOracle.F_extendOracle_eq_of_calls_agree F x _ _ (fun y h => ih y h)

end Function

namespace Fib
open Function Classical

/-- Open-recursion form of Fibonacci: `F n k` returns the n-th Fib using `k` as the recursive oracle. -/
def F : (n : ℕ) → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | 1, _ => 1
  | n+2, k => k (n+1) + k n

/-- Structured form: takes a partial oracle, returning Fib using `<` as the well-founded relation. -/
def F' : (n : ℕ) → ((m : ℕ) → m < n → ℕ) → ℕ
  | 0, _ => 0
  | 1, _ => 1
  | n+2, ih => ih (n+1) (by omega) + ih n (by omega)

/-- Fibonacci via the opaque-recursor framework. -/
def fibFun (n : ℕ) : ℕ := extrinsicFix F n

/-- Fibonacci via core's well-founded recursion. -/
def fibWf (n : ℕ) : ℕ := WellFounded.extrinsicFix (· < ·) F' n

variable {α : Type u} {C : α → Sort v}

/-- Project a structured `F'` (taking proofs of `r y x`) to an open-recursion `F` (taking total oracle). -/
def project {r : α → α → Prop}
    (F' : (x : α) → ((y : α) → r y x → C y) → C x) :
    (x : α) → ((y : α) → C y) → C x :=
  fun x k => F' x (fun y _ => k y)

def project' {r : α → α → Prop} [DecidableRel r] [∀ y, Inhabited (C y)] {x}: ((y : α) → r y x → C y) → ((y : α) → C y) :=
  fun k => fun y => if h : r y x then k y h else default

section project

variable {r : α → α → Prop}
  (F' : (x : α) → ((y : α) → r y x → C y) → C x)

/-- The compatibility hypothesis is automatic for projections. -/
theorem F_eq_F'_project  [DecidableRel r] [∀ y, Inhabited (C y)]
    (x : α) (ih : (y : α) → r y x → C y) :
    project F' x (project' ih) = F' x ih := by
  unfold project project'
  congr
  ext y hy
  simp [hy]

end project

import Pullback.Unquote.TypeLift

/-! ## Test: deriving TypeLift -/

inductive MyPair (α : Type u) (β : Type v) where
  | mk : α → β → MyPair α β
  deriving TypeLift

inductive MyOption (α : Type u) where
  | none : MyOption α
  | some : α → MyOption α
  deriving TypeLift

inductive MyList (α : Type u) where
  | nil : MyList α
  | cons : α → MyList α → MyList α
  deriving TypeLift

-- Test that the derived instances work
example : TypeLift (MyPair Nat Bool) (MyPair (ULift.{1} Nat) (ULift.{1} Bool)) := inferInstance
example : TypeLift (MyOption Nat) (MyOption (ULift.{1} Nat)) := inferInstance
example : TypeLift (MyList Nat) (MyList (ULift.{1} Nat)) := inferInstance

-- Test round-trip
example (p : MyPair Nat Bool) : TypeLift.down (TypeLift.up p) = p := TypeLift.roundtrip p

-- Derive for standard library types
deriving instance TypeLift for Prod
deriving instance TypeLift for Sum
deriving instance TypeLift for Option

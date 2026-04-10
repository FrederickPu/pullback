universe u v w t

/-! # TypeLift: automatic universe cumulativity

Analogous to `SizeOf` — every type gets a canonical way to lift
itself into a target universe. The typeclass machinery handles
the plumbing so you never manually write ULift.

Models the inclusion map `V_u ↪ V_w` from the cumulative hierarchy. -/

/-! ## Core typeclass -/

/-- `TypeLift A B` witnesses that `A` can be lifted to `B`,
    with `B` living in a (possibly) higher universe.
    Think of it as the inclusion map `V_u ↪ V_w` in the
    cumulative hierarchy. -/
class TypeLift (A : Type u) (B : outParam (Type w)) where
  up   : A → B
  down : B → A
  roundtrip : ∀ a, down (up a) = a

/-! ## Base instance: ULift handles the ground case -/

instance : TypeLift.{u, max u w} A (ULift.{max u w, u} A) where
  up   := ULift.up
  down := ULift.down
  roundtrip _ := rfl

/-! ## Identity: if already at the right universe, do nothing -/

instance : TypeLift.{u, u} A A where
  up   := id
  down := id
  roundtrip _ := rfl

/-! ## Composed instances for type formers -/

/-- Prod lifts componentwise. -/
instance [TypeLift.{u, t} A A'] [TypeLift.{v, t} B B']
    : TypeLift.{max u v, t} (A × B) (A' × B') where
  up   p := (TypeLift.up p.1, TypeLift.up p.2)
  down p := (TypeLift.down p.1, TypeLift.down p.2)
  roundtrip p := by simp only [TypeLift.roundtrip]

/-- Sum lifts componentwise. -/
instance [TypeLift.{u, t} A A'] [TypeLift.{v, t} B B']
    : TypeLift.{max u v, t} (A ⊕ B) (A' ⊕ B') where
  up
    | .inl a => .inl (TypeLift.up a)
    | .inr b => .inr (TypeLift.up b)
  down
    | .inl a => .inl (TypeLift.down a)
    | .inr b => .inr (TypeLift.down b)
  roundtrip
    | .inl _ => by simp [TypeLift.roundtrip]
    | .inr _ => by simp [TypeLift.roundtrip]

/-- Option lifts the inner type. -/
instance [TypeLift.{u, t} A A'] : TypeLift.{u, t} (Option A) (Option A') where
  up
    | some a => some (TypeLift.up a)
    | none   => none
  down
    | some a => some (TypeLift.down a)
    | none   => none
  roundtrip
    | some _ => by simp [TypeLift.roundtrip]
    | none   => rfl

/-- List lifts the element type. -/
instance [TypeLift.{u, t} A A'] : TypeLift.{u, t} (List A) (List A') where
  up   := List.map TypeLift.up
  down := List.map TypeLift.down
  roundtrip xs := by
    simp only [List.map_map, Function.comp_def, TypeLift.roundtrip, List.map_id']

/-- Function types: lift domain contravariantly, codomain covariantly.
    We avoid putting universe constraints on the instance head to
    sidestep `imax` unification issues. Instead we constrain the
    components and let Lean compute the function type's universe. -/
instance typeLiftFun [TypeLift.{u, t} A A'] [TypeLift.{v, t} B B']
    : TypeLift (A → B) (A' → B') where
  up   f := fun a' => TypeLift.up (f (TypeLift.down a'))
  down f := fun a  => TypeLift.down (f (TypeLift.up a))
  roundtrip f := by funext a; simp [TypeLift.roundtrip]

/-! ## Ergonomic API -/

/-- Lift a value into a higher universe. -/
def typeLift [TypeLift.{u, w} A B] (a : A) : B :=
  TypeLift.up a

/-- Unlift a value back to its original universe. -/
def typeUnlift [TypeLift.{u, w} A B] (b : B) : A :=
  TypeLift.down b

/-! ## Context: a list of types at a given universe -/

/-- A typing context for metavariables, all at universe u. -/
def Ctx.{uu} := List (Type uu)

namespace Ctx

def nil.{uu} : Ctx.{uu} := []

def cons.{uu} (A : Type uu) (ctx : Ctx.{uu}) : Ctx.{uu} := A :: ctx

/-- Lift each type in a context to a higher universe. -/
def lift (ctx : Ctx.{u}) : Ctx.{max u v} :=
  List.map (ULift.{max u v, u} ·) ctx

/-- Append two contexts, lifting both to a common universe. -/
def append (ctx₁ : Ctx.{u}) (ctx₂ : Ctx.{v}) : Ctx.{max u v} :=
  List.append (ctx₁.lift) (ctx₂.lift)

end Ctx

/-! ## Examples -/

section Examples

-- Lift a Nat value to a higher universe — automatic
example : ULift.{1} Nat := typeLift 42

-- Lift Prod.mk — both components lifted automatically
example : ULift.{1} Nat × ULift.{1} Bool :=
  typeLift (Prod.mk 42 true)

-- Lift a function Nat → Bool, now works on lifted types
def isEven' : ULift.{1} Nat → ULift.{1} Bool :=
  typeLift (fun n => n % 2 == 0 : Nat → Bool)

-- N-ary: binary function lifted automatically via currying
def add' : ULift.{1} Nat → ULift.{1} Nat → ULift.{1} Nat :=
  typeLift (fun a b => a + b : Nat → Nat → Nat)

-- N-ary: ternary
def add3' : ULift.{1} Nat → ULift.{1} Nat → ULift.{1} Nat → ULift.{1} Nat :=
  typeLift (fun a b c => a + b + c : Nat → Nat → Nat → Nat)

-- Round-trip: lift then unlift = id
example (n : Nat) : typeUnlift (typeLift (B := ULift.{1} Nat) n) = n := rfl

-- List of Nats lifted automatically
example : List (ULift.{1} Nat) := typeLift [1, 2, 3]

-- Contexts at the same universe
def ctx₀ : Ctx.{0} := [Nat, Bool]
def ctx₀' : Ctx.{0} := [Int]
def combined₀ : Ctx.{0} := ctx₀.append ctx₀'

-- Heterogeneous: different universes, lifted automatically
def ctx₁ : Ctx.{1} := [Type]
def combined₁ : Ctx.{1} := ctx₀.append ctx₁

end Examples

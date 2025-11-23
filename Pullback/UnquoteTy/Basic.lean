/-
  TODO :: emulate Monad where proof carrying logic is moved into a seperate typeclass called LawfulUnquoteTy
-/
class UnquoteTy (Ty : Type) where
  -- `syntax T` returns Type describing the syntax of quoted type `T : Ty`
  «syntax» : Ty → Type
  -- `interpret t` returns Type describing the smenatics of quoted type `t : Ty`
  interpret : Ty → Type
  unquote  (T : Ty) (t : «syntax» T) : interpret T
  imp (α β : Ty) : Ty
  interpret_imp (α β : Ty) : interpret (imp α β) = (interpret α → interpret β)
  unit : Ty
  hUnit : interpret unit = Unit

infixr:30 "→" => UnquoteTy.imp
open UnquoteTy

-- can be defined using map and `UnquoteTy.interpret_imp`
def UnquoteTy.app {Ty : Type} [UnquoteTy Ty] (α β : Ty) : «syntax» (α → β) → «syntax» α → «syntax» β := sorry

/-
  TODO should add this to `push_cast` and `norm_cast` tactic somehow
-/
example {Ty : Type} [UnquoteTy Ty] {α β : Ty} : «syntax» (α → β) = («syntax» α) → («syntax» β) := sorry

class MonadTy {Ty : Type} [UnquoteTy Ty] (m : Ty → Ty) where
  map {α β : Ty} : «syntax» (((α → β) → (m α)) → (m β))
  mapConst {α β : Ty} : «syntax» (α → m β → m α)
  pure {α : Ty} : «syntax» (α → (m α))
  seq {α β : Ty} : «syntax» ((m (imp α β)) → (unit → (m α)) → (m β))
  seqLeft {α β : Ty} : «syntax» ((m α) → (unit : Ty) → (m β) → (m α))
  seqRight {α β : Ty} : «syntax» ((m α) → (unit : Ty) → (m β) → (m β))
  bind {α β : Ty} : «syntax» ((m α) → (α → (m β)) → (m β))


-- A simple object language with just base types and functions
inductive SimpleTy where
  | nat : SimpleTy
  | bool : SimpleTy
  | unit : SimpleTy
  | arrow : SimpleTy → SimpleTy → SimpleTy

-- Define syntax interpretation recursively
def SimpleTy.syntax : SimpleTy → Type
  | .nat => Nat
  | .bool => Bool
  | unit => Unit
  | .arrow α β => SimpleTy.syntax α → SimpleTy.syntax β

-- Define semantic interpretation recursively
def SimpleTy.interpret : SimpleTy → Type
  | .nat => Nat
  | .bool => Bool
  | unit => Unit
  | .arrow α β => interpret α → interpret β

theorem crux : SimpleTy.syntax = SimpleTy.interpret := by
  ext T
  induction T
  · rfl
  · rfl
  · rfl
  · expose_names
    simp [SimpleTy.syntax, SimpleTy.interpret, a_ih, a_ih_1]

-- UnquoteTy instance for our simple type language
instance : UnquoteTy SimpleTy where
  «syntax» := SimpleTy.syntax
  interpret := SimpleTy.interpret
  unquote := fun T t => cast (by simp [crux]) t
  imp := SimpleTy.arrow
  interpret_imp := fun α β => rfl
  unit := SimpleTy.unit
  hUnit := rfl

instance : MonadTy (id : SimpleTy → SimpleTy) := sorry

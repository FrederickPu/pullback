/-
  TODO :: emulate Monad where proof carrying logic is moved into a seperate typeclass called LawfulUnquoteTy

  note that UnquoteTy's unquoting operation doesn't support dependent types so can only model simple type theory.

  goal: no explicit judgements (all judgements done implcitly through ambient type theory / lean's unification system)
-/
class UnquoteTy (Ty : Type) where
  -- `syntax T` returns Type describing the syntax of quoted type `T : Ty`
  «syntax» : Ty → Type
  -- `interpret t` returns Type describing the smenatics of quoted type `t : Ty`
  interpret : Ty → Type
  unquote  (T : Ty) (t : «syntax» T) : interpret T
  imp (α β : Ty) : Ty
  interpret_imp (α β : Ty) : interpret (imp α β) = (interpret α → interpret β)
  /-
    TODO should add this to `push_cast` and `norm_cast` tactic somehow
  -/
  app {α β : Ty} : «syntax» (imp α β) → «syntax» α → «syntax» β

#check Bind
class Unquote (Ty : Type) (rules : List (List Ty × Ty)) where
  -- `interpret t` returns Type describing the smenatics of quoted type `t : Ty`
  interpret : List Ty → Ty → Type
  unquote_intro (ruleIdx : Fin rules.length) : interpret (rules.get ruleIdx).1 (rules.get ruleIdx).2
  unquote_cut (Γ' Γ : List Ty) (T α : Ty) (a : interpret Γ' α) (t : interpret (α::Γ) T) : interpret (Γ' ++ Γ) T

inductive WompWomp (Ty : Type) (rules : List (List Ty × Ty)) : (Γ : List Ty) → (T : Ty) → Type where
| intro (ruleIdx : Fin rules.length) : WompWomp Ty rules (rules.get ruleIdx).1 (rules.get ruleIdx).2
| cut (Γ' Γ : List Ty) (T α : Ty) (a : WompWomp Ty rules Γ' α) (t : WompWomp Ty rules (α::Γ) T) : WompWomp Ty rules (Γ' ++ Γ) T

inductive WompWompLam (Ty : Type) (rules : List (List Ty × Ty)) : (Γ : List Ty) → (T : Ty) → Type where
| intro (ruleIdx : Fin rules.length) : WompWompLam Ty rules (rules.get ruleIdx).1 (rules.get ruleIdx).2
| cut (Γ' Γ : List Ty) (T α : Ty) (a : WompWompLam Ty rules Γ' α) (t : WompWompLam Ty rules (α::Γ) T) : WompWompLam Ty rules (Γ' ++ Γ) T
| var (Γ : List Ty) (i : Fin Γ.length) : WompWompLam Ty rules Γ (Γ.get i)


def WompWomp.unquote
  {Ty : Type} {rules : List (List Ty × Ty)}
  [U : Unquote Ty rules]
  : (Γ : List Ty) → (T : Ty) → WompWomp Ty rules Γ T →
      Unquote.interpret rules Γ T
| _, _, WompWomp.intro ruleIdx => U.unquote_intro ruleIdx
| _, _, WompWomp.cut Γ' Γ T α a t =>
  let ua := WompWomp.unquote Γ' α a
  let ut := WompWomp.unquote (α :: Γ) T t
  U.unquote_cut Γ' Γ T α ua ut

open WompWompLam

def nestedVarLam
  {Ty : Type} {rules : List (List Ty × Ty)} [Unquote Ty rules]
  : (Γ : List Ty) → (i : Fin Γ.length) →
    Unquote.interpret rules Γ (Γ.get i) :=
  sorry


def WompWompLam.unquote
  {Ty : Type} {rules : List (List Ty × Ty)}
  [U : Unquote Ty rules]
  : (Γ : List Ty) → (T : Ty) → WompWompLam Ty rules Γ T →
      Unquote.interpret rules Γ T
| _, _, WompWompLam.intro ruleIdx =>
  U.unquote_intro ruleIdx
| _, _, WompWompLam.cut Γ' Γ'' T α a t =>
  let ua := WompWompLam.unquote Γ' α a
  let ut := WompWompLam.unquote (α :: Γ'') T t
  U.unquote_cut Γ' Γ'' T α ua ut
| _, _, WompWompLam.var Γ i => nestedVarLam Γ i

open UnquoteTy

infixr:30 "→" => UnquoteTy.imp


inductive MyLang where
| A : MyLang
| Arrow : MyLang -> MyLang -> MyLang

def CounterExample.syntax : MyLang → Type
| MyLang.A => Nat
| MyLang.Arrow X Y => CounterExample.syntax X → CounterExample.syntax Y

/-
  Parametricity theorem
-/
example : ¬ ∀ [UnquoteTy MyLang] (f : («syntax» (imp MyLang.A MyLang.A : MyLang))), app f = id := by {
  simp only [Classical.not_forall]
  apply Exists.intro {
    «syntax» := CounterExample.syntax
    interpret := CounterExample.syntax,
    unquote := fun x y => y
    imp := fun x y => MyLang.Arrow x y
    interpret_imp := by
      intro α β
      rfl
    app := fun f x => f x
  }
  apply Exists.intro ((cast rfl) (fun x => 2 * x : Nat → Nat))
  simp only [cast_eq]
  intro h
  have := congrFun h (1:Nat)
  simp at this
}

def MyLang.syntax : MyLang → Type
| MyLang.A => Nat
| MyLang.Arrow MyLang.A MyLang.A => Unit
| MyLang.Arrow X Y => MyLang.syntax X → MyLang.syntax Y

def MyLang.interpret : MyLang → Type
| MyLang.A => Nat
| MyLang.Arrow X Y => MyLang.syntax X → MyLang.syntax Y

open UnquoteTy

notation:20 x "<||" y => UnquoteTy.app x y


class MonadTy {Ty : Type} [UnquoteTy Ty] (m : Ty → Ty) where
  unit : Ty
  hUnit : interpret unit = Unit
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
  app := (fun {α β} f a => by {
    simp [SimpleTy.syntax] at f
    exact f a
  })

instance : MonadTy (id : SimpleTy → SimpleTy) := sorry

open UnquoteTy
instance : Coe Nat («syntax» SimpleTy.nat) :=
  ⟨fun x => x⟩

def SimpleTy.idNat : «syntax» (SimpleTy.nat → id SimpleTy.nat) := id

/-!
Note why quoting is necessary/you cant just use paraemtric types. For example if you try to make a syntehtic where all functino are polynomial time eg (can only use succ) you will always be able to escape that theory by using lean's native recursors:

```
axiom P : Type → Type
axiom succ : P ℕ → P ℕ

noncomputable example (a : P ℕ) : P ℕ :=
  Nat.rec a (fun n b => succ b) (1000 * 1000^2)
```


idea : make `Ty` where all function types are continuous, surjective, injective etc
-/

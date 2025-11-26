-- dependent contexts

/-
  dependently typed vector
-/
inductive DVec (α : Nat → Type) : Nat → Type
  | nil : DVec α 0
  | push {n : Nat} : DVec α n → α n → DVec α (n + 1)

def DVec.cons {α : Nat → Type} : α 0 → DVec α n → DVec α (n + 1) := sorry

/-
  dependently typed list
-/
abbrev DList (α : Nat → Type) := Sigma (fun (n : Nat) => DVec α n)

/--
  The dependently typed list whose first element is `head`, where `tail` is the rest of the list.
  Usually written `head ::: tail`.
-/
def DList.cons {α : Nat → Type} : α 0 → DList α → DList α :=
  fun a l => ⟨_, DVec.cons a l.2⟩

@[inherit_doc] infixr:67 " ::: " => DList.cons

def DList.get {α : Nat → Type} {n : Nat} (l : DList α) (i : Fin n) : α i := sorry

def DList.get' {α : Nat → Type} {n : Nat} (l : DList α) (i : Fin n) : α n := sorry

inductive DTerm (Ty : Type) (i : Nat) where
| type (t : Ty)
| var (i : Nat)
| app (T₁ T₂ : Ty)

def DTerm.shift {Ty : Type} {i : Nat} {j} : DTerm Ty i → DTerm Ty (i + j) := sorry

instance {α : Nat → Type} : Append (DList α) := sorry

theorem DList.cons_size {α : Nat → Type} (A B : DList α) : (A ++ B).1 = A.1 + B.1 := sorry

/-
  `(Γ : DContext Ty)` is a dependtly typed context over a quoted type universe `Ty`
  a context is a list of terms where each term is either a type or a variable references one of the terms occuring before it in the context
-/
abbrev DContext (Ty : Type) := DList (fun i => DTerm Ty i)

inductive WompWompLam (Ty : Type) (rules : List ((Γ : DContext Ty) × (DTerm Ty Γ.1))) : (Γ : DContext Ty) → (T : DTerm Ty Γ.1) → Type where
| intro (ruleIdx : Fin rules.length) : WompWompLam Ty rules (rules.get ruleIdx).1 (rules.get ruleIdx).2
| cut (Γ' Γ : DContext Ty) (α : Ty) (T : DTerm Ty Γ.1) (a : WompWompLam Ty rules Γ' (DTerm.type α)) : (t : WompWompLam Ty rules ((DTerm.type α):::Γ) T.shift) → WompWompLam Ty rules (Γ' ++ Γ) (cast (by {
  congr
  rw [DList.cons_size, Nat.add_comm]
}) (T.shift (j := Γ'.1)))
| var (Γ : DContext Ty) (i : Fin Γ.1) : WompWompLam Ty rules Γ (Γ.get' i)


class Unquote (Ty : Type) (rules : List ((Γ : DContext Ty) × DTerm Ty Γ.1)) where
  -- `interpret t` returns Type describing the smenatics of quoted type `t : Ty`
  interpret : (Γ : DContext Ty) → DTerm Ty Γ.1 → Type
  unquote_intro (ruleIdx : Fin rules.length) : interpret (rules.get ruleIdx).1 (rules.get ruleIdx).2
  unquote_cut (Γ' Γ : DContext Ty) (α : Ty) (T : DTerm Ty Γ.1) (a : interpret Γ' (DTerm.type α)) (t : interpret (DTerm.type α:::Γ) T.shift) : interpret (Γ' ++ Γ) (cast (by {
  congr
  rw [DList.cons_size, Nat.add_comm]
}) (T.shift (j := Γ'.1)))

def nestedVarLam
  {Ty : Type} {rules : List ((Γ : DContext Ty) × DTerm Ty Γ.1)} [Unquote Ty rules]
  : (Γ : DContext Ty) → (i : Fin Γ.1) →
    Unquote.interpret rules Γ (Γ.get' i) :=
  sorry

def WompWompLam.unquote
  {Ty : Type} {rules : List ((Γ : DContext Ty) × DTerm Ty Γ.1)}
  [U : Unquote Ty rules]
  : (Γ : DContext Ty) → (T : DTerm Ty Γ.1) → WompWompLam Ty rules Γ T →
      Unquote.interpret rules Γ T
| _, _, WompWompLam.intro ruleIdx =>
  U.unquote_intro ruleIdx
| _, _, WompWompLam.cut Γ' Γ'' α T a t =>
  let ua := WompWompLam.unquote Γ' (DTerm.type α) a
  let ut := WompWompLam.unquote (DTerm.type α ::: Γ'') T.shift t
  U.unquote_cut Γ' Γ'' α T ua ut
| _, _, WompWompLam.var Γ i => nestedVarLam Γ i

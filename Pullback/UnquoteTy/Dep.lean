-- dependent contexts

/-
  dependently typed vector
-/
inductive DVec (α : Nat → Type) : Nat → Type
  | nil : DVec α 0
  | push {n : Nat} : DVec α n → α n → DVec α (n + 1)

def DVec.cons {n : Nat} {α : Nat → Type}
  (shift : {i : Nat} → α i → α (i + 1))
  (a0 : α 0)
    : DVec α n → DVec α (n + 1)
  | nil           => push nil a0
  | push tail x   => push (DVec.cons shift a0 tail) (shift x)

/-- Get the `i`-th element of a dependent vector. -/
def DVec.get {α : Nat → Type} : {n : Nat} → DVec α n → (i : Fin n) → α i
| 0, DVec.nil, i =>
  False.elim <| Nat.not_lt_zero i i.isLt
| n + 1, DVec.push v a, i =>
  if h : i.val < n then
    DVec.get v ⟨i.val, h⟩
  else
    have : i.val = n := by
      rw [Nat.not_lt] at h
      exact Nat.eq_of_le_of_lt_succ h i.isLt
    cast (by {
      rw [this]
    }) a

/-
  dependently typed list
-/
abbrev DList (α : Nat → Type) := Sigma (fun (n : Nat) => DVec α n)

/--
  The dependently typed list whose first element is `head`, where `tail` is the rest of the list.
  Usually written `head ::: tail`.
-/
def DList.cons {α : Nat → Type} (shift : {i : Nat} → α i → α (i + 1)) : α 0 → DList α → DList α :=
  fun a l => ⟨_, DVec.cons shift a l.2⟩

def DList.get {α : Nat → Type} (l : DList α) (i : Fin l.1) : α i :=
  l.2.get i

inductive DTerm (Ty : Type) (i : Nat) where
| type (t : Ty)
| var (i : Nat)
| app (T₁ T₂ : Ty)

def DTerm.lift {Ty : Type} {i : Nat} {j} : DTerm Ty i → DTerm Ty (i + j)
| .type t => .type t
| .var q => .var q
| .app T₁ T₂ => .app T₁ T₂

def DTerm.shiftRight {Ty : Type} {i : Nat} {j} : DTerm Ty i → DTerm Ty (i + j)
| .type t => .type t
| .var q => .var (q + j)
| .app T₁ T₂ => .app T₁ T₂

def DVec.append {α : Nat → Type} (shift : {i j : Nat} → α i → α (i + j)):
  {m n : Nat} → DVec α m → DVec α n → DVec α (m + n)
  | m, 0, ys, DVec.nil => cast (by simp) ys
  | m, n + 1, xs, DVec.push ys y =>
    (DVec.append @shift xs ys).push (cast (by rw [Nat.add_comm]) (shift (j := m) y))

def DList.append {α : Nat → Type} (shift : {i j : Nat} → α i → α (i + j)) :
    DList α → DList α → DList α :=
  fun ⟨_, xs⟩ ⟨_, ys⟩ => ⟨_, DVec.append @shift xs ys⟩

/-
  `(Γ : DContext Ty)` is a dependtly typed context over a quoted type universe `Ty`
  a context is a list of terms where each term is either a type or a variable references one of the terms occuring before it in the context
-/
abbrev DContext (Ty : Type) := DList (fun i => DTerm Ty i)

instance {Ty : Type} : Append (DContext Ty) := ⟨DList.append DTerm.shiftRight⟩

theorem DContext.cons_size {Ty : Type} : (A B : DContext Ty) → (A ++ B).1 = A.1 + B.1
| ⟨_, xs⟩, ⟨_, ys⟩ => by
  simp only [HAppend.hAppend, Append.append]
  rw [DList.append]

/--
  adds DTerm to start of context
  usually written as `a:::l`
-/
def DContext.cons {Ty : Type} (a : DTerm Ty 0)  (l : DContext Ty) : DContext Ty :=
  DList.cons (fun t =>
    match t with
    | .type t => .type t
    | .var i => .var (i + 1)
    | .app T₁ T₂ => .app T₁ T₂
  ) a l

def DContext.get' {n : Nat} {Ty : Type} (l : DContext Ty) (i : Fin l.1) : DTerm Ty n :=
  match l.2.get i with
  | .type t => .type t
  | .var i => .var (i + 1)
  | .app T₁ T₂ => .app T₁ T₂


@[inherit_doc] infixr:67 " ::: " => DContext.cons

inductive WompWompLam (Ty : Type) (rules : List ((Γ : DContext Ty) × (DTerm Ty Γ.1))) : (Γ : DContext Ty) → (T : DTerm Ty Γ.1) → Type where
| intro (ruleIdx : Fin rules.length) : WompWompLam Ty rules (rules.get ruleIdx).1 (rules.get ruleIdx).2
| cut (Γ' Γ : DContext Ty) (α : Ty) (T : DTerm Ty Γ.1) (a : WompWompLam Ty rules Γ' (DTerm.type α)) : (t : WompWompLam Ty rules ((DTerm.type α):::Γ) T.lift) → WompWompLam Ty rules (Γ' ++ Γ) (cast (by {
  rw [DContext.cons_size, Nat.add_comm]
}) (T.shiftRight (j := Γ'.1)))
| var (Γ : DContext Ty) (i : Fin Γ.1) : WompWompLam Ty rules Γ (Γ.get' i)


class Unquote (Ty : Type) (rules : List ((Γ : DContext Ty) × DTerm Ty Γ.1)) where
  -- `interpret t` returns Type describing the smenatics of quoted type `t : Ty`
  interpret : (Γ : DContext Ty) → DTerm Ty Γ.1 → Type
  unquote_intro (ruleIdx : Fin rules.length) : interpret (rules.get ruleIdx).1 (rules.get ruleIdx).2
  unquote_cut (Γ' Γ : DContext Ty) (α : Ty) (T : DTerm Ty Γ.1) (a : interpret Γ' (DTerm.type α)) (t : interpret (DTerm.type α:::Γ) T.lift) : interpret (Γ' ++ Γ) (cast (by {
  rw [DContext.cons_size, Nat.add_comm]
}) (T.shiftRight (j := Γ'.1)))

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
  let ut := WompWompLam.unquote (DTerm.type α ::: Γ'') T.lift t
  U.unquote_cut Γ' Γ'' α T ua ut
| _, _, WompWompLam.var Γ i => nestedVarLam Γ i

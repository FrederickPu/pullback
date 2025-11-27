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
| 0, DVec.nil, i => nomatch i
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

inductive DTerm (Ty : Type) (vars : Nat) : Type
| type (t : Ty) : DTerm Ty vars
| var (i : Fin vars) : DTerm Ty vars
| app (T₁ T₂ : Ty) : DTerm Ty vars
| pi (T₁ T₂ : Ty) : DTerm Ty vars

def DTerm.lift {Ty : Type} {i : Nat} {j} : DTerm Ty i → DTerm Ty (i + j)
| .type t => .type t
| .var q => .var ⟨q, Nat.lt_add_right j q.isLt⟩
| .app T₁ T₂ => .app T₁ T₂
| .pi T₁ T₂ => .app T₁ T₂

def DTerm.shiftRight {Ty : Type} {i : Nat} {j} : DTerm Ty i → DTerm Ty (i + j)
| .type t => .type t
| .var q => .var ⟨q + j, Nat.add_lt_add_right q.isLt j⟩
| .app T₁ T₂ => .app T₁ T₂
| .pi T₁ T₂ => .pi T₁ T₂

def DVec.append {α : Nat → Type} (shift : {i j : Nat} → α i → α (i + j)):
  {m n : Nat} → DVec α m → DVec α n → DVec α (m + n)
  | m, 0, ys, DVec.nil => cast (by simp) ys
  | m, n + 1, xs, DVec.push ys y =>
    (DVec.append @shift xs ys).push (cast (by rw [Nat.add_comm]) (shift (j := m) y))

def DList.push {α : Nat → Type} (l : DList α) (a : α l.1) : DList α :=
  ⟨_, l.2.push a⟩

def DList.append {α : Nat → Type} (shift : {i j : Nat} → α i → α (i + j)) :
    DList α → DList α → DList α :=
  fun ⟨_, xs⟩ ⟨_, ys⟩ => ⟨_, DVec.append @shift xs ys⟩

/-
  `(Γ : DContext Ty)` is a dependtly typed context over a quoted type universe `Ty`
  a context is a list of terms where each term is either a type or a variable references one of the terms occuring before it in the context
-/
abbrev DContext (Ty : Type) := DList (fun i => DTerm Ty i)

instance {Ty : Type} : Append (DContext Ty) := ⟨DList.append DTerm.shiftRight⟩

theorem DContext.size_append {Ty : Type} : (A B : DContext Ty) → (A ++ B).1 = A.1 + B.1
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
    | .var q => .var ⟨q + 1, Nat.add_lt_add_right q.isLt 1⟩
    | .app T₁ T₂ => .app T₁ T₂
    | .pi T₁ T₂ => .pi T₁ T₂
  ) a l

def DContext.get' {Ty : Type} (l : DContext Ty) (i : Fin l.1) : DTerm Ty l.1 :=
  match l.2.get i with
  | .type t => .type t
  | .var q => .var ⟨q, Nat.lt_trans q.isLt i.isLt⟩
  | .app T₁ T₂ => .app T₁ T₂
  | .pi T₁ T₂ => .pi T₁ T₂

open Lean
macro_rules
  | `([ $elems,* ]) => do
    let rec expand (i : Nat) (acc : TSyntax `term) : MacroM Syntax := do
      if h : i < elems.getElems.size then
        let elem := ⟨elems.getElems[i]⟩
        expand (i+1) (← ``(DVec.push $acc $elem))
      else
        dbg_trace acc
        pure acc
    expand 0 (← ``((DVec.nil : DVec _ 0)))

-- this works
#check fun {Ty : Type} (T : Ty)=> ((DVec.nil.push (DTerm.type T)).push (DTerm.type T): DVec (DTerm Ty) 2)
#check fun {Ty : Type} (T : Ty)=> ([DTerm.type T, DTerm.var 0]: DVec (DTerm Ty) 2)


@[inherit_doc] infixr:67 " ::: " => DContext.cons

inductive WompWompLam (Ty : Type) (rules : List ((Γ : DContext Ty) × (DTerm Ty Γ.1))) : (Γ : DContext Ty) → (T : DTerm Ty Γ.1) → Type where
| intro (ruleIdx : Fin rules.length) : WompWompLam Ty rules (rules.get ruleIdx).1 (rules.get ruleIdx).2
| cut (Γ' Γ : DContext Ty) (α : Ty) (T : DTerm Ty Γ.1) (a : WompWompLam Ty rules Γ' (DTerm.type α)) : (t : WompWompLam Ty rules ((DTerm.type α):::Γ) T.lift) → WompWompLam Ty rules (Γ' ++ Γ) (cast (by {
  rw [DContext.size_append, Nat.add_comm]
}) (T.shiftRight (j := Γ'.1)))
| var (Γ : DContext Ty) (i : Fin Γ.1) : WompWompLam Ty rules Γ (Γ.get' i)
/-- simple pi types: pi types where the return type isn't depenedent on the input type -/
| pi (Γ : DContext Ty) (α T : Ty) (f : WompWompLam Ty rules (Γ.push (.type α)) (.type T)) : WompWompLam Ty rules Γ (.pi α T)


class Unquote (Ty : Type) (rules : List ((Γ : DContext Ty) × DTerm Ty Γ.1)) where
  -- `interpret t` returns Type describing the smenatics of quoted type `t : Ty`
  interpret : (Γ : DContext Ty) → DTerm Ty Γ.1 → Type
  unquote_intro (ruleIdx : Fin rules.length) : interpret (rules.get ruleIdx).1 (rules.get ruleIdx).2
  unquote_cut (Γ' Γ : DContext Ty) (α : Ty) (T : DTerm Ty Γ.1) (a : interpret Γ' (DTerm.type α)) (t : interpret (DTerm.type α:::Γ) T.lift) : interpret (Γ' ++ Γ) (cast (by {
      rw [DContext.size_append, Nat.add_comm]
    }) (T.shiftRight (j := Γ'.1)))
  unquote_var : (Γ : DContext Ty) → (i : Fin Γ.1) →
    interpret Γ (Γ.get' i)
  unquote_pi (Γ : DContext Ty) (α T : Ty) (f : interpret (Γ.push (.type α)) (.type T)) : interpret Γ (.pi α T)


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
| _, _, WompWompLam.var Γ i => Unquote.unquote_var Γ i
| _, _, WompWompLam.pi Γ α β f => Unquote.unquote_pi Γ α β (WompWompLam.unquote (Γ.push (.type α)) (.type β) f)

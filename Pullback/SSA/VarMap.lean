import Pullback.SSA.Basic

open Lean

variable {α β} [DecidableEq α]

def Map.get_uniqueKeys (x : Map α β) (hx : x.uniqueKeys) : ∀ y ∈ x, x.get y.1 = y.2 := sorry

theorem Map.get_eq_some_imp_any (vars : Map α β) (key : α) (a : β) :
        vars.get key = some a → vars.any (·.1 = key) := by
    simp [Map.get, Array.findLast?, Array.find?_eq_some_iff_getElem]
    grind

theorem Map.get_isSome_iff_any (vars : Map α β) (key : α) :
    (vars.get key).isSome ↔ vars.any (·.1 = key) := sorry

theorem Map.get_mem {α β} [DecidableEq α] (vars : Map α β) (key : α) (val : β) :
        (key, val) ∈ vars → ∃ a, vars.get key = some a := by
    intro h
    have := Map.get_isSome_iff_any (α := α) (β := β)
    simp only [Option.isSome_iff_exists] at this
    simp only [this, Array.any_eq_true, decide_eq_true_eq]
    simp only [Array.mem_iff_getElem] at h
    grind


theorem Map.mem_get (vars: Map α β) (key : α) (val : β) :
    vars.get key = some val → (key, val) ∈ vars := sorry

theorem Map.get_push (vars : Map α β) (last : α × β) (key : α) :
    Map.get (vars.push last) key = if last.1 = key then some last.2 else vars.get key := sorry


theorem Map.get_eq_none_iff_not_any (vars : Map α β) (key : α) : vars.get key = none ↔ ¬ vars.any (·.1 = key) := sorry

/- two VarMaps are equivalent if the non shadowed variables agree on types at all names, and the set of unshadowed names is the same -/
def Map.equiv (vars₁ vars₂ : Map α β) : Prop :=
    {name | vars₁.any (·.1 = name)} = {name | vars₂.any (·.1 = name)} ∧ ∀ name, vars₁.any (·.1 = name) → vars₁.get name = vars₂.get name

def Map.equiv_symm {vars₁ vars₂ : Map α β} : vars₁.equiv vars₂ → vars₂.equiv vars₁ := by
    simp only [equiv, Array.any_eq_true', decide_eq_true_eq, forall_exists_index, and_imp]
    intro h1 h2
    have : ∀ (name : α) (x : α × β), x ∈ vars₂ → x.1 = name → Map.get vars₂ name = Map.get vars₁ name := by
        intro name a ha1 ha2
        rw [Set.ext_iff] at h1
        specialize h1 a.1
        grind
    tauto

def Map.equiv_push (vars₁ vars₂ : Map α β) (hvars : vars₁.equiv vars₂) (varname : α) (vartype : β) : Map.equiv (vars₁.push (varname, vartype)) (vars₂.push (varname, vartype)) := by
    simp only [equiv, Array.any_eq_true, decide_eq_true_eq, forall_exists_index, Array.size_push, Array.any_push', Bool.or_eq_true] at ⊢ hvars
    apply And.intro
    · ext name
      rw [Set.ext_iff] at hvars
      grind only [usr Set.mem_setOf_eq]
    · intro name H
      have := Map.get_push (α := α) (β := β)
      simp only [Prod.forall] at this
      rw [this]
      cases em (varname = name) with
      | inl hl =>
        simp only [hl, ↓reduceIte]
        cases H with
        | inl hll => grind
        | inr hlr =>
            grind only
      | inr hr =>
        simp [hr]
        grind only

def Map.equiv_push_of_shadow (vars : Map α β) (varname : α) (vartype : β) (hvar_type : vars.get varname = some vartype): Map.equiv vars (vars.push (varname, vartype)) := sorry

theorem SSAExpr.inferType_eq_of_vars_equiv (vars₁ vars₂ : VarMap) (hvars : vars₁.equiv vars₂) : (expr : SSAExpr) → expr.inferType vars₁ = expr.inferType vars₂
| const c => by simp only [inferType]
| letE varname val body => by
    simp only [inferType]
    rw [inferType_eq_of_vars_equiv vars₁ vars₂ hvars val]
    congr
    ext valType a
    have := inferType_eq_of_vars_equiv (vars₁.push (varname, valType)) (vars₂.push (varname, valType)) (Map.equiv_push vars₁ vars₂ hvars varname valType) body
    grind only
| lam varname type body => by
    simp only [inferType]
    have := inferType_eq_of_vars_equiv (vars₁.push (varname, type)) (vars₂.push (varname, type)) (Map.equiv_push vars₁ vars₂ hvars varname type) body
    grind only
| app f x => by
    simp only [inferType]
    rw [inferType_eq_of_vars_equiv vars₁ vars₂ hvars f, inferType_eq_of_vars_equiv vars₁ vars₂ hvars x]
| var name => by
    simp only [inferType]
    simp only [Map.equiv] at hvars
    match h : vars₁.get name with
    | some type =>
        have h' := h
        apply Map.get_eq_some_imp_any at h
        have := hvars.2 name (by grind)
        grind
    | none =>
        have h' := h
        rw [Map.get_eq_none_iff_not_any] at h
        have := hvars.1
        rw [Set.ext_iff] at this
        specialize this name
        simp only [Array.any_eq_true, decide_eq_true_eq, Set.mem_setOf_eq] at this
        grind only [Array.any_eq_true, Map.get_eq_none_iff_not_any]

def Map.submap (vars₁ vars₂ : Map α β) : Prop :=
    {name | vars₁.any (·.1 = name)} ⊆ {name | vars₂.any (·.1 = name)} ∧ ∀ name, vars₁.any (·.1 = name) → vars₁.get name = vars₂.get name

def Map.submap_push (vars₁ vars₂ : Map α β) (hvars : vars₁.submap vars₂) (varname : α) (vartype : β) : Map.submap (vars₁.push (varname, vartype)) (vars₂.push (varname, vartype)) := by
    simp only [submap, Array.any_eq_true, decide_eq_true_eq, forall_exists_index, Array.size_push, Array.any_push', Bool.or_eq_true] at ⊢ hvars
    apply And.intro
    · intro name
      simp only [Set.mem_setOf_eq]
      have := hvars.1
      intro HH
      cases HH with
      | inl hl =>
        specialize this hl
        grind
      | inr hr =>
        grind
    · intro name hName
      have := Map.get_push (α := α) (β := β)
      simp at this
      simp [this]
      cases em (varname = name) with
      | inl hl =>
        simp only [hl, ↓reduceIte]
      | inr hr =>
        simp only [hr, or_false, ↓reduceIte] at ⊢ hName
        grind

theorem Map.push_valid {var : α} {varT : β} {mutVars vars : Map α β} (hvarT : Map.get mutVars var = some varT) (hMut₂ : ∀ x ∈ mutVars, vars.get x.1 = some x.2) : ∀ (x : α × β), x ∈ mutVars → Map.get (Array.push vars (var, varT)) x.1 = some x.2 := by
    simp [Map.get_push]
    have : Map.get mutVars var = Map.get vars var := by
        have := Map.mem_get mutVars var varT hvarT
        specialize hMut₂ _ this
        grind
    have : Map.get vars var = varT := by grind
    grind

theorem SSAExpr.inferType!_eq_of_vars_equiv {vars₁ vars₂ : VarMap} (hvars : Map.equiv vars₁ vars₂) {expr : SSAExpr} :
    expr.inferType! vars₁ = expr.inferType! vars₂ := sorry

def ArgMap.submapVars (args : ArgMap) (vars : VarMap) : Prop := Map.submap (args.map (fun (name, x) => (name, x.inferType))) vars

def ArgMap.equivVars (args : ArgMap) (vars : VarMap) : Prop := Map.equiv (args.map (fun (name, x) => (name, x.inferType))) vars

def ArgMap.equivTypes (args₁ args₂ : ArgMap) : Prop := args₁.map (fun x => (x.1, x.2.inferType)) = args₂.map (fun x => (x.1, x.2.inferType))

theorem ArgMap.equivTypes_rfl (args: ArgMap) : args.equivTypes args := sorry

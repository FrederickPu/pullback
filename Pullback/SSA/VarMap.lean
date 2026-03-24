import Pullback.SSA.Basic

open Lean

theorem VarMap.get_eq_some_imp_any (vars : VarMap) (key : Name) (a : SSAType) : vars.get key = some a → vars.any (·.1 = key) := by
    simp [Array.get, Array.findLast?, Array.find?_eq_some_iff_getElem]
    grind

theorem VarMap.get_isSome_iff_any (vars : VarMap) (key : Name) : (vars.get key).isSome ↔ vars.any (·.1 = key) := sorry

theorem VarMap.get_mem (vars : VarMap) (name : Name) (type : SSAType) : (name, type) ∈ vars → ∃ a, vars.get name = some a := by
    intro h
    have := VarMap.get_isSome_iff_any
    simp only [Option.isSome_iff_exists] at this
    simp only [this, Array.any_eq_true, decide_eq_true_eq]
    simp only [Array.mem_iff_getElem] at h
    grind


theorem VarMap.mem_get (vars: VarMap) (name : Name) (type : SSAType) : vars.get name = some type → (name, type) ∈ vars := sorry

theorem VarMap.get_push (vars : VarMap) (last : Name × SSAType) (key : Name) : ((vars.push last)).get key = if last.1 = key then some last.2 else vars.get key := sorry


theorem VarMap.get_eq_none_iff_not_any (vars : VarMap) (key : Name) : vars.get key = none ↔ ¬ vars.any (·.1 = key) := sorry

/- two VarMaps are equivalent if the non shadowed variables agree on types at all names, and the set of unshadowed names is the same -/
def VarMap.equiv (vars₁ vars₂ : VarMap) : Prop :=
    {name | vars₁.any (·.1 = name)} = {name | vars₂.any (·.1 = name)} ∧ ∀ name, vars₁.any (·.1 = name) → vars₁.get name = vars₂.get name

def VarMap.equiv_push (vars₁ vars₂ : VarMap) (hvars : vars₁.equiv vars₂) (varname : Name) (vartype : SSAType) : (cast (β := VarMap) rfl (vars₁.push (varname, vartype))).equiv (vars₂.push (varname, vartype)) := by
    simp only [cast_eq]
    simp only [equiv, Array.any_eq_true, decide_eq_true_eq, forall_exists_index, Array.size_push, Array.any_push', Bool.or_eq_true] at ⊢ hvars
    apply And.intro
    · ext name
      rw [Set.ext_iff] at hvars
      grind only [usr Set.mem_setOf_eq]
    · intro name H
      have := VarMap.get_push
      simp only [cast_eq, Prod.forall] at this
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

theorem SSAExpr.inferType_eq_of_vars_equiv (vars₁ vars₂ : VarMap) (hvars : vars₁.equiv vars₂) : (expr : SSAExpr) → expr.inferType vars₁ = expr.inferType vars₂
| const c => by simp only [inferType]
| letE varname val body => by
    simp only [inferType]
    rw [inferType_eq_of_vars_equiv vars₁ vars₂ hvars val]
    congr
    ext valType a
    have := inferType_eq_of_vars_equiv (vars₁.push (varname, valType)) (vars₂.push (varname, valType)) (VarMap.equiv_push vars₁ vars₂ hvars varname valType) body
    grind only
| lam varname type body => by
    simp only [inferType]
    have := inferType_eq_of_vars_equiv (vars₁.push (varname, type)) (vars₂.push (varname, type)) (VarMap.equiv_push vars₁ vars₂ hvars varname type) body
    grind only
| app f x => by
    simp only [inferType]
    rw [inferType_eq_of_vars_equiv vars₁ vars₂ hvars f, inferType_eq_of_vars_equiv vars₁ vars₂ hvars x]
| var name => by
    simp only [inferType]
    simp only [VarMap.equiv] at hvars
    match h : vars₁.get name with
    | some type =>
        have h' := h
        apply VarMap.get_eq_some_imp_any at h
        have := hvars.2 name (by grind)
        grind
    | none =>
        have h' := h
        rw [VarMap.get_eq_none_iff_not_any] at h
        have := hvars.1
        rw [Set.ext_iff] at this
        specialize this name
        simp only [Array.any_eq_true, decide_eq_true_eq, Set.mem_setOf_eq] at this
        grind only [Array.any_eq_true, VarMap.get_eq_none_iff_not_any]

def VarMap.submap (vars₁ vars₂ : VarMap) : Prop :=
    {name | vars₁.any (·.1 = name)} ⊆ {name | vars₂.any (·.1 = name)} ∧ ∀ name, vars₁.any (·.1 = name) → vars₁.get name = vars₂.get name

def VarMap.submap_push (vars₁ vars₂ : VarMap) (hvars : vars₁.submap vars₂) (varname : Name) (vartype : SSAType) : (cast (β := VarMap) rfl (vars₁.push (varname, vartype))).submap (vars₂.push (varname, vartype)) := by
    simp only [cast_eq]
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
      have := VarMap.get_push
      simp at this
      simp [this]
      cases em (varname = name) with
      | inl hl =>
        simp only [hl, ↓reduceIte]
      | inr hr =>
        simp only [hr, or_false, ↓reduceIte] at ⊢ hName
        grind

theorem VarMap.push_valid {var : Name} {varT : SSAType} {mutVars vars : VarMap} (hvarT : Array.get mutVars var = some varT) (hMut₂ : ∀ x ∈ mutVars, vars.get x.1 = some x.2) : ∀ (x : Name × SSAType), x ∈ mutVars → (Array.push vars (var, varT)).get x.1 = some x.2 := by
    simp [VarMap.get_push]
    have : Array.get mutVars var = Array.get vars var := by
        have := VarMap.mem_get mutVars var varT hvarT
        specialize hMut₂ _ this
        grind
    have : Array.get vars var = varT := by grind
    grind

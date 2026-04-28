import Pullback.SSA.Basic

theorem List.subset_of_isPrefixOf {α} [BEq α] [LawfulBEq α] (x y : List α) : x.isPrefixOf y → x ⊆ y := by
    rw [List.isPrefixOf_iff_prefix]
    exact fun a => IsPrefix.subset a

open List

-- theorem Array.isPrefixOf_toList_isPrefixOf {α} [BEq α] (x y : Array α) : x.isPrefixOf y → x.toList.isPrefixOf y.toList := by
--     apply Array.isPrefixOf_toList

theorem Array.isPrefixOf_sublist {α} [BEq α] [LawfulBEq α] (as bs : Array α) : as.isPrefixOf bs → as.toList <+ bs.toList :=
    fun h =>
    have : as.toList.isPrefixOf (bs.toList) := by
        grind only [= Array.isPrefixOf_toList]
    have : List.IsPrefix as.toList bs.toList :=
        isPrefixOf_iff_prefix.mp this
    IsPrefix.sublist this

theorem Array.mem_isPrefixOf {α} [BEq α] [LawfulBEq α] (as bs : Array α) : as.isPrefixOf bs → ∀ x ∈ as, x ∈ bs := by
    intro h
    have := Array.isPrefixOf_sublist as bs h
    have : as.toList ⊆ bs.toList := Sublist.subset this
    intro x hx
    have : x ∈ as.toList := hx.val
    grind only [= List.subset_def, = mem_toList_iff, #d8ea]

open Lean

variable {α β} [DecidableEq α]


theorem Map.get_uniqueKeys (x : Map α β) (hx : x.uniqueKeys) : ∀ y ∈ x, x.get y.1 = y.2 := by
    intro y hy
    simp [Map.get, Array.findLast?, Map.uniqueKeys, Array.find?_eq_some_iff_getElem] at *
    sorry -- todo :: need Array.findLast?_eq_some_iff... style lemma

theorem Map.get_key (x : Map α β) : ∀ y ∈ x.keys, ∃ yy ∈ x, yy.1 = y ∧ (x.get y) = yy.2 := sorry

theorem Map.get_eq_some_imp_any (vars : Map α β) (key : α) (a : β) :
        vars.get key = some a → vars.any (·.1 = key) := by
    simp [Map.get, Array.findLast?, Array.find?_eq_some_iff_getElem]
    grind

theorem Map.get_isSome_iff_any (vars : Map α β) (key : α) :
    (vars.get key).isSome ↔ vars.any (·.1 = key) := by
    simp only [get, Array.findLast?, Option.isSome_map, Array.find?_isSome, Array.mem_reverse,
      decide_eq_true_eq, Prod.exists, exists_and_right, exists_eq_right, Array.any_eq_true']


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

def Map.push_submap_push (vars₁ vars₂ : Map α β) (hvars : vars₁.submap vars₂) (varname : α) (vartype : β) : Map.submap (vars₁.push (varname, vartype)) (vars₂.push (varname, vartype)) := by
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

theorem ArgMap.equivTypes_rfl (args: ArgMap) : args.equivTypes args := by
    grind [equivTypes]

theorem SSAExpr.inferType_mkMutTuple' (vars : VarMap) : (mutVars : VarMap) → (h1 : mutVars.uniqueKeys) → (h2 : mutVars.submap vars) → (mkMutTuple mutVars).fst.inferType vars = (mkMutTuple mutVars).snd := by
    intro mutVars h1 h2
    apply SSAExpr.inferType_mkMutTuple
    intro x hx
    simp only [Map.submap, Array.any_eq_true', decide_eq_true_eq,
        Set.setOf_subset_setOf] at h2
    apply Map.get_uniqueKeys at h1
    have hx' : x ∈ mutVars := by grind
    rw [← h1 x (by grind)]
    simp only [forall_exists_index] at h2
    exact (h2.2 x.1 x (by grind)).symm

open List

theorem Map.keys_subset_sublist (a b : Map α β) (hab : a.toList <+ b.toList) : a.keys.toList <+ b.keys.toList := by
    simp only [keys, Array.toList_map]
    grind

theorem Map.keys_prefixOf_sublist [BEq (α × β)] [LawfulBEq (α × β)] (a b : Map α β) (hab : Array.isPrefixOf a b) : a.keys.toList <+ b.keys.toList := by
    apply keys_subset_sublist
    exact Array.isPrefixOf_sublist a b hab

theorem Map.uniqueKeys_sublist (a b : Map α β) (hb : b.uniqueKeys) (hab : a.toList <+ b.toList) : a.uniqueKeys := by
    simp only [uniqueKeys] at *
    have := Map.keys_subset_sublist a b hab
    exact Sublist.nodup this hb

theorem Map.uniqueKeys_prefixOf [BEq (α × β)] [LawfulBEq (α × β)] (a b : Map α β) (hb : b.uniqueKeys) (hab : Array.isPrefixOf a b) : a.uniqueKeys := by
    simp only [uniqueKeys] at *
    have : a.keys.toList <+ b.keys.toList :=
        keys_prefixOf_sublist a b hab
    exact Sublist.nodup this hb

theorem Map.submap_trans (a b c : Map α β) : a.submap b → b.submap c → a.submap c := by
    simp only [submap, Array.any_eq_true', decide_eq_true_eq, Set.setOf_subset_setOf,
      forall_exists_index, and_imp]
    grind

theorem Map.submap_sublist [BEq (α × β)] [LawfulBEq (α × β)] (a b : Map α β) (hb : b.uniqueKeys) (hab : a.toList <+ b.toList) : a.submap b := by
    simp only [submap, Array.any_eq_true', decide_eq_true_eq, Set.setOf_subset_setOf,
      forall_exists_index]
    apply Map.keys_subset_sublist at hab
    have : a.keys.toList ⊆ b.keys.toList := by exact Sublist.subset hab
    apply And.intro
    sorry
    intro name x hh
    have hn : name ∈ a.keys := sorry
    have : name ∈ a.keys.toList := by sorry
    have : name ∈ b.keys := by (expose_names; exact Array.mem_def.mpr (this_1 this))
    have := get_key _ _ hn
    obtain ⟨x', hx'1, hx'2, Hx'⟩ := this
    rw [Hx']
    symm
    have := get_uniqueKeys b sorry x' sorry
    rw [← this]
    grind

theorem Map.submap_prefixOf [BEq (α × β)] [LawfulBEq (α × β)] (a b : Map α β) (hb : b.uniqueKeys) (hab : a.isPrefixOf b) : a.submap b := by
    sorry

theorem Map.keys_push {key val} (x : Map α β) : Map.keys (x.push (key, val)) = x.keys.push key := by
    grind [Map.keys]

theorem Map.keys_append (x y : Map α β) : Map.keys (x ++ y) = x.keys ++ y.keys := by
    simp [Map.keys]

theorem Map.keys_toArray (o : Option α) (v : β) :
        Map.keys (Option.map (fun a => (a, v)) o).toArray = o.toArray := by
    cases o
    case none => simp [Map.keys, Option.map, Option.toArray]
    case some a => simp [Map.keys, Option.map, Option.toArray]

theorem Map.mem_keys_option_map_toArray (o : Option α) (v : β) (x : α) :
        x ∈ Map.keys (Option.map (fun a => (a, v)) o).toArray ↔ x ∈ o.toArray := by
    cases o
    case none => simp [Option.map, Option.toArray, Map.keys]
    case some val => simp [Option.map, Option.toArray, Map.keys]

theorem Map.mem_keys_append_iff (x y : Map α β) (k : α) :
        k ∈ Map.keys (x ++ y) ↔ k ∈ x.keys ∨ k ∈ y.keys := by
    simp [Map.keys_append]

theorem Map.submap_push {key val} (x y : Map α β) (hxy : x.submap y) (hkey : key ∉ x.keys) : x.submap (y.push (key, val)) := sorry

theorem Map.uniqueKeys_push (m : Map α β) (k : α) (v : β)
    (hm : m.uniqueKeys) (hk : k ∉ m.keys) :
    Map.uniqueKeys (m.push (k, v)) := by
  simp only [uniqueKeys, keys, Array.map_push, Array.toList_push]
  simp [uniqueKeys] at hm
  rw [List.nodup_append]
  sorry

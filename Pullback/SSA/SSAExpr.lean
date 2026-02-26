import Pullback.SSA.VarMap

theorem SSAExpr.welltyped_app_iff (vars : VarMap) (f x : SSAExpr) : ((f.app x).inferType vars).isSome ↔ (do pure ((← f.inferType vars).funDom? = (← x.inferType vars))) = some True := by
    simp only [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff, SSAType.funDom?,
      Option.pure_def, Option.bind_eq_bind, Option.some.injEq, eq_iff_iff, iff_true]
    grind only


theorem SSAExpr.inferType_eq_of_vars_submap (vars₁ vars₂ : VarMap) (hvars : vars₁.submap vars₂) : (expr : SSAExpr) → (expr.inferType vars₁).isSome → expr.inferType vars₁ = expr.inferType vars₂
| const c => by simp [inferType]
| letE varname val body => by
    simp only [inferType]
    intro H
    simp [Option.isSome_iff_exists, Option.bind_eq_some_iff] at H
    rw [← inferType_eq_of_vars_submap vars₁ vars₂ hvars val]
    obtain ⟨bodyT, valT, hvalT, hbodyT⟩ := H
    simp [hvalT, hbodyT]
    have := inferType_eq_of_vars_submap (vars₁.push (varname, valT)) (vars₂.push (varname, valT)) (VarMap.submap_push _ _ hvars _ _) body (by grind)
    grind
    grind
| lam varname type body => by
    simp only [inferType]
    intro H
    simp [Option.isSome_iff_exists, Option.bind_eq_some_iff] at H
    obtain ⟨bodyT, hbodyT⟩ := H
    simp [hbodyT]
    have := inferType_eq_of_vars_submap (vars₁.push (varname, type)) (vars₂.push (varname, type)) (VarMap.submap_push _ _ hvars _ _) body (by grind)
    grind
| app f x => by
    simp only [inferType]
    intro H
    simp [Option.isSome_iff_exists, Option.bind_eq_some_iff] at H
    obtain ⟨finaltype, ftype, hftype, xtype, hxtype, hfinaltype⟩ := H
    have cruxf := inferType_eq_of_vars_submap vars₁ vars₂ hvars f (by grind)
    have cruxx := inferType_eq_of_vars_submap vars₁ vars₂ hvars x (by grind)
    simp [hftype, hxtype, ← cruxf, ← cruxx]
| var name => by
    simp only [inferType]
    intro H
    simp only [Option.isSome_iff_exists] at H
    obtain ⟨type, htype⟩ := H
    simp only [VarMap.submap, Array.any_eq_true, decide_eq_true_eq, Set.setOf_subset_setOf,
      forall_exists_index] at hvars
    have := VarMap.get_eq_some_imp_any _ _  _ htype
    simp only [Array.any_eq_true, decide_eq_true_eq] at this
    obtain ⟨i, hi, Hi⟩ := this
    grind only

open Lean

theorem SSAExpr.inferType_push_eq_of_hygenic (vars : VarMap) (newvar : Name) (newVarType : SSAType) (hHygenic : ¬ vars.any (·.1 = newvar)) : (expr : SSAExpr) → (expr.inferType vars).isSome → expr.inferType (vars.push (newvar, newVarType)) = expr.inferType vars
| const c => by simp [inferType]
| letE varName val body => by
    intro H
    simp only [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff] at H
    obtain ⟨bodyT, valT, hvalT, hbodyT⟩ := H
    have crux1 := inferType_push_eq_of_hygenic vars newvar newVarType hHygenic val (Option.isSome_of_mem hvalT)
    simp [inferType, hvalT, crux1]
    symm
    apply SSAExpr.inferType_eq_of_vars_submap
    simp [VarMap.submap]
    apply And.intro
    grind
    intro name hName
    have := VarMap.get_push
    simp at this
    simp [this]
    cases em (varName = name) with
    | inl hl =>
        simp [hl]
    | inr hr =>
        simp [hr]
        simp [Array.get, Array.findLast?, Array.find?_eq_some_iff_getElem]
        grind
    grind
| lam varname type body => by
    intro H
    simp only [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff, Option.some.injEq,
      ↓existsAndEq, and_true] at H
    obtain ⟨bodyT, hbodyT⟩ := H
    simp only [inferType, hbodyT, Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq,
      SSAType.fun.injEq, true_and, exists_eq_right]
    symm
    rw [← hbodyT]
    apply SSAExpr.inferType_eq_of_vars_submap
    simp [VarMap.submap]
    apply And.intro
    grind
    intro name hName
    have := VarMap.get_push
    simp at this
    simp [this]
    cases em (varname = name) with
    | inl hl =>
        simp [hl]
    | inr hr =>
        simp [hr]
        simp [Array.get, Array.findLast?, Array.find?_eq_some_iff_getElem]
        grind
    grind
| app f x => by
    intro H
    simp only [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff] at H
    obtain ⟨finaltype, ftype, hftype, xtype, hxtype, Hfinal⟩ := H
    simp only [inferType, hftype, hxtype, Option.bind_some]
    have cruxf := inferType_push_eq_of_hygenic vars newvar newVarType hHygenic f (Option.isSome_of_mem hftype)
    have cruxx := inferType_push_eq_of_hygenic vars newvar newVarType hHygenic x (Option.isSome_of_mem hxtype)
    simp only [cruxf, hftype, cruxx, hxtype, Option.bind_some]
| var name => by
    intro H
    simp only [inferType, Option.isSome_iff_exists] at H
    have := VarMap.get_push
    simp at this
    simp [inferType, this]
    obtain ⟨t, ht⟩ := H
    have := VarMap.get_eq_some_imp_any _ _ _ ht
    simp only [Array.any_eq_true, decide_eq_true_eq] at this
    simp at hHygenic
    grind

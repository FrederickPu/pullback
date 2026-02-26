import Pullback.SSA.Basic
import Pullback.SSA.VarMap
import Pullback.SSA.SSAExpr
import Pullback.SSA.SSADo

open Lean

theorem List.subset_of_isPrefixOf {α} [BEq α] [LawfulBEq α] (x y : List α) : x.isPrefixOf y → x ⊆ y := by
    rw [List.isPrefixOf_iff_prefix]
    exact fun a => IsPrefix.subset a


-- theorem Array.isPrefixOf_toList_isPrefixOf {α} [BEq α] (x y : Array α) : x.isPrefixOf y → x.toList.isPrefixOf y.toList := by
--     apply Array.isPrefixOf_toList


#check VarMap.get_mem
#check SSAType.funDom?_eq_some_iff
theorem SSADo.toSSAExpr_wellTyped (vars : VarMap) (mutVars : VarMap) (continueMutVars : VarMap) (hcontMutVars : continueMutVars.isPrefixOf mutVars) (kbreak kcontinue : Option Name) (hMut₁ : (mutVars.toList.map (·.1)).Nodup) (hMut₂ : ∀ x ∈ mutVars, vars.get x.1 = some x.2) : (prog : SSADo) → (hkBreak : validContinutationRef vars mutVars continueMutVars kbreak prog) → (hkContinue : validContinutationRef vars mutVars continueMutVars kcontinue prog) → (hp : (prog.toSSAExpr vars mutVars continueMutVars kbreak kcontinue).isSome) → (((prog.toSSAExpr vars mutVars continueMutVars kbreak kcontinue).get hp).inferType vars).isSome
| .expr e, hkBreak, hkContinue => by
    intro hp
    simp [toSSAExpr] at hp
    simp [Option.isSome_iff_exists, Option.bind_eq_some_iff] at hp
    obtain ⟨res, et, het, hres⟩ := hp
    match hkc : kcontinue with
    | some kc =>
        simp [validContinutationRef, validContinutation, Option.bind_eq_some_iff] at hkContinue
        obtain ⟨_, ⟨fkc, hfkc⟩, _⟩ := hkContinue
        have crux : (SSAExpr.inferType vars (mkMutTuple continueMutVars).fst) = (mkMutTuple continueMutVars).snd :=
          SSAExpr.inferType_mkMutTuple vars continueMutVars (by {
            intro x hx
            have : continueMutVars.toList.isPrefixOf (mutVars.toList) := by grind only [=
                Array.isPrefixOf_toList]
            have : continueMutVars.toList ⊆ mutVars.toList :=
              List.subset_of_isPrefixOf continueMutVars.toList mutVars.toList this
            have : x ∈ mutVars :=
                Array.mem_def.mpr (this hx.val)
            grind
          })
        have := hfkc.2
        obtain ⟨β, hb⟩ : ∃ β, fkc = .fun (mkMutTuple continueMutVars).2 β :=
          SSAType.funDom?_eq_some_iff fkc (mkMutTuple continueMutVars).2 this
        simp [toSSAExpr, SSAExpr.inferType, crux, hfkc.1, hb]
    | none =>
        simp [toSSAExpr, het]
| .letE var val rest, hkBreak, hkContinue => by
    intro hp
    simp only [toSSAExpr, Array.any_eq_true', decide_eq_true_eq, Option.bind_eq_bind,
        Option.isSome_iff_exists, Option.ite_none_left_eq_some, not_exists,
        Option.bind_eq_some_iff, Option.some.injEq, exists_and_left, ↓existsAndEq, and_true] at hp
    obtain ⟨h1, valT, hvalT, restExpr, hrestExpr⟩ := hp
    have : ∀ k, validContinutationRef vars mutVars continueMutVars k (letE var val rest) → validContinutationRef (vars.push (var, valT)) mutVars continueMutVars k rest := by
        intro k hk
        match k with
        | some k =>
            use hk.1
            simp [VarMap.get_push]
            have : var ≠ k := by
                have := hk.2.2
                simp [SSADo.vars] at this
                tauto
            simp [this]
            use hk.2.1
            have := hk.2.2
            simp [SSADo.vars] at this
            grind
        | none => grind [validContinutationRef]
    have := toSSAExpr_wellTyped (vars.push (var, valT)) mutVars continueMutVars (by grind) kbreak kcontinue hMut₁ (by grind [VarMap.get_push]) rest (this kbreak hkBreak) (this kcontinue hkContinue) (by grind)
    grind [toSSAExpr, SSAExpr.inferType, Option.isSome_iff_exists]
| .letM var val rest, hkBreak, hkContinue => by
    intro hp
    simp only [toSSAExpr, Array.any_eq_true', decide_eq_true_eq, Option.bind_eq_bind,
      Option.bind_none, Option.pure_def, Option.bind_some, Option.isSome_iff_exists,
      Option.ite_none_left_eq_some, not_exists, Option.bind_eq_some_iff, Option.some.injEq,
      exists_and_left, ↓existsAndEq, and_true] at hp
    obtain ⟨h1, varT, hvarT, a2, ha2⟩ := hp
    have : ∀ k, validContinutationRef vars mutVars continueMutVars k (letM var val rest) → validContinutationRef (vars.push (var, varT)) (mutVars.push (var, varT)) continueMutVars k rest := by
        intro k hk
        match k with
        | some k =>
            have : var ≠ k := by
                have := hk.2.2
                simp only [SSADo.vars, Array.append_eq_append, Array.mem_append, List.mem_toArray,
                  List.mem_cons, List.not_mem_nil, or_false, not_or] at this
                tauto
            refine ⟨?_, ?_, ?_⟩
            · rw [Array.any_push]
              simp only [hk.1, this, decide_false, Bool.or_self, Bool.false_eq_true,
                not_false_eq_true]
            · simp [VarMap.get_push, this]
              have := hk.2.1
              exact this
            · have := hk.2.2
              simp only [SSADo.vars, Array.append_eq_append, Array.mem_append, List.mem_toArray,
                List.mem_cons, List.not_mem_nil, or_false, not_or] at this
              tauto
        | none => grind [validContinutationRef]
    have := toSSAExpr_wellTyped (vars.push (var, varT)) (mutVars.push (var, varT)) continueMutVars (by {
        simp only [← Array.isPrefixOf_toList, List.isPrefixOf_iff_prefix,
          Array.toList_push] at ⊢ hcontMutVars
        grind only [usr List.prefix_append_of_prefix]
    }) kbreak kcontinue (by grind) (by grind [VarMap.get_push]) rest (this kbreak hkBreak) (this kcontinue hkContinue) (by simp [ha2])
    grind [toSSAExpr, SSAExpr.inferType, Option.isSome_iff_exists]
| .assign var val rest, hkBreak, hkContinue => by
    intro hp
    simp only [toSSAExpr, bne_iff_ne, ne_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_none,
      Option.bind_some, ite_not, Option.isSome_iff_exists, Option.bind_eq_some_iff,
      Option.ite_none_right_eq_some, Option.some.injEq, ↓existsAndEq, true_and, and_true,
      exists_and_left] at hp
    obtain ⟨varT, hvarT, HT, restExpr, hRestExpr⟩ := hp
    have : ∀ k, validContinutationRef vars mutVars continueMutVars k (assign var val rest) → validContinutationRef (vars.push (var, varT)) mutVars continueMutVars k rest := by
        intro k hk
        match k with
        | some k =>
            use hk.1
            simp [VarMap.get_push]
            have : var ≠ k := by
                have := hk.1
                apply VarMap.get_eq_some_imp_any at hvarT
                grind
            simp [this]
            use hk.2.1
            have := hk.2.2
            simp [SSADo.vars] at this
            grind
        | none => grind [validContinutationRef]
    have := toSSAExpr_wellTyped (vars.push ⟨var, varT⟩) mutVars continueMutVars (by {
        simp only [← Array.isPrefixOf_toList, List.isPrefixOf_iff_prefix] at ⊢ hcontMutVars
        grind only [usr List.prefix_append_of_prefix]
    }) kbreak kcontinue (by grind) (by {
        simp [VarMap.get_push]
        have : Array.get mutVars var = Array.get vars var := by
            have := VarMap.mem_get mutVars var varT hvarT
            specialize hMut₂ _ this
            grind
        have : Array.get vars var = varT := by grind
        grind
    }) rest (this kbreak hkBreak) (this kcontinue hkContinue) (by simp [hRestExpr])
    simp only [toSSAExpr, hvarT, HT, bne_iff_ne, ne_eq, Option.pure_def, Option.bind_eq_bind,
      Option.bind_none, Option.bind_some, ite_not, ↓reduceIte, Option.get_bind, Option.get_some,
      SSAExpr.inferType, this]
| .break, hkBreak, hkContinue => by
    intro hp
    match kbreak with
    | some kbreak' =>
        simp [toSSAExpr, Option.isSome_iff_exists, Option.bind_eq_some_iff] at hp
        obtain ⟨a, ha, H⟩ := hp
        simp only [toSSAExpr, Option.bind_eq_bind, Option.bind_some]
        have : (a.funDom?) = (mkMutTuple continueMutVars).2 := by
            grind
        apply SSAType.funDom?_eq_some_iff at this
        simp [ha, SSAExpr.inferType]
        rw [SSAExpr.inferType_mkMutTuple]
        grind
        · rw [← Array.isPrefixOf_toList] at hcontMutVars
          have := List.subset_of_isPrefixOf _ _ hcontMutVars
          intro x hx
          have := this hx.val
          rw [Array.mem_toList_iff] at this
          grind
    | none =>
        simp [toSSAExpr] at hp
| .continue, hkBreak, hkContinue => by
    intro hp
    match kcontinue with
    | some kcontinue' =>
        simp [toSSAExpr, Option.isSome_iff_exists, Option.bind_eq_some_iff] at hp
        obtain ⟨a, ha, H⟩ := hp
        simp only [toSSAExpr, Option.bind_eq_bind, Option.bind_some]
        have : (a.funDom?) = (mkMutTuple continueMutVars).2 := by
            grind
        apply SSAType.funDom?_eq_some_iff at this
        simp [ha, SSAExpr.inferType]
        rw [SSAExpr.inferType_mkMutTuple]
        grind
        · rw [← Array.isPrefixOf_toList] at hcontMutVars
          have := List.subset_of_isPrefixOf _ _ hcontMutVars
          intro x hx
          have := this hx.val
          rw [Array.mem_toList_iff] at this
          grind
    | none =>
        simp [toSSAExpr] at hp
| .return out, hkBreak, hkContinue => by
    intro hp
    grind [toSSAExpr, Option.isSome_iff_exists, Option.bind_eq_some_iff]
| .ifthenelse c t e rest, hkBreak, hkContinue => by
    unfold toSSAExpr
    extract_lets nKContinue nKBreak restMutVars nS
    intro hp
    simp [Option.isSome_iff_exists, Option.bind_eq_some_iff] at hp
    obtain ⟨⟨restExpr, hRestExpr⟩, hctype, tExpr, htExpr, type, htype₁, eExpr, heExpr, htype₂⟩ := hp
    have := toSSAExpr_wellTyped vars mutVars mutVars sorry nKBreak nKContinue hMut₁ hMut₂ t sorry sorry (by simp [htExpr])
    rw [Option.isSome_iff_exists] at this
    obtain ⟨tType, htType⟩ := this
    have := toSSAExpr_wellTyped vars mutVars mutVars sorry nKBreak nKContinue hMut₁ hMut₂ e sorry sorry (by simp [heExpr])
    rw [Option.isSome_iff_exists] at this
    obtain ⟨eType, heType⟩ := this
    have := toSSAExpr_wellTyped (Array.push vars (nS, (mkMutTuple mutVars).2))  mutVars continueMutVars sorry kbreak kcontinue hMut₁ sorry rest sorry sorry sorry
    rw [Option.isSome_iff_exists] at this
    obtain ⟨restType, hRestType⟩ := this
    simp [hRestExpr] at hRestType
    -- want lemma about `inferType (destructMutTuple) = .fun _ inferType`
    simp [SSAExpr.inferType, hctype]
    rw [SSAExpr.inferType_destructMutTuple]
    have : (SSAExpr.inferType (Array.push vars (nS, (mkMutTuple mutVars).2) ++ mutVars) restExpr) = (SSAExpr.inferType (Array.push vars (nS, (mkMutTuple mutVars).2)) restExpr) := sorry
    simp [hRestExpr, this, hRestType]
    rw [SSAExpr.inferType_destructMutTuple]
    have : (SSAExpr.inferType
              ((Array.push vars (nKBreak, (mkMutTuple mutVars).2.fun restType)).push (nS, (mkMutTuple mutVars).2) ++
                mutVars)
              restExpr) = (SSAExpr.inferType (Array.push vars (nS, (mkMutTuple mutVars).2)) restExpr) := sorry
    simp [this, hRestType, SSAConst.inferType]
    have : (SSAExpr.inferType
                  ((Array.push vars (nKBreak, (mkMutTuple mutVars).2.fun restType)).push
                    (nKContinue, (mkMutTuple mutVars).2.fun restType))
                  c) = SSAType.ofBase .int := sorry
    simp [this, htExpr]
    have : (SSAExpr.inferType
              ((Array.push vars (nKBreak, (mkMutTuple mutVars).2.fun restType)).push
                (nKContinue, (mkMutTuple mutVars).2.fun restType))
              tExpr) = tType := sorry
    simp [this]
    have : (SSAExpr.inferType vars tExpr) = tType := sorry
    simp [this, heExpr]
    have : (SSAExpr.inferType
          ((Array.push vars (nKBreak, (mkMutTuple mutVars).2.fun restType)).push
            (nKContinue, (mkMutTuple mutVars).2.fun restType))
          eExpr) = eType := sorry
    simp [this]
    grind
    sorry
    sorry
| .loop body rest, hkBreak, hkContinue => sorry
| .seq s₁ s₂, hkBreak, hkContinue => sorry

#check SSADo

#check HEq

/- if deep embedding evaluates to a const it will evaluate to the same value of given by the shallow embedding -/
-- theorem SSADo.eval_eq_toexpr_interp (args : VarMap) (prog : SSADo) : ∀ input, ∀ x, prog.eval args input = some x → ∃ y, prog.toSSAExpr args #[] none none = some y ∧ x.interp ≍ y.interp! args := sorry

/-
     IR.eval
   IR ----> Const
   |
   |           ==
   |
   V     SSADO.eval
   SSADo ----> Const
-/
/-
    IR --> (SSADo ---> SSAExpr ----> Const) = IR --> (SSADo ---> Const)
    IR ---> SSADo ---> Const = IR ---> Const

    translation : IR ---> Lean.Expr
    proof of equivalence : IR ---> Lean.Expr
-/
-- IR deep embedding

-- note: eventually to fully have unambiguous semantics will eventually want to have a verified parser too
-- this can be done is a decoupled way by having a spec for what a lawful parscombinator ( the << thing for parsers in lean) to allow for different implementations of the same parser (eg recursive parsing vs shunting yard)

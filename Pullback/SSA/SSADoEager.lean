import Pullback.SSA.Basic
import Pullback.SSA.VarMap
import Pullback.SSA.SSAExpr
import Pullback.SSA.SSADo
import Pullback.SSA.Tactic

open Lean

def SSADo.toSSAExpr? (vars : VarMap) (mutVars : VarMap) (kMutVars : VarMap) (kbreak kcontinue : Option Name) : SSADo → Option SSAExpr
-- note: only trailing exprs are interpreted as return types
-- ie: `do if cond then 10 else 10` is invalid but `do if cond then return 10 else (); 10` is valid
| expr e => do
    -- e needs to be well typed
    let etype ← e.inferType vars
    match kcontinue with
    | some kcontinue =>
        -- loop body should not end in non unit type
        if etype = .ofBase .unit then
            -- todo :: don't discard `e` and use bind
            SSAExpr.app (SSAExpr.var kcontinue) (mkMutTuple kMutVars).1
        else
            none
    | none => do
        some e
| seq s₁ s₂ => do pure <| SSAExpr.letE (freshName (Array.append s₁.mutVars s₂.mutVars) `x) (← s₁.toSSAExpr? vars mutVars kMutVars kbreak kcontinue) (← s₂.toSSAExpr? vars mutVars kMutVars kbreak kcontinue)
| letE var val rest => do
    if mutVars.any (·.1 = var) then
        none
    else
        let valT ← val.inferType vars
        SSAExpr.letE var val (← rest.toSSAExpr? (vars.push (var, valT)) mutVars kMutVars kbreak kcontinue)
| letM var val rest => do
    if mutVars.any (·.1 = var) then
        none
    let valT ← val.inferType vars

    SSAExpr.letE var val (← rest.toSSAExpr? (vars.push (var, valT)) (mutVars.push (var, valT)) kMutVars kbreak kcontinue)
| assign var val rest => do
    let varT ← mutVars.get var
    let valT ← val.inferType vars
    if valT != varT then
        none
    return SSAExpr.letE var val (← rest.toSSAExpr? (vars.push (var, valT)) mutVars kMutVars kbreak kcontinue)
| loop body rest => do
    let (mutTuple, mutTupleType) := (mkMutTuple mutVars)
    let bodyMutVars : Array Name  := body.mutVars
    let nS : Name := freshName (Array.append (mutVars.map (·.1)) bodyMutVars) `s
    let restExpr ← rest.toSSAExpr? vars mutVars kMutVars kbreak kcontinue
    let breakNew : SSAExpr ← SSAExpr.lam nS mutTupleType <| (destructMutTuple nS mutVars restExpr)
    let nKBreak : Name := freshName (vars.map (·.1) ++ body.vars) `kbreak
    let nKContinue : Name := freshName (vars.map (·.1) ++ body.vars) `kcontinue
    -- todo :: modify mutvars passed into toSSAExpr for body
    let bodyExpr ← body.toSSAExpr? vars mutVars mutVars nKBreak nKContinue
    let bodyType ← bodyExpr.inferType vars
    if (← restExpr.inferType vars) != bodyType then
        none
    let body' : SSAExpr ← destructMutTuple nS mutVars bodyExpr
    SSAExpr.letE nKBreak breakNew <|
        SSAExpr.app (SSAExpr.app (SSAExpr.const (SSAConst.loop mutTupleType bodyType)) mutTuple) (SSAExpr.lam nKContinue (SSAType.fun mutTupleType (SSAType.ofBase .unit)) (SSAExpr.lam nS mutTupleType body'))
| .break => do
    let (kmutTuple, kmutType) := (mkMutTuple kMutVars)
    let kbreak' ← kbreak
    if kmutType != (← vars.get kbreak').funDom? then
        none
    SSAExpr.app (SSAExpr.var kbreak') kmutTuple
| .continue => do
    let (kmutTuple, kmutType) := (mkMutTuple kMutVars)
    let kcontinue' ← kcontinue
    if kmutType != (← vars.get kcontinue').funDom? then
        none
    SSAExpr.app (SSAExpr.var (← kcontinue)) kmutTuple
| .return out => do
    let _ ← out.inferType vars
    return out
| ifthenelse cond t e rest => do
    let (_, mutTupleType) := (mkMutTuple mutVars)
    let nKContinue : Name := freshName ((vars.map (·.1) ++ t.vars ++ e.vars)) `kcontinue
    let nKBreak : Name := freshName ((vars.map (·.1) ++ t.vars ++ e.vars)) `kbreak
    let restMutVars : Array Name := rest.mutVars
    let nS : Name := freshName (Array.append (mutVars.map (·.1)) restMutVars) `s
    -- todo :: pass expanded mutvars into toSSAExpr
    let restExpr ← rest.toSSAExpr? vars mutVars kMutVars kbreak kcontinue
    let restType ← restExpr.inferType vars
    let continue' := (SSAExpr.lam nS mutTupleType <| destructMutTuple nS mutVars restExpr)
    let kbreak' := (SSAExpr.lam nS mutTupleType <| destructMutTuple nS mutVars restExpr)
    if (← cond.inferType vars) != SSAType.ofBase .int then
        none
    let texpr ← t.toSSAExpr? (vars.push (nKBreak, .fun mutTupleType restType)) mutVars mutVars nKBreak nKContinue
    let tExprType ← texpr.inferType (Array.push vars (nKBreak, (mkMutTuple mutVars).2.fun restType))
    let eExpr ← e.toSSAExpr? (vars.push (nKBreak, .fun mutTupleType restType)) mutVars mutVars nKBreak nKContinue
    let eExprType ← eExpr.inferType (Array.push vars (nKBreak, (mkMutTuple mutVars).2.fun restType))
    if tExprType != eExprType then
        none
    SSAExpr.letE nKBreak kbreak' <| SSAExpr.letE nKContinue continue' <|
    SSAExpr.app (SSAExpr.app (SSAExpr.app (.const (.ifthenelse tExprType)) cond) texpr) (eExpr)

-- example (l r : List Nat) : l ⊆ r → ∀ x ∈ l, x ∈ r := by grind only [= List.subset_def,
--   #0b8b]

theorem SSADo.toSSAExpr?_wellTyped (vars : VarMap) (mutVars : VarMap) (continueMutVars : VarMap) (hcontMutVars : continueMutVars.isPrefixOf mutVars) (kbreak kcontinue : Option Name) (hMut₁ : (mutVars.toList.map (·.1)).Nodup) (hMut₂ : ∀ x ∈ mutVars, vars.get x.1 = some x.2) : (prog : SSADo) → (hkBreak : validContinutationRef vars mutVars continueMutVars kbreak prog) → (hkContinue : validContinutationRef vars mutVars continueMutVars kcontinue prog) → (hp : (prog.toSSAExpr? vars mutVars continueMutVars kbreak kcontinue).isSome) → (((prog.toSSAExpr? vars mutVars continueMutVars kbreak kcontinue).get hp).inferType vars).isSome
| .expr e, hkBreak, hkContinue => by sorry
    -- intro hp
    -- simp only [toSSAExpr] at hp
    -- option_elim
    -- match hkc : kcontinue with
    -- | some kc =>
    --     simp [validContinutationRef, validContinutation, Option.bind_eq_some_iff] at hkContinue
    --     obtain ⟨_, ⟨fkc, hfkc⟩, _⟩ := hkContinue
    --     have crux : (SSAExpr.inferType vars (mkMutTuple continueMutVars).fst) = (mkMutTuple continueMutVars).snd :=
    --       SSAExpr.inferType_mkMutTuple vars continueMutVars (by {
    --         intro x hx
    --         have : x ∈ mutVars :=
    --           Array.mem_isPrefixOf continueMutVars mutVars hcontMutVars x hx
    --         grind
    --       })
    --     have := hfkc.2
    --     obtain ⟨β, hb⟩ : ∃ β, fkc = .fun (mkMutTuple continueMutVars).2 β :=
    --       SSAType.funDom?_eq_some_iff fkc (mkMutTuple continueMutVars).2 this
    --     simp [toSSAExpr, SSAExpr.inferType, crux, hfkc.1, hb, SSAType.funDom?, SSAType.funCodom?]
    -- | none =>
    --     simp [toSSAExpr, hetype]
| .letE var val rest, hkBreak, hkContinue => by sorry
    -- intro hp
    -- option_elim
    -- simp only [toSSAExpr, Array.any_eq_true', decide_eq_true_eq, Option.bind_eq_bind,
    --   Option.ite_none_left_eq_some] at hp
    -- obtain ⟨h1, hp⟩ := hp
    -- option_elim
    -- have : ∀ k, validContinutationRef vars mutVars continueMutVars k (letE var val rest) → validContinutationRef (vars.push (var, valT)) mutVars continueMutVars k rest :=
    --   fun k a => validContinutationRef_letE_elim k a
    -- have := toSSAExpr_wellTyped (vars.push (var, valT)) mutVars continueMutVars (by grind) kbreak kcontinue hMut₁ (by grind [VarMap.get_push]) rest (this kbreak hkBreak) (this kcontinue hkContinue) (by grind)
    -- grind [toSSAExpr, SSAExpr.inferType, Option.isSome_iff_exists]
| .letM var val rest, hkBreak, hkContinue => by sorry
    -- intro hp
    -- simp only [toSSAExpr, Array.any_eq_true', decide_eq_true_eq] at hp
    -- option_elim
    -- -- TODO :: make option_elim handle if then else better so this step can be done by option_elim too
    -- rw [Option.bind_eq_bind, Option.bind_none, Option.ite_none_left_eq_some] at hp
    -- obtain ⟨hvar, hp⟩ := hp
    -- option_elim
    -- have : ∀ k, validContinutationRef vars mutVars continueMutVars k (letM var val rest) → validContinutationRef (vars.push (var, valT)) (mutVars.push (var, valT)) continueMutVars k rest :=
    --   fun k a => validContinutationRef_letM_elim k a
    -- have := toSSAExpr_wellTyped (vars.push (var, valT)) (mutVars.push (var, valT)) continueMutVars (by {
    --     simp only [← Array.isPrefixOf_toList, List.isPrefixOf_iff_prefix,
    --       Array.toList_push] at ⊢ hcontMutVars
    --     grind only [usr List.prefix_append_of_prefix]
    -- }) kbreak kcontinue (by grind) (by grind [VarMap.get_push]) rest (this kbreak hkBreak) (this kcontinue hkContinue) (by simp [hdolift])
    -- grind [toSSAExpr, SSAExpr.inferType, Option.isSome_iff_exists]
| .assign var val rest, hkBreak, hkContinue => by sorry
    -- intro hp
    -- simp only [toSSAExpr] at hp
    -- option_elim
    -- rw [Option.bind_eq_bind, Option.bind_none, Option.ite_none_left_eq_some] at hp
    -- obtain ⟨hvalT', hRestExpr⟩ := hp
    -- option_elim
    -- have : ∀ k, validContinutationRef vars mutVars continueMutVars k (assign var val rest) → validContinutationRef (vars.push (var, varT)) mutVars continueMutVars k rest :=
    --   fun k a => validContinutationRef_assign_elim hvarT k a
    -- have := toSSAExpr_wellTyped (vars.push ⟨var, varT⟩) mutVars continueMutVars (by {
    --     simp only [← Array.isPrefixOf_toList, List.isPrefixOf_iff_prefix] at ⊢ hcontMutVars
    --     grind only [usr List.prefix_append_of_prefix]
    -- }) kbreak kcontinue (by grind) (VarMap.push_valid hvarT hMut₂) rest (this kbreak hkBreak) (this kcontinue hkContinue) (by {
    --     expose_names
    --     simp at hvalT'
    --     rw [hvalT'] at hdolift
    --     simp [hdolift]
    -- })
    -- expose_names
    -- simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hvalT'
    -- grind [toSSAExpr, SSAExpr.inferType]
| .break, hkBreak, hkContinue => by sorry
    -- intro hp
    -- match kbreak with
    -- | some kbreak' =>
    --     simp only [toSSAExpr] at hp
    --     option_elim
    --     simp only [bne_iff_ne, ne_eq, Option.bind_eq_bind, Option.bind_none, Option.pure_def,
    --       Option.bind_some, ite_not, Option.ite_none_right_eq_some, Option.some.injEq] at hp
    --     obtain ⟨ha, H⟩ := hp
    --     simp only [toSSAExpr, Option.bind_eq_bind, Option.bind_some]
    --     have : (dolift.funDom?) = (mkMutTuple continueMutVars).2 := by
    --         grind
    --     apply SSAType.funDom?_eq_some_iff at this
    --     simp [ha, SSAExpr.inferType]
    --     rw [SSAExpr.inferType_mkMutTuple]
    --     grind [SSAExpr.inferType, toSSAExpr, SSAType.funDom?, SSAType.funCodom?]
    --     · rw [← Array.isPrefixOf_toList] at hcontMutVars
    --       have := List.subset_of_isPrefixOf _ _ hcontMutVars
    --       intro x hx
    --       have := this hx.val
    --       rw [Array.mem_toList_iff] at this
    --       grind
    -- | none =>
    --     simp [toSSAExpr] at hp
| .continue, hkBreak, hkContinue => by sorry
    -- intro hp
    -- match kcontinue with
    -- | some kcontinue' =>
    --     simp only [toSSAExpr] at hp
    --     option_elim
    --     simp only [bne_iff_ne, ne_eq, Option.bind_some, Option.bind_eq_bind, Option.bind_none,
    --       Option.pure_def, ite_not, Option.ite_none_right_eq_some, Option.some.injEq] at hp
    --     obtain ⟨ha', H⟩ := hp
    --     simp only [toSSAExpr, Option.bind_eq_bind, Option.bind_some]
    --     have : (dolift.funDom?) = (mkMutTuple continueMutVars).2 := by
    --         grind
    --     apply SSAType.funDom?_eq_some_iff at this
    --     simp [ha', SSAExpr.inferType]
    --     rw [SSAExpr.inferType_mkMutTuple]
    --     grind [SSAExpr.inferType, toSSAExpr, SSAType.funDom?, SSAType.funCodom?]
    --     · rw [← Array.isPrefixOf_toList] at hcontMutVars
    --       have := List.subset_of_isPrefixOf _ _ hcontMutVars
    --       intro x hx
    --       have := this hx.val
    --       rw [Array.mem_toList_iff] at this
    --       grind
    -- | none =>
    --     simp [toSSAExpr] at hp
| .return out, hkBreak, hkContinue => by sorry
    -- intro hp
    -- grind [toSSAExpr, Option.isSome_iff_exists, Option.bind_eq_some_iff]
| .ifthenelse c t e rest, hkBreak, hkContinue => by
    unfold toSSAExpr?
    extract_lets nKContinue nKBreak restMutVars nS
    intro hp
    option_elim
    simp at hp
    option_elim
    simp at hp
    obtain ⟨hc, hp⟩ := hp
    option_elim
    simp at hp
    obtain ⟨Hte, hp⟩ := hp
    expose_names
    simp [ha_1, hdolift, hc]
    apply SSAExpr.welltyped_letE_of_welltyped_val_body _ _ _ _ (.fun (mkMutTuple mutVars).2 restType) sorry
    apply SSAExpr.welltyped_letE_of_welltyped_val_body _ _ _ _ (.fun (mkMutTuple mutVars).2 restType) sorry
    sorry
    -- rw [SSAExpr.inferType_destructMutTuple]
    -- have : (SSAExpr.inferType (Array.push vars (nS, (mkMutTuple mutVars).2) ++ mutVars) a_1) = restType := sorry
    -- simp [this]
    -- rw [SSAExpr.inferType_destructMutTuple]
    -- have : SSAExpr.inferType
    --           ((Array.push vars (nKBreak, (mkMutTuple mutVars).2.fun restType)).push (nS, (mkMutTuple mutVars).2) ++
    --             mutVars)
    --           a_1 = restType := sorry
    -- simp [this]
    -- have :  SSAExpr.inferType vars c = SSAType.ofBase SSABaseType.int := by grind
    -- have : SSAExpr.inferType
    --               ((Array.push vars (nKBreak, (mkMutTuple mutVars).2.fun restType)).push
    --                 (nKContinue, (mkMutTuple mutVars).2.fun restType))
    --               c = SSAType.ofBase SSABaseType.int := sorry
    -- simp [this]

    -- simp only [bne_iff_ne, ne_eq, Option.bind_none, Option.pure_def,
    --   Option.bind_some, ite_not, Option.isSome_iff_exists, Option.bind_eq_some_iff,
    --   Option.ite_none_right_eq_some, Option.some.injEq, ↓existsAndEq, true_and, and_true,
    --   exists_and_left] at hp

    -- obtain ⟨restExpr, hRestExpr, restType, hRestType, hctype, tExpr, htExpr, type, htype₁, eExpr, heExpr, htype₂⟩ := hp
    -- have := toSSAExpr_wellTyped (Array.push vars (nKBreak, (mkMutTuple mutVars).2.fun restType)) mutVars mutVars (by {
    --     rw [← Array.isPrefixOf_toList]
    --     grind
    -- }) nKBreak nKContinue hMut₁ (by {
    --     simp [VarMap.get_push]
    --     intro a b hab

    --     have : nKBreak ≠ a := by sorry
    --     simp [this]
    --     grind
    -- }) t (by {sorry}) sorry (by simp [htExpr])
    -- rw [Option.isSome_iff_exists] at this
    -- obtain ⟨tType, htType⟩ := this
    -- have := toSSAExpr_wellTyped (Array.push vars (nKBreak, (mkMutTuple mutVars).2.fun restType)) mutVars mutVars sorry nKBreak nKContinue hMut₁ sorry e sorry sorry (by simp [heExpr])
    -- rw [Option.isSome_iff_exists] at this
    -- obtain ⟨eType, heType⟩ := this
    -- have := toSSAExpr_wellTyped (vars)  mutVars continueMutVars sorry kbreak kcontinue hMut₁ sorry rest sorry sorry sorry
    -- rw [Option.isSome_iff_exists] at this
    -- -- want lemma about `inferType (destructMutTuple) = .fun _ inferType`
    -- simp only [hctype, bne_iff_ne, ne_eq, Option.bind_eq_bind, Option.bind_none, Option.pure_def,
    --   Option.bind_some, ite_not, ↓reduceIte, Option.get_bind, Option.get_ite, SSAExpr.inferType]
    -- rw [SSAExpr.inferType_destructMutTuple]
    -- have : (SSAExpr.inferType (Array.push vars (nS, (mkMutTuple mutVars).2) ++ mutVars) restExpr) = (SSAExpr.inferType (Array.push vars (nS, (mkMutTuple mutVars).2)) restExpr) := sorry
    -- simp only [hRestExpr, Option.get_some, this, hRestType]
    -- have : SSAExpr.inferType (Array.push vars (nS, (mkMutTuple mutVars).2)) restExpr = SSAExpr.inferType vars restExpr := sorry
    -- rw [this]
    -- simp only [hRestType, Option.bind_some]
    -- rw [SSAExpr.inferType_destructMutTuple]
    -- have : (SSAExpr.inferType
    --           ((Array.push vars (nKBreak, (mkMutTuple mutVars).2.fun restType)).push (nS, (mkMutTuple mutVars).2) ++
    --             mutVars)
    --           restExpr) = (SSAExpr.inferType (vars) restExpr) := sorry
    -- simp only [this, hRestType, Option.bind_some, SSAConst.inferType]
    -- have : (SSAExpr.inferType
    --               ((Array.push vars (nKBreak, (mkMutTuple mutVars).2.fun restType)).push
    --                 (nKContinue, (mkMutTuple mutVars).2.fun restType))
    --               c) = SSAType.ofBase .int := sorry
    -- simp only [this, htExpr, Option.get_some, Option.bind_some, ↓reduceIte]
    -- have : (SSAExpr.inferType
    --           ((Array.push vars (nKBreak, (mkMutTuple mutVars).2.fun restType)).push
    --             (nKContinue, (mkMutTuple mutVars).2.fun restType))
    --           tExpr) = tType := sorry
    -- simp only [this, Option.bind_some]
    -- have : (SSAExpr.inferType vars tExpr) = tType := sorry
    -- simp only [this, Option.get_some, ↓reduceIte, heExpr, Option.bind_some]
    -- have : (SSAExpr.inferType
    --       ((Array.push vars (nKBreak, (mkMutTuple mutVars).2.fun restType)).push
    --         (nKContinue, (mkMutTuple mutVars).2.fun restType))
    --       eExpr) = eType := sorry
    -- simp only [this, Option.bind_some, Option.isSome_ite]
    -- grind
    -- sorry
    -- sorry
| .loop body rest, hkBreak, hkContinue => sorry
| .seq s₁ s₂, hkBreak, hkContinue => sorry

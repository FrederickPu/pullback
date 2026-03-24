import Pullback.SSA.Basic
import Pullback.SSA.VarMap
import Pullback.SSA.SSAExpr
import Pullback.SSA.SSADo
import Pullback.SSA.Tactic

open Lean

theorem List.subset_of_isPrefixOf {α} [BEq α] [LawfulBEq α] (x y : List α) : x.isPrefixOf y → x ⊆ y := by
    rw [List.isPrefixOf_iff_prefix]
    exact fun a => IsPrefix.subset a

set_option maxHeartbeats 100000

-- theorem Array.isPrefixOf_toList_isPrefixOf {α} [BEq α] (x y : Array α) : x.isPrefixOf y → x.toList.isPrefixOf y.toList := by
--     apply Array.isPrefixOf_toList

theorem Array.isPrefixOf_sublist {α} [BEq α] [LawfulBEq α] (as bs : Array α) : as.isPrefixOf bs → as.toList ⊆ bs.toList :=
    fun h =>
    have : as.toList.isPrefixOf (bs.toList) := by
        grind only [= Array.isPrefixOf_toList]
    List.subset_of_isPrefixOf as.toList bs.toList this

theorem Array.mem_isPrefixOf {α} [BEq α] [LawfulBEq α] (as bs : Array α) : as.isPrefixOf bs → ∀ x ∈ as, x ∈ bs := by
    intro h
    have := Array.isPrefixOf_sublist as bs h
    intro x hx
    have : x ∈ as.toList := hx.val
    grind only [= List.subset_def, = mem_toList_iff, #d8ea]

theorem SSADo.validContinutationRef_letE_elim {vars mutVars continueMutVars} : ∀ k, validContinutationRef vars mutVars continueMutVars k (letE var val rest) → validContinutationRef (vars.push (var, valT)) mutVars continueMutVars k rest := by
    intro k hk
    match k with
    | some k =>
        use hk.1
        simp only [VarMap.get_push, Option.pure_def, Option.bind_eq_bind]
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

theorem SSADo.validContinutationRef_letM_elim{vars mutVars continueMutVars} : ∀ k, validContinutationRef vars mutVars continueMutVars k (letM var val rest) → validContinutationRef (vars.push (var, varT)) (mutVars.push (var, varT)) continueMutVars k rest := by
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

theorem SSADo.validContinutationRef_assign_elim {vars mutVars continueMutVars} (hvarT : Array.get mutVars var = some varT) : ∀ k, validContinutationRef vars mutVars continueMutVars k (assign var val rest) → validContinutationRef (vars.push (var, varT)) mutVars continueMutVars k rest := by
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

#check VarMap.get_push
#check VarMap.get_mem
#check SSAType.funDom?_eq_some_iff

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

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

theorem SSADo.eval_eq_eval_toSSAExpr! {kbreak kcontinue : Option (ArgMap → Option SSAConst)} {nkbreak nkcontinue : Option Name} {args mutArgs kmutArgs : ArgMap} {vars mutVars kmutVars : VarMap}
 (hMut₁ : (mutVars.toList.map (·.1)).Nodup) (hMut₂ : ∀ x ∈ mutVars, vars.get x.1 = some x.2)
 (hcontMutVars : kmutVars.isPrefixOf mutVars)
 (halign : args.submapVars vars)
 (halignMut : mutArgs.equivVars mutVars)
 (halignkMut : kmutArgs.equivVars kmutVars)
 (prog : SSADo)
 (hkBreak : kbreak.All kmutArgs.validContinutation)
 (hkContinue : kcontinue.All kmutArgs.validContinutation)
 (hnkBreak : nkbreak.All (prog.validContinutationRef vars mutVars kmutVars))
 (hnkContinue : nkcontinue.All (prog.validContinutationRef vars mutVars kmutVars)) :
    ∀ x, prog.eval args mutArgs kmutArgs kbreak kcontinue = some x →
        x = (prog.toSSAExpr! vars mutVars kmutVars nkbreak nkcontinue).eval args := sorry
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

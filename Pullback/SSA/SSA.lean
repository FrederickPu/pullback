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

#check Subtype.mk
def Option.subtypeMap {α : Type} {P Q : α → Prop} (hP : ∀ x, P x → Q x) : Option (Subtype P) → Option (Subtype Q) :=
    Option.map (Subtype.map _ hP)


theorem Map.submap_get_uniqueKeys {α β} [DecidableEq α] (vars₁ vars₂ : Map α β) (hvars₁ : vars₁.uniqueKeys) :
        vars₁.submap vars₂ → ∀ x ∈ vars₁, vars₂.get x.1 = some x.2 := by
    intro hvars
    simp only [submap, Array.any_eq_true', decide_eq_true_eq, Set.setOf_subset_setOf,
     forall_exists_index] at hvars
    have := hvars.2
    intro x hx
    specialize this x.1 x ⟨hx, (by grind)⟩
    rw [← this]
    exact get_uniqueKeys vars₁ hvars₁ x hx

-- todo :: add hyps for alignment between the continutations in name and function form (kbreak and nkbreak)
def SSADo.evalRefined {args mutArgs kmutArgs : ArgMap} {kbreak kcontinue : Option (ArgMap → Option SSAConst)} {vars mutVars kmutVars : VarMap} {nkbreak nkcontinue : Option Name}
    (hMut : mutVars.uniqueKeys)
    (hcontMutVars : kmutVars.isPrefixOf mutVars)
    (halign : args.submapVars vars)
    (halignMut : mutArgs.equivVars mutVars)
    (halignkMut : kmutArgs.equivVars kmutVars) :
    (prog : SSADo) →
        Option {x : SSAConst //
            (hkBreak : kbreak.All kmutArgs.validContinutation) →
            (hkContinue : kcontinue.All kmutArgs.validContinutation) →
            (hnkBreak : nkbreak.All (prog.validContinutationRef vars mutVars kmutVars)) →
            (hnkContinue : nkcontinue.All (prog.validContinutationRef vars mutVars kmutVars)) →
            x = (prog.toSSAExpr! vars mutVars kmutVars nkbreak nkcontinue).eval args}
| expr e => do
    match kcontinue with
    | some kcontinue =>
        -- todo :: don't discard `e` and use bind
        (kcontinue kmutArgs).attachWith _
            fun x hx => sorry
    | none =>
        (e.eval args).attachWith _
            fun x hx => sorry
| seq s₁ s₂ => do
    let ⟨x, hx⟩ ← (s₁.eval args mutArgs kmutArgs kbreak kcontinue).attach
    s₂.evalRefined hMut hcontMutVars halign halignMut halignkMut |>.subtypeMap
        fun x hx => sorry
| letE var val rest => do
    if hvar : mutArgs.any (·.1 == var) then
        -- cannot shadow mutVars
        none
    else
        let ⟨valConst, hvalConst⟩ ← (val.eval args).attach
        have halign' : ArgMap.submapVars (args.push (var, valConst)) (vars.push (var, val.inferType! vars)) := sorry
        rest.evalRefined hMut hcontMutVars halign' halignMut halignkMut |>.subtypeMap
            fun x hx => sorry
| letM var val rest => do
    if hvar : mutArgs.any (·.1 == var) then
        -- cannot shadow mutVars
        none
    else
        let ⟨val', hval'⟩ ← (val.eval args).attach
        have halign' : ArgMap.submapVars (args.push (var, val')) (vars.push (var, val.inferType! vars)) := sorry
        have halignMut' : ArgMap.equivVars (mutArgs.push (var, val')) (mutVars.push (var, val.inferType! vars)) := sorry
        have hMut' : Map.uniqueKeys (mutVars.push (var, val.inferType! vars)) := sorry
        have hcontMutVars' : Array.isPrefixOf kmutVars (Array.push mutVars (var, SSAExpr.inferType! vars val)) := sorry
        rest.evalRefined hMut' hcontMutVars' halign' halignMut' halignkMut |>.subtypeMap
            fun x hx => sorry
| assign var val rest => do
    let ⟨idx, hidx⟩ ← ((mutArgs).findFinIdx? (·.1 == var)).attach
    let ⟨val', hval'⟩ ← (val.eval args).attach
    if h : val'.inferType == mutArgs[idx].2.inferType then
        -- we're changing value not the underlying type so alignment is perserved
        have halignMut' : ArgMap.equivVars (mutArgs.set idx (var, val')) mutVars := by
            sorry
        rest.evalRefined hMut hcontMutVars halign halignMut' halignkMut |>.subtypeMap
            fun x hx => sorry
    else
        none
| loop body rest => do
    let kMutArgs' := mutArgs
    let ⟨kcontinue, hkcontinue⟩ ← kcontinue.attach
    let kcontinue' :=
        fun mutArgs' : Array (Name × SSAConst) =>
            kcontinue (kMutArgs'.map (fun (n, _) => (n, (mutArgs'.findLast? (·.1 == n)).get!.2)))
    SSA.loop mutArgs (fun mutArgs' kcont =>
        body.eval (args ++ mutArgs') mutArgs' kMutArgs' kcontinue' kcont) |>.attachWith _
            fun x hx => sorry
| .break =>
    match kbreak with
    | some kbreak' => kbreak' mutArgs |>.attachWith _
        fun x hx => sorry
    | none => none
| .continue =>
    match kcontinue with
    | some kcontinue' => kcontinue' mutArgs |>.attachWith _
        fun x hx => sorry
    | none => none
| .return out =>
    out.eval args |>.attachWith _
        fun x hx => sorry
| ifthenelse c t e rest => do
    let kMutArgs' := mutArgs
    let kcontinue' :=
        fun mutArgs' : Array (Name × SSAConst) =>
            let mutArgsNew : Array (Name × SSAConst) := (kMutArgs'.map (fun (n, _) => (n, (mutArgs'.findLast? (·.1 == n)).get!.2)))
            rest.eval (args ++ mutArgsNew) mutArgsNew mutArgsNew kbreak kcontinue
    match ← c.eval args with
    | .ofBase (.int ci) =>
        if ci != 0 then
            t.eval args mutArgs kMutArgs' kbreak kcontinue'
        else
            e.eval args mutArgs kMutArgs kbreak kcontinue'
    | _ => none

theorem SSADo.eval_eq_eval_toSSAExpr! {kbreak kcontinue : Option (ArgMap → Option SSAConst)} {nkbreak nkcontinue : Option Name} {args mutArgs kmutArgs : ArgMap} {vars mutVars kmutVars : VarMap}
    (hMut₁ : (mutVars.toList.map (·.1)).Nodup) (hMut₂ : ∀ x ∈ mutVars, vars.get x.1 = some x.2)
    (hcontMutVars : kmutVars.isPrefixOf mutVars)
    (halign : args.submapVars vars)
    (halignMut : mutArgs.equivVars mutVars)
    (halignkMut : kmutArgs.equivVars kmutVars) :
    (prog : SSADo) →
    (hkBreak : kbreak.All kmutArgs.validContinutation) →
    (hkContinue : kcontinue.All kmutArgs.validContinutation) →
    (hnkBreak : nkbreak.All (prog.validContinutationRef vars mutVars kmutVars)) →
    (hnkContinue : nkcontinue.All (prog.validContinutationRef vars mutVars kmutVars)) →
        ∀ x, prog.eval args mutArgs kmutArgs kbreak kcontinue = some x →
            x = (prog.toSSAExpr! vars mutVars kmutVars nkbreak nkcontinue).eval args := by sorry
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

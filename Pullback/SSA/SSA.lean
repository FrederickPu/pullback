import Pullback.SSA.Basic
import Pullback.SSA.VarMap
import Pullback.SSA.SSAExpr
import Pullback.SSA.SSADo
import Pullback.SSA.Tactic

open Lean

theorem List.subset_of_isPrefixOf {α} [BEq α] [LawfulBEq α] (x y : List α) : x.isPrefixOf y → x ⊆ y := by
    rw [List.isPrefixOf_iff_prefix]
    exact fun a => IsPrefix.subset a

set_option maxHeartbeats 1000000

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

def Option.All₂ (p : α → β → Prop) (x : Option α) (y : Option β) : Prop :=
    match x, y with
    | some a, some b => p a b
    | none, none => True
    | _, _ => False

def ContinuationRefines
    (args : ArgMap)
    (kmutArgs : ArgMap)
    (kmutVars : VarMap)
    (nk : Name)
    (k : { mutArgs' : ArgMap // mutArgs'.equivTypes kmutArgs } → Option SSAConst) : Prop :=
    ∀ x,
        k ⟨kmutArgs, ArgMap.equivTypes_rfl kmutArgs⟩ = some x →
            SSAExpr.eval args ((SSAExpr.var nk).app (mkMutTuple kmutVars).1) = some x

def ContinuationPairValid
    (args kmutArgs : ArgMap)
    (vars mutVars kmutVars : VarMap)
    (prog : SSADo)
    (nk : Option Name)
    (k : Option ({ mutArgs' : ArgMap // mutArgs'.equivTypes kmutArgs } → Option SSAConst)) : Prop :=
    nk.All (prog.validContinutationRef vars mutVars kmutVars) ∧
    Option.All₂ (fun nk kb => ContinuationRefines args kmutArgs kmutVars nk kb) nk k

theorem continuationRefines_eq_some
    {args : ArgMap}
    {kmutArgs : ArgMap}
    {kmutVars : VarMap}
    {nk : Name}
    {k : { mutArgs' : ArgMap // mutArgs'.equivTypes kmutArgs } → Option SSAConst}
    {x : SSAConst}
    (href : ContinuationRefines args kmutArgs kmutVars nk k)
    (hx : k ⟨kmutArgs, ArgMap.equivTypes_rfl kmutArgs⟩ = some x) :
    some x = SSAExpr.eval args ((SSAExpr.var nk).app (mkMutTuple kmutVars).1) := by
    simpa [eq_comm] using href x hx


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

instance (args : ArgMap) : Inhabited { args' : ArgMap // args'.equivTypes args } :=
    ⟨⟨args, by simp [ArgMap.equivTypes]⟩⟩

-- Helper lemmas for seq branch alignment/refinement threading

theorem ArgMap.equivTypes_equivVars_trans
    {args₁ args₂ : ArgMap} {vars : VarMap}
    (h₁ : args₁.equivTypes args₂)
    (h₂ : args₂.equivVars vars) :
    args₁.equivVars vars := by
  simp [ArgMap.equivVars, ArgMap.equivTypes] at h₁ h₂ ⊢
  rw [h₁]; exact h₂

theorem ArgMap.equivTypes_preserves_submapVars
    {mutArgs mutArgs' : ArgMap} {vars : VarMap}
    (h_equiv : mutArgs'.equivTypes mutArgs)
    (h_submap : mutArgs.submapVars vars) :
    mutArgs'.submapVars vars := by
  simp [ArgMap.submapVars, ArgMap.equivTypes] at h_equiv h_submap ⊢
  rw [h_equiv]; exact h_submap

#check Option.All₂
-- todo :: add hyps for alignment between the continutations in name and function form (kbreak and nkbreak)
def SSADo.evalRefined {args mutArgs kmutArgs : ArgMap} (kbreak kcontinue : Option ({mutArgs' : ArgMap // mutArgs'.equivTypes kmutArgs} → Option SSAConst)) {vars mutVars kmutVars : VarMap} (nkbreak nkcontinue : Option Name)
    (hMut : mutVars.uniqueKeys)
    (hcontMutVars : kmutVars.isPrefixOf mutVars)
    (halign : args.submapVars vars)
    (halignMut : mutArgs.equivVars mutVars)
    (halignkMut : kmutArgs.equivVars kmutVars) :
    (prog : SSADo) →
    (hbreak : ContinuationPairValid args kmutArgs vars mutVars kmutVars prog nkbreak kbreak) →
    (hcontinue : ContinuationPairValid args kmutArgs vars mutVars kmutVars prog nkcontinue kcontinue) →
        Option {x : SSAConst //
            x = (prog.toSSAExpr! vars mutVars kmutVars nkbreak nkcontinue).eval args}
| expr e, hcont, hcontinue => do
    match kcontinue with
    | some kcontinue =>
        -- todo :: don't discard `e` and use bind
        (kcontinue ⟨kmutArgs, (ArgMap.equivTypes_rfl kmutArgs)⟩).attachWith _
            fun x hx => (by {
                simp [toSSAExpr!]
                cases hnkcontinue : nkcontinue with
                | none => grind [Option.All₂, ContinuationPairValid]
                | some nkcontinue' =>
                    have hcontRef : ContinuationRefines args kmutArgs kmutVars nkcontinue' kcontinue := by
                        have := hcontinue.2
                        simpa [hnkcontinue, Option.All₂] using this
                    have hgoal : some x = SSAExpr.eval args ((SSAExpr.var nkcontinue').app (mkMutTuple kmutVars).1) :=
                        continuationRefines_eq_some hcontRef hx
                    simpa [hnkcontinue] using hgoal
            })
    | none =>
        (e.eval args).attachWith _
            fun x hx => by
                cases hnkcontinue : nkcontinue with
                | none =>
                    simpa [toSSAExpr!, hnkcontinue] using hx.symm
                | some nkcontinue' =>
                    simpa [hnkcontinue, Option.All₂] using hcontinue.2
| seq s₁ s₂, hbreak, hcontinue => do
    let n := freshName (Array.append s₁.mutVars s₂.mutVars) `x
    -- todo :: don't discard s₁ when using non identity monad
    let ⟨e1, he1⟩ ← s₁.evalRefined kbreak kcontinue nkbreak nkcontinue hMut hcontMutVars halign halignMut halignkMut sorry sorry
    s₂.evalRefined kbreak kcontinue nkbreak nkcontinue hMut hcontMutVars
        halign
        halignMut halignkMut
        sorry
        sorry |>.subtypeMap
        fun x hx => by
            rw [hx]
            simp [toSSAExpr!]
            rw [SSAExpr.eval_letE_bv]
            grind only [= Option.isSome_some]
            grind only [= Option.isSome_some]
| letE var val rest, hbreak, hcontinue => do
    if hvar : mutArgs.any (·.1 == var) then
        -- cannot shadow mutVars
        none
    else
        let ⟨valConst, hvalConst⟩ ← (val.eval args).attach
        have halign' : ArgMap.submapVars (args.push (var, valConst)) (vars.push (var, val.inferType! vars)) := sorry
        rest.evalRefined kbreak kcontinue nkbreak nkcontinue hMut hcontMutVars halign' halignMut halignkMut
            ⟨sorry, sorry⟩
            ⟨sorry, sorry⟩ |>.subtypeMap
            fun x hx => sorry
| letM var val rest, hkbreak, hkcontinue => do
    if hvar : mutArgs.any (·.1 == var) then
        -- cannot shadow mutVars
        none
    else
        let ⟨val', hval'⟩ ← (val.eval args).attach
        have halign' : ArgMap.submapVars (args.push (var, val')) (vars.push (var, val.inferType! vars)) := sorry
        have halignMut' : ArgMap.equivVars (mutArgs.push (var, val')) (mutVars.push (var, val.inferType! vars)) := sorry
        have hMut' : Map.uniqueKeys (mutVars.push (var, val.inferType! vars)) := sorry
        have hcontMutVars' : Array.isPrefixOf kmutVars (Array.push mutVars (var, SSAExpr.inferType! vars val)) := sorry
        rest.evalRefined kbreak kcontinue nkbreak nkcontinue hMut' hcontMutVars' halign' halignMut' halignkMut
            ⟨sorry, sorry⟩
            ⟨sorry, sorry⟩ |>.subtypeMap
            fun x hx => sorry
| assign var val rest, hkbreak, hkcontinue => do
    let ⟨idx, hidx⟩ ← ((mutArgs).findFinIdx? (·.1 == var)).attach
    let ⟨val', hval'⟩ ← (val.eval args).attach
    if h : val'.inferType == mutArgs[idx].2.inferType then
        -- we're changing value not the underlying type so alignment is perserved
        have halignMut' : ArgMap.equivVars (mutArgs.set idx (var, val')) mutVars := by
            sorry
        rest.evalRefined kbreak kcontinue nkbreak nkcontinue hMut hcontMutVars halign halignMut' halignkMut
            ⟨sorry, sorry⟩
            ⟨sorry, sorry⟩ |>.subtypeMap
            fun x hx => sorry
    else
        none
| loop body rest, hkbreak, hkcontinue => do
    let kMutArgs' := mutArgs
    let ⟨kcontinue, hkcontinue⟩ ← kcontinue.attach
    let kcontinue' : { mutArgs' : ArgMap // mutArgs'.equivTypes kMutArgs' } → Option SSAConst :=
        fun ⟨mutArgs', hmutArgs'⟩ =>
            kcontinue ⟨(kMutArgs'.map (fun (n, _) => (n, (mutArgs'.get n).get!))), sorry⟩
    let nKBreak : Name := freshName (vars.map (·.1) ++ body.vars) `kbreak
    let nKContinue : Name := freshName (vars.map (·.1) ++ body.vars) `kcontinue
    SSA.loop (⟨mutArgs, ArgMap.equivTypes_rfl mutArgs⟩ : { mutArgs' : ArgMap // mutArgs'.equivTypes kMutArgs' }) (fun mutArgs' kcont =>
        body.evalRefined (some (fun x => kcont x)) kcontinue' nKBreak nKContinue hMut sorry halign halignMut halignMut
            ⟨sorry, sorry⟩
            ⟨sorry, sorry⟩ |>.subtypeMap sorry
    )
| .break, hkbreak, hkcontinue =>
    match kbreak with
    | some kbreak' => kbreak' ⟨mutArgs, sorry⟩ |>.attachWith _
        fun x hx => by
            sorry
    | none => none
| .continue, hkbreak, hkcontinue =>
    match kcontinue with
    | some kcontinue' => kcontinue' ⟨mutArgs, sorry⟩ |>.attachWith _
        fun x hx => sorry
    | none => none
| .return out, hkbreak, hkcontinue =>
    out.eval args |>.attachWith _
        fun x hx => sorry
| ifthenelse c t e rest, hkbreak, hkcontinue => do
    let kMutArgs' := mutArgs
    let kcontinue' : { x : ArgMap // x.equivTypes kMutArgs' } → Option SSAConst :=
        fun ⟨mutArgs', hmutArgs'⟩ =>
            let mutArgsNew : Array (Name × SSAConst) := (kMutArgs'.map (fun (p : Name × SSAConst) => (p.1, (mutArgs'.get p.1).get!)))
            have halign' : ArgMap.submapVars (args ++ mutArgsNew) (vars) := sorry
            have halignMut' : ArgMap.equivVars (mutArgsNew) (mutVars) := sorry
            (rest.evalRefined kbreak kcontinue nkbreak nkcontinue hMut hcontMutVars halign' halignMut' halignkMut
                ⟨sorry, sorry⟩
                ⟨sorry, sorry⟩).map Subtype.val
    let kbreak' : Option ({ x : ArgMap // x.equivTypes kMutArgs' } → Option SSAConst) :=
        kbreak.map (fun kbreak =>
            fun ⟨mutArgs', hmutArgs'⟩ =>
                -- want to use the outer contiuation args
                let mutArgsRestricted := kmutArgs.map (fun (p : Name × SSAConst) => (p.1, (mutArgs'.get p.1).get!))
                kbreak ⟨mutArgsRestricted, sorry⟩
        )
    let nkcontinue : Name := freshName ((vars.map (·.1) ++ t.vars ++ e.vars)) `kcontinue
    let nkbreak : Option Name := kbreak.map (fun _ => freshName ((vars.map (·.1) ++ t.vars ++ e.vars)) `kbreak)
    match ← c.eval args with
    | .ofBase (.int ci) =>
        if ci != 0 then
            t.evalRefined (some kcontinue') (kbreak') nkbreak nkcontinue hMut sorry halign halignMut halignMut
                ⟨sorry, sorry⟩
                ⟨sorry, sorry⟩ |>.subtypeMap sorry
        else
            e.evalRefined (some kcontinue') (kbreak') nkbreak nkcontinue hMut sorry halign halignMut halignMut
                ⟨sorry, sorry⟩
                ⟨sorry, sorry⟩ |>.subtypeMap sorry
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

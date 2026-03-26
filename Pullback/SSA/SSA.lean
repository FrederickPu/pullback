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

theorem Array.findLast?_eq_some_imp_any_fst_eq {β : Type}
    (args : Array (Name × β)) (n : Name) (x : β) :
    args.findLast? (fun p => p.1 == n) = some (n, x) → args.any (·.1 == n) = true := by
    intro h
    simp [Array.findLast?, Array.find?_eq_some_iff_getElem] at h ⊢
    grind

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

def DoResult.applyContinutations
    (onBreak onContinue : Array (Name × SSAConst) → SSAConst) :
    DoResult → SSAConst
| .return a => a
| .pure (.break st) => onBreak st
| .pure (.continue st) => onContinue st

def SSADo.argsAlignVars
    (vars : VarMap)
    (args : Array (Name × SSAConst))
    (kbreak kcontinue : Option Name) : Prop :=
    ∀ n ty,
        vars.get n = some ty →
        kbreak ≠ some n →
        kcontinue ≠ some n →
        ∃ c, args.findLast? (fun p => p.1 == n) = some (n, c) ∧ c.inferType = ty

def SSADo.continuationTypesAlign
    (vars kMutVars : VarMap)
    (kbreak kcontinue : Option Name)
    (contTy : SSAType) : Prop :=
    (match kbreak with
    | some kb => vars.get kb = some (.fun (mkMutTuple kMutVars).2 contTy)
    | none => True) ∧
    (match kcontinue with
    | some kc => vars.get kc = some (.fun (mkMutTuple kMutVars).2 contTy)
    | none => True)

def SSADo.continuationValuesAlign
    (args : Array (Name × SSAConst))
    (kbreak kcontinue : Option Name)
    (onBreak onContinue : Array (Name × SSAConst) → SSAConst) : Prop :=
    (match kbreak with
    | some kb => ∀ st, ∃ c, args.findLast? (fun p => p.1 == kb) = some (kb, c) ∧ onBreak st = c
    | none => True) ∧
    (match kcontinue with
    | some kc => ∀ st, ∃ c, args.findLast? (fun p => p.1 == kc) = some (kc, c) ∧ onContinue st = c
    | none => True)

def SSADo.contRuntimeSpec
    (kMutVars : VarMap)
    (kbreak kcontinue : Option Name)
    (inloop : Bool)
    (onBreak onContinue : Array (Name × SSAConst) → SSAConst) : Prop :=
    (!inloop → kbreak = none ∧ kcontinue = none) ∧
    (inloop = true → (∃ kb, kbreak = some kb) ∧ ∃ kc, kcontinue = some kc) ∧
    (∀ {args' : Array (Name × SSAConst)} {st : Array (Name × SSAConst)} {kb : Name},
        kbreak = some kb →
        ((SSAExpr.app (SSAExpr.var kb) (mkMutTuple kMutVars).1).eval args' = some (onBreak st))) ∧
    (∀ {args' : Array (Name × SSAConst)} {st : Array (Name × SSAConst)} {kc : Name},
        kcontinue = some kc →
        ((SSAExpr.app (SSAExpr.var kc) (mkMutTuple kMutVars).1).eval args' = some (onContinue st)))

-- ---------------------------------------------------------------------------
-- Alignment propagation lemmas
-- ---------------------------------------------------------------------------

lemma SSADo.argsAlignVars_push
    {vars : VarMap} {args : Array (Name × SSAConst)} {kbreak kcontinue : Option Name}
    {var : Name} {ty : SSAType} {v : SSAConst}
        (h : SSADo.argsAlignVars vars args kbreak kcontinue)
        (hv : v.inferType = ty) :
        SSADo.argsAlignVars (vars.push (var, ty)) (args.push (var, v)) kbreak kcontinue := by
        simp [argsAlignVars] at h ⊢
        intro n nty hget hkb hkc
        have hpush := VarMap.get_push vars (var, ty) n
        rw [hpush] at hget
        cases em (var = n) with
        | inl hEq =>
            subst hEq
            simp at hget
            refine ⟨v, ?_⟩
            constructor
            · simp [Array.findLast?]
            · simpa [hget] using hv
        | inr hNe =>
            have hgetOld : vars.get n = some nty := by
                simpa [hNe] using hget
            rcases h n nty hgetOld hkb hkc with ⟨c, hcfind, hcty⟩
            refine ⟨c, ?_⟩
            constructor
            · simpa [Array.findLast?, hNe] using hcfind
            · exact hcty

lemma SSADo.continuationTypesAlign_push
    {vars : VarMap} {kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {contTy : SSAType} {var : Name} {ty : SSAType}
    (h : SSADo.continuationTypesAlign vars kMutVars kbreak kcontinue contTy)
    (hkb : kbreak ≠ some var) (hkc : kcontinue ≠ some var) :
        SSADo.continuationTypesAlign (vars.push (var, ty)) kMutVars kbreak kcontinue contTy := by
    cases hkbreak : kbreak with
    | none =>
        cases hkcontinue : kcontinue with
        | none =>
            simp [continuationTypesAlign]
        | some kc =>
            simp [continuationTypesAlign, hkbreak, hkcontinue] at h ⊢
            have hNe : var ≠ kc := by
                intro hv
                apply hkc
                simp [hkcontinue, hv]
            have hpush := VarMap.get_push vars (var, ty) kc
            simpa [hpush, hNe] using h
    | some kb =>
        cases hkcontinue : kcontinue with
        | none =>
            simp [continuationTypesAlign, hkbreak, hkcontinue] at h ⊢
            have hNe : var ≠ kb := by
                intro hv
                apply hkb
                simp [hkbreak, hv]
            have hpush := VarMap.get_push vars (var, ty) kb
            simpa [hpush, hNe] using h
        | some kc =>
            simp [continuationTypesAlign, hkbreak, hkcontinue] at h ⊢
            refine And.intro ?_ ?_
            · have hNe : var ≠ kb := by
                intro hv
                apply hkb
                simp [hkbreak, hv]
              have hpush := VarMap.get_push vars (var, ty) kb
              simpa [hpush, hNe] using h.1
            · have hNe : var ≠ kc := by
                intro hv
                apply hkc
                simp [hkcontinue, hv]
              have hpush := VarMap.get_push vars (var, ty) kc
              simpa [hpush, hNe] using h.2

lemma SSADo.continuationValuesAlign_push
    {args : Array (Name × SSAConst)} {kbreak kcontinue : Option Name}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst} {var : Name} {v : SSAConst}
    (h : SSADo.continuationValuesAlign args kbreak kcontinue onBreak onContinue)
    (hkb : kbreak ≠ some var) (hkc : kcontinue ≠ some var) :
    SSADo.continuationValuesAlign (args.push (var, v)) kbreak kcontinue onBreak onContinue := by
    cases hkbreak : kbreak with
    | none =>
        cases hkcontinue : kcontinue with
        | none =>
            simp [continuationValuesAlign]
        | some kc =>
            simp [continuationValuesAlign, hkbreak, hkcontinue] at h ⊢
            intro st
            have hNe : var ≠ kc := by
                intro hv
                apply hkc
                simp [hkcontinue, hv]
            simpa [Array.findLast?, hNe] using h st
    | some kb =>
        cases hkcontinue : kcontinue with
        | none =>
            simp [continuationValuesAlign, hkbreak, hkcontinue] at h ⊢
            intro st
            have hNe : var ≠ kb := by
                intro hv
                apply hkb
                simp [hkbreak, hv]
            simpa [Array.findLast?, hNe] using h st
        | some kc =>
            simp [continuationValuesAlign, hkbreak, hkcontinue] at h ⊢
            refine And.intro ?_ ?_
            · intro st
              have hNe : var ≠ kb := by
                intro hv
                apply hkb
                simp [hkbreak, hv]
              simpa [Array.findLast?, hNe] using h.1 st
            · intro st
              have hNe : var ≠ kc := by
                intro hv
                apply hkc
                simp [hkcontinue, hv]
              simpa [Array.findLast?, hNe] using h.2 st

-- ---------------------------------------------------------------------------
-- toSSAExpr! correctness lemmas
-- Each takes an IH (r.property from the recursive evalprop call) as a hypothesis.
-- ---------------------------------------------------------------------------

private abbrev compileProp
    (vars mutVars kMutVars : VarMap) (kbreak kcontinue : Option Name)
    (args : Array (Name × SSAConst)) (inloop : Bool)
    (onBreak onContinue : Array (Name × SSAConst) → SSAConst)
    (prog : SSADo) (x : if !inloop then SSAConst else DoResult) : Prop :=
    (prog.toSSAExpr! vars mutVars kMutVars kbreak kcontinue).eval args =
        some (if h : inloop then
            (cast (by grind) x : DoResult).applyContinutations onBreak onContinue
        else
            cast (by grind) x)

theorem SSAExpr.eval_isSome_inferType_local (vars : VarMap) (args : Array (Name × SSAConst))
    (expr : SSAExpr) (v : SSAConst)
    (heval : expr.eval args = some v) :
    (expr.inferType vars).isSome := by
    exact SSAExpr.eval_isSome_inferType vars args expr v heval

theorem SSAExpr.eval_inferType_eq_local (vars : VarMap) (args : Array (Name × SSAConst))
    (expr : SSAExpr) (v : SSAConst)
    (heval : expr.eval args = some v) :
    expr.inferType vars = some v.inferType := by
    sorry

lemma SSADo.compilesTo_expr_false_core
    {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {args : Array (Name × SSAConst)} {inloop : Bool}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst}
    {e : SSAExpr} {c : SSAConst}
    (hn : !inloop)
    (hkc : kcontinue = none)
    (heval : e.eval args = some c) :
    compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
        (SSADo.expr e) (cast (by grind) c) := by
    simp [compileProp, SSADo.toSSAExpr!, hn, hkc, heval]
    intro hIn
    simp [hIn] at hn

lemma SSADo.compilesTo_expr_false
    {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {args : Array (Name × SSAConst)} {inloop : Bool}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst}
    {e : SSAExpr} {c : SSAConst}
    (hNoContWhenNotInLoop : !inloop → kcontinue = none)
    (hn : !inloop) (heval : e.eval args = some c) :
    compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
        (SSADo.expr e) (cast (by grind) c) :=
    compilesTo_expr_false_core hn (hNoContWhenNotInLoop hn) heval

lemma SSADo.compilesTo_expr_true_core
    {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {args : Array (Name × SSAConst)} {inloop : Bool}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst}
    {e : SSAExpr} {st : Array (Name × SSAConst)} {kc : Name}
    (h : inloop = true)
    (hkc : kcontinue = some kc)
    (hContAppEval : ((SSAExpr.app (SSAExpr.var kc) (mkMutTuple kMutVars).1).eval args = some (onContinue st))) :
    compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
        (SSADo.expr e) (cast (by grind) (DoResult.pure (LoopStep.continue st))) := by
    simp [compileProp, SSADo.toSSAExpr!, h, hkc, hContAppEval, DoResult.applyContinutations]

lemma SSADo.compilesTo_expr_true
    {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {args : Array (Name × SSAConst)} {inloop : Bool} {contTy : SSAType}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst}
    {e : SSAExpr} {st : Array (Name × SSAConst)}
    (h : inloop = true)
        (_hContVal : SSADo.continuationValuesAlign args kbreak kcontinue onBreak onContinue)
        (_hContTy : SSADo.continuationTypesAlign vars kMutVars kbreak kcontinue contTy)
        (_hunit : (e.eval args).map (·.inferType) = some (.ofBase .unit))
    (hkc : ∃ kc, kcontinue = some kc)
    (hContAppEval : ∀ kc, kcontinue = some kc →
      ((SSAExpr.app (SSAExpr.var kc) (mkMutTuple kMutVars).1).eval args = some (onContinue st))) :
    compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
        (SSADo.expr e) (cast (by grind) (DoResult.pure (LoopStep.continue st))) := by
    rcases hkc with ⟨kc, hk⟩
    exact compilesTo_expr_true_core h hk (hContAppEval kc hk)

lemma SSADo.compilesTo_seq
    {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {args : Array (Name × SSAConst)} {inloop : Bool}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst}
    {s₁ s₂ : SSADo} {x : if !inloop then SSAConst else DoResult}
    (ih : compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue s₂ x) :
        compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue (SSADo.seq s₁ s₂) x := by
        simpa [compileProp, SSADo.toSSAExpr!]
            using Eq.trans
                (SSAExpr.eval_letE args
                    (freshName (Array.append s₁.mutVars s₂.mutVars) `x)
                    (s₁.toSSAExpr! vars mutVars kMutVars kbreak kcontinue)
                    (s₂.toSSAExpr! vars mutVars kMutVars kbreak kcontinue))
                ih

lemma SSADo.compilesTo_letE
    {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {args : Array (Name × SSAConst)} {inloop : Bool}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst}
    {var : Name} {val : SSAExpr} {rest : SSADo} {v : SSAConst}
    {x : if !inloop then SSAConst else DoResult}
    (hval : val.eval args = some v)
    (htype : (val.inferType vars).isSome)
    (ih : compileProp (vars.push (var, v.inferType)) mutVars kMutVars kbreak kcontinue
        (args.push (var, v)) inloop onBreak onContinue rest x) :
    compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
        (SSADo.letE var val rest) x := by
        have hInferTypeEq : val.inferType vars = val.inferType! vars :=
            SSAExpr.inferType_eq_some_inferType!_of_isSome vars val htype
        have hEvalTypeEq : val.inferType vars = some v.inferType :=
            SSAExpr.eval_inferType_eq_local vars args val v hval
        have htype_eq : val.inferType! vars = v.inferType := by
            apply Option.some.inj
            calc
                some (val.inferType! vars) = val.inferType vars := by simpa using hInferTypeEq.symm
                _ = some v.inferType := hEvalTypeEq
        simpa [compileProp, hInferTypeEq]
            using Eq.trans
                (SSADo.eval_letE hval htype_eq)
                ih

lemma SSADo.compilesTo_letM
    {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {args : Array (Name × SSAConst)} {inloop : Bool}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst}
    {var : Name} {val : SSAExpr} {rest : SSADo} {v : SSAConst}
    {x : if !inloop then SSAConst else DoResult}
    (hval : val.eval args = some v)
    (htype : (val.inferType vars).isSome)
    (ih : compileProp (vars.push (var, v.inferType)) (mutVars.push (var, v.inferType)) kMutVars
        kbreak kcontinue (args.push (var, v)) inloop onBreak onContinue rest x) :
    compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
        (SSADo.letM var val rest) x := by
        have hInferTypeEq : val.inferType vars = val.inferType! vars :=
            SSAExpr.inferType_eq_some_inferType!_of_isSome vars val htype
        have hEvalTypeEq : val.inferType vars = some v.inferType :=
            SSAExpr.eval_inferType_eq_local vars args val v hval
        have htype_eq : val.inferType! vars = v.inferType := by
            apply Option.some.inj
            calc
                some (val.inferType! vars) = val.inferType vars := by simpa using hInferTypeEq.symm
                _ = some v.inferType := hEvalTypeEq
        simpa [compileProp, hInferTypeEq]
            using Eq.trans
                (SSADo.eval_letM hval htype_eq)
                ih

lemma SSADo.compilesTo_assign
    {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {args : Array (Name × SSAConst)} {inloop : Bool}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst}
    {var : Name} {val : SSAExpr} {rest : SSADo} {v : SSAConst}
    {x : if !inloop then SSAConst else DoResult}
    (hval : val.eval args = some v)
    (ih : compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue rest x) :
    compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
                (SSADo.assign var val rest) x := by
        simpa [compileProp] using Eq.trans (SSADo.eval_assign hval) ih

lemma SSADo.compilesTo_loop_return
    {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {args : Array (Name × SSAConst)} {inloop : Bool}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst}
    {body rest : SSADo} {x : SSAConst}
    (hloop_return_eval :
        compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
            (SSADo.loop body rest)
            (if h : inloop then cast (by grind) (DoResult.return x) else cast (by grind) x)) :
    compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
        (SSADo.loop body rest)
        (if h : inloop then cast (by grind) (DoResult.return x) else cast (by grind) x) :=
    hloop_return_eval

lemma SSADo.compilesTo_loop_break
    {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {args : Array (Name × SSAConst)} {inloop : Bool}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst}
    {body rest : SSADo} {x : if !inloop then SSAConst else DoResult}
    (hloop_break_bridge :
        (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue (SSADo.loop body rest)).eval args =
            (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue rest).eval args)
    (ih : compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue rest x) :
    compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
        (SSADo.loop body rest) x := by
    simpa [compileProp] using Eq.trans hloop_break_bridge ih

lemma SSADo.compilesTo_break
    {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {args : Array (Name × SSAConst)} {inloop : Bool}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst}
    {st : Array (Name × SSAConst)}
    (h : inloop = true)
    (hkb : ∃ kb, kbreak = some kb)
    (hBreakAppEval : ∀ kb, kbreak = some kb →
        ((SSAExpr.app (SSAExpr.var kb) (mkMutTuple kMutVars).1).eval args = some (onBreak st))) :
    compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
        SSADo.break (cast (by grind) (DoResult.pure (LoopStep.break st))) := by
    rcases hkb with ⟨kb, hk⟩
    have hbreak_eval :
        (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue SSADo.break).eval args =
            some (onBreak st) := by
      simpa [SSADo.toSSAExpr!, hk] using hBreakAppEval kb hk
    simpa [compileProp, h, DoResult.applyContinutations] using hbreak_eval

lemma SSADo.compilesTo_continue
    {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {args : Array (Name × SSAConst)} {inloop : Bool}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst}
    {st : Array (Name × SSAConst)}
    (h : inloop = true)
    (hkc : ∃ kc, kcontinue = some kc)
    (hContinueAppEval : ∀ kc, kcontinue = some kc →
        ((SSAExpr.app (SSAExpr.var kc) (mkMutTuple kMutVars).1).eval args = some (onContinue st))) :
    compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
        SSADo.continue (cast (by grind) (DoResult.pure (LoopStep.continue st))) := by
    rcases hkc with ⟨kc, hk⟩
    have hcontinue_eval :
        (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue SSADo.continue).eval args =
            some (onContinue st) := by
      simpa [SSADo.toSSAExpr!, hk] using hContinueAppEval kc hk
    simpa [compileProp, h, DoResult.applyContinutations] using hcontinue_eval

lemma SSADo.compilesTo_return
    {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {args : Array (Name × SSAConst)} {inloop : Bool}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst}
    {out : SSAExpr} {res : SSAConst}
    (heval : out.eval args = some res) :
    compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
        (SSADo.return out)
        (if h : inloop then cast (by grind) (DoResult.return res) else cast (by grind) res) := by
    by_cases h : inloop
    · simp [compileProp, SSADo.toSSAExpr!, h, heval, DoResult.applyContinutations]
    · simp [compileProp, SSADo.toSSAExpr!, h, heval]

lemma SSADo.compilesTo_ifthenelse_return
    {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {args : Array (Name × SSAConst)} {inloop : Bool}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst}
    {c : SSAExpr} {t e rest : SSADo}
    {rv : if !inloop then SSAConst else DoResult} {x : SSAConst}
    (h : inloop = true)
    (hcast : cast (β := DoResult) (by grind) rv = DoResult.return x)
    (ih : compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
        (if c.eval args != SSAConst.ofInt 0 then t else e) rv) :
    compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
                (SSADo.ifthenelse c t e rest) (cast (by grind) (DoResult.return x)) := by
        have hif_return_bridge :
                (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue (SSADo.ifthenelse c t e rest)).eval args =
                (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue
                        (if c.eval args != SSAConst.ofInt 0 then t else e)).eval args := by
            sorry
        have ih' : compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
                (if c.eval args != SSAConst.ofInt 0 then t else e)
                (cast (by grind) (DoResult.return x)) := by
            sorry
        simpa [compileProp, h, DoResult.applyContinutations]
            using Eq.trans hif_return_bridge ih'

lemma SSADo.compilesTo_ifthenelse_rest
    {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {args : Array (Name × SSAConst)} {inloop : Bool}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst}
    {c : SSAExpr} {t e rest : SSADo} {x : if !inloop then SSAConst else DoResult}
    (ih : compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue rest x) :
    compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
                (SSADo.ifthenelse c t e rest) x := by
        have hif_rest_bridge :
                (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue (SSADo.ifthenelse c t e rest)).eval args =
                (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue rest).eval args := by
            sorry
        simpa [compileProp] using Eq.trans hif_rest_bridge ih

lemma SSADo.compilesTo_ifthenelse_base
    {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
    {args : Array (Name × SSAConst)} {inloop : Bool}
    {onBreak onContinue : Array (Name × SSAConst) → SSAConst}
    {c : SSAExpr} {t e rest : SSADo} {x : if !inloop then SSAConst else DoResult}
    (hn : ¬inloop)
    (ih : compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
        (if c.eval args != SSAConst.ofInt 0 then t else e) x) :
    compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
        (SSADo.ifthenelse c t e rest) x := by
    have hif_base_bridge :
        (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue (SSADo.ifthenelse c t e rest)).eval args =
        (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue
            (if c.eval args != SSAConst.ofInt 0 then t else e)).eval args := by
      sorry
    simpa [compileProp] using Eq.trans hif_base_bridge ih

-- ---------------------------------------------------------------------------

def SSADo.evalprop
    (vars mutVars kMutVars : VarMap)
    (kbreak kcontinue : Option Name)
    (args : Array (Name × SSAConst))
    (inloop : Bool)
    (onBreak onContinue : Array (Name × SSAConst) → SSAConst)
    (contTy : SSAType)
    (hArgs : SSADo.argsAlignVars vars args kbreak kcontinue)
    (hContTy : SSADo.continuationTypesAlign vars kMutVars kbreak kcontinue contTy)
    (hContVal : SSADo.continuationValuesAlign args kbreak kcontinue onBreak onContinue)
    (hContRuntime : SSADo.contRuntimeSpec kMutVars kbreak kcontinue inloop onBreak onContinue) :
    (prog : SSADo) →
    StateT (Array (Name × SSAConst)) Option
        { x : if !inloop then SSAConst else DoResult //
            compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue prog x }
| expr e => do
    have hNoContWhenNotInLoop : !inloop → kcontinue = none := by
        intro hn
        exact (hContRuntime.1 hn).2
    have hHasContWhenInLoop : inloop = true → ∃ kc, kcontinue = some kc := by
        intro hi
        exact (hContRuntime.2.1 hi).2
    have hContinueAppEval :
        ∀ {args' : Array (Name × SSAConst)} {st : Array (Name × SSAConst)} {kc : Name},
            SSADo.continuationValuesAlign args' kbreak kcontinue onBreak onContinue →
            kcontinue = some kc →
            ((SSAExpr.app (SSAExpr.var kc) (mkMutTuple kMutVars).1).eval args' = some (onContinue st)) := by
        intro args' st kc _ hk
        exact hContRuntime.2.2.2 hk
    let ⟨c, hc⟩ ← (e.eval args).attach
    if h : !inloop then
        pure ⟨cast (by grind) c, compilesTo_expr_false hNoContWhenNotInLoop h hc⟩
    else
        if hty : c.inferType != .ofBase .unit then
            none
        else
            let st ← get
            have hunit : c.inferType = (SSAType.ofBase .unit) := by
                grind
            pure ⟨cast (by grind) (DoResult.pure (LoopStep.continue st)),
                  compilesTo_expr_true (by grind) hContVal hContTy (by grind)
                    (hHasContWhenInLoop (by grind))
                    (fun kc hk => hContinueAppEval hContVal hk)⟩
| seq s₁ s₂ => do
    let r ← s₂.evalprop vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue contTy
        hArgs hContTy hContVal hContRuntime
    pure ⟨r.val, compilesTo_seq r.property⟩
| letE var val rest => do
    if (← get).any (·.1 == var) then none
    else
        if hkb' : kbreak = some var then none
        else
            if hkc' : kcontinue = some var then none
            else
                let ⟨v, hv⟩ ← (val.eval args).attach
                let r ← rest.evalprop (vars.push (var, v.inferType)) mutVars kMutVars kbreak kcontinue
                    (args.push (var, v)) inloop onBreak onContinue contTy
                    (argsAlignVars_push hArgs rfl)
                    (continuationTypesAlign_push hContTy hkb' hkc')
                    (continuationValuesAlign_push hContVal hkb' hkc')
                    hContRuntime
                pure ⟨r.val, compilesTo_letE hv (SSAExpr.eval_isSome_inferType_local vars args val v hv) r.property⟩
| letM var val rest => do
    if hshadow : args.any (·.1 == var) then none
    else
        let before ← get
        let ⟨v, hv⟩ ← (val.eval args).attach
        set (before.push (var, v))
        have hkb' : kbreak ≠ some var := by
            intro hk
            have hBreak := hContVal.1
            rw [hk] at hBreak
            rcases hBreak args with ⟨c, hcfind, _⟩
            have hAny : args.any (·.1 == var) = true :=
                Array.findLast?_eq_some_imp_any_fst_eq args var c hcfind
            simp [hshadow] at hAny
        have hkc' : kcontinue ≠ some var := by
            intro hk
            have hCont := hContVal.2
            rw [hk] at hCont
            rcases hCont args with ⟨c, hcfind, _⟩
            have hAny : args.any (·.1 == var) = true :=
                Array.findLast?_eq_some_imp_any_fst_eq args var c hcfind
            simp [hshadow] at hAny
        let r ← rest.evalprop (vars.push (var, v.inferType)) (mutVars.push (var, v.inferType)) kMutVars
            kbreak kcontinue (args.push (var, v)) inloop onBreak onContinue contTy
            (argsAlignVars_push hArgs rfl)
            (continuationTypesAlign_push hContTy hkb' hkc')
            (continuationValuesAlign_push hContVal hkb' hkc')
            hContRuntime
        set before
        pure ⟨r.val, compilesTo_letM hv (SSAExpr.eval_isSome_inferType_local vars args val v hv) r.property⟩
| assign var val rest => do
    let mutvars ← get
    let idx ← mutvars.findFinIdx? (·.1 == var)
    let ⟨v, hv⟩ ← (val.eval args).attach
    set (mutvars.set idx (var, v))
    let r ← rest.evalprop vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue contTy
        hArgs hContTy hContVal hContRuntime
    pure ⟨r.val, compilesTo_assign hv r.property⟩
| loop body rest =>
    let nKBreak   := freshName (vars.map (·.1) ++ body.vars) `kbreak
    let nKContinue := freshName (vars.map (·.1) ++ body.vars) `kcontinue
    SSA.loop Unit.unit fun _ kloopContinue => do
        let br ← body.evalprop vars mutVars mutVars (some nKBreak) (some nKContinue) args true
            (fun _ => sorry) (fun _ => sorry) contTy (by sorry) (by sorry) (by sorry)
            (by sorry)
        match cast (β := DoResult) (by grind) br.val with
        | .return x =>
            pure ⟨if h : inloop then cast (by grind) (DoResult.return x) else cast (by grind) x,
                  compilesTo_loop_return (by sorry)⟩
        | .pure (.break st) =>
            set st
            (rest.evalprop vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue contTy
                hArgs hContTy hContVal hContRuntime).map fun r => ⟨r.val, compilesTo_loop_break (by sorry) r.property⟩
        | .pure (.continue st) =>
            set st; kloopContinue ()
| .break => do
    if h : inloop then
        have hHasBreakWhenInLoop : inloop = true → ∃ kb, kbreak = some kb := by
            intro hi
            exact (hContRuntime.2.1 hi).1
        have hBreakAppEval :
            ∀ {kb : Name} {st : Array (Name × SSAConst)},
                kbreak = some kb →
                ((SSAExpr.app (SSAExpr.var kb) (mkMutTuple kMutVars).1).eval args = some (onBreak st)) := by
            intro kb st hk
            exact hContRuntime.2.2.1 hk
        pure ⟨cast (by grind) (DoResult.pure (LoopStep.break (← get))),
              compilesTo_break h (hHasBreakWhenInLoop (by simpa using h))
                (fun kb hk => hBreakAppEval hk)⟩
    else none
| .continue => do
    if h : inloop then
        have hHasContWhenInLoop : inloop = true → ∃ kc, kcontinue = some kc := by
            intro hi
            exact (hContRuntime.2.1 hi).2
        have hContinueAppEval :
            ∀ {kc : Name} {st : Array (Name × SSAConst)},
                kcontinue = some kc →
                ((SSAExpr.app (SSAExpr.var kc) (mkMutTuple kMutVars).1).eval args = some (onContinue st)) := by
            intro kc st hk
            exact hContRuntime.2.2.2 hk
        pure ⟨cast (by grind) (DoResult.pure (LoopStep.continue (← get))),
              compilesTo_continue h (hHasContWhenInLoop (by simpa using h))
                (fun kc hk => hContinueAppEval hk)⟩
    else none
| .return out => do
    let ⟨res, hres⟩ ← (out.eval args).attach
    pure ⟨if h : inloop then cast (by grind) <| DoResult.return res else cast (by grind) res,
          compilesTo_return hres⟩
| ifthenelse c t e rest =>
    if h_cond : c.eval args != SSAConst.ofInt (0 : Int) then do
        let r ← t.evalprop vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue contTy
            hArgs hContTy hContVal hContRuntime
        if h : inloop then
            match hcast : cast (β := DoResult) (by grind) r.val with
            | .return x =>
                have ih : compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
                        (if c.eval args != SSAConst.ofInt 0 then t else e) r.val := by
                    simp [h_cond]; exact r.property
                pure ⟨cast (by grind) (DoResult.return x), compilesTo_ifthenelse_return h hcast ih⟩
            | .pure _ =>
                (rest.evalprop vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue contTy
                    hArgs hContTy hContVal hContRuntime).map fun r => ⟨r.val, compilesTo_ifthenelse_rest r.property⟩
        else
            have ih : compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
                    (if c.eval args != SSAConst.ofInt 0 then t else e) r.val := by
                simp [h_cond]; exact r.property
            pure ⟨r.val, compilesTo_ifthenelse_base (by grind) ih⟩
    else do
        let r ← e.evalprop vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue contTy
            hArgs hContTy hContVal hContRuntime
        if h : inloop then
            match hcast : cast (β := DoResult) (by grind) r.val with
            | .return x =>
                have ih : compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
                        (if c.eval args != SSAConst.ofInt 0 then t else e) r.val := by
                    simp [h_cond]; exact r.property
                pure ⟨cast (by grind) (DoResult.return x), compilesTo_ifthenelse_return h hcast ih⟩
            | .pure _ =>
                (rest.evalprop vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue contTy
                    hArgs hContTy hContVal hContRuntime).map fun r => ⟨r.val, compilesTo_ifthenelse_rest r.property⟩
        else
            have ih : compileProp vars mutVars kMutVars kbreak kcontinue args inloop onBreak onContinue
                    (if c.eval args != SSAConst.ofInt 0 then t else e) r.val := by
                simp [h_cond]; exact r.property
            pure ⟨r.val, compilesTo_ifthenelse_base (by grind) ih⟩

theorem SSADo.eval_eq_toexpr_interp
    (vars mutVars kMutVars : VarMap)
    (kbreak kcontinue : Option Name)
    (args mutState : Array (Name × SSAConst))
    (inloop : Bool)
    (onBreak onContinue : Array (Name × SSAConst) → SSAConst)
    (contTy : SSAType)
    (hArgs : SSADo.argsAlignVars vars args kbreak kcontinue)
    (hContTy : SSADo.continuationTypesAlign vars kMutVars kbreak kcontinue contTy)
    (hContVal : SSADo.continuationValuesAlign args kbreak kcontinue onBreak onContinue) :
    (prog : SSADo) →
    ∀ x,
        (prog.eval args inloop).run' mutState = some x →
        (prog.toSSAExpr! vars mutVars kMutVars kbreak kcontinue).eval args =
            some
                (if h : inloop then
                    (cast (by grind) x : DoResult).applyContinutations onBreak onContinue
                else
                    cast (by grind) x) := sorry
-- /- if deep embedding evaluates to a const it will evaluate to the same value of given by the shallow embedding -/
-- theorem SSADo.eval_eq_toexpr_interp (args : Array (Name × SSAConst)) (prog : SSADo) : ∀ x, (prog.eval args).run' #[] = some x → (prog.toSSAExpr! (args.map (fun (x, y) => (x, y.inferType))) #[] #[] none none).eval args = some x := sorry

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

import Pullback.SSA.SSAExpr
open Lean

inductive SSADo where
| expr : SSAExpr → SSADo
| seq (s₁ s₂ : SSADo) : SSADo
| letE (var : Name) (val : SSAExpr) (rest : SSADo) : SSADo
| letM (var : Name) (val : SSAExpr) (rest : SSADo) : SSADo -- let mut
| assign (var : Name) (val : SSAExpr) (rest : SSADo) : SSADo
| loop (body : SSADo) (rest : SSADo) : SSADo
| break : SSADo
| continue : SSADo
| return (out : SSAExpr) : SSADo
| ifthenelse (cond : SSAExpr) (t e : SSADo) (rest : SSADo) : SSADo

/- collect mut vars in top level scope (specifically for hygiene for mut var tuples) -/
def SSADo.mutVars : SSADo → Array Name
| expr e => #[]
| seq s₁ s₂ =>  Array.append (s₁.mutVars) (s₂.mutVars)
| letE var val rest => rest.mutVars
| letM var val rest => Array.append #[var] (rest.mutVars)
| assign var val rest => rest.mutVars
| loop (body : SSADo) (rest : SSADo) => rest.mutVars
| .break => #[]
| .continue => #[]
| .return _ => #[]
| ifthenelse _ _ _ _ => #[]

def SSADo.vars : SSADo → Array Name
| expr e => #[]
| seq s₁ s₂ =>  Array.append (s₁.vars) (s₂.vars)
| letE var val rest => Array.append #[var] rest.vars
| letM var val rest => Array.append #[var] rest.vars
| assign var val rest => rest.vars
| loop (body : SSADo) (rest : SSADo) => rest.vars
| .break => #[]
| .continue => #[]
| .return _ => #[]
| ifthenelse _ _ _ _ => #[]

def SSADo.toSSAExpr (vars : VarMap) (mutVars : VarMap) (kMutVars : VarMap) (kbreak kcontinue : Option Name) : SSADo → Option SSAExpr
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
| seq s₁ s₂ => do pure <| SSAExpr.letE (freshName (Array.append s₁.mutVars s₂.mutVars) `x) (← s₁.toSSAExpr vars mutVars kMutVars kbreak kcontinue) (← s₂.toSSAExpr vars mutVars kMutVars kbreak kcontinue)
| letE var val rest => do
    if mutVars.any (·.1 = var) then
        none
    else
        let valT ← val.inferType vars
        SSAExpr.letE var val (← rest.toSSAExpr (vars.push (var, valT)) mutVars kMutVars kbreak kcontinue)
| letM var val rest => do
    if mutVars.any (·.1 = var) then
        none
    let valT ← val.inferType vars

    SSAExpr.letE var val (← rest.toSSAExpr (vars.push (var, valT)) (mutVars.push (var, valT)) kMutVars kbreak kcontinue)
| assign var val rest => do
    let varT ← mutVars.get var
    let valT ← val.inferType vars
    if valT != varT then
        none
    return SSAExpr.letE var val (← rest.toSSAExpr (vars.push (var, valT)) mutVars kMutVars kbreak kcontinue)
| loop body rest => do
    let (mutTuple, mutTupleType) := (mkMutTuple mutVars)
    let bodyMutVars : Array Name  := body.mutVars
    let nS : Name := freshName (Array.append (mutVars.map (·.1)) bodyMutVars) `s
    let restExpr ← rest.toSSAExpr vars mutVars kMutVars kbreak kcontinue
    let breakNew : SSAExpr ← SSAExpr.lam nS mutTupleType <| (destructMutTuple nS mutVars restExpr)
    let nKBreak : Name := freshName (vars.map (·.1) ++ body.vars) `kbreak
    let nKContinue : Name := freshName (vars.map (·.1) ++ body.vars) `kcontinue
    -- todo :: modify mutvars passed into toSSAExpr for body
    let bodyExpr ← body.toSSAExpr vars mutVars mutVars nKBreak nKContinue
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
    let continue' := (SSAExpr.lam nS mutTupleType <| destructMutTuple nS mutVars (← rest.toSSAExpr (vars.push (nS, mutTupleType)) mutVars kMutVars kbreak kcontinue))
    let kbreak' := (SSAExpr.lam nS mutTupleType <| destructMutTuple nS mutVars (← rest.toSSAExpr (vars.push (nS, mutTupleType)) mutVars kMutVars kbreak kcontinue))
    if (← cond.inferType vars) != SSAType.ofBase .int then
        none
    let texpr ← t.toSSAExpr vars mutVars mutVars nKBreak nKContinue
    let tExprType ← texpr.inferType vars
    let eExpr ← e.toSSAExpr vars mutVars mutVars nKBreak nKContinue
    let eExprType ← eExpr.inferType vars
    if tExprType != eExprType then
        none
    SSAExpr.letE nKBreak kbreak' <| SSAExpr.letE nKContinue continue' <|
    SSAExpr.app (SSAExpr.app (SSAExpr.app (.const (.ifthenelse tExprType)) cond) texpr) (eExpr)

def SSAExpr.eval (args : Arr): SSAExpr → Option SSAConst := sorry

def SSADo.loopStep (args : Array (Name × SSAConst)) (mutvars : Array (Name × SSAConst)) : SSADo → Option (ForInStep SSAConst) := sorry

inductive LoopStep where
| continue (mutvars : Array (Name × SSAConst)) : LoopStep
| break (mutvars : Array (Name × SSAConst)) : LoopStep

inductive DoResult (α : Type) where
/- early return-/
| return (a : SSAConst) : DoResult α
| pure (a : α) : DoResult α
deriving Inhabited

instance : Inhabited (DoResult (if (!inloop) = true then SSAConst else LoopStep)) := sorry

#check StateT.run_modify

def SSADo.eval (args : Array (Name × SSAConst)) (inloop : Bool := false) : SSADo → StateT (Array (Name × SSAConst)) Option (DoResult (if !inloop then SSAConst else LoopStep))
| expr x => do
    let c ← x.eval args
    if h : !inloop then
        some (DoResult.pure (cast (by grind) c))
    else
        -- since all break, continue, return are trailing, expr will only be with inloop := true if it is a trailing expr
        some (DoResult.pure (cast (by grind) (LoopStep.continue (← get))))
/- todo :: don't discard s₁ after switching to non identity monad -/
-- note that all break, continue, return will be trailing in their respective scopes so s₁ can be evaluated with inloop := false
| seq s₁ s₂ => s₂.eval args inloop
| letE var val rest => do
    -- cannot shadow mutvars
    if (← get).any (·.1 == var) then
        failure
    rest.eval (args.push (var, ← val.eval args)) inloop
| letM var val rest => do
    if args.any (·.1 == var) then
        failure
    modify (·.push (var, ← val.eval args))
    rest.eval (args.push (var, ← val.eval args)) inloop
| assign var val rest => do
    let mutvars ← get
    let idx ← (mutvars).findFinIdx? (·.1 == var)
    set (mutvars.set idx (var, ← val.eval args))
    rest.eval args inloop
| loop body rest => do
    SSA.loop Unit.unit (fun x kcontinue => do
        match (← body.eval args true) with
        | .return x => pure (DoResult.return x)
        | .pure x =>
            match x with
            | .continue x => set x; kcontinue ()
            | .break x =>
                set x
                rest.eval args inloop
    )
| .break => do  if h : inloop then some (DoResult.pure (cast (by grind) (LoopStep.break (← get)))) else none
| .continue => do if h : inloop then some (DoResult.pure (cast (by grind) (LoopStep.continue (← get)))) else none
| .return x => do  some (DoResult.return (← x.eval args))
| ifthenelse c t e rest => do
    let res ←
        if c.eval args != SSAConst.ofInt (0 : Int) then
            t.eval args inloop
        else
            e.eval args inloop
    match res with
    | .return x => some <| .return x
    | .pure x =>  some (← rest.eval args inloop)

theorem SSADo.toSSAExpr_eq_of_vars_equiv (vars₁ vars₂ : VarMap) (mutVars contMutVars : VarMap) (kbreak kcontinue : Option Name) (hvars : vars₁.equiv vars₂) : (s : SSADo) → s.toSSAExpr vars₁ mutVars contMutVars kbreak kcontinue = s.toSSAExpr vars₂ mutVars contMutVars kbreak kcontinue := sorry

theorem SSADo.toSSAExpr_eq_of_vars_submap (vars₁ vars₂ : VarMap) (mutVars contMutVars : VarMap) (kbreak kcontinue : Option Name) (hvars : vars₁.submap vars₂) : (s : SSADo) →  (s.toSSAExpr vars₁ mutVars contMutVars kbreak kcontinue).isSome →  s.toSSAExpr vars₁ mutVars contMutVars kbreak kcontinue = s.toSSAExpr vars₂ mutVars contMutVars kbreak kcontinue := sorry

/-
    name `k` referes to a valid continutation for the current mutvars
-/
def SSADo.validContinutation (vars : VarMap) (mutVars : VarMap) (continueMutVars : VarMap) (k : Name) (prog : SSADo) := ¬ mutVars.any (·.1 = k) ∧ (do pure <| (← vars.get k).funDom? = (mkMutTuple continueMutVars).2) = some true ∧ k ∉ prog.vars

-- example (l r : List Nat) : l ⊆ r → ∀ x ∈ l, x ∈ r := by grind only [= List.subset_def,
--   #0b8b]

#check VarMap.get_eq_none_iff_not_any
theorem SSADo.validContinutation_push_of_not_mut (vars : VarMap) (mutVars : VarMap) (continueMutVars : VarMap) (k knew: Name) (prog : SSADo) (ktype : SSAType) (hk : vars.get k = some ktype) (hknew : ∀ var ∈ vars, var.1 ≠ knew) (hknew₁ : knew ∉ prog.vars) (var : Name) (hknew' : knew ≠ var) (varType : SSAType) (hMut₂ : mutVars.toList ⊆ vars.toList) : (SSADo.validContinutation vars mutVars continueMutVars k prog) → (SSADo.validContinutation ((vars.push (knew, ktype)).push (var, varType)) mutVars continueMutVars knew prog) := by
    intro H
    simp only [validContinutation, Array.any_eq_true, decide_eq_true_eq, not_exists,
      Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at H
    refine ⟨?_, ?_, ?_⟩
    · simp only [Array.any_eq_true, decide_eq_true_eq, not_exists]
      intro i hi
      apply hknew
      rw [List.subset_def] at hMut₂
      have := @hMut₂ mutVars[i] (by grind)
      simp only [Array.mem_toList_iff] at this
      grind only [= Array.mem_push, = Array.mem_map]
    · have := VarMap.get_push
      simp only [Prod.forall] at this
      simp only [this, ↓reduceIte, Option.pure_def, Option.bind_eq_bind]
      cases em (var = knew) with
      | inl hl =>
        grind
      | inr hr =>
        simp only [hr, ↓reduceIte, Option.bind_some, Option.some.injEq, decide_eq_true_eq]
        obtain ⟨a, ha⟩ := H.2
        grind only
    · exact hknew₁

/-
    `k` is the name of a valid continuation or none
-/
def SSADo.validContinutationRef (vars : VarMap) (mutVars : VarMap) (continueMutVars : VarMap)  (k : Option Name) (prog : SSADo) :=
    match k with
    | some k' => validContinutation vars mutVars continueMutVars k' prog
    | none => True

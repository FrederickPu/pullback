import Pullback.SSA.Basic
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
| ifthenelse _ t e rest => t.vars ++ e.vars ++ rest.vars

def SSADo.toSSAExpr! (vars : VarMap) (mutVars : VarMap) (kMutVars : VarMap) (kbreak kcontinue : Option Name) : SSADo → SSAExpr
-- note: only trailing exprs are interpreted as return types
-- ie: `do if cond then 10 else 10` is invalid but `do if cond then return 10 else (); 10` is valid
| expr e =>
    match kcontinue with
    | some kcontinue =>
        -- todo :: don't discard `e` and use bind
        SSAExpr.app (SSAExpr.var kcontinue) (mkMutTuple kMutVars).1
    | none => e
| seq s₁ s₂ => SSAExpr.letE (freshName (Array.append s₁.mutVars s₂.mutVars) `x) (s₁.toSSAExpr! vars mutVars kMutVars kbreak kcontinue) (s₂.toSSAExpr! vars mutVars kMutVars kbreak kcontinue)
| letE var val rest =>
    let valT := val.inferType! vars
    SSAExpr.letE var val (rest.toSSAExpr! (vars.push (var, valT)) mutVars kMutVars kbreak kcontinue)
| letM var val rest =>
    let valT := val.inferType! vars
    SSAExpr.letE var val (rest.toSSAExpr! (vars.push (var, valT)) (mutVars.push (var, valT)) kMutVars kbreak kcontinue)
| assign var val rest =>
    let valT := val.inferType! vars
    SSAExpr.letE var val (rest.toSSAExpr! (vars.push (var, valT)) mutVars kMutVars kbreak kcontinue)
| loop body rest =>
    let (mutTuple, mutTupleType) := (mkMutTuple mutVars)
    let bodyMutVars : Array Name  := body.mutVars
    let nS : Name := freshName (Array.append (mutVars.map (·.1)) bodyMutVars) `s
    let restExpr := rest.toSSAExpr! vars mutVars kMutVars kbreak kcontinue
    let breakNew : SSAExpr := SSAExpr.lam nS mutTupleType <| (destructMutTuple nS mutVars restExpr)
    let nKBreak : Name := freshName (vars.map (·.1) ++ body.vars) `kbreak
    let nKContinue : Name := freshName (vars.map (·.1) ++ body.vars) `kcontinue
    -- todo :: modify mutvars passed into toSSAExpr for body
    let bodyExpr := body.toSSAExpr! vars mutVars mutVars nKBreak nKContinue
    let bodyType := bodyExpr.inferType! vars
    let body' : SSAExpr := destructMutTuple nS mutVars bodyExpr
    SSAExpr.letE nKBreak breakNew <|
        SSAExpr.app (SSAExpr.app (SSAExpr.const (SSAConst.loop mutTupleType bodyType)) mutTuple) (SSAExpr.lam nKContinue (SSAType.fun mutTupleType (SSAType.ofBase .unit)) (SSAExpr.lam nS mutTupleType body'))
| .break =>
    match kbreak with
    | some kbreak' =>
        let (kmutTuple, _) := (mkMutTuple kMutVars)
        SSAExpr.app (SSAExpr.var kbreak') kmutTuple
    | none => panic! "no continution for break provided"
| .continue =>
    match kcontinue with
    | some kcontinue' =>
        let (kmutTuple, _) := (mkMutTuple kMutVars)
        SSAExpr.app (SSAExpr.var kcontinue') kmutTuple
    | none => panic! "no continuation for continue provided"
| .return out =>
    out
| ifthenelse cond t e rest =>
    let (_, mutTupleType) := (mkMutTuple mutVars)
    let nKContinue : Name := freshName ((vars.map (·.1) ++ t.vars ++ e.vars)) `kcontinue
    let nKBreak : Name := freshName ((vars.map (·.1) ++ t.vars ++ e.vars)) `kbreak
    let restMutVars : Array Name := rest.mutVars
    let nS : Name := freshName (Array.append (mutVars.map (·.1)) restMutVars) `s
    -- todo :: pass expanded mutvars into toSSAExpr
    let restExpr := rest.toSSAExpr! vars mutVars kMutVars kbreak kcontinue
    let restType := restExpr.inferType! vars
    let continue' := (SSAExpr.lam nS mutTupleType <| destructMutTuple nS mutVars restExpr)
    let kbreak' := (SSAExpr.lam nS mutTupleType <| destructMutTuple nS mutVars restExpr)
    let texpr := t.toSSAExpr! (vars.push (nKBreak, .fun mutTupleType restType)) mutVars mutVars nKBreak nKContinue
    let tExprType := texpr.inferType! (Array.push vars (nKBreak, (mkMutTuple mutVars).2.fun restType))
    let eExpr := e.toSSAExpr! (vars.push (nKBreak, .fun mutTupleType restType)) mutVars mutVars nKBreak nKContinue
    SSAExpr.letE nKBreak kbreak' <| SSAExpr.letE nKContinue continue' <|
    SSAExpr.app (SSAExpr.app (SSAExpr.app (.const (.ifthenelse tExprType)) cond) texpr) (eExpr)

def SSADo.loopStep (args : Array (Name × SSAConst)) (mutvars : Array (Name × SSAConst)) : SSADo → Option (ForInStep SSAConst) := sorry

inductive LoopStep where
| continue (mutvars : Array (Name × SSAConst)) : LoopStep
| break (mutvars : Array (Name × SSAConst)) : LoopStep
deriving Inhabited

inductive DoResult where
/- early return-/
| return (a : SSAConst) : DoResult
| pure (a : LoopStep) : DoResult
deriving Inhabited


-- note: `kcontinue` doubles both as for jumping to next loop iteration and for invoking rest of the program
-- eg in `if c then t else e; rest` the `kcontinue` gets invoked after evaluating `t` to "jump" to `rest`
-- however the `continue` keyword in do notation is reserved for loop bodys
def SSADo.eval (args mutArgs kMutArgs : Array (Name × SSAConst)) (kbreak kcontinue : Option (Array (Name × SSAConst) → Option SSAConst)) : SSADo → Option SSAConst
| expr e =>
    match kcontinue with
    | some kcontinue =>
        -- todo :: don't discard `e` and use bind
        kcontinue kMutArgs
    | none => e.eval args
| seq s₁ s₂ => do
    let x ← (s₁.eval args mutArgs kMutArgs kbreak kcontinue)
    s₂.eval args mutArgs kMutArgs kbreak kcontinue
| letE var val rest => do
    if mutArgs.any (·.1 == var) then
        -- cannot shadow mutVars
        none
    rest.eval (args.push (var, ← val.eval args)) mutArgs kMutArgs kbreak kcontinue
| letM var val rest => do
    if mutArgs.any (·.1 == var) then
        -- cannot shadow mutVars
        none
    let val' ← val.eval args
    rest.eval (args.push (var, val')) (mutArgs.push (var, val')) kMutArgs kbreak kcontinue
| assign var val rest => do
    let idx ← (mutArgs).findFinIdx? (·.1 == var)
    let val' ← val.eval args
    if val'.inferType == mutArgs[idx].2.inferType then
        rest.eval args (mutArgs.set idx (var, val')) kMutArgs kbreak kcontinue
    else
        none
| loop body rest => do
    let kMutArgs' := mutArgs
    let kcontinue' := kcontinue' kMutArgs' (← kcontinue)
    SSA.loop mutArgs (fun mutArgs' kcont =>
        body.eval (args ++ mutArgs') mutArgs' kMutArgs' kcontinue' kcont)
| .break =>
    match kbreak with
    | some kbreak' => kbreak' mutArgs
    | none => none
| .continue =>
    match kcontinue with
    | some kcontinue' => kcontinue' mutArgs
    | none => none
| .return out =>
    out.eval args
| ifthenelse c t e rest => do
    let kMutArgs' := mutArgs
    let kcontinue' := kcontinue' kMutArgs' (← kcontinue)
    match ← c.eval args with
    | .ofBase (.int ci) =>
        if ci != 0 then
            t.eval args mutArgs kMutArgs' kbreak kcontinue'
        else
            e.eval args mutArgs kMutArgs kbreak kcontinue'
    | _ => none
where
    kcontinue' (kMutArgs' : Array (Name × SSAConst)) (kcontinue : Array (Name × SSAConst) → Option SSAConst) : Array (Name × SSAConst) → Option SSAConst :=
        fun mutArgs' : Array (Name × SSAConst) =>
            kcontinue (kMutArgs'.map (fun (n, _) => (n, (mutArgs'.findLast? (·.1 == n)).get!.2)))

-- def SSADo.eval (args : Array (Name × SSAConst)) (inloop : Bool := false) : SSADo → StateT (Array (Name × SSAConst)) Option (if !inloop then SSAConst else DoResult)
-- | expr x => do
--     let c ← x.eval args
--     if h : !inloop then
--         some <| cast (by grind) c
--     else
--         if (← x.eval args).inferType != .ofBase .unit then
--             none
--         -- since all break, continue, return are trailing, expr will only be with inloop := true if it is a trailing expr
--         some (cast (by grind) (DoResult.pure (LoopStep.continue (← get))))
-- /- todo :: don't discard s₁ after switching to non identity monad -/
-- -- note that all break, continue, return will be trailing in their respective scopes so s₁ can be evaluated with inloop := false
-- | seq s₁ s₂ => s₂.eval args inloop
-- | letE var val rest => do
--     -- cannot shadow mutvars
--     if (← get).any (·.1 == var) then
--         none
--     rest.eval (args.push (var, ← val.eval args)) inloop
-- | letM var val rest => do
--     if args.any (·.1 == var) then
--         none
--     let before ← get
--     set (before.push (var, ← val.eval args))
--     let x ← rest.eval (args.push (var, ← val.eval args)) inloop
--     set before
--     return x
-- | assign var val rest => do
--     let mutvars ← get
--     let idx ← (mutvars).findFinIdx? (·.1 == var)
--     let val' ← val.eval args
--     if val'.inferType == mutvars[idx].2.inferType then
--         set (mutvars.set idx (var, val'))
--         rest.eval args inloop
--     else
--         none
-- | loop body rest => do
--     SSA.loop Unit.unit (fun x kcontinue => do
--         match (← body.eval args true) with
--         | .return x => pure (
--             if h : inloop then
--                 cast (by grind) (DoResult.return x)
--             else
--                 cast (by grind) x)
--         | .pure x =>
--             match x with
--             | .continue x => set x; kcontinue ()
--             | .break x =>
--                 set x
--                 rest.eval args inloop
--     )
-- | .break => do  if h : inloop then some (cast (by grind) (DoResult.pure (LoopStep.break (← get)))) else none
-- | .continue => do if h : inloop then some (cast (by grind) (DoResult.pure (LoopStep.continue (← get)))) else none
-- | .return x => do
--     let res ← x.eval args
--     some (
--     if h : inloop then
--         cast (by grind) <| DoResult.return res
--     else
--         cast (by grind) res)
-- | ifthenelse c t e rest => do
--     let res ←
--         if c.eval args != SSAConst.ofInt (0 : Int) then
--             t.eval args inloop
--         else
--             e.eval args inloop
--     if h : inloop then
--         match cast (β := DoResult) (by grind) res with
--         | .return x => some <| (cast (by grind) <| DoResult.return x)
--         | .pure x =>  some (← rest.eval args inloop)
--     else
--         return res



-- /-
--     name `k` referes to a valid continutation for the current mutvars
-- -/
-- def SSADo.validContinutation (vars : VarMap) (mutVars : VarMap) (continueMutVars : VarMap) (k : Name) (prog : SSADo) := ¬ mutVars.any (·.1 = k) ∧ (do pure <| (← vars.get k).funDom? = (mkMutTuple continueMutVars).2) = some true ∧ k ∉ prog.vars

-- #check VarMap.get_eq_none_iff_not_any
-- theorem SSADo.validContinutation_push_of_not_mut (vars : VarMap) (mutVars : VarMap) (continueMutVars : VarMap) (k knew: Name) (prog : SSADo) (ktype : SSAType) (hk : vars.get k = some ktype) (hknew : ∀ var ∈ vars, var.1 ≠ knew) (hknew₁ : knew ∉ prog.vars) (var : Name) (hknew' : knew ≠ var) (varType : SSAType) (hMut₂ : mutVars.toList ⊆ vars.toList) : (SSADo.validContinutation vars mutVars continueMutVars k prog) → (SSADo.validContinutation ((vars.push (knew, ktype)).push (var, varType)) mutVars continueMutVars knew prog) := by
--     intro H
--     simp only [validContinutation, Array.any_eq_true, decide_eq_true_eq, not_exists,
--       Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at H
--     refine ⟨?_, ?_, ?_⟩
--     · simp only [Array.any_eq_true, decide_eq_true_eq, not_exists]
--       intro i hi
--       apply hknew
--       rw [List.subset_def] at hMut₂
--       have := @hMut₂ mutVars[i] (by grind)
--       simp only [Array.mem_toList_iff] at this
--       grind only [= Array.mem_push, = Array.mem_map]
--     · have := VarMap.get_push
--       simp only [Prod.forall] at this
--       simp only [this, ↓reduceIte, Option.pure_def, Option.bind_eq_bind]
--       cases em (var = knew) with
--       | inl hl =>
--         grind
--       | inr hr =>
--         simp only [hr, ↓reduceIte, Option.bind_some, Option.some.injEq, decide_eq_true_eq]
--         obtain ⟨a, ha⟩ := H.2
--         grind only
--     · exact hknew₁

-- theorem SSADo.eval_letE
--     {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
--     {args : Array (Name × SSAConst)}
--     {var : Name} {val : SSAExpr} {rest : SSADo} {v : SSAConst}
--     (hval : val.eval args = some v)
--         (htype_eq : val.inferType! vars = v.inferType) :
--     (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue (SSADo.letE var val rest)).eval args =
--         (SSADo.toSSAExpr! (vars.push (var, v.inferType)) mutVars kMutVars kbreak kcontinue rest).eval (args.push (var, v)) := by
--     rw [← htype_eq]
--     simpa [SSADo.toSSAExpr!] using
--       SSAExpr.eval_letE_push_of_eval args var val
--         (rest.toSSAExpr! (vars.push (var, val.inferType! vars)) mutVars kMutVars kbreak kcontinue)
--         v hval

-- theorem SSADo.eval_letM
--     {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
--     {args : Array (Name × SSAConst)}
--     {var : Name} {val : SSAExpr} {rest : SSADo} {v : SSAConst}
--     (hval : val.eval args = some v)
--     (htype_eq : val.inferType! vars = v.inferType) :
--     (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue (SSADo.letM var val rest)).eval args =
--         (SSADo.toSSAExpr! (vars.push (var, v.inferType)) (mutVars.push (var, v.inferType)) kMutVars kbreak kcontinue rest).eval (args.push (var, v)) := by
--     rw [← htype_eq]
--     simpa [SSADo.toSSAExpr!] using
--       SSAExpr.eval_letE_push_of_eval args var val
--         (rest.toSSAExpr! (vars.push (var, val.inferType! vars)) (mutVars.push (var, val.inferType! vars)) kMutVars kbreak kcontinue)
--         v hval


-- theorem SSADo.toSSAExpr!_vars_equiv
--     {vars₁ vars₂ mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
--     (hvars : VarMap.equiv vars₁ vars₂) :
--     {rest : SSADo} →
--     (rest.toSSAExpr! vars₁ mutVars kMutVars kbreak kcontinue) =
--     (rest.toSSAExpr! vars₂ mutVars kMutVars kbreak kcontinue)
-- | expr x => by
--     simp [toSSAExpr!]
-- | letE varName val body => by
--     simp only [toSSAExpr!, SSAExpr.letE.injEq, true_and]
--     apply SSADo.toSSAExpr!_vars_equiv
--     have : SSAExpr.inferType! vars₁ val = SSAExpr.inferType! vars₂ val :=
--       SSAExpr.inferType!_eq_of_vars_equiv hvars
--     rw [this]
--     exact VarMap.equiv_push vars₁ vars₂ hvars varName (SSAExpr.inferType! vars₂ val)
-- | letM varName val body => by
--     simp only [toSSAExpr!, SSAExpr.letE.injEq, true_and]
--     have : SSAExpr.inferType! vars₁ val = SSAExpr.inferType! vars₂ val :=
--       SSAExpr.inferType!_eq_of_vars_equiv hvars
--     rw [this]
--     apply toSSAExpr!_vars_equiv
--     exact VarMap.equiv_push vars₁ vars₂ hvars varName (SSAExpr.inferType! vars₂ val)
-- | assign varname val body => by
--     simp [toSSAExpr!]
--     apply SSADo.toSSAExpr!_vars_equiv
--     have : SSAExpr.inferType! vars₁ val = SSAExpr.inferType! vars₂ val :=
--       SSAExpr.inferType!_eq_of_vars_equiv hvars
--     rw [this]
--     exact VarMap.equiv_push vars₁ vars₂ hvars varname (SSAExpr.inferType! vars₂ val)
-- | .return out => by simp [toSSAExpr!]
-- | .break => by simp [toSSAExpr!]
-- | .continue => by simp [toSSAExpr!]
-- | seq s₁ s₂ => by
--     simp [toSSAExpr!]
--     apply And.intro
--     · exact toSSAExpr!_vars_equiv hvars
--     · exact toSSAExpr!_vars_equiv hvars
-- | loop body rest => by
--     simp [toSSAExpr!]
--     have : freshName (Array.map (fun x => x.1) vars₁ ++ body.vars) =
--     freshName (Array.map (fun x => x.1) vars₂ ++ body.vars) := sorry
--     simp [this]
--     simp [toSSAExpr!_vars_equiv hvars, SSAExpr.inferType!_eq_of_vars_equiv hvars]
-- | ifthenelse c t e rest => by
--     simp [toSSAExpr!]
--     have hfresh :
--         freshName (Array.map (fun x => x.1) vars₁ ++ (t.vars ++ e.vars)) =
--         freshName (Array.map (fun x => x.1) vars₂ ++ (t.vars ++ e.vars)) := by
--         sorry
--     have hEqPush : ∀ kb τ, VarMap.equiv (Array.push vars₁ (kb, τ)) (Array.push vars₂ (kb, τ)) :=
--         VarMap.equiv_push vars₁ vars₂ hvars
--     simp [hfresh]
--     simp [toSSAExpr!_vars_equiv hvars, toSSAExpr!_vars_equiv (hEqPush _ _), SSAExpr.inferType!_eq_of_vars_equiv hvars, SSAExpr.inferType!_eq_of_vars_equiv (hEqPush _ _)]

-- theorem SSADo.toSSAExpr_var_push
--     {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
--     {var : Name} {val : SSAExpr} {rest : SSADo} :
--     (hvar_type : vars.get var = some (val.inferType! vars)) →
--     (rest.toSSAExpr! (vars.push (var, val.inferType! vars)) mutVars kMutVars kbreak kcontinue) =
--     (rest.toSSAExpr! vars mutVars kMutVars kbreak kcontinue) := by
--     intro hvar_type
--     have hpush_equiv : VarMap.equiv (vars.push (var, val.inferType! vars)) vars := by
--         apply VarMap.equiv_symm
--         apply  VarMap.equiv_push_of_shadow
--         grind
--     simpa using SSADo.toSSAExpr!_vars_equiv
--         (vars₁ := (vars.push (var, val.inferType! vars)))
--         (vars₂ := vars)
--         (mutVars := mutVars)
--         (kMutVars := kMutVars)
--         (kbreak := kbreak)
--         (kcontinue := kcontinue)
--         (rest := rest)
--         hpush_equiv

-- theorem SSADo.eval_assign
--     {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
--     {args : Array (Name × SSAConst)}
--     {var : Name} {val : SSAExpr} {rest : SSADo} {v : SSAConst}
--     (hvar_type : vars.get var = some (val.inferType! vars))
--     (_hval : val.eval args = some v) :
--     (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue (SSADo.assign var val rest)).eval args =
--             (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue rest).eval args := by
--     have hassign_bridge :
--             (rest.toSSAExpr! (vars.push (var, val.inferType! vars)) mutVars kMutVars kbreak kcontinue).eval args =
--             (rest.toSSAExpr! vars mutVars kMutVars kbreak kcontinue).eval args := by
--         exact congrArg (fun e => e.eval args) <|
--             SSADo.toSSAExpr_var_push (vars := vars) (mutVars := mutVars) (kMutVars := kMutVars)
--                 (kbreak := kbreak) (kcontinue := kcontinue) (var := var) (val := val)
--                 (rest := rest) hvar_type
--     have hlet :
--             (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue (SSADo.assign var val rest)).eval args =
--             (rest.toSSAExpr! (vars.push (var, val.inferType! vars)) mutVars kMutVars kbreak kcontinue).eval args := by
--         simpa [SSADo.toSSAExpr!] using SSAExpr.eval_letE args var val
--             (rest.toSSAExpr! (vars.push (var, val.inferType! vars)) mutVars kMutVars kbreak kcontinue)
--     exact (Eq.trans hlet hassign_bridge)

-- theorem SSADo.eval_ifthenelse_branch
--     {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
--     {args : Array (Name × SSAConst)}
--     {c : SSAExpr} {t e rest : SSADo} :
--     (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue (SSADo.ifthenelse c t e rest)).eval args =
--     (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue
--         (if c.eval args != SSAConst.ofInt 0 then t else e)).eval args := by
--     sorry

-- theorem SSADo.eval_ifthenelse_rest
--     {vars mutVars kMutVars : VarMap} {kbreak kcontinue : Option Name}
--     {args : Array (Name × SSAConst)}
--     {c : SSAExpr} {t e rest : SSADo} :
--     (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue (SSADo.ifthenelse c t e rest)).eval args =
--     (SSADo.toSSAExpr! vars mutVars kMutVars kbreak kcontinue rest).eval args := by
--     sorry


-- /-
--     `k` is the name of a valid continuation or none
-- -/
-- def SSADo.validContinutationRef (vars : VarMap) (mutVars : VarMap) (continueMutVars : VarMap)  (k : Option Name) (prog : SSADo) :=
--     match k with
--     | some k' => validContinutation vars mutVars continueMutVars k' prog
--     | none => True

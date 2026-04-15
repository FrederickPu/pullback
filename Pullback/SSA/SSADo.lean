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

#check mkMutTuple
def SSADo.toSSAExpr! (vars : VarMap) (mutVars : VarMap) (kMutVars : VarMap) (kbreak kcontinue k : Option Name) (ktype : SSAType) : SSADo → SSAExpr
-- note: only trailing exprs are interpreted as return types
-- ie: `do if cond then 10 else 10` is invalid but `do if cond then return 10 else (); 10` is valid
| expr e =>
    match k with
    | some k' =>
        -- todo :: don't discard `e` and use bind
        SSAExpr.app (SSAExpr.var k') (mkMutTuple kMutVars).1
    | none => e
| seq s₁ s₂ => SSAExpr.letE (freshName (Array.append s₁.mutVars s₂.mutVars) `x) (s₁.toSSAExpr! vars mutVars kMutVars kbreak kcontinue k ktype) (s₂.toSSAExpr! vars mutVars kMutVars kbreak kcontinue k ktype)
| letE var val rest =>
    let valT := val.inferType! vars
    SSAExpr.letE var val (rest.toSSAExpr! (vars.push (var, valT)) mutVars kMutVars kbreak kcontinue k ktype)
| letM var val rest =>
    let valT := val.inferType! vars
    SSAExpr.letE var val (rest.toSSAExpr! (vars.push (var, valT)) (mutVars.push (var, valT)) kMutVars kbreak kcontinue k ktype)
| assign var val rest =>
    let valT := val.inferType! vars
    SSAExpr.letE var val (rest.toSSAExpr! (vars.push (var, valT)) mutVars kMutVars kbreak kcontinue k ktype)
| loop body rest =>
    let (mutTuple, mutTupleType) := (mkMutTuple mutVars)
    let bodyMutVars : Array Name  := body.mutVars
    let nS : Name := freshName (Array.append (mutVars.map (·.1)) bodyMutVars) `s
    let restExpr := rest.toSSAExpr! vars mutVars kMutVars kbreak kcontinue kcontinue ktype
    let breakNew : SSAExpr := SSAExpr.lam nS mutTupleType <| (destructMutTuple nS mutVars restExpr)
    let nKBreak : Name := freshName (vars.map (·.1) ++ body.vars) `kbreak
    let nKContinue : Name := freshName (vars.map (·.1) ++ body.vars) `kcontinue
    -- todo :: modify mutvars passed into toSSAExpr for body
    let bodyExpr := body.toSSAExpr! (vars ++ #[(nKBreak, .fun mutTupleType ktype), (nKContinue, .fun mutTupleType ktype)]) mutVars mutVars nKBreak nKContinue k ktype
    let body' : SSAExpr := destructMutTuple nS mutVars bodyExpr
    SSAExpr.letE nKBreak breakNew <|
        SSAExpr.app (SSAExpr.app (SSAExpr.const (SSAConst.loop mutTupleType ktype)) mutTuple) (SSAExpr.lam nKContinue (SSAType.fun mutTupleType (SSAType.ofBase .unit)) (SSAExpr.lam nS mutTupleType body'))
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
    let nKContinue : Option Name := kcontinue.map (fun _ => freshName ((vars.map (·.1) ++ t.vars ++ e.vars)) `kcontinue)
    let restMutVars : Array Name := rest.mutVars
    let nS : Name := freshName (Array.append (mutVars.map (·.1)) restMutVars) `s
    -- todo :: pass expanded mutvars into toSSAExpr
    let restExpr := rest.toSSAExpr! vars mutVars kMutVars kbreak kcontinue k ktype
    -- route to outer continutation (from while loop)
    let continue' := (SSAExpr.lam nS mutTupleType <| destructMutTuple nS mutVars (mkMutTuple kMutVars).1)

    let nKBreak : Option Name := kbreak.map (fun _ => freshName ((vars.map (·.1) ++ t.vars ++ e.vars)) `kbreak)
    -- route to outer continutation (from while loop)
    let kbreak' := (SSAExpr.lam nS mutTupleType <| destructMutTuple nS mutVars (mkMutTuple kMutVars).1)

    let nkif := freshName ((vars.map (·.1) ++ t.vars ++ e.vars)) `kif
    let kif := (SSAExpr.lam nS mutTupleType <| destructMutTuple nS mutVars restExpr)

    let vars' := vars.push (nkif, .fun mutTupleType ktype)
    let vars'' := match nKBreak with
    | some x => (vars'.push (x, .fun mutTupleType ktype))
    | _ => vars'

    let vars''' := match nKContinue with
    | some x => vars''.push (x, .fun mutTupleType ktype)
    | none => vars''

    let texpr := t.toSSAExpr! vars''' mutVars mutVars nKBreak nKContinue nkif ktype
    let tExprType := texpr.inferType! vars'''
    let eExpr := e.toSSAExpr! vars''' mutVars mutVars nKBreak nKContinue nkif ktype
    let base := SSAExpr.letE nkif kif <|
    SSAExpr.app (SSAExpr.app (SSAExpr.app (.const (.ifthenelse tExprType)) cond) texpr) (eExpr)
   let base' := match nKBreak with
    | some x => SSAExpr.letE x kbreak' base
    | _ => base

    match nKContinue with
    | some x => SSAExpr.letE x continue' base'
    | none => base'

def SSADo.inferType (vars : VarMap) (mutVars kmutVars : Array Name) (hasBreak : Bool) (hasContinue : Bool) (hasK : Bool) (continutationType : Option SSAType) : SSADo → Option SSAType
| expr e => do
    let et ← e.inferType vars
    if hasK then
        if et = .ofBase .unit then
            continutationType
        else
            none
    else
        return et
| seq s₁ s₂ => do
    let _ ← s₁.inferType vars mutVars kmutVars hasBreak hasContinue hasK continutationType
    s₂.inferType vars mutVars kmutVars hasBreak hasContinue hasK continutationType
| letE var val rest => do
    if mutVars.any (· == var) then
        -- cannot shadow mutVars
        none
    rest.inferType (vars.push (var, ← val.inferType vars)) mutVars kmutVars hasBreak hasContinue hasK continutationType
| letM var val rest => do
    if mutVars.any (· == var) then
        -- cannot shadow mutVars
        none
    let valT ← val.inferType vars
    rest.inferType (vars.push (var, valT)) (mutVars.push var) kmutVars hasBreak hasContinue hasK continutationType
| assign var val rest => do
    let valT ← val.inferType vars
    if valT == vars.get var then
        rest.inferType (vars.push (var, valT)) mutVars kmutVars hasBreak hasContinue hasK continutationType
    else
        -- mut var type can never change
        none
| loop body rest => do
    let restT ← rest.inferType vars mutVars kmutVars hasBreak hasContinue hasK continutationType
    let bodyT ← body.inferType vars mutVars mutVars true true true restT
    if bodyT = restT then
        return bodyT
    else
        none
| .break =>
    if hasBreak then
        continutationType
    else
        none
| .continue =>
    if hasBreak then
        continutationType
    else
        none
| .return out => do
    let outT ← out.inferType vars
    match continutationType with
    | some ct => if ct == outT then return outT else none
    | none => return outT
| ifthenelse cond t e rest => do
    if (← cond.inferType vars) != .ofBase .int then
        none
    let restT ← rest.inferType vars mutVars kmutVars hasBreak hasContinue hasK continutationType
    let tT ← t.inferType vars mutVars kmutVars hasBreak hasContinue hasK restT
    if tT != restT then
        none
    let tE ← e.inferType vars mutVars kmutVars hasBreak hasContinue hasK restT
    if tE != restT then
        none
    return restT

def Option.All {α} (p : α → Prop) (x : Option α) : Prop :=
    match x with
    | some x => p x
    | none => True

/-
    name `k` referes to a valid continutation for the current mutvars
-/
def SSADo.validContinuationRef (vars mutVars continueMutVars : VarMap) (prog : SSADo) (ktype : SSAType) (k : Name) := ¬ mutVars.any (·.1 = k) ∧ (do pure <| (← vars.get k) = .fun (mkMutTuple continueMutVars).2 ktype) = some true ∧ k ∉ prog.vars

structure validVars (vars mutVars kmutVars : VarMap) : Prop where
  hMut₁ : mutVars.uniqueKeys
  hMut₂ : mutVars.submap vars
  hcontMutVars : kmutVars.isPrefixOf mutVars

#check mkMutTuple
def SSADo.interp (vars mutVars kmutVars : VarMap) (kbreak kcontinue k : Option Name) (ktype : Option SSAType) (hvalidVars : validVars vars mutVars kmutVars) :
    (prog : SSADo) →
    (hprog : prog.inferType vars mutVars.keys kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype |>.isSome) →
    let ktype := (prog.inferType vars mutVars.keys kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype).get hprog;
    kbreak.All (validContinuationRef vars mutVars kmutVars prog ktype) →
    kcontinue.All (validContinuationRef vars mutVars kmutVars prog ktype) →
    k.All (validContinuationRef vars mutVars kmutVars prog ktype) → DVector (Array.toList (vars.map (·.2.type))) →
    ktype.type
| expr e, hprog, hkbreak, hkcontinue, hk, args =>
    have he : (e.inferType vars).isSome := by sorry
    match k with
    | some k' =>
        have : (e.inferType vars).get he = .ofBase .unit := by grind [inferType]
        have hkRef : (vars.findLastFinIdx? (·.1 == k')).isSome := sorry
        let kfun := cast (β := (mkMutTuple kmutVars).2.type → (ktype.get (by grind [inferType])).type)
            sorry
            (args.get (cast (by grind) ((vars.findLastFinIdx? (·.1 == k')).get hkRef)))
        cast sorry <|
            kfun (cast sorry ((mkMutTuple kmutVars).1.interp vars sorry args))
    | none =>
        cast (by grind [inferType]) (e.interp vars he args)
        -- cast (by grind [inferType]) ((base.interp vars) (by grind [inferType]) args)
| seq s₁ s₂, hprog, hkbreak, hkcontinue, hk, args =>
    have hs₁ : (s₁.inferType vars mutVars.keys kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype).isSome := by
        grind [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff]
    have hs₂ : (s₂.inferType vars mutVars.keys kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype).isSome := by
        grind [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff]
    let _ := s₁.interp vars mutVars kmutVars kbreak kcontinue k ktype hvalidVars hs₁ sorry sorry sorry args
    cast (by grind [inferType]) (s₂.interp vars mutVars kmutVars kbreak kcontinue k ktype hvalidVars hs₂ sorry sorry sorry args)
-- | letE var val rest, hprog, hkbreak, hkcontinue, hk, args =>
--     have hval : (val.inferType vars).isSome := by grind [inferType]
--     have : rest.inferType (vars.push (var, (val.inferType vars).get hval)) mutVars kmutVars kbreak.isSome kcontinue.isSome
| _, _, _, _, _, _ => sorry

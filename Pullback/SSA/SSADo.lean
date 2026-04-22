import Pullback.SSA.Basic
import Pullback.SSA.SSAExpr
open Lean

set_option maxHeartbeats 1000000


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
| seq s₁ s₂ => SSAExpr.letE (freshName (Array.append s₁.mutVars s₂.mutVars) `x) (s₁.toSSAExpr! vars mutVars kMutVars none none none (.ofBase .unit)) (s₂.toSSAExpr! vars mutVars kMutVars kbreak kcontinue k ktype)
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
    let _ ← s₁.inferType vars mutVars kmutVars false false false (some <| .ofBase .unit)
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
    if var ∈ mutVars ∧ valT = vars.get var then
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
    if hasContinue then
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

def Option.Any {α} (p : α → Prop) (x : Option α) : Prop :=
    match x with
    | some x => p x
    | none => False

def Option.All_intro {α} {p : α → Prop} {x : Option α} (h : ∀ x', x = some x' → p x') : Option.All p x := by
    match x with
    | some x' => grind [All]
    | none => grind [All]

theorem SSADo.inferType_ktype (vars : VarMap) (mutVars kmutVars : Array Name) (hasBreak : Bool) (hasContinue : Bool) (hasK : Bool) (ktype : SSAType) (prog : SSADo): prog.inferType vars mutVars kmutVars hasBreak hasContinue hasK ktype |>.All (· = ktype) := sorry

theorem SSADo.inferType_ktype_roundtrip (vars : VarMap) (mutVars kmutVars : Array Name)
    (hasBreak hasContinue hasK : Bool) (ktype : Option SSAType) (ktype' : SSAType) (prog : SSADo)
    (h : prog.inferType vars mutVars kmutVars hasBreak hasContinue hasK ktype = some ktype') :
    prog.inferType vars mutVars kmutVars hasBreak hasContinue hasK (some ktype') = some ktype' := sorry


theorem SSADo.inferType_push_eq_of_hygenic
    (vars : VarMap) (mutVars kmutVars : Array Name)
    (hasBreak hasContinue hasK : Bool) (continuationType : Option SSAType)
    (newvar : Name) (newVarType : SSAType)
    (hHygenic : ¬ vars.any (·.1 = newvar))
    (hNotMut : ¬ mutVars.any (· == newvar)) :
    (prog : SSADo) →
    (prog.inferType vars mutVars kmutVars hasBreak hasContinue hasK continuationType).isSome →
    prog.inferType (vars.push (newvar, newVarType)) mutVars kmutVars hasBreak hasContinue hasK continuationType =
    prog.inferType vars mutVars kmutVars hasBreak hasContinue hasK continuationType := sorry

#check Option.all
/-
    name `k` referes to a valid continutation for the current mutvars
-/
def SSADo.validContinuationRef (vars mutVars continueMutVars : VarMap) (prog : SSADo) (ktype : SSAType) (k : Name) :=
  ¬ mutVars.any (·.1 = k) ∧
  Option.Any (· = .fun (mkMutTuple continueMutVars).2 ktype) (vars.get k) ∧
  k ∉ prog.vars

theorem SSADo.validContinuationRef_subset_progvars (vars mutVars continueMutVars : VarMap) (prog prog' : SSADo) (ktype : SSAType) (k : Name) (hprogVars : prog'.vars.toList ⊆ prog.vars.toList) :
    validContinuationRef vars mutVars continueMutVars prog ktype k →
    validContinuationRef vars mutVars continueMutVars prog' ktype k := sorry

def validVars (vars mutVars kmutVars : VarMap) : Prop := mutVars.uniqueKeys ∧ mutVars.submap vars ∧ kmutVars.isPrefixOf mutVars

instance (vm : VarMap) : Inhabited (DVector (vm.map (·.2.type)).toList) := sorry

theorem SSADo.inferType_continutation (vars mutVars kmutVars : VarMap) (k : Name) (prog : SSADo) (ktype : SSAType) (hvalid : validContinuationRef vars mutVars kmutVars prog ktype k) :
    (SSAExpr.var k).inferType vars = SSAType.fun (mkMutTuple kmutVars).2 ktype := sorry

open List

#check Fin.cast
def SSADo.interp (vars mutVars kmutVars : VarMap) (kbreak kcontinue k : Option Name) (ktype : Option SSAType) (hvalidVars : validVars vars mutVars kmutVars) :
    (prog : SSADo) →
    (hprog : prog.inferType vars mutVars.keys kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype |>.isSome) →
    let ktype := (prog.inferType vars mutVars.keys kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype).get hprog;
    kbreak.All (validContinuationRef vars mutVars kmutVars prog ktype) →
    kcontinue.All (validContinuationRef vars mutVars kmutVars prog ktype) →
    k.All (validContinuationRef vars mutVars kmutVars prog ktype) → DVector (Array.toList (vars.map (·.2.type))) →
    ktype.type
| expr e, hprog, hkbreak, hkcontinue, hk, args =>
    have he : (e.inferType vars).isSome := by grind [inferType]
    match hhk : k with
    | some k' =>
        have : (e.inferType vars).get he = .ofBase .unit := by grind [inferType]
        have hktype : ktype.isSome := by grind [inferType]
        let kfun := cast (β := (mkMutTuple kmutVars).2.type → (ktype.get hktype).type)
            (by {
                have : ktype = ktype.get hktype := by grind
                have qq : inferType vars (Map.keys mutVars) (Map.keys kmutVars) kbreak.isSome kcontinue.isSome k.isSome (ktype.get hktype) (expr e) = (inferType vars (Map.keys mutVars) (Map.keys kmutVars) kbreak.isSome kcontinue.isSome k.isSome (ktype.get hktype) (expr e)).get (by rw [← this, hhk]; exact hprog) := by grind
                have := inferType_ktype vars mutVars.keys kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome (ktype.get hktype) (.expr e)
                rw [qq] at this
                simp [Option.All, hhk] at this
                simp [this] at hk
                have := inferType_continutation vars mutVars kmutVars k' (.expr e) (ktype.get hktype) hk
                simp [this, SSAType.type]
            })
            ((SSAExpr.var k').interp vars (by {
                simp only [SSAExpr.inferType]
                simp only [Option.All, Option.isSome_some] at hk
                have := hk.2.1
                simp only [Option.Any] at this
                grind only [= Option.isSome_some]
            }) args)
        have : (SSAExpr.inferType vars (mkMutTuple kmutVars).1) = (mkMutTuple kmutVars).2 := by
            have h1 : kmutVars.uniqueKeys :=
                Map.uniqueKeys_prefixOf kmutVars mutVars hvalidVars.1 hvalidVars.2.2
            have : kmutVars.submap mutVars :=
                Map.submap_prefixOf _ _  hvalidVars.1 hvalidVars.2.2
            have h2 : kmutVars.submap vars := Map.submap_trans kmutVars mutVars vars this hvalidVars.2.1
            exact SSAExpr.inferType_mkMutTuple' vars kmutVars h1 h2
        cast (by grind [inferType_ktype, inferType]) <|
            kfun (cast (by grind) ((mkMutTuple kmutVars).1.interp vars (by grind) args))
    | none =>
        cast (by grind [inferType]) (e.interp vars he args)
| seq s₁ s₂, hprog, hkbreak, hkcontinue, hk, args =>
    have hs₁ : (s₁.inferType vars mutVars.keys kmutVars.keys none.isSome none.isSome none.isSome (some <| .ofBase .unit)).isSome := by
        simp [inferType] at hprog
        option_elim
        grind
    have hs₂ : (s₂.inferType vars mutVars.keys kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype).isSome := by
        grind [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff]
    have : s₁.vars.toList ⊆ (seq s₁ s₂).vars.toList := by simp [SSADo.vars]
    let _ := s₁.interp vars mutVars kmutVars none none none (some <| .ofBase .unit) hvalidVars hs₁ (by simp [Option.All]) (by simp [Option.All]) (by simp [Option.All]) args
    have : s₂.vars.toList ⊆ (seq s₁ s₂).vars.toList := by simp [SSADo.vars]
    cast (by grind [inferType]) (s₂.interp vars mutVars kmutVars kbreak kcontinue k ktype hvalidVars hs₂ (by {
        apply Option.All_intro
        intro kbreak' hkbreak'
        simp [Option.All, hkbreak'] at hkbreak
        simp [inferType] at hkbreak
        simp [hkbreak']
        exact
          validContinuationRef_subset_progvars vars mutVars kmutVars (s₁.seq s₂) s₂
            _
            kbreak' this hkbreak
    }) sorry sorry args)
| letE var val rest, hprog, hkbreak, hkcontinue, hk, args =>
    have hval : (val.inferType vars).isSome := by grind [inferType]
    have hrest : (rest.inferType (vars.push (var, (val.inferType vars).get hval)) mutVars.keys kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype).isSome := by grind [inferType]
    have qq : ¬ mutVars.keys.any (· == var) := by grind [inferType]
    let ktype' := ((SSADo.letE var val rest).inferType vars mutVars.keys kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype).get hprog
    have letE_validCont : ∀ (kX : Option Name),
    kX.All (validContinuationRef vars mutVars kmutVars (letE var val rest) ktype') →
    kX.All (validContinuationRef (vars.push (var, (val.inferType vars).get hval)) mutVars kmutVars rest ktype') := by
        intro kX hkX
        apply Option.All_intro
        intro kX' hkX'
        simp [hkX', Option.All] at hkX
        refine ⟨hkX.1, ?_, ?_⟩
        · have := hkX.2.1
          simp only [Option.Any] at this
          have hget : Map.get (Array.push vars (var, (SSAExpr.inferType vars val).get hval)) kX' = vars.get kX' := by
              rw [Map.get_push]
              simp only [Option.some_get, ite_eq_right_iff]
              have := hkX.2.2; simp [SSADo.vars] at this; grind
          simp only [Option.Any, hget]
          have : Map.get vars kX' = (Map.get vars kX').get (by grind) := by grind
          grind
        · have := hkX.2.2
          simp only [SSADo.vars, Array.append_eq_append, Array.mem_append, mem_toArray, mem_cons,
                not_mem_nil, or_false, not_or] at this
          exact this.2
    have hrest' : (inferType (Array.push vars (var, (SSAExpr.inferType vars val).get hval)) (Map.keys mutVars) (Map.keys kmutVars)
        kbreak.isSome kcontinue.isSome k.isSome (some ktype') rest) = ktype' := by
        have : (inferType (Array.push vars (var, (SSAExpr.inferType vars val).get hval)) (Map.keys mutVars) (Map.keys kmutVars)
      kbreak.isSome kcontinue.isSome k.isSome ktype rest) = ktype' := by grind [inferType]
        grind [inferType_ktype_roundtrip]
    have hrest'' : (inferType (Array.push vars (var, (SSAExpr.inferType vars val).get hval)) (Map.keys mutVars) (Map.keys kmutVars)
        kbreak.isSome kcontinue.isSome k.isSome (some ktype') rest).isSome := by grind
    have ktype_eq : ktype' = (rest.inferType (vars.push (var, (val.inferType vars).get hval))
    (Map.keys mutVars) (Map.keys kmutVars) kbreak.isSome kcontinue.isSome k.isSome ktype') := by
        have := inferType_ktype vars mutVars.keys kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype' (.letE var val rest)
        grind
    cast (by grind [inferType]) (rest.interp (vars.push (var, (val.inferType vars).get hval)) mutVars kmutVars kbreak kcontinue k ktype' ⟨hvalidVars.1, ⟨by {
        apply Map.submap_push _ _ hvalidVars.2.1
        grind [Array.any_eq_true']
    }, hvalidVars.2.2⟩⟩ hrest'' (by grind) (by grind) (by grind) (cast (by simp only [Array.map_push]) (args.push (val.interp vars (by grind only) args))))
| letM var val rest, hprog, hkbreak, hkcontinue, hk, args =>
    have hval : (val.inferType vars).isSome := by grind [inferType]
    have hh : ¬ mutVars.keys.any (· == var) := by grind [inferType]
    let valT := (val.inferType vars).get hval
    let ktype' := ((SSADo.letM var val rest).inferType vars mutVars.keys kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype).get hprog
    have letM_validCont : ∀ (kX : Option Name),
    kX.All (validContinuationRef vars mutVars kmutVars (letM var val rest) ktype') →
    kX.All (validContinuationRef (vars.push (var, (val.inferType vars).get hval)) (mutVars.push (var, (val.inferType vars).get hval)) kmutVars rest ktype') := by
        intro kX hkX
        apply Option.All_intro
        intro kX' hkX'
        simp [hkX', Option.All] at hkX
        have : ¬var = kX' := by
            have : var ∈ (letM var val rest).vars := by simp [SSADo.vars]
            have := hkX.2.2
            grind
        refine ⟨?_, ?_, ?_⟩
        · simp only [Array.any_push, Bool.or_eq_true, decide_eq_true_eq, not_or]
          have := hkX.1
          grind
        · have := hkX.2.1
          simp only [Option.Any] at this
          have hget : Map.get (Array.push vars (var, (SSAExpr.inferType vars val).get hval)) kX' = vars.get kX' := by
            rw [Map.get_push]
            simp only [Option.some_get, ite_eq_right_iff]
            have := hkX.2.2; simp [SSADo.vars] at this; grind
          have : Map.get vars kX' = (Map.get vars kX').get (by grind) := by grind
          simp [Option.Any, Map.get_push]
          grind
        · have := hkX.2.2
          simp only [SSADo.vars, Array.append_eq_append, Array.mem_append, mem_toArray, mem_cons,
                not_mem_nil, or_false, not_or] at this
          grind
    have : rest.inferType (vars.push (var, valT)) (Map.keys (mutVars.push (var, valT))) kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype' = ktype' := by
        have : rest.inferType (vars.push (var, valT)) (Map.keys (mutVars.push (var, valT))) kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype = ktype' := by
            grind [inferType, Map.keys_push]
        grind [inferType_ktype_roundtrip]
    have : (rest.inferType (vars.push (var, valT)) (Map.keys (mutVars.push (var, valT))) kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype').isSome := by grind
    cast (by grind [inferType, Map.keys_push]) (rest.interp (vars.push (var, valT)) (mutVars.push (var, valT)) kmutVars kbreak kcontinue k ktype' (by {
        refine ⟨?_, ?_, ?_⟩
        sorry
        exact Map.push_submap_push _ _ hvalidVars.2.1 _ _
        sorry
    }) this (by grind) (by grind) (by grind) (cast (by simp [valT]) (args.push (val.interp vars (by grind only) args))))
| assign var val rest, hprog, hkbreak, hkcontinue, hk, args =>
    have hval : (val.inferType vars).isSome := by grind [inferType]
    let valT := (val.inferType vars).get hval
    have : var ∈ mutVars.keys ∧ valT = vars.get var := by grind [inferType]
    have : (rest.inferType (vars.push (var, valT)) mutVars.keys kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype).isSome := by grind [inferType]
    cast (by {
        sorry
    }) <| rest.interp (vars.push (var, valT)) mutVars kmutVars kbreak kcontinue k ktype sorry this sorry sorry sorry (cast (by simp [valT]) (args.push (val.interp vars (by grind only) args)))
| loop body rest, hprog, hkbreak, hkcontinue, hk, args =>
    let ktype' := ((loop body rest).inferType vars mutVars.keys kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype).get hprog
    let init : DVector (Array.toList (mutVars.map (·.2.type))) := mutVars.mapDVector _ (fun a => cast sorry <| args.get (Fin.cast (by simp) ((vars.findLastFinIdx? (·.1 == a.1)).get sorry)))
    let kbreak' := sorry
    let kcontinue' := sorry
    let k' := sorry
    let bodyFun : DVector (Array.toList (mutVars.map (·.2.type))) → (DVector (Array.toList (mutVars.map (·.2.type))) → Id ktype'.type) → Id ktype'.type :=
        fun mutArgs' kc =>
            -- todo:: push the modified kbreak and kcontinue and k functions to the vars and args
            have : (body.inferType vars mutVars.keys kmutVars.keys true true true ktype').isSome := sorry
            cast (by {
                simp [Id]
                apply congrArg
                sorry
                -- inferType with non none ktype isSome only if it matches the input ktype
            }) (body.interp vars mutVars kmutVars (some kbreak') (some kcontinue') (some k') ktype' hvalidVars this sorry sorry sorry (vars.mapDVector _ (fun x => if x.1 ∈ mutVars.keys then cast (by sorry) (mutArgs'.get (Fin.cast (by simp) ((mutVars.findLastFinIdx? (·.1 == x.1)).get sorry))) else cast (by sorry) <| args.get (Fin.cast (by simp) ((vars.findLastFinIdx? (·.1 == x.1)).get sorry)))))
    SSA.loop init bodyFun
| .break, hprog, hkbreak, hkcontinue, hk, args =>
    match kbreak with
    | some kbreak' =>
        let ktype' := (SSADo.continue.inferType vars mutVars.keys kmutVars.keys kbreak.isSome (some kbreak').isSome k.isSome ktype).get hprog
        let kbreakFun : (mkMutTuple kmutVars).2.type → ktype'.type := cast sorry <| (SSAExpr.var kbreak').interp vars
        kbreakFun (cast sorry <| (mkMutTuple kmutVars).1.interp vars)
    | none => by grind [inferType]
| .continue, hprog, hkbreak, hkcontinue, hk, args =>
    match kcontinue with
    | some kcontinue' =>
        let ktype' := (SSADo.continue.inferType vars mutVars.keys kmutVars.keys kbreak.isSome (some kcontinue').isSome k.isSome ktype).get hprog
        let kcontinueFun : (mkMutTuple kmutVars).2.type → ktype'.type := cast sorry <| (SSAExpr.var kcontinue').interp vars
        kcontinueFun (cast sorry <| (mkMutTuple kmutVars).1.interp vars)
    | none => by grind [inferType]
| .return out, hprog, hkbreak, hkcontine, hk, args =>
    have : (out.inferType vars).isSome := by grind [inferType]
    cast (by grind [inferType]) (out.interp vars this args)
| ifthenelse c t e rest, hprog, hkbreak, hkcontinue, hk, args =>
    let ktype' := ((ifthenelse c t e rest).inferType vars mutVars.keys kmutVars.keys kbreak.isSome kcontinue.isSome k.isSome ktype).get hprog
    have : (c.inferType vars).isSome := by grind [inferType]
    let cval : Int := cast sorry (c.interp vars this)
    have ht : (t.inferType vars mutVars.keys kmutVars.keys true true true ktype').isSome := sorry
    have he : (e.inferType vars mutVars.keys kmutVars.keys true true true ktype').isSome := sorry
    let kbreak' := sorry
    let kcontinue' := sorry
    let k' := sorry
    -- todo:: push the modified kbreak and kcontinue and k functions to the vars and args
    if cval != 0 then
        cast sorry <| t.interp vars mutVars kmutVars (some kbreak') (some kcontinue') (some k') ktype' hvalidVars ht sorry sorry sorry args
    else
        cast sorry <| e.interp vars mutVars kmutVars (some kbreak') (some kcontinue') (some k') ktype' hvalidVars he sorry sorry sorry args

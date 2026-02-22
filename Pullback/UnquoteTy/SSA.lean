import Lean
import Mathlib.Logic.ExistsUnique
import Mathlib.Data.Fin.Tuple.Basic

open Lean

inductive SSABaseType where
| float : SSABaseType
| int : SSABaseType
| unit : SSABaseType
deriving DecidableEq

inductive SSAType where
| ofBase : SSABaseType → SSAType
| fun : SSAType → SSAType → SSAType
| prod : SSAType → SSAType → SSAType
deriving DecidableEq

inductive SSAConst where
/- use Rat instead of Float for underlying value since Float is opaque -/
| ofFloat : Rat → SSAConst
| ofInt : Int → SSAConst
| ofUnit : Unit → SSAConst
| loop (ty out : SSAType) : SSAConst
| prod (α β : SSAType) : SSAConst
| prod₁ (α β : SSAType) : SSAConst
| prod₂ (α β : SSAType) : SSAConst
| ifthenelse (ty : SSAType) : SSAConst
/-prop stuff-/
| eq (ty : SSABaseType) : SSAConst
| and : SSAConst
| or: SSAConst
deriving DecidableEq

inductive SSAExpr where
| const : SSAConst → SSAExpr
| letE (var : Name) (val : SSAExpr) (body : SSAExpr) : SSAExpr
| var (name : Name) : SSAExpr
| app (f : SSAExpr) (arg : SSAExpr)
| lam (varName : Name) (varType : SSAType) (body : SSAExpr) : SSAExpr
deriving Inhabited, DecidableEq

abbrev VarMap := Array (Name × SSAType)

def Fin.last' {n : Nat} [NeZero n] : Fin n :=
    match h :  n with
    | (k + 1) => Fin.last k
    | 0 => by {
        apply False.elim
        expose_names
        rw [h] at inst
        simp at inst
    }

def Fin.val_last'_eq {n : Nat} [NeZero n] : (Fin.last' (n := n)).val = n - 1 := by
    cases n with
    | succ k => simp [last']
    | zero => grind only

def Fin.le_last' {n : Nat} [NeZero n] : ∀ i : Fin n, i ≤ (Fin.last' (n := n)) := by
    cases n with
    | succ k =>
        intro i
        have : i.val ≤ (last' : Fin (k + 1)).val := by
            simp only [val_last'_eq, Nat.add_one_sub_one]
            have := i.isLt
            grind only
        exact this
    | zero => grind only

def Array.findLast? {α : Type u} (p : α → Bool) (as : Array α) : Option α := as.reverse.find? p

def Array.findLastFinIdx? {α : Type u} (p : α → Bool) (as : Array α) : Option (Fin as.size) := Option.map (fun res => have : NeZero as.size := ⟨by {
    have := res.isLt
    grind
}⟩;
Fin.last' - Fin.cast (size_reverse) res) (as.reverse.findFinIdx? p)

def Array.get (map : VarMap) (key : Name) : Option SSAType :=
    map.findLast? (·.1 = key) |>.map (·.2)

#check Array.find?_eq_some_iff_getElem

theorem VarMap.get_eq_some_imp_any (vars : VarMap) (key : Name) (a : SSAType) : vars.get key = some a → vars.any (·.1 = key) := by
    simp [Array.get, Array.findLast?, Array.find?_eq_some_iff_getElem]
    grind

theorem VarMap.get_isSome_iff_any (vars : VarMap) (key : Name) : (vars.get key).isSome ↔ vars.any (·.1 = key) := sorry

theorem VarMap.get_mem (vars : VarMap) (name : Name) (type : SSAType) : (name, type) ∈ vars → ∃ a, vars.get name = some a := by
    intro h
    have := VarMap.get_isSome_iff_any
    simp only [Option.isSome_iff_exists] at this
    simp only [this, Array.any_eq_true, decide_eq_true_eq]
    simp only [Array.mem_iff_getElem] at h
    grind


theorem VarMap.mem_get (vars: VarMap) (name : Name) (type : SSAType) : vars.get name = some type → (name, type) ∈ vars := sorry

theorem VarMap.get_push (vars : VarMap) (last : Name × SSAType) (key : Name) : ((vars.push last)).get key = if last.1 = key then some last.2 else vars.get key := sorry


theorem VarMap.get_eq_none_iff_not_any (vars : VarMap) (key : Name) : vars.get key = none ↔ ¬ vars.any (·.1 = key) := sorry

def SSAConst.inferType : SSAConst → SSAType
| ofFloat _ => .ofBase .float
| ofInt _ => .ofBase .int
| ofUnit _ => .ofBase .unit
| loop ty out => .fun (ty) <|
        .fun (.fun (ty) (.fun (.fun ty out) out))
        out

    -- the step function takes in a kcontinue continuation and returns ty (loop in CPS form)
| prod α β => .fun α (.fun β (.prod α β))
| prod₁ α β => .fun (.prod α β) α
| prod₂ α β => .fun (.prod α β) β
| ifthenelse ty => .fun (.ofBase .int) (.fun ty (.fun ty ty))
| eq ty => .fun (.ofBase ty) (.fun (.ofBase ty) (.ofBase .int))
| and => .fun (.ofBase .int) (.fun (.ofBase .int) (.ofBase .int))
| or => .fun (.ofBase .int) (.fun (.ofBase .int) (.ofBase .int))

/-
    none is returned the input expr doesn't typecheck
-/
def SSAExpr.inferType (vars : VarMap) : SSAExpr → Option SSAType
| const base => base.inferType
| letE name val body =>
    (val.inferType vars).bind <|
        fun valType => body.inferType (vars.push ⟨name, valType⟩)
| var name => vars.get name
| app f arg =>
    f.inferType vars |>.bind
    fun fType =>
    arg.inferType vars |>.bind
    fun argType =>
        match fType, argType with
        | SSAType.fun α β, x  => if α = x then β else none
        | _, _ => none
| lam name varType body => body.inferType (vars.push (name, varType)) |>.bind (fun bodyType => SSAType.fun varType bodyType)

def SSABaseType.type : SSABaseType → Type
| float => Rat
| int => Int
| unit => Unit

def SSAType.type : SSAType → Type
| .ofBase baseTy => baseTy.type
| .fun α β => α.type → β.type
| prod α β => α.type × β.type

#check Nat × Int × Int
def DVector : List Type → Type
| [] => Unit
| α::l => α × DVector l

def DVector.cons {L: List Type} {α : Type} : α → DVector L → DVector (α::L)
| a, l => (a, l)

def DVector.push : {L: Array Type} → {α : Type} → DVector L.toList → α → DVector (L.push α).toList
| ⟨[]⟩, α, _, a => (a, ())
| ⟨l::ls⟩, α, (x, xs), a => DVector.cons x <| DVector.push xs a

/-
    recursive structure follows List.get exactly
-/
def DVector.get : {L : List Type} → (v : DVector L) → (i : Fin L.length) → L.get i
| .cons _ _, (a, _), ⟨0, _⟩ => a
| .cons _ _, (_, as), ⟨Nat.succ i, h⟩ => DVector.get as ⟨i, Nat.le_of_succ_le_succ h⟩

theorem Array.find?_eq_getElem_findFinIdx? {α : Type u} (xs : Array α) (p : α → Bool) :
      xs.find? p = (xs.findFinIdx? p).map (xs[·]) := by
    rcases xs with ⟨xs⟩; ext
    simp [List.findFinIdx?_eq_pmap_findIdx?, List.findIdx?_eq_fst_find?_zipIdx,
        List.find?_eq_some_iff_getElem]
    constructor
    · rintro ⟨_, _, _, rfl, _⟩; grind
    · grind

#check ForIn
def SSA.loop {α β : Type u} {m : Type u → Type v} [Monad m] [Inhabited α] (init : α) (step : α → (α → m β) → m β) : m β := sorry

private def SSABaseType.decEq : (ty : SSABaseType) → DecidableEq ty.type
| float => by
    simp [SSABaseType.type]
    infer_instance
| int => by
    simp [SSABaseType.type]
    infer_instance
| unit => by
    simp [SSABaseType.type]
    infer_instance

instance (ty : SSABaseType) : DecidableEq (SSAType.ofBase ty).type := by
    simp [SSAType.type]
    exact SSABaseType.decEq ty

private def SSABaseType.inhabit : (ty : SSABaseType) → ty.type
| int => (0 : Int)
| float => (0 : Rat)
| unit => ()

instance {ty : SSABaseType} : Inhabited (SSAType.ofBase ty).type := by
    simp [SSAType.type]
    exact ⟨SSABaseType.inhabit ty⟩

instance {ty : SSAType} : Inhabited ty.type := sorry

def SSAConst.interp : (e : SSAConst) → (e.inferType).type
| ofFloat f => f
| ofInt i => i
| ofUnit () => ()
| ifthenelse ty => fun c t e => if (cast (by simp [SSAType.type, SSABaseType.type]) c : Int) != 0 then t else e
| loop ty out => SSA.loop (m := Id)
| prod α β => (@Prod.mk α.type β.type)
| prod₁ α β => fun ab => ab.1
| prod₂ α β => fun ab => ab.2
| eq ty => fun t₁ t₂ => if t₁ = t₂ then (1:Int) else (0:Int)
| or => fun x y => if x != (0: Int) || y != (0:Int) then (1:Int) else (0:Int)
| and => fun x y => if x != (0 : Int) && y != (0 : Int) then (1 : Int) else (0 : Int)

def SSAExpr.interp (vars : VarMap) : (e : SSAExpr) → (he : e.inferType vars |>.isSome) → DVector (Array.toList (vars.map (·.2.type))) → (Option.get (e.inferType vars) he).type
| .const base, he, _ => base.interp
| .letE name val body, he, ctx =>
    match hh : val.inferType vars with
    | some valType => cast (by simp [inferType, hh]) <| body.interp (vars.push ⟨name, valType⟩) (by {
        simp [inferType, Option.isSome_bind] at he
        grind only [= Option.any_some]
    }) (cast (by {
        simp [Array.map_push, hh]
    }) <| ctx.push (val.interp vars (by simp [hh]) ctx))
    | none => by {
        simp [inferType, Option.isSome_bind] at he
        grind only [= Option.any_none]
    }
| var name, he, ctx =>
    match h : (vars.findLastFinIdx? (·.1 == name)) with
    | some x => cast (by {
        simp [inferType, Array.get] at he
        calc
            _ = ((Array.findLast? (fun x => decide (x.fst = name)) vars).get he).2.type := by {
                have : x = (some x).get rfl := rfl
                rw [this]
                simp [← h]
                congr
                simp only [Array.findLast?, Array.findLastFinIdx?]
                simp [Array.find?_eq_getElem_findFinIdx?]
                congr
                rw [Fin.sub_val_of_le]
                simp [Fin.val_last'_eq]
                grind
                have : NeZero (Array.size vars) := ⟨by {
                    have := x.isLt
                    grind
                }⟩
                exact Fin.le_last' _
            }
            _ = _ := by {
                simp [Array.findLast?, inferType, Array.get]
            }

    }) (ctx.get (Fin.cast (by {
        simp only [Array.toList_map, List.length_map, Array.length_toList]
    }) x))
    | none => by {
        simp only [inferType, Array.get, Array.findLast?, Option.isSome_map] at he
        simp only [Array.findLastFinIdx?, Option.map_eq_none_iff] at h
        grind only [= Option.isSome_none, = Array.find?_eq_none, = Array.findFinIdx?_eq_none_iff,
          = Array.size_reverse]
    }
| app f arg, he, ctx =>
    match hf : f.inferType vars with
    | some (.fun α β) =>
        cast (by {
            grind [inferType]
        }) <|
        (cast (β := α.type → β.type) (by {
            simp [inferType, Option.isSome_bind, Option.any_eq_true_iff_get] at he
            have : inferType vars f = some (.fun α β) := by grind
            simp [this, SSAType.type]
        }) <| f.interp vars (by grind [inferType]) ctx) (cast (β := α.type) (by {
            simp [inferType, Option.isSome_bind, Option.any_eq_true_iff_get] at he
            grind
        }) <| arg.interp vars (by {
            simp only [inferType, Option.isSome_bind, Option.any_eq_true_iff_get] at he
            grind only
        }) ctx)
    | some (.prod α β) => by {
        simp [inferType, Option.isSome_bind, Option.any_eq_true_iff_get] at he
        apply False.elim
        grind
    }
    | some (.ofBase bTy) => by {
        simp [inferType, Option.isSome_bind, Option.any_eq_true_iff_get] at he
        apply False.elim
        grind
    }
    | none => by {
        simp [inferType, hf] at he
    }
| lam name valType body, he, ctx => cast (by {
    simp [inferType, Option.isSome_bind] at he
    simp [inferType, SSAType.type]
}) <|
    fun val : valType.type => (body.interp (vars.push ⟨name, valType⟩) (by {
        simp [inferType, Option.isSome_bind] at he
        grind
    }) (cast (by simp) <| ctx.push val))


def SSAExpr.interp! (vars : VarMap) : (e : SSAExpr) → DVector (Array.toList (vars.map (·.2.type))) → (match e.inferType vars with
| some ty => ty.type
| none => Unit) := fun e ctx =>
    match he : e.inferType vars with
    | some ty => cast (by simp only [he, Option.get_some]) (e.interp vars (by simp [he]) ctx)
    | none => ()

def mkMutTuple : VarMap → SSAExpr × SSAType
| ⟨[]⟩ => (.const (SSAConst.ofUnit ()), .ofBase .unit)
| ⟨[(name, type)]⟩ => (.var name, type)
| ⟨(name, type)::b::l⟩ =>
    let (rightExpr, rightType) := mkMutTuple ⟨(b::l)⟩;
    (.app (.app (.const (.prod type rightType)) (.var name)) rightExpr, .prod type rightType)
termination_by as => as.size

theorem SSAExpr.inferType_mkMutTuple (vars : VarMap) : (mutVars : VarMap) → (h' : ∀ x ∈ mutVars, vars.get x.1 = x.2) → (mkMutTuple mutVars).fst.inferType vars = (mkMutTuple mutVars).snd
| ⟨[]⟩ => by simp [inferType, mkMutTuple, SSAConst.inferType]
| ⟨[(name, type)]⟩ => by
    simp only [List.mem_toArray,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq, mkMutTuple, inferType, imp_self]
| ⟨(name, type)::b::l⟩ => by
    simp
    intro h1 h2 h3
    have := inferType_mkMutTuple vars ⟨b::l⟩ (by grind)
    simp [inferType, mkMutTuple, this, h1, SSAConst.inferType]
termination_by as => as.size

def destructMutTuple (tupleName : Name) : VarMap → SSAExpr → SSAExpr
| ⟨[]⟩, body => body
| ⟨[(name, _)]⟩, body => .letE name (.var tupleName) body
| ⟨(name, type)::b::l⟩, body =>
    let (_, rightTupleType) := mkMutTuple ⟨b::l⟩
    .letE name (.app (.const (.prod₁ type rightTupleType)) (.var tupleName)) (.letE tupleName (.app (.const (.prod₂ type rightTupleType)) (.var tupleName)) (destructMutTuple tupleName ⟨b::l⟩ body))
termination_by as _ => as.size

#check Lean.LocalContext
#check Lean.LocalContext.getUnusedName
#check Lean.LocalContext.getUnusedName
#check Name.appendIndexAfter

/- todo :: should be able to prove termination by showing that each name will have a maximal number of prefix occurances in the mutvars varmap -/
private partial def freshNameAux (vars : Array Name) (baseName : Name) (idx : Nat) : Name :=
    if vars.any (· == baseName.appendIndexAfter idx) then
        freshNameAux vars baseName (idx + 1)
    else
        baseName.appendIndexAfter idx
/-
    for fixed mutVars, if baseName1 and baseName2 don't share a prefix then freshName will give different fresh names.
-/
def freshName (vars : Array Name) (baseName : Name) : Name :=
    if vars.any (· == baseName) then
        freshNameAux vars baseName 1
    else
        baseName

theorem freshName_hygenic (vars : Array Name) (baseName : Name) : ∀ var ∈ vars, var ≠ freshName vars baseName := sorry

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

-- returns domain of function type if the type is a function type
def SSAType.funDom? : SSAType → Option SSAType
| .fun α _ => α
| _ => none

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
    let restMutVars : Array Name := rest.mutVars
    let nS : Name := freshName (Array.append (mutVars.map (·.1)) restMutVars) `s
    -- todo :: pass expanded mutvars into toSSAExpr
    let continue' ← (SSAExpr.lam nS mutTupleType <| destructMutTuple nS mutVars (← rest.toSSAExpr (vars.push (nS, mutTupleType)) mutVars kMutVars kbreak kcontinue))
    if (← cond.inferType vars) != SSAType.ofBase .int then
        none
    let texpr ← t.toSSAExpr vars mutVars mutVars kbreak nKContinue
    let tExprType ← texpr.inferType vars
    let eExpr ← e.toSSAExpr vars mutVars mutVars kbreak nKContinue
    let eExprType ← eExpr.inferType vars
    if tExprType != eExprType then
        none
    SSAExpr.letE nKContinue continue' <|
    SSAExpr.app (SSAExpr.app (SSAExpr.app (.const (.ifthenelse tExprType)) cond) texpr) (eExpr)

#check List.Nodup
#check List.instHasSubset

theorem SSAType.funDom?_eq_some_iff (f : SSAType) (dom : SSAType): f.funDom? = some dom → ∃ β, f = .fun dom β := by
    intro h
    match f with
    | .fun α β =>
        grind [funDom?]
    | ofBase _ => simp [funDom?] at h
    | prod α β => simp [funDom?] at h

-- returns codomain of function type if the type is a function type
def SSAType.funCodom? : SSAType → Option SSAType
| .fun _ β => β
| _ => none

theorem SSAExpr.welltyped_app_iff (vars : VarMap) (f x : SSAExpr) : ((f.app x).inferType vars).isSome ↔ (do pure ((← f.inferType vars).funDom? = (← x.inferType vars))) = some True := by
    simp only [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff, SSAType.funDom?,
      Option.pure_def, Option.bind_eq_bind, Option.some.injEq, eq_iff_iff, iff_true]
    grind only

#check Option.getD

/- two VarMaps are equivalent if the non shadowed variables agree on types at all names, and the set of unshadowed names is the same -/
def VarMap.equiv (vars₁ vars₂ : VarMap) : Prop :=
    {name | vars₁.any (·.1 = name)} = {name | vars₂.any (·.1 = name)} ∧ ∀ name, vars₁.any (·.1 = name) → vars₁.get name = vars₂.get name

def VarMap.equiv_push (vars₁ vars₂ : VarMap) (hvars : vars₁.equiv vars₂) (varname : Name) (vartype : SSAType) : (cast (β := VarMap) rfl (vars₁.push (varname, vartype))).equiv (vars₂.push (varname, vartype)) := by
    simp only [cast_eq]
    simp only [equiv, Array.any_eq_true, decide_eq_true_eq, forall_exists_index, Array.size_push, Array.any_push', Bool.or_eq_true] at ⊢ hvars
    apply And.intro
    · ext name
      rw [Set.ext_iff] at hvars
      grind only [usr Set.mem_setOf_eq]
    · intro name H
      have := VarMap.get_push
      simp only [cast_eq, Prod.forall] at this
      rw [this]
      cases em (varname = name) with
      | inl hl =>
        simp only [hl, ↓reduceIte]
        cases H with
        | inl hll => grind
        | inr hlr =>
            grind only
      | inr hr =>
        simp [hr]
        grind only

theorem SSAExpr.inferType_eq_of_vars_equiv (vars₁ vars₂ : VarMap) (hvars : vars₁.equiv vars₂) : (expr : SSAExpr) → expr.inferType vars₁ = expr.inferType vars₂
| const c => by simp only [inferType]
| letE varname val body => by
    simp only [inferType]
    rw [inferType_eq_of_vars_equiv vars₁ vars₂ hvars val]
    congr
    ext valType a
    have := inferType_eq_of_vars_equiv (vars₁.push (varname, valType)) (vars₂.push (varname, valType)) (VarMap.equiv_push vars₁ vars₂ hvars varname valType) body
    grind only
| lam varname type body => by
    simp only [inferType]
    have := inferType_eq_of_vars_equiv (vars₁.push (varname, type)) (vars₂.push (varname, type)) (VarMap.equiv_push vars₁ vars₂ hvars varname type) body
    grind only
| app f x => by
    simp only [inferType]
    rw [inferType_eq_of_vars_equiv vars₁ vars₂ hvars f, inferType_eq_of_vars_equiv vars₁ vars₂ hvars x]
| var name => by
    simp only [inferType]
    simp only [VarMap.equiv] at hvars
    match h : vars₁.get name with
    | some type =>
        have h' := h
        apply VarMap.get_eq_some_imp_any at h
        have := hvars.2 name (by grind)
        grind
    | none =>
        have h' := h
        rw [VarMap.get_eq_none_iff_not_any] at h
        have := hvars.1
        rw [Set.ext_iff] at this
        specialize this name
        simp only [Array.any_eq_true, decide_eq_true_eq, Set.mem_setOf_eq] at this
        grind only [Array.any_eq_true, VarMap.get_eq_none_iff_not_any]

def VarMap.submap (vars₁ vars₂ : VarMap) : Prop :=
    {name | vars₁.any (·.1 = name)} ⊆ {name | vars₂.any (·.1 = name)} ∧ ∀ name, vars₁.any (·.1 = name) → vars₁.get name = vars₂.get name

def VarMap.submap_push (vars₁ vars₂ : VarMap) (hvars : vars₁.submap vars₂) (varname : Name) (vartype : SSAType) : (cast (β := VarMap) rfl (vars₁.push (varname, vartype))).submap (vars₂.push (varname, vartype)) := by
    simp only [cast_eq]
    simp only [submap, Array.any_eq_true, decide_eq_true_eq, forall_exists_index, Array.size_push, Array.any_push', Bool.or_eq_true] at ⊢ hvars
    apply And.intro
    · intro name
      simp only [Set.mem_setOf_eq]
      have := hvars.1
      intro HH
      cases HH with
      | inl hl =>
        specialize this hl
        grind
      | inr hr =>
        grind
    · intro name hName
      have := VarMap.get_push
      simp at this
      simp [this]
      cases em (varname = name) with
      | inl hl =>
        simp only [hl, ↓reduceIte]
      | inr hr =>
        simp only [hr, or_false, ↓reduceIte] at ⊢ hName
        grind

theorem SSAExpr.inferType_eq_of_vars_submap (vars₁ vars₂ : VarMap) (hvars : vars₁.submap vars₂) : (expr : SSAExpr) → (expr.inferType vars₁).isSome → expr.inferType vars₁ = expr.inferType vars₂
| const c => by simp [inferType]
| letE varname val body => by
    simp only [inferType]
    intro H
    simp [Option.isSome_iff_exists, Option.bind_eq_some_iff] at H
    rw [← inferType_eq_of_vars_submap vars₁ vars₂ hvars val]
    obtain ⟨bodyT, valT, hvalT, hbodyT⟩ := H
    simp [hvalT, hbodyT]
    have := inferType_eq_of_vars_submap (vars₁.push (varname, valT)) (vars₂.push (varname, valT)) (VarMap.submap_push _ _ hvars _ _) body (by grind)
    grind
    grind
| lam varname type body => by
    simp only [inferType]
    intro H
    simp [Option.isSome_iff_exists, Option.bind_eq_some_iff] at H
    obtain ⟨bodyT, hbodyT⟩ := H
    simp [hbodyT]
    have := inferType_eq_of_vars_submap (vars₁.push (varname, type)) (vars₂.push (varname, type)) (VarMap.submap_push _ _ hvars _ _) body (by grind)
    grind
| app f x => by
    simp only [inferType]
    intro H
    simp [Option.isSome_iff_exists, Option.bind_eq_some_iff] at H
    obtain ⟨finaltype, ftype, hftype, xtype, hxtype, hfinaltype⟩ := H
    have cruxf := inferType_eq_of_vars_submap vars₁ vars₂ hvars f (by grind)
    have cruxx := inferType_eq_of_vars_submap vars₁ vars₂ hvars x (by grind)
    simp [hftype, hxtype, ← cruxf, ← cruxx]
| var name => by
    simp only [inferType]
    intro H
    simp only [Option.isSome_iff_exists] at H
    obtain ⟨type, htype⟩ := H
    simp only [VarMap.submap, Array.any_eq_true, decide_eq_true_eq, Set.setOf_subset_setOf,
      forall_exists_index] at hvars
    have := VarMap.get_eq_some_imp_any _ _  _ htype
    simp only [Array.any_eq_true, decide_eq_true_eq] at this
    obtain ⟨i, hi, Hi⟩ := this
    grind only

theorem SSAExpr.inferType_push_eq_of_hygenic (vars : VarMap) (newvar : Name) (newVarType : SSAType) (hHygenic : ¬ vars.any (·.1 = newvar)) : (expr : SSAExpr) → (expr.inferType vars).isSome → expr.inferType (vars.push (newvar, newVarType)) = expr.inferType vars
| const c => by simp [inferType]
| letE varName val body => by
    intro H
    simp only [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff] at H
    obtain ⟨bodyT, valT, hvalT, hbodyT⟩ := H
    have crux1 := inferType_push_eq_of_hygenic vars newvar newVarType hHygenic val (Option.isSome_of_mem hvalT)
    simp [inferType, hvalT, crux1]
    symm
    apply SSAExpr.inferType_eq_of_vars_submap
    simp [VarMap.submap]
    apply And.intro
    grind
    intro name hName
    have := VarMap.get_push
    simp at this
    simp [this]
    cases em (varName = name) with
    | inl hl =>
        simp [hl]
    | inr hr =>
        simp [hr]
        simp [Array.get, Array.findLast?, Array.find?_eq_some_iff_getElem]
        grind
    grind
| lam varname type body => by
    intro H
    simp only [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff, Option.some.injEq,
      ↓existsAndEq, and_true] at H
    obtain ⟨bodyT, hbodyT⟩ := H
    simp only [inferType, hbodyT, Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq,
      SSAType.fun.injEq, true_and, exists_eq_right]
    symm
    rw [← hbodyT]
    apply SSAExpr.inferType_eq_of_vars_submap
    simp [VarMap.submap]
    apply And.intro
    grind
    intro name hName
    have := VarMap.get_push
    simp at this
    simp [this]
    cases em (varname = name) with
    | inl hl =>
        simp [hl]
    | inr hr =>
        simp [hr]
        simp [Array.get, Array.findLast?, Array.find?_eq_some_iff_getElem]
        grind
    grind
| app f x => by
    intro H
    simp only [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff] at H
    obtain ⟨finaltype, ftype, hftype, xtype, hxtype, Hfinal⟩ := H
    simp only [inferType, hftype, hxtype, Option.bind_some]
    have cruxf := inferType_push_eq_of_hygenic vars newvar newVarType hHygenic f (Option.isSome_of_mem hftype)
    have cruxx := inferType_push_eq_of_hygenic vars newvar newVarType hHygenic x (Option.isSome_of_mem hxtype)
    simp only [cruxf, hftype, cruxx, hxtype, Option.bind_some]
| var name => by
    intro H
    simp only [inferType, Option.isSome_iff_exists] at H
    have := VarMap.get_push
    simp at this
    simp [inferType, this]
    obtain ⟨t, ht⟩ := H
    have := VarMap.get_eq_some_imp_any _ _ _ ht
    simp only [Array.any_eq_true, decide_eq_true_eq] at this
    simp at hHygenic
    grind

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

-- theorem Array.isPrefixOf_toList_isPrefixOf {α} [BEq α] (x y : Array α) : x.isPrefixOf y → x.toList.isPrefixOf y.toList := by
--     apply Array.isPrefixOf_toList

theorem List.subset_of_isPrefixOf {α} [BEq α] [LawfulBEq α] (x y : List α) : x.isPrefixOf y → x ⊆ y := by
    rw [List.isPrefixOf_iff_prefix]
    exact fun a => IsPrefix.subset a

#check VarMap.get_mem
#check SSAType.funDom?_eq_some_iff
theorem SSADo.toSSAExpr_wellTyped (vars : VarMap) (mutVars : VarMap) (continueMutVars : VarMap) (hcontMutVars : continueMutVars.isPrefixOf mutVars) (kbreak kcontinue : Option Name) (hMut₁ : (mutVars.toList.map (·.1)).Nodup) (hMut₂ : ∀ x ∈ mutVars, vars.get x.1 = some x.2) : (prog : SSADo) → (hkBreak : validContinutationRef vars mutVars continueMutVars kbreak prog) → (hkContinue : validContinutationRef vars mutVars continueMutVars kcontinue prog) → (hp : (prog.toSSAExpr vars mutVars continueMutVars kbreak kcontinue).isSome) → (((prog.toSSAExpr vars mutVars continueMutVars kbreak kcontinue).get hp).inferType vars).isSome
| .expr e, hkBreak, hkContinue => by
    intro hp
    simp [toSSAExpr] at hp
    simp [Option.isSome_iff_exists, Option.bind_eq_some_iff] at hp
    obtain ⟨res, et, het, hres⟩ := hp
    match hkc : kcontinue with
    | some kc =>
        simp [validContinutationRef, validContinutation, Option.bind_eq_some_iff] at hkContinue
        obtain ⟨_, ⟨fkc, hfkc⟩, _⟩ := hkContinue
        have crux : (SSAExpr.inferType vars (mkMutTuple continueMutVars).fst) = (mkMutTuple continueMutVars).snd :=
          SSAExpr.inferType_mkMutTuple vars continueMutVars (by {
            intro x hx
            have : continueMutVars.toList.isPrefixOf (mutVars.toList) := by grind only [=
                Array.isPrefixOf_toList]
            have : continueMutVars.toList ⊆ mutVars.toList :=
              List.subset_of_isPrefixOf continueMutVars.toList mutVars.toList this
            have : x ∈ mutVars :=
                Array.mem_def.mpr (this hx.val)
            grind
          })
        have := hfkc.2
        obtain ⟨β, hb⟩ : ∃ β, fkc = .fun (mkMutTuple continueMutVars).2 β :=
          SSAType.funDom?_eq_some_iff fkc (mkMutTuple continueMutVars).2 this
        simp [toSSAExpr, SSAExpr.inferType, crux, hfkc.1, hb]
    | none =>
        simp [toSSAExpr, het]
| .letE var val rest, hkBreak, hkContinue => by
    intro hp
    simp only [toSSAExpr, Array.any_eq_true', decide_eq_true_eq, Option.bind_eq_bind,
        Option.isSome_iff_exists, Option.ite_none_left_eq_some, not_exists,
        Option.bind_eq_some_iff, Option.some.injEq, exists_and_left, ↓existsAndEq, and_true] at hp
    obtain ⟨h1, valT, hvalT, restExpr, hrestExpr⟩ := hp
    have : ∀ k, validContinutationRef vars mutVars continueMutVars k (letE var val rest) → validContinutationRef (vars.push (var, valT)) mutVars continueMutVars k rest := by
        intro k hk
        match k with
        | some k =>
            use hk.1
            simp [VarMap.get_push]
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
    have := toSSAExpr_wellTyped (vars.push (var, valT)) mutVars continueMutVars (by grind) kbreak kcontinue hMut₁ (by grind [VarMap.get_push]) rest (this kbreak hkBreak) (this kcontinue hkContinue) (by grind)
    grind [toSSAExpr, SSAExpr.inferType, Option.isSome_iff_exists]
| .letM var val rest, hkBreak, hkContinue => by
    intro hp
    simp only [toSSAExpr, Array.any_eq_true', decide_eq_true_eq, Option.bind_eq_bind,
      Option.bind_none, Option.pure_def, Option.bind_some, Option.isSome_iff_exists,
      Option.ite_none_left_eq_some, not_exists, Option.bind_eq_some_iff, Option.some.injEq,
      exists_and_left, ↓existsAndEq, and_true] at hp
    obtain ⟨h1, varT, hvarT, a2, ha2⟩ := hp
    have : ∀ k, validContinutationRef vars mutVars continueMutVars k (letM var val rest) → validContinutationRef (vars.push (var, varT)) (mutVars.push (var, varT)) continueMutVars k rest := by
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
    have := toSSAExpr_wellTyped (vars.push (var, varT)) (mutVars.push (var, varT)) continueMutVars (by {
        simp only [← Array.isPrefixOf_toList, List.isPrefixOf_iff_prefix,
          Array.toList_push] at ⊢ hcontMutVars
        grind only [usr List.prefix_append_of_prefix]
    }) kbreak kcontinue (by grind) (by grind [VarMap.get_push]) rest (this kbreak hkBreak) (this kcontinue hkContinue) (by simp [ha2])
    grind [toSSAExpr, SSAExpr.inferType, Option.isSome_iff_exists]
| .assign var val rest, hkBreak, hkContinue => by
    intro hp
    simp only [toSSAExpr, bne_iff_ne, ne_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_none,
      Option.bind_some, ite_not, Option.isSome_iff_exists, Option.bind_eq_some_iff,
      Option.ite_none_right_eq_some, Option.some.injEq, ↓existsAndEq, true_and, and_true,
      exists_and_left] at hp
    obtain ⟨varT, hvarT, HT, restExpr, hRestExpr⟩ := hp
    have : ∀ k, validContinutationRef vars mutVars continueMutVars k (assign var val rest) → validContinutationRef (vars.push (var, varT)) mutVars continueMutVars k rest := by
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
    have := toSSAExpr_wellTyped (vars.push ⟨var, varT⟩) mutVars continueMutVars (by {
        simp only [← Array.isPrefixOf_toList, List.isPrefixOf_iff_prefix] at ⊢ hcontMutVars
        grind only [usr List.prefix_append_of_prefix]
    }) kbreak kcontinue (by grind) (by {
        simp [VarMap.get_push]
        have : Array.get mutVars var = Array.get vars var := by
            have := VarMap.mem_get mutVars var varT hvarT
            specialize hMut₂ _ this
            grind
        have : Array.get vars var = varT := by grind
        grind
    }) rest (this kbreak hkBreak) (this kcontinue hkContinue) (by simp [hRestExpr])
    simp only [toSSAExpr, hvarT, HT, bne_iff_ne, ne_eq, Option.pure_def, Option.bind_eq_bind,
      Option.bind_none, Option.bind_some, ite_not, ↓reduceIte, Option.get_bind, Option.get_some,
      SSAExpr.inferType, this]
| .break, hkBreak, hkContinue => by
    intro hp
    match kbreak with
    | some kbreak' =>
        simp [toSSAExpr, Option.isSome_iff_exists, Option.bind_eq_some_iff] at hp
        obtain ⟨a, ha, H⟩ := hp
        simp only [toSSAExpr, Option.bind_eq_bind, Option.bind_some]
        have : (a.funDom?) = (mkMutTuple continueMutVars).2 := by
            grind
        apply SSAType.funDom?_eq_some_iff at this
        simp [ha, SSAExpr.inferType]
        rw [SSAExpr.inferType_mkMutTuple]
        grind
        · rw [← Array.isPrefixOf_toList] at hcontMutVars
          have := List.subset_of_isPrefixOf _ _ hcontMutVars
          intro x hx
          have := this hx.val
          rw [Array.mem_toList_iff] at this
          grind
    | none =>
        simp [toSSAExpr] at hp
| .continue, hkBreak, hkContinue => by
    intro hp
    match kcontinue with
    | some kcontinue' =>
        simp [toSSAExpr, Option.isSome_iff_exists, Option.bind_eq_some_iff] at hp
        obtain ⟨a, ha, H⟩ := hp
        simp only [toSSAExpr, Option.bind_eq_bind, Option.bind_some]
        have : (a.funDom?) = (mkMutTuple continueMutVars).2 := by
            grind
        apply SSAType.funDom?_eq_some_iff at this
        simp [ha, SSAExpr.inferType]
        rw [SSAExpr.inferType_mkMutTuple]
        grind
        · rw [← Array.isPrefixOf_toList] at hcontMutVars
          have := List.subset_of_isPrefixOf _ _ hcontMutVars
          intro x hx
          have := this hx.val
          rw [Array.mem_toList_iff] at this
          grind
    | none =>
        simp [toSSAExpr] at hp
| .return out, hkBreak, hkContinue => by
    intro hp
    grind [toSSAExpr, Option.isSome_iff_exists, Option.bind_eq_some_iff]
| .ifthenelse c t e rest, hkBreak, hkContinue => by
    intro hp
    simp [toSSAExpr, Option.isSome_iff_exists, Option.bind_eq_some_iff] at hp
    sorry
| _, hkBreak, hkContinue => sorry

#check SSADo

def SSAExpr.eval (args : Arr): SSAExpr → Option SSAConst := sorry

#check (failure : Option Nat)
#check Option.all_bind

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

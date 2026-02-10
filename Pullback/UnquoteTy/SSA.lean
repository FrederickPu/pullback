import Lean
import Mathlib.Logic.ExistsUnique
import Std.Tactic.Do

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
deriving Inhabited

def VarMap := Array (Name × SSAType)

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

def VarMap.get (map : VarMap) (key : Name) : Option SSAType :=
    map.findLast? (·.1 = key) |>.map (·.2)

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
        simp [inferType, VarMap.get] at he
        calc
            _ = ((Array.findLast? (fun x => decide (x.fst = name)) vars).get he).2.type := by {
                have : x = (some x).get rfl := rfl
                rw [this]
                simp [← h]
                congr
                simp only [Array.findLast?, Array.findLastFinIdx?]
                simp [Array.find?_eq_getElem_findFinIdx?]
                congr
                push_cast
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
                simp [Array.findLast?, inferType, VarMap.get]
            }

    }) (ctx.get (Fin.cast (by {
        simp only [Array.toList_map, List.length_map, Array.length_toList]
    }) x))
    | none => by {
        simp only [inferType, VarMap.get, Array.findLast?, Option.isSome_map] at he
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
private partial def freshNameAux (mutVars : Array Name) (baseName : Name) (idx : Nat) : Name :=
    if mutVars.any (· == baseName.appendIndexAfter idx) then
        freshNameAux mutVars baseName (idx + 1)
    else
        baseName.appendIndexAfter idx
/-
    for fixed mutVars, if baseName1 and baseName2 don't share a prefix then freshName will give different fresh names.
-/
def freshName (mutVars : Array Name) (baseName : Name) : Name :=
    if mutVars.any (· == baseName) then
        freshNameAux mutVars baseName 1
    else
        baseName

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
def SSADo.collectMutVars : SSADo → Array Name
| expr e => #[]
| seq s₁ s₂ =>  Array.append (s₁.collectMutVars) (s₂.collectMutVars)
| letE var val rest => rest.collectMutVars
| letM var val rest => Array.append #[var] (rest.collectMutVars)
| assign var val rest => rest.collectMutVars
| loop (body : SSADo) (rest : SSADo) => rest.collectMutVars
| .break => #[]
| .continue => #[]
| .return _ => #[]
| ifthenelse _ _ _ _ => #[]

def SSADo.toSSAExpr (vars : VarMap) (mutVars : VarMap) (kbreak kcontinue : Option Name) : SSADo → Option SSAExpr
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
            SSAExpr.app (SSAExpr.var kcontinue) (mkMutTuple mutVars).1
        else
            none
    | none => do
        some e
| seq s₁ s₂ => do pure <| SSAExpr.letE (freshName (Array.append s₁.collectMutVars s₂.collectMutVars) `x) (← s₁.toSSAExpr vars mutVars kbreak kcontinue) (← s₂.toSSAExpr vars mutVars kbreak kcontinue)
| letE var val rest => do
    if mutVars.any (·.1 = var) then
        none
    let valT ← val.inferType vars
    return SSAExpr.letE var val (← rest.toSSAExpr (vars.push (var, valT)) mutVars kbreak kcontinue)
| letM var val rest => do
    if mutVars.any (·.1 = var) then
        none
    let valT ← val.inferType vars
    return SSAExpr.letE var val (← rest.toSSAExpr (vars.push (var, valT)) (mutVars.push (var, valT)) kbreak kcontinue)
| assign var val rest => do
    let valT ← val.inferType vars
    return SSAExpr.letE var val (← rest.toSSAExpr (vars.push (var, valT)) mutVars kbreak kcontinue)
| loop body rest => do
    let (mutTuple, mutTupleType) := (mkMutTuple mutVars)
    let bodyMutVars : Array Name  := body.collectMutVars
    let nS : Name := freshName (Array.append (mutVars.map (·.1)) bodyMutVars) `s
    let restExpr ← rest.toSSAExpr vars mutVars kbreak kcontinue
    let breakNew : SSAExpr ← SSAExpr.lam nS mutTupleType <| (destructMutTuple nS mutVars restExpr)
    let nKBreak : Name := freshName (mutVars.map (·.1)) `kbreak
    let nKContinue : Name := freshName (mutVars.map (·.1)) `kcontinue
    -- todo :: modify mutvars passed into toSSAExpr for body
    let bodyExpr ← body.toSSAExpr vars mutVars nKBreak nKContinue
    let bodyType ← bodyExpr.inferType vars
    if (← restExpr.inferType vars) != bodyType then
        none
    let body' : SSAExpr ← destructMutTuple nS mutVars bodyExpr
    SSAExpr.letE nKBreak breakNew <|
        SSAExpr.app (SSAExpr.app (SSAExpr.const (SSAConst.loop mutTupleType bodyType)) mutTuple) (SSAExpr.lam nKContinue (SSAType.fun mutTupleType (SSAType.ofBase .unit)) (SSAExpr.lam nS mutTupleType body'))
| .break => do
    let (mutTuple, mutType) := (mkMutTuple mutVars)
    let kbreak' ← kbreak
    if mutType != (vars.get kbreak') then
        none
    SSAExpr.app (SSAExpr.var kbreak') mutTuple
| .continue => do
    let (mutTuple, mutType) := (mkMutTuple mutVars)
    let kcontinue' ← kcontinue
    if mutType != (vars.get kcontinue') then
        none
    SSAExpr.app (SSAExpr.var (← kcontinue)) mutTuple
| .return out => do
    let _ ← out.inferType vars
    return out
| ifthenelse cond t e rest => do
    let (_, mutTupleType) := (mkMutTuple mutVars)
    let nKContinue : Name := freshName (mutVars.map (·.1)) `kcontinue
    let restMutVars : Array Name := rest.collectMutVars
    let nS : Name := freshName (Array.append (mutVars.map (·.1)) restMutVars) `s
    -- todo :: pass expanded mutvars into toSSAExpr
    let continue' ← (SSAExpr.lam nS mutTupleType <| destructMutTuple nS mutVars (← rest.toSSAExpr vars mutVars kbreak kcontinue))
    let texpr ← t.toSSAExpr vars mutVars kbreak nKContinue
    let tExprType ← texpr.inferType vars
    SSAExpr.letE nKContinue continue' <|
    SSAExpr.app (SSAExpr.app (SSAExpr.app (.const (.ifthenelse tExprType)) cond) (← t.toSSAExpr vars mutVars kbreak nKContinue)) (← e.toSSAExpr vars mutVars kbreak nKContinue)

#check List.Nodup
#check List.instHasSubset

-- returns domain of function type if the type is a function type
def SSAType.funDom? : SSAType → Option SSAType
| .fun α _ => α
| _ => none

-- returns codomain of function type if the type is a function type
def SSAType.funCodom? : SSAType → Option SSAType
| .fun _ β => β
| _ => none

theorem SSAExpr.welltyped_app_iff (vars : VarMap) (f x : SSAExpr) : ((f.app x).inferType vars).isSome ↔ (do pure ((← f.inferType vars).funDom? = (← x.inferType vars))) = some True := sorry

#check Option.getD

/-
    name `k` referes to a valid continutation for the current mutvars
-/
def SSADo.validContinutation (vars : VarMap) (mutVars : VarMap) (k : Name) := (do pure <| (← vars.get k).funDom? = (mkMutTuple mutVars).2) = some true

/-
    `k` is the name of a valid continuation or none
-/
def SSADo.validContinutationRef (vars : VarMap) (mutVars : VarMap) (k : Option Name) :=
    match k with
    | some k' => validContinutation vars mutVars k'
    | none => True

open Std Do
/--
Adequacy lemma for `Option`.
Useful if you want to prove a property about a complex expression `prog : Option α` that you have
generalized to a variable `x` and you want to use `mvcgen` to reason about `prog`.
-/
theorem Std.Do.Option.of_wp_eq {α} {x prog : Option α} (h : prog = x) (P : Option α → Prop) :
    (⊢ₛ wp⟦prog⟧ post⟨fun a => ⌜P (some a)⌝, fun _ => ⌜P none⌝⟩) → P x := by
  subst h
  intro hspec
  simp only [wp, Id.run, PredTrans.pushOption_apply, PredTrans.pure_apply, SPred.entails_nil,
    SPred.down_pure] at hspec
  split at hspec <;> exact hspec True.intro


theorem SSADo.toSSAExpr_wellTyped (vars : VarMap) (mutVars : VarMap) (kbreak kcontinue : Option Name) (hkBreak : validContinutationRef vars mutVars kbreak) (hkContinue : validContinutationRef vars mutVars kcontinue) (hMut₁ : (mutVars.toList.map (·.1)).Nodup) (hMut₂ : mutVars.toList ⊆ vars.toList) (hMut₃ : ∀ mutvar ∈ mutVars.toList, ∃! var ∈ vars.toList, var.1 = mutvar.1) : (prog : SSADo) → (hp : (prog.toSSAExpr vars mutVars kbreak kcontinue).isSome) → (((prog.toSSAExpr vars mutVars kbreak kcontinue).get hp).inferType vars).isSome
| .expr e => by
    intro hp
    simp [toSSAExpr] at hp
    simp [Option.isSome_iff_exists, Option.bind_eq_some_iff] at hp
    obtain ⟨res, et, het, hres⟩ := hp
    match hkc : kcontinue with
    | some kc =>
        simp [validContinutationRef, validContinutation, Option.bind_eq_some_iff] at hkContinue
        obtain ⟨fkc, hfkc⟩ := hkContinue
        have crux : (SSAExpr.inferType vars (mkMutTuple mutVars).fst) = (mkMutTuple mutVars).snd := sorry
        obtain ⟨β, hb⟩ : ∃ β, fkc = .fun (mkMutTuple mutVars).snd β := sorry
        simp [toSSAExpr, SSAExpr.inferType, crux, hfkc, hb]
    | none =>
        simp [toSSAExpr, het]
| .letE var val rest => by
    intro hp
    match hv : mutVars.any (·.1 = var) with
    | false =>
        simp [toSSAExpr, hv, Option.isSome_iff_exists, Option.bind_eq_some_iff] at hp
        obtain ⟨a, varT, hvarT, a2, ha2⟩ := hp
        have := toSSAExpr_wellTyped (vars.push (var, varT)) mutVars kbreak kcontinue sorry sorry sorry sorry sorry rest (by simp [ha2.1])
        grind [toSSAExpr, SSAExpr.inferType, Option.isSome_iff_exists]
    | true =>
        simp [toSSAExpr, hv] at hp
| .letM var val rest => by
    intro hp
    match hv : mutVars.any (·.1 = var) with
    | false =>
        simp [toSSAExpr, hv, Option.isSome_iff_exists, Option.bind_eq_some_iff] at hp
        obtain ⟨a, varT, hvarT, a2, ha2⟩ := hp
        have := toSSAExpr_wellTyped (vars.push (var, varT)) (mutVars.push (var, varT)) kbreak kcontinue sorry sorry sorry sorry sorry rest (by simp [ha2.1])
        grind [toSSAExpr, SSAExpr.inferType, Option.isSome_iff_exists]
    | true =>
        simp [toSSAExpr, hv] at hp
| .assign var val rest => by
    intro hp
    simp [toSSAExpr, Option.isSome_iff_exists, Option.bind_eq_some_iff] at hp
    obtain ⟨a, varT, hvarT, a2, ha2⟩ := hp
    have := toSSAExpr_wellTyped (vars.push ⟨var, varT⟩) mutVars kbreak kcontinue sorry sorry sorry sorry sorry rest (by grind)
    grind [toSSAExpr, SSAExpr.inferType, Option.isSome_iff_exists]
| .break => by
    intro hp
    match kbreak with
    | some kbreak' =>
        simp [toSSAExpr, Option.isSome_iff_exists] at hp
        have : (mkMutTuple mutVars).fst.inferType vars = (mkMutTuple mutVars).snd := sorry
        simp [toSSAExpr]
        grind [toSSAExpr, validContinutationRef, validContinutation, toSSAExpr, SSAExpr.welltyped_app_iff, SSAExpr.inferType, Option.isSome_iff_exists]
    | none =>
        simp [toSSAExpr] at hp
| .continue => by
    intro hp
    match kcontinue with
    | some kcontinue' =>
        simp [toSSAExpr, Option.isSome_iff_exists] at hp
        have : (mkMutTuple mutVars).fst.inferType vars = (mkMutTuple mutVars).snd := sorry
        simp [toSSAExpr]
        grind [toSSAExpr, validContinutationRef, validContinutation, toSSAExpr, SSAExpr.welltyped_app_iff, SSAExpr.inferType, Option.isSome_iff_exists]
    | none =>
        simp [toSSAExpr] at hp
| .return out => by
    intro hp
    grind [toSSAExpr, Option.isSome_iff_exists, Option.bind_eq_some_iff]
| _ => sorry

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

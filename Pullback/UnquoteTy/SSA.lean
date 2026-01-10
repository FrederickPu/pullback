import Lean

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
| ofFloat : Float → SSAConst
| ofInt : Int → SSAConst
| ofUnit : Unit → SSAConst
| loop (ty : SSABaseType) : SSAConst
| prod (α β : SSAType) : SSAConst
| ifthenelse (ty : SSAType) : SSAConst

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

def Fin.val_last'_eq {n : Nat} [NeZero n] : (Fin.last' (n := n)).val = n - 1 := sorry

def Fin.le_last' {n : Nat} [NeZero n] : ∀ i : Fin n, i ≤ (Fin.last' (n := n)) := sorry

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
| loop ty => .fun (.ofBase ty) (.fun (.fun (.ofBase ty) (.prod (.ofBase ty) (.ofBase .int))) (.ofBase ty))-- ((x, 1) denotes break anything else denotes continue) todo :: adapt loop to use ForInStep and be inline with Lean.Loop
| prod α β => .fun α (.fun β (.prod α β))
| ifthenelse ty => .fun (.ofBase .int) (.fun ty (.fun ty ty))

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
| float => Float
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

def DVector.push {L: Array Type} {α : Type} : DVector L.toList → α → DVector (L.push α).toList := sorry

def DVector.get {L : List Type} (v : DVector L) (i : Fin L.length) : L.get i := sorry

#check Array.toList

def SSAExpr.toBool (vars : VarMap) : SSAExpr → Bool := sorry

theorem Array.find?_eq_getElem_findFinIdx? {α : Type u} (xs : Array α) (p : α → Bool): xs.find? p = (xs.findFinIdx? p).map (xs[·]) := sorry

#check cast

#check Prod.mk Nat Nat

-- (a : α, true) means break (a : α, false) means continue
def SSA.loop {α : Type u} [Inhabited α] (init : α) (step : α → α × Bool) : α := sorry

private def SSABaseType.inhabit : (ty : SSABaseType) → ty.type
| int => (0 : Int)
| float => (0 : Float)
| unit => ()

instance {ty : SSABaseType} : Inhabited ty.type := ⟨ty.inhabit⟩

instance {ty : SSABaseType} : Inhabited (SSAType.ofBase ty).type := by
    simp [SSAType.type]
    infer_instance


def SSAConst.interp : (e : SSAConst) → (e.inferType).type
| ofFloat f => f
| ofInt i => i
| ofUnit () => ()
| ifthenelse ty => fun c t e => if (cast (by simp [SSAType.type, SSABaseType.type]) c : Int) != 0 then t else e
| loop ty => fun init => fun step => SSA.loop (α := (SSAType.ofBase ty).type) init (fun x => let (a, b) := step x; (a, cast (β := Int) (by simp [SSAType.type, SSABaseType.type]) b == 1))
| prod α β => (@Prod.mk α.type β.type)

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

def mkMutTuple (mutVars : VarMap) : SSAExpr × SSAType := sorry

def destructMutTuple (mutVars : VarMap) (body : SSAExpr) : SSAExpr := sorry

/-
    for fixed mutVars, if baseName1 and baseName2 don't share a prefix then freshName will give different fresh names.
-/
def freshName (mutVars : VarMap) (baseName : Name) : Name := sorry

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

-- partial def SSADo.toSSAExpr (mutVars : VarMap) (kbreak kcontinue : Option Name) : SSADo → SSAExpr
-- | expr (.const (.ofUnit ())) =>
--     match kcontinue with
--     | some kcontinue => SSAExpr.app (SSAExpr.var kcontinue) (mkMutTuple mutVars).1
--     | none => (.const (.ofUnit ()))
-- -- note: only trailing exprs are interpreted as return types
-- -- ie: `do if cond then 10 else 10` is invalid but `do if cond then return 10 else (); 10` is valid
-- | expr e =>
--     match kcontinue with
--     | some kcontinue => e
--     | none => sorry -- loop body should not end in non unit type
-- | seq s₁ s₂ => SSAExpr.letE `x (s₁.toSSAExpr mutVars kbreak kcontinue) (s₂.toSSAExpr mutVars kbreak kcontinue)
-- | letE var val rest => SSAExpr.letE var val (rest.toSSAExpr mutVars kbreak kcontinue)
-- | letM var val rest => SSAExpr.letE var val (rest.toSSAExpr (mutVars.push (var, val.inferType)) kbreak kcontinue)
-- | assign var val rest => SSAExpr.letE var val (rest.toSSAExpr mutVars kbreak kcontinue)
-- | loop body rest =>
--     let (mutTuple, mutTupleType) := (mkMutTuple mutVars)
--     let bodyMutVars : VarMap := sorry
--     let nS : Name := freshName (Array.append mutVars bodyMutVars) `s
--     let breakNew : SSAExpr := SSAExpr.lam nS mutTupleType <| (destructMutTuple mutVars (rest.toSSAExpr mutVars kbreak kcontinue))
--     let nKBreak : Name := freshName mutVars `kbreak
--     let nKContinue : Name := freshName mutVars `kcontinue
--     -- todo :: modify mutvars passed into toSSAExpr for body
--     let body' : SSAExpr := destructMutTuple mutVars (body.toSSAExpr mutVars nKBreak nKContinue)
--     SSAExpr.letE nKBreak breakNew <|
--         SSAExpr.app (SSAExpr.app (SSAExpr.const (SSAConst.loop mutTupleType)) (SSAExpr.lam nKContinue (SSAType.fun mutTupleType (SSAType.ofBase .unit)) (SSAExpr.lam nS mutTupleType body'))) mutTuple
-- | .break =>
--     match kbreak with
--     | some kbreak =>
--         let mutTuple : SSAExpr := (mkMutTuple mutVars).1
--         SSAExpr.app (SSAExpr.var kbreak) mutTuple
--     | none => sorry -- violates grammer
-- | .continue =>
--     match kcontinue with
--     | some kcontinue =>
--         let mutTuple : SSAExpr := (mkMutTuple mutVars).1
--         SSAExpr.app (SSAExpr.var kcontinue) mutTuple
--     | none => sorry -- violates grammer
-- | .return out => out
-- | ifthenelse cond t e rest =>
--     let (mutTuple, mutTupleType) := (mkMutTuple mutVars)
--     let nKContinue : Name := freshName mutVars `kcontinue
--     let restMutVars : VarMap := sorry
--     let nS : Name := freshName (Array.append mutVars restMutVars) `s
--     -- todo :: pass expanded mutvars into toSSAExpr
--     let continue' := SSAExpr.lam nS mutTupleType <| rest.toSSAExpr mutVars kbreak kcontinue
--     SSAExpr.letE nKContinue continue' <|
--     SSAExpr.ifthenelse cond (t.toSSAExpr mutVars kbreak nKContinue) (e.toSSAExpr mutVars kbreak nKContinue)

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

inductive SSAExpr where
| const : SSAConst → SSAExpr
| letE (var : Name) (val : SSAExpr) (body : SSAExpr) : SSAExpr
| var (name : Name) : SSAExpr
| app (f : SSAExpr) (arg : SSAExpr)
| lam (varName : Name) (varType : SSAType) (body : SSAExpr) : SSAExpr
| loop (ty : SSAType) : SSAExpr
| prod (α : SSAType) (β : SSAType): SSAExpr → SSAExpr → SSAExpr
| ifthenelse (cond t e : SSAExpr) : SSAExpr
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

def SSAConst.baseType : SSAConst → SSABaseType
| ofFloat _ => .float
| ofInt _ => .int
| ofUnit _ => .unit

/-
    none is returned the input expr doesn't typecheck
-/
def SSAExpr.inferType (vars : VarMap) : SSAExpr → Option SSAType
| const base => SSAType.ofBase base.baseType
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
| lam _ varType body => body.inferType vars |>.bind (fun bodyType => SSAType.fun varType bodyType)
| loop ty => ty
| prod α β a b =>
    a.inferType vars |>.bind
    fun aType =>
    b.inferType vars |>.bind
    fun bType =>
        if aType == α ∧ bType == α then
            SSAType.prod α β
        else
            none
| ifthenelse c t e =>
    c.inferType vars |>.bind
    fun cType =>
    t.inferType vars |>.bind
    fun tType =>
    e.inferType vars |>.bind
    fun eType =>
        if tType == eType then tType else none

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

def SSAConst.toBool : SSAConst → Bool
| ofFloat f => !(f == 0)
| ofInt i => !(i == 0)
| ofUnit _ => true

def SSAExpr.toBool (vars : VarMap) : SSAExpr → Bool := sorry

theorem Array.find?_eq_getElem_findFinIdx? {α : Type u} (xs : Array α) (p : α → Bool): xs.find? p = (xs.findFinIdx? p).map (xs[·]) := sorry

def SSAExpr.interp (vars : VarMap) : (e : SSAExpr) → (he : e.inferType vars |>.isSome) → DVector (Array.toList (vars.map (·.2.type))) → (Option.get (e.inferType vars) he).type
| .const base, _, _ => sorry
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
| app f arg, he, ctx => (f.interp vars) (arg.interp vars sorry ctx)
| lam name valType body, he, ctx => cast sorry <|
    fun val : valType.type => cast (by sorry) <| body.interp (vars.push ⟨name, valType⟩) (by sorry) (cast (by simp) <| ctx.push val)
| loop ty, he, ctx => sorry -- todo :: use extrinsicFix somehow
| prod α β a b, he, ctx => cast sorry (a.interp vars sorry ctx, b.interp vars sorry ctx)
| ifthenelse c t e, he, ctx => cast sorry <| if c.toBool vars then t.interp vars sorry ctx else cast sorry <| e.interp vars sorry ctx

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

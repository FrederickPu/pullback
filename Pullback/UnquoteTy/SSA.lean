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

#check Std.HashMap.insert

#check Std.TreeMap

#eval (((Std.HashMap.empty : Std.HashMap Name Int).insert `b 123).insert `a 456).keys

def VarMap := Array (Name × SSAType)

def VarMap.get (map : VarMap) (key : Name) : Option SSAType :=
    map.find? (·.1 = key) |>.map (·.2)

def VarMap.insert (map : VarMap) (key : Name) (val : SSAType) : VarMap :=
    if map.any (·.1 = key) then map else map.push (key, val)

def SSAConst.baseType : SSAConst → SSABaseType
| ofFloat _ => .float
| ofInt _ => .int
| ofUnit _ => .unit

/-
    none is returned the input expr doesn't typecheck
-/
def SSAExpr.inferType (vars : VarMap): SSAExpr → Option SSAType
| const base => SSAType.ofBase base.baseType
| letE name val body =>
    (val.inferType vars).bind <|
        fun valType => body.inferType (vars.insert name valType)
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
| prod α β _ _ => SSAType.prod α β
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

def mkMutTuple (mutVars : VarMap) : SSAExpr × SSAType := sorry

def destructMutTuple (mutVars : VarMap) (body : SSAExpr) : SSAExpr := sorry

/-
    for fixed mutVars, if baseName1 and baseName2 don't share a prefix then freshName will give different fresh names.
-/
def freshName (mutVars : VarMap) (baseName : Name) : Name := sorry

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

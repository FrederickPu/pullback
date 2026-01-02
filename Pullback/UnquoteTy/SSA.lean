import Lean

open Lean

inductive SSABaseType where
| float : SSABaseType
| int : SSABaseType
| unit : SSABaseType

inductive SSAType where
| ofBase : SSABaseType → SSAType
| fun : SSAType → SSAType → SSAType
| prod : SSAType → SSAType → SSAType

inductive SSAConst where
| loop (ty : SSAType) : SSAConst
| ofFloat : Float → SSAConst
| ofInt : Float → SSAConst

inductive SSAExpr where
| letE (var : Name) (val : SSAExpr) (body : SSAExpr) : SSAExpr
| var (name : Name) : SSAExpr
| const : SSAConst → SSAExpr
| app (f : SSAExpr) (arg : SSAExpr)
| lam (var : Name) (varType : SSAType) (body : SSAExpr) : SSAExpr
| prod (α : SSAType) (β : SSAType): SSAExpr → SSAExpr → SSAExpr
deriving Inhabited

inductive SSADo where
| expr : SSAExpr → SSADo
| seq (s₁ s₂ : SSADo) : SSADo
| letE (var : Name) (val : SSAExpr) (body : SSADo) : SSADo
| letM (var : Name) (val : SSAExpr) (body : SSADo) : SSADo -- let mut
| assign (var : Name) (val : SSAExpr) (body : SSADo) : SSADo
| loop (body : SSADo) (rest : SSADo) : SSADo
| break : SSADo
| continue : SSADo
| return (out : SSAExpr) : SSADo

#check Std.HashMap.insert

#check Std.TreeMap

#eval (((Std.HashMap.empty : Std.HashMap Name Int).insert `b 123).insert `a 456).keys


def SSAExpr.inferType : SSAExpr → SSAType := sorry

def VarMap := Array (Name × SSAType)

def mkMutTuple (mutVars : VarMap) : SSAExpr × SSAType := sorry

def destructMutTuple (mutVars : VarMap) (body : SSADo) : SSADo := sorry

/-
    for fixed mutVars, if baseName1 and baseName2 don't share a prefix then freshName will give different fresh names.
-/
def freshName (mutVars : VarMap) (baseName : Name) : Name := sorry

partial def SSADo.toSSAExpr (mutVars : VarMap) (kbreak kcontinue : Option Name) : SSADo → SSAExpr
| expr e => e
| seq s₁ s₂ => SSAExpr.letE `x (s₁.toSSAExpr mutVars kbreak kcontinue) (s₂.toSSAExpr mutVars kbreak kcontinue)
| letE var val body => SSAExpr.letE var val (body.toSSAExpr mutVars kbreak kcontinue)
| letM var val body => SSAExpr.letE var val (body.toSSAExpr (mutVars.push (var, val.inferType)) kbreak kcontinue)
| assign var val body => SSAExpr.letE var val (body.toSSAExpr mutVars kbreak kcontinue)
| loop body rest =>
    let (mutTuple, mutTupleType) := (mkMutTuple mutVars)
    let bodyMutVars : VarMap := sorry
    let trailingReturn : Bool := sorry -- using body
    let nS : Name := freshName (Array.append mutVars bodyMutVars) `s
    let breakNew : SSAExpr := SSAExpr.lam nS mutTupleType <| (destructMutTuple mutVars rest).toSSAExpr mutVars kbreak kcontinue
    let nKBreak : Name := freshName mutVars `kbreak
    let nKContinue : Name := freshName mutVars `kcontinue
    let body' : SSAExpr :=
        if trailingReturn then
            destructMutTuple mutVars body |>.toSSAExpr mutVars nKBreak nKContinue
        else
            (SSADo.seq (destructMutTuple mutVars body) (.expr mutTuple)).toSSAExpr mutVars nKBreak nKContinue
    SSAExpr.letE nKBreak breakNew <|
        SSAExpr.app (SSAExpr.app (SSAExpr.const (SSAConst.loop mutTupleType)) (SSAExpr.lam nKContinue (SSAType.fun mutTupleType (SSAType.ofBase .unit)) (SSAExpr.lam nS mutTupleType body'))) mutTuple
| .break =>
    match kbreak with
    | some kbreak =>
        let mutTuple : SSAExpr := (mkMutTuple mutVars).1
        SSAExpr.app (SSAExpr.var kbreak) mutTuple
    | none => sorry -- violates grammer
| .continue =>
    match kcontinue with
    | some kcontinue =>
        let mutTuple : SSAExpr := (mkMutTuple mutVars).1
        SSAExpr.app (SSAExpr.var kcontinue) mutTuple
    | none => sorry -- violates grammer
| .return out => out

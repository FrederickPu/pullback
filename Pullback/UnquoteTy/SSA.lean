import Lean

open Lean

inductive SSABaseType where
| float : SSABaseType
| int : SSABaseType

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
| lam (var : Name) (body : SSAExpr) : SSAExpr

inductive SSADo where
| expr : SSAExpr → SSADo
| seq (s₁ s₂ : SSADo) : SSADo
| letE (var : Name) (val : SSAExpr) (body : SSADo) : SSADo
| letM (var : Name) (val : SSAExpr) (body : SSADo) : SSADo -- let mut
| assign (var : Name) (val : SSAExpr) (body : SSADo) : SSADo
| loop (body : SSADo) : SSADo
| break : SSADo
| continue : SSADo
| return (out : SSAExpr) : SSADo

#check Std.HashMap.insert

def SSAExpr.inferType : SSAExpr → SSAType := sorry

def SSADo.toSSAExpr (mutVars : Std.HashMap Name SSAType) (kbreak kcontinue : Option Name) (kreturn : SSAExpr) : SSADo → SSAExpr
| expr e => e
| seq s₁ s₂ => SSAExpr.letE `x (s₁.toSSAExpr mutVars kbreak kcontinue kreturn) (s₂.toSSAExpr mutVars kbreak kcontinue kreturn)
| letE var val body => SSAExpr.letE var val (body.toSSAExpr mutVars kbreak kcontinue kreturn)
| letM var val body => SSAExpr.letE var val (body.toSSAExpr (mutVars.insert var val.inferType) kbreak kcontinue kreturn)
| assign var val body => SSAExpr.letE var val (body.toSSAExpr mutVars kbreak kcontinue kreturn)
| loop body =>
    let (body', mutTupleType) : SSAExpr × SSAType := sorry -- turn body into function that returns all mut vars at end (in big tuple) (this portion should handle break, continue)
    let nKBreak : Name := sorry -- get fresh name
    let nKContinue : Name := sorry -- get fresh name
    SSAExpr.app (SSAExpr.const (SSAConst.loop mutTupleType)) (SSAExpr.lam nKBreak (SSAExpr.lam nKContinue body'))
| .break =>
    match kbreak with
    | some kbreak =>
        let mutTuple : SSAExpr := sorry
        SSAExpr.app (SSAExpr.var kbreak) mutTuple
    | none => sorry -- violates grammer
| .continue =>
    match kcontinue with
    | some kcontinue =>
        let mutTuple : SSAExpr := sorry
        SSAExpr.app (SSAExpr.var kcontinue) mutTuple
    | none => sorry -- violates grammer
| .return out =>
    SSAExpr.app kreturn out

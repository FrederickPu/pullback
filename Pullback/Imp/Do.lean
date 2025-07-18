import Lean
import Init
import Std.Data.HashMap.Basic
import Pullback.Imp.Syntax

open Lean
open Std

namespace Imp

abbrev ImpM := EStateM String (HashMap String Value)

def evalExpr : Expr → ImpM Value
  | Expr.const v => return v
  | Expr.var x => do
    let env ← get
    match env.get? x with
    | some v => return v
    | none => throw s!"unbound variable {x}"
  | Expr.add e₁ e₂ => do
    let v₁ ← evalExpr e₁
    let v₂ ← evalExpr e₂
    return v₁ + v₂
  | Expr.lt e₁ e₂ => do
    let v₁ ← evalExpr e₁
    let v₂ ← evalExpr e₂
    return if v₁ < v₂ then 1 else 0

def evalStmt : Stmt → ImpM Unit
  | Stmt.assign x e => do
    let v ← evalExpr e
    modify (fun env => env.insert x v)
  | Stmt.seq s₁ s₂ => do
    evalStmt s₁
    evalStmt s₂
  | Stmt.IfThenElse c t e => do
    let v ← evalExpr c
    if v ≠ 0 then evalStmt t else evalStmt e
  | Stmt.while c b => do
    while (← evalExpr c) ≠ 0 do
      evalStmt b

-- Example use
def testStmt : Stmt :=
  stmt{
    while (x < 10) {
      x := x + 1;
    }
  }

def initialEnv : HashMap String Value :=
  HashMap.empty.insert "x" 0


def runTest : IO Unit := do
  let res := evalStmt testStmt |>.run initialEnv
  match res with
  | EStateM.Result.ok _ finalEnv =>
    match finalEnv.get? "x" with
    | some xVal => IO.println s!"Final value of x: {xVal}"
    | none => IO.println "x not found in environment"
  | EStateM.Result.error err _ =>
    IO.println s!"Error: {err}"

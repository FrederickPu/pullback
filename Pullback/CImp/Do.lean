import Lean
import Init
import Std.Data.HashMap.Basic
import Pullback.CImp.Syntax

open Lean
open Std

namespace CImp

abbrev ImpM := EStateM String (HashMap String Value)

def toSyntaxExpr : Expr → MetaM (TSyntax `term)
  | Expr.const v => do return (quote v.toNat)
  | Expr.var x => do
    `($(mkIdent x):ident)
  | Expr.add e₁ e₂ => do
    let v₁ ← toSyntaxExpr e₁
    let v₂ ← toSyntaxExpr e₂
    `($v₁ + $v₂)
  | Expr.lt e₁ e₂ => do
    let v₁ ← toSyntaxExpr e₁
    let v₂ ← toSyntaxExpr e₂
    `(if $v₁ < $v₂ then 1 else 0)
  | Expr.deref e => do
    let e' ← toSyntaxExpr e
    -- note: the below is a valid term since it only requires the Bind typeclass instance and doesnt need do notation to work
    `(← Memory.read $e')

def toDoElem : Stmt → MetaM (TSyntaxArray `Lean.Parser.Term.doSeqItem)
  | .assign n e => do
    let xId := mkIdent n
    let eSyn ← toSyntaxExpr e
    pure #[← `(Lean.Parser.Term.doSeqItem| let mut $xId := $eSyn)]
  | .assignPtr ptr e => do
    let ptr' ← toSyntaxExpr ptr
    let e' ← toSyntaxExpr e
    pure #[← `(Lean.Parser.Term.doSeqItem| Memory.write $ptr' $e')]
  | .seq s₁ s₂ => do
    return (← toDoElem s₁) ++ (← toDoElem s₂)
  | .while c b => do
    let cSyn ← toSyntaxExpr c
    let bSyn ← toDoElem b
    let bSyn ← `(Lean.Parser.Term.doSeqItem| while $cSyn do $bSyn*)
    pure #[bSyn]
  | .IfThenElse c t e => do
    let cSyn ← toSyntaxExpr c
    let tSyn ← toDoElem t
    let eSyn ← toDoElem e
    pure #[← `(Lean.Parser.Term.doSeqItem| if $cSyn then do $tSyn* else do $eSyn*)]

-- Example use
def testStmt : Stmt :=
  stmt{
    while (x < 10) {
      x := x + 1;
    }
  }

universe u₁ u₂

class Memory (m : Type u₁ → Type u₂) (Pointer : Type u₁) (Val : Type u₁) where
  read  : Pointer → m Val
  write : Pointer → Val → m PUnit

/-
  C memory system
  (assume 32-bit archetecture)
-/
instance {α : Type} : Memory IO UInt32 α := sorry

#eval do let x ← toDoElem testStmt; `(do $x*)

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

#check evalStmt testStmt

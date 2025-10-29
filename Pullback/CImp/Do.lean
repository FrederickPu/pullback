import Lean
import Init
import Std.Data.HashMap.Basic
import Pullback.CImp.Syntax
import Qq

open Lean
open Std

namespace CImp

abbrev ImpM := EStateM String (HashMap String Value)

def Expr.toTerm: Expr → MetaM (TSyntax `term)
  | Expr.const v => do return (quote v.toNat)
  | Expr.var x => do
    `($(mkIdent x):ident)
  | Expr.add e₁ e₂ => do
    let v₁ ← Expr.toTerm e₁
    let v₂ ← Expr.toTerm e₂
    `($v₁ + $v₂)
  | Expr.lt e₁ e₂ => do
    let v₁ ← Expr.toTerm e₁
    let v₂ ← Expr.toTerm e₂
    `(if $v₁ < $v₂ then 1 else 0)
  | _ => `(0)
  -- | Expr.deref e => do
  --   let e' ← Expr.toTerm e
  --   -- note: the below is a valid term since it only requires the Bind typeclass instance and doesnt need do notation to work
  --   `(← Memory.read $e')

#check HashSet

def Stmt.toDoSeqItem : Stmt → StateT (HashSet Name) MetaM (TSyntaxArray `Lean.Parser.Term.doSeqItem)
  | .assign n e => do
    let xId := mkIdent n
    let eSyn ← Expr.toTerm e
    if !((← get).contains n) then
      modify (fun x => x.insert n)
      pure #[← `(Lean.Parser.Term.doSeqItem| let mut $xId ← $eSyn:term)]
    else
      pure #[← `(Lean.Parser.Term.doSeqItem| $xId:ident ← $eSyn:term)]
  -- | .assignPtr ptr e => do
  --   let ptr' ← Expr.toTerm ptr
  --   let e' ← Expr.toTerm e
  --   pure #[← `(Lean.Parser.Term.doSeqItem| Memory.write $ptr' $e')]
  | .seq s₁ s₂ => do
    return (← toDoSeqItem s₁) ++ (← toDoSeqItem s₂)
  | .while c b => do
    let cSyn ← Expr.toTerm c
    let bSyn ← toDoSeqItem b
    let bSyn ← `(Lean.Parser.Term.doSeqItem| while $cSyn do $bSyn*)
    pure #[bSyn]
  | .IfThenElse c t e => do
    let cSyn ← Expr.toTerm c
    let tSyn ← toDoSeqItem t
    let eSyn ← toDoSeqItem e
    pure #[← `(Lean.Parser.Term.doSeqItem| if $cSyn then do $tSyn* else do $eSyn*)]
  | _ => pure #[]

-- Example use
def testStmt : Stmt :=
  stmt{
    x := 1;
    while (x < 0){
      x := x + 1;
    }
  }

-- def womp : Id Nat := do
--   let x ← 1
--   return x

universe u₁ u₂

class Memory (m : Type u₁ → Type u₂) (Pointer : Type u₁) (Val : Type u₁) where
  read  : Pointer → m Val
  write : Pointer → Val → m PUnit

/-
  C memory system
  (assume 32-bit archetecture)
-/
instance {α : Type} : Memory IO UInt32 α := sorry

#reduce expr{x + 0}

-- #eval (do
--   let x ← Expr.toTerm (expr{x + 0})
--   let nihe ← Lean.Elab.Term.elabTerm (x) none
--   IO.println (← Lean.Meta.ppExpr nihe).pretty
-- : Lean.Elab.Term.TermElabM Unit)
-- Unknown identifier `x`

open Qq


#eval (do
  let (x, _) ← (Stmt.toDoSeqItem testStmt).run {};
  IO.println (← `(do $x*)).raw
  let nihee ← Lean.Elab.Term.elabTermAndSynthesize (← `(do $x*)) q(Id Nat)
  IO.println "bruhh"
  IO.println (← Lean.Meta.ppExpr nihee).pretty
  : Lean.Elab.Term.TermElabM Unit)

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

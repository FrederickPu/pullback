-- This file demonstrates the formal verification of a Python program
-- using a custom embedded DSL in Lean.

-- First, we import the necessary files that define the Python abstract
-- syntax tree (AST), the evaluation function, and the big-step semantics.
import Init
import Lean
import Pullback.Python.src.BigStep
import Pullback.Python.src.Syntax


-- The Python code we want to verify is a simple program that
-- swaps the values of two variables, 'i' and 'j', using a
-- temporary variable 'z'.
/-
  z = i;
  i = j;
  j = z;
-/

-- We can now use our custom syntax to represent this Python program
-- within Lean.

open Python

def swap_program : Stmt := python {
  z = i
  i = j
  j = z
}

-- Let's do a quick check to see how Lean parses this program.
-- The #check command will show us the underlying AST representation.
#print swap_program
-- It looks like this:
-- def swap_program : Stmt :=
-- (Stmt.assign "z" (Expr.var "i")).seq ((Stmt.assign "i" (Expr.var "j")).seq (Stmt.assign "j" (Expr.var "z")))


-- Proof
theorem swap_swaps (σ σ' : Env) (h : BigStep σ swap_program σ') :
     σ'.get "i" = σ.get "j" ∧ σ'.get "j" = σ.get "i" := by
  cases h with | seq h' h =>
  cases h'
  cases h with | seq h' h =>
  cases h'
  cases h
  constructor
  · simp only [eval, ne_eq, String.reduceEq, not_false_eq_true, Env.get_set_different,
    Env.get_set_same]
  · simp only [eval, ne_eq, String.reduceEq, not_false_eq_true, Env.get_set_different,
    Env.get_set_same]

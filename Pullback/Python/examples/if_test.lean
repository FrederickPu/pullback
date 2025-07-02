import Init
import Lean
import Pullback.Python.src.BigStep
import Pullback.Python.src.Syntax

open Python

def equal : Stmt := python {
  x = 3
  y = 2
  if x == y :
    x = x
  else :
    x = y
}

theorem equal_check (σ σ' : Env) (h : BigStep σ equal σ') :
  σ'.get "x" = σ'.get "y" := by
  cases h with | seq h' h =>
  cases h'
  cases h with | seq h' h =>
  cases h'
  sorry

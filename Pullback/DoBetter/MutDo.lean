import Lean
open Lean

/-!
# `mut_do` — do-notation where every `return e` becomes `return (f e)`

## Usage
```
mut_do[f]
  let x ← someAction
  return x          -- becomes: return (f x)
```
-/

namespace MutDo

/-- Walk the syntax tree. The structure of `doReturn` is:
    NODE[Lean.Parser.Term.doReturn]
      ATOM: "return"
      NODE[null]          ← wrapper node
        <expr>            ← the actual returned expression

    We replace `<expr>` with `(f <expr>)` built via quotation. -/
partial def rewriteReturns (f : TSyntax `term) : Syntax → MacroM Syntax
  | .node info kind args => do
    if kind == ``Lean.Parser.Term.doReturn && args.size == 2 then
      let nullNode := args[1]!
      match nullNode with
      | .node nullInfo nullKind nullArgs =>
        if nullArgs.size > 0 then
          let innerExpr ← rewriteReturns f nullArgs[0]!
          let innerTerm : TSyntax `term := ⟨innerExpr⟩
          -- Use quotation to build a properly structured `(f e)` term
          let wrapped ← `(($f $innerTerm))
          -- Place it back inside the null wrapper node
          let newNullNode := Syntax.node nullInfo nullKind (nullArgs.set! 0 wrapped.raw)
          return .node info kind (args.set! 1 newNullNode)
        else
          return .node info kind args
      | _ =>
        return .node info kind args
    else
      let newArgs ← args.mapM (rewriteReturns f)
      return .node info kind newArgs
  | other => return other

end MutDo

syntax "mut_do" "[" term "]" doSeq : term

macro_rules
  | `(mut_do[ $f ] $seq) => do
    let seq' ← MutDo.rewriteReturns f (seq : Syntax)
    let tsSeq : TSyntax `Lean.Parser.Term.doSeq := ⟨seq'⟩
    `(do $tsSeq)

/-! ## Tests -/

def test1 : IO (Option Nat) :=
  mut_do[Option.some]
    let x ← pure 42
    if x > 10 then
      return x
    return 0

def double (n : Nat) : Nat := n * 2

def test2 : IO Nat :=
  mut_do[double]
    let x ← pure 21
    return x

def test3 (xs : List Nat) : IO (Option Nat) :=
  mut_do[Option.some]
    for x in xs do
      if x > 10 then
        return x
    return 0

/-! ## Value tests -/

-- test1: x = 42 > 10, so early return wraps x → some 42
#eval do
  let r ← test1
  assert! r == some 42
  IO.println s!"test1: {repr r}"  -- expected: some 42

-- test2: x = 21, return wraps x → double 21 = 42
#eval do
  let r ← test2
  assert! r == 42
  IO.println s!"test2: {repr r}"  -- expected: 42

-- test3 with a match: 15 > 10, early return wraps 15 → some 15
#eval do
  let r ← test3 [3, 5, 15, 20]
  assert! r == some 15
  IO.println s!"test3 (match): {repr r}"  -- expected: some 15

-- test3 with no match: falls through, wraps 0 → some 0
#eval do
  let r ← test3 [1, 2, 3]
  assert! r == some 0
  IO.println s!"test3 (no match): {repr r}"  -- expected: some 0

-- Lambda wrapper: return wraps via (· + 100)
def test4 : IO Nat :=
  mut_do[(· + 100)]
    let x ← pure 5
    return x

#eval do
  let r ← test4
  assert! r == 105
  IO.println s!"test4: {repr r}"  -- expected: 105

-- Nested if/else: both branches get wrapped
def test5 (b : Bool) : IO (Option String) :=
  mut_do[Option.some]
    if b then
      return "yes"
    else
      return "no"

#eval do
  let r1 ← test5 true
  let r2 ← test5 false
  assert! r1 == some "yes"
  assert! r2 == some "no"
  IO.println s!"test5: {repr r1}, {repr r2}"  -- expected: some "yes", some "no"

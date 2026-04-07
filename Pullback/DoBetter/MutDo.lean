import Lean
open Lean

/-!
# `mut_do` — do-notation with mutable variables (non-CPS)

## Return convention

`return e` inside `mut_do[x : T, y : U]` becomes `return (e, x, y)`.

Since Lean tuples are right-associated, `(e, x, y)` = `(e, (x, y))`,
so the return type is naturally `RetVal × (T × U)` — the return value
first, then the mutable state as a single tuple.

## Defining a mut function

```lean
def increment (amount : Nat) (count : Nat) : IO (String × Nat) :=
  mut_do[count : Nat]
    count := count + amount
    return s!"incremented by {amount}"
-- returns (message, updatedCount)
```

## Calling with `mut_call`

```lean
  mut_call[count] msg ← increment 5
-- expands to: let (msg, count) ← increment 5 count
```

## Simple form

`mut_do[f]`: every `return e` → `return (f e)` (no mut vars).
-/

namespace MutDo

-- ============================================================
-- Helpers
-- ============================================================

def mkTupleStx (vars : Array Syntax) : MacroM (TSyntax `term) := do
  match vars.size with
  | 0 => `(())
  | 1 => return ⟨vars[0]!⟩
  | _ =>
    let mut acc : TSyntax `term := ⟨vars[vars.size - 1]!⟩
    for i in [:vars.size - 1] do
      let idx := vars.size - 2 - i
      let v : TSyntax `term := ⟨vars[idx]!⟩
      acc ← `(($v, $acc))
    return acc

-- ============================================================
-- Syntax tree rewriting
-- ============================================================

/-- Rewrite `return e` → `return (e, x₁, x₂, ...)`.
    Since Lean tuples are right-associated, `(e, x, y)` = `(e, (x, y))`. -/
partial def rewriteReturnsTuple (varNames : Array Syntax)
    : Syntax → MacroM Syntax
  | .node info kind args => do
    if kind == ``Lean.Parser.Term.doReturn && args.size == 2 then
      let nullNode := args[1]!
      match nullNode with
      | .node nullInfo nullKind nullArgs =>
        if nullArgs.size > 0 then
          let innerExpr ← rewriteReturnsTuple varNames nullArgs[0]!
          let innerTerm : TSyntax `term := ⟨innerExpr⟩
          -- Build (e, x, y, ...) — return value first, then mutvars
          let allElems := #[innerTerm.raw] ++ varNames
          let tup ← mkTupleStx allElems
          let newNullNode := Syntax.node nullInfo nullKind (nullArgs.set! 0 tup.raw)
          return .node info kind (args.set! 1 newNullNode)
        else
          -- bare `return` — pack just the mutvars as ((), x, y, ...)
          let unit ← `(())
          let allElems := #[unit.raw] ++ varNames
          let tup ← mkTupleStx allElems
          let newNullNode := Syntax.node SourceInfo.none `null #[tup.raw]
          return .node info kind (args.set! 1 newNullNode)
      | _ =>
        return .node info kind args
    else
      let newArgs ← args.mapM (rewriteReturnsTuple varNames)
      return .node info kind newArgs
  | other => return other

/-- Simple form: rewrite `return e` → `return (f e)`. -/
partial def rewriteReturns (f : TSyntax `term) : Syntax → MacroM Syntax
  | .node info kind args => do
    if kind == ``Lean.Parser.Term.doReturn && args.size == 2 then
      let nullNode := args[1]!
      match nullNode with
      | .node nullInfo nullKind nullArgs =>
        if nullArgs.size > 0 then
          let innerExpr ← rewriteReturns f nullArgs[0]!
          let innerTerm : TSyntax `term := ⟨innerExpr⟩
          let wrapped ← `(($f $innerTerm))
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

-- ============================================================
-- Node construction helpers
-- ============================================================

def getDoSeqItems (seq : Syntax) : Array Syntax :=
  match seq with
  | .node _ _ #[.node _ _ items] => items
  | _ => #[]

def mkDoSeqIndent (template : Syntax) (items : Array Syntax) : Syntax :=
  match template with
  | .node seqInfo seqKind #[.node nullInfo nullKind _] =>
    Syntax.node seqInfo seqKind #[Syntax.node nullInfo nullKind items]
  | _ => template

def mkLetMutItem (n : TSyntax `ident) (t : TSyntax `term) : MacroM Syntax := do
  let helper ← `(do let mut $n : $t := $n; pure ())
  return helper.raw[1][0][0]

/-- Build a `let <pat> ← <rhs>` doSeqItem by template surgery. -/
def mkLetBindItem (pat : Syntax) (rhs : Syntax) : MacroM Syntax := do
  let helper ← `(do let _ph ← pure (); pure ())
  let item := helper.raw[1][0][0]
  let doLetArrow := item[0]
  let doIdDecl := doLetArrow[2]
  let doIdDecl := doIdDecl.setArg 0 pat
  let doExpr := doIdDecl[3]
  let doExpr := doExpr.setArg 0 rhs
  let doIdDecl := doIdDecl.setArg 3 doExpr
  let doLetArrow := doLetArrow.setArg 2 doIdDecl
  let item := item.setArg 0 doLetArrow
  return item

end MutDo

-- ============================================================
-- Syntax
-- ============================================================

syntax mutBinder := ident " : " term

/-- Full form: `mut_do[x : T, y : U] body` -/
syntax "mut_do" "[" mutBinder,+ "]" doSeq : term

/-- Simple form: `mut_do[f] body` -/
syntax "mut_do" "[" term "]" doSeq : term

/-- Call syntax: `mut_call[x, y] v ← f args` -/
syntax "mut_call" "[" ident,+ "]" ident " ← " term : doElem

-- ============================================================
-- Macro rules
-- ============================================================

/-- Simple form -/
macro_rules
  | `(mut_do[ $f:term ] $seq) => do
    let seq' ← MutDo.rewriteReturns f (seq : Syntax)
    let tsSeq : TSyntax `Lean.Parser.Term.doSeq := ⟨seq'⟩
    `(do $tsSeq)

/-- Full form: introduces `let mut` binders, rewrites `return e` → `return (e, x, y, ...)` -/
macro_rules
  | `(mut_do[ $binders,* ] $seq) => do
    let binders := binders.getElems
    let mut varNames : Array (TSyntax `ident) := #[]
    let mut varTypes : Array (TSyntax `term) := #[]
    for b in binders do
      let name : TSyntax `ident := ⟨b.raw[0]⟩
      let ty : TSyntax `term := ⟨b.raw[2]⟩
      varNames := varNames.push name
      varTypes := varTypes.push ty
    let varNamesSyntax : Array Syntax := varNames.map (·.raw)
    let seq' ← MutDo.rewriteReturnsTuple varNamesSyntax (seq : Syntax)
    let mut letMutItems : Array Syntax := #[]
    for i in [:varNames.size] do
      let item ← MutDo.mkLetMutItem varNames[i]! varTypes[i]!
      letMutItems := letMutItems.push item
    let bodyItems := MutDo.getDoSeqItems seq'
    let allItems := letMutItems ++ bodyItems
    let newSeq : TSyntax `Lean.Parser.Term.doSeq := ⟨MutDo.mkDoSeqIndent seq' allItems⟩
    `(do $newSeq)

/-- `mut_call[x, y] v ← f args` expands to:
    `let (v, x, y) ← f args x y`
    Since `(v, x, y)` = `(v, (x, y))`, the return value and mut state separate naturally. -/
macro_rules
  | `(doElem| mut_call[ $mutVars,* ] $v:ident ← $f:term) => do
    let vars := mutVars.getElems
    -- Build pattern: (v, x, y, ...) — return value first, then mutvars
    let mut allIdents : Array (TSyntax `ident) := #[v]
    for mv in vars do
      allIdents := allIdents.push mv
    let pat ← MutDo.mkTupleStx (allIdents.map (·.raw))
    -- Build call: f args x y (pass mut vars as trailing args)
    let mut callExpr : TSyntax `term := f
    for mv in vars do
      let mvTerm : TSyntax `term := ⟨mv.raw⟩
      callExpr ← `($callExpr $mvTerm)
    -- Build: let (v, x, y) ← callExpr
    let item ← MutDo.mkLetBindItem pat.raw callExpr.raw
    let doElem : TSyntax `doElem := ⟨item[0]⟩
    return doElem

-- ============================================================
-- Tests: simple form
-- ============================================================

section SimpleTests

def testSimple1 : IO (Option Nat) :=
  mut_do[Option.some]
    let x ← pure 42
    if x > 10 then
      return x
    return 0

#eval do
  let r ← testSimple1
  assert! r == some 42
  IO.println s!"testSimple1: {repr r}"

def double (n : Nat) : Nat := n * 2

def testSimple2 : IO Nat :=
  mut_do[double]
    let x ← pure 21
    return x

#eval do
  let r ← testSimple2
  assert! r == 42
  IO.println s!"testSimple2: {repr r}"

end SimpleTests

-- ============================================================
-- Tests: full form
-- ============================================================

section MutTests

/-- Single mut var. Returns (retval, count). -/
def testMut1 : IO (String × Nat) :=
  let count := 0
  mut_do[count : Nat]
    count := count + 1
    count := count + 1
    return "done"

#eval do
  let r ← testMut1
  assert! r == ("done", 2)
  IO.println s!"testMut1: {repr r}"

/-- Two mut vars. Returns (retval, x, y) = (retval, (x, y)). -/
def testMut2 : IO (String × Nat × Nat) :=
  let x := 1
  let y := 2
  mut_do[x : Nat, y : Nat]
    x := x + 10
    y := y + 20
    return "hello"

#eval do
  let r ← testMut2
  assert! r == ("hello", 11, 22)
  IO.println s!"testMut2: {repr r}"

/-- Early return from a loop. -/
def testMut3 (threshold : Nat) : IO (Bool × Nat) :=
  let acc := 0
  mut_do[acc : Nat]
    for i in [0:5] do
      acc := acc + i
      if acc > threshold then
        return true
    return false

#eval do
  let r1 ← testMut3 100
  assert! r1 == (false, 10)
  IO.println s!"testMut3 (no early): {repr r1}"
  let r2 ← testMut3 3
  assert! r2.1 == true
  IO.println s!"testMut3 (early): {repr r2}"

/-- Three mut vars. -/
def testMut4 : IO (Unit × Nat × String × Bool) :=
  let a := 0
  let b := "hello"
  let c := false
  mut_do[a : Nat, b : String, c : Bool]
    a := a + 42
    b := b ++ " world"
    c := !c
    return ()

#eval do
  let r ← testMut4
  assert! r == ((), 42, "hello world", true)
  IO.println s!"testMut4: {repr r}"

end MutTests

-- ============================================================
-- Tests: standalone functions + mut_call
-- ============================================================

section CallTests

/-- Increment: returns (message, newCount). -/
def increment (amount : Nat) (count : Nat) : IO (String × Nat) :=
  mut_do[count : Nat]
    count := count + amount
    return s!"incremented by {amount}"

/-- Double: returns ((), newX). -/
def doubleM (x : Nat) : IO (Unit × Nat) :=
  mut_do[x : Nat]
    x := x * 2
    return ()

#eval do
  let r ← increment 5 10
  assert! r == ("incremented by 5", 15)
  IO.println s!"increment direct: {repr r}"

/-- Single mut_call. -/
def testCall1 : IO (String × Nat) :=
  let count := 0
  mut_do[count : Nat]
    mut_call[count] msg ← increment 5
    return msg

#eval do
  let r ← testCall1
  assert! r == ("incremented by 5", 5)
  IO.println s!"testCall1: {repr r}"

/-- Chained mut_calls. -/
def testCall2 : IO ((String × String) × Nat) :=
  let count := 0
  mut_do[count : Nat]
    mut_call[count] msg1 ← increment 3
    mut_call[count] msg2 ← increment 7
    return (msg1, msg2)

#eval do
  let r ← testCall2
  assert! r == (("incremented by 3", "incremented by 7"), 10)
  IO.println s!"testCall2: {repr r}"

/-- Double twice. -/
def testCall3 : IO (Unit × Nat) :=
  let x := 5
  mut_do[x : Nat]
    mut_call[x] u1 ← doubleM
    mut_call[x] u2 ← doubleM
    return ()

#eval do
  let r ← testCall3
  assert! r == ((), 20)
  IO.println s!"testCall3: {repr r}"

/-- Non-captured mutvars stay in scope across mut_calls. -/
def testCall4 : IO (Nat × Nat) :=
  let x := 5
  mut_do[x : Nat]
    let mut y := 0
    mut_call[x] u1 ← doubleM
    y := y + 1
    mut_call[x] u2 ← doubleM
    y := y + 1
    return y

#eval do
  let r ← testCall4
  -- x: 5 → 10 → 20, y: 0 → 1 → 2
  assert! r == (2, 20)
  IO.println s!"testCall4: {repr r}"

end CallTests

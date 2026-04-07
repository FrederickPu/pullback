import Lean
open Lean

/-!
# `mut_do` — do-notation with mutable variables and a continuation wrapper

## Full form

```
mut_do[k; x : Nat, y : String]
  x := x + 1
  y := y ++ "!"
  return 42
```

Expands to:

```
do
  let mut x : Nat := x      -- shadows the outer `x`, initialised from it
  let mut y : String := y
  x := x + 1
  y := y ++ "!"
  return (k (x, y) 42)      -- every return is wrapped with k applied to the mut-tuple
```

The continuation `k : MutTuple → RetVal → FinalOut` receives the final
mutable state and the returned value.

The variable names in the binders must already be in scope — they provide
the initial values for the mutable bindings.

## Simple form

`mut_do[f]` (no semicolon, no binders): every `return e` becomes `return (f e)`.
-/

namespace MutDo

-- ============================================================
-- Helpers
-- ============================================================

/-- Build a tuple expression from variable idents.
    0 vars → `()`
    1 var  → `x`
    2 vars → `(x, y)`
    3 vars → `(x, y, z)`   (i.e. `(x, (y, z))`) -/
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

/-- Rewrite `return e` → `return (k (x₁, ..., xₙ) e)`.

    doReturn structure (from syntax dump):
      NODE[Lean.Parser.Term.doReturn]
        ATOM: "return"
        NODE[null]
          <expr>
-/
partial def rewriteReturnsK (k : TSyntax `term) (varNames : Array Syntax)
    : Syntax → MacroM Syntax
  | .node info kind args => do
    if kind == ``Lean.Parser.Term.doReturn && args.size == 2 then
      let nullNode := args[1]!
      match nullNode with
      | .node nullInfo nullKind nullArgs =>
        if nullArgs.size > 0 then
          let innerExpr ← rewriteReturnsK k varNames nullArgs[0]!
          let innerTerm : TSyntax `term := ⟨innerExpr⟩
          let tup ← mkTupleStx varNames
          let wrapped ← `(($k $tup $innerTerm))
          let newNullNode := Syntax.node nullInfo nullKind (nullArgs.set! 0 wrapped.raw)
          return .node info kind (args.set! 1 newNullNode)
        else
          return .node info kind args
      | _ =>
        return .node info kind args
    else
      let newArgs ← args.mapM (rewriteReturnsK k varNames)
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

end MutDo

-- ============================================================
-- Syntax
-- ============================================================

syntax mutBinder := ident " : " term

/-- Full form with continuation and mutable binders -/
syntax "mut_do" "[" term " ; " mutBinder,+ "]" doSeq : term

/-- Simple form -/
syntax "mut_do" "[" term "]" doSeq : term

-- ============================================================
-- Macro rules
-- ============================================================

macro_rules
  | `(mut_do[ $f ] $seq) => do
    let seq' ← MutDo.rewriteReturns f (seq : Syntax)
    let tsSeq : TSyntax `Lean.Parser.Term.doSeq := ⟨seq'⟩
    `(do $tsSeq)

macro_rules
  | `(mut_do[ $k ; $binders,* ] $seq) => do
    let binders := binders.getElems
    let mut varNames : Array (TSyntax `ident) := #[]
    let mut varTypes : Array (TSyntax `term) := #[]
    for b in binders do
      let name : TSyntax `ident := ⟨b.raw[0]⟩
      let ty : TSyntax `term := ⟨b.raw[2]⟩
      varNames := varNames.push name
      varTypes := varTypes.push ty
    -- Rewrite returns: `return e` → `return (k (vars...) e)`
    let varNamesSyntax : Array Syntax := varNames.map (·.raw)
    let seq' ← MutDo.rewriteReturnsK k varNamesSyntax (seq : Syntax)
    -- Build `let mut` doSeqItems by creating a dummy do block and extracting the item.
    -- A doSeq has structure:
    --   NODE[doSeqIndent]
    --     NODE[null] [doSeqItem, doSeqItem, ...]
    -- We extract doSeqItems from helper do blocks.
    let mut letMutItems : Array Syntax := #[]
    for i in [:varNames.size] do
      let n := varNames[i]!
      let t := varTypes[i]!
      -- Build `do let mut n : t := n; pure ()` and extract the first doSeqItem
      let helper ← `(do let mut $n : $t := $n; pure ())
      -- helper is a `do` term: NODE[do] [ATOM "do", doSeqIndent]
      -- doSeqIndent: NODE[doSeqIndent] [NODE[null] [item1, item2]]
      let doSeqIndent := helper.raw[1]  -- the doSeqIndent
      let nullNode := doSeqIndent[0]     -- the null node
      let firstItem := nullNode[0]       -- the first doSeqItem (let mut ...)
      letMutItems := letMutItems.push firstItem
    -- Now prepend these items to the rewritten seq's item list
    -- seq' structure: NODE[doSeqIndent] [NODE[null] [items...]]
    match seq' with
    | .node seqInfo seqKind #[.node nullInfo nullKind bodyItems] =>
      let allItems := letMutItems ++ bodyItems
      let newNull := Syntax.node nullInfo nullKind allItems
      let newSeq : TSyntax `Lean.Parser.Term.doSeq := ⟨Syntax.node seqInfo seqKind #[newNull]⟩
      `(do $newSeq)
    | _ =>
      -- Fallback: shouldn't happen but just in case
      let tsSeq : TSyntax `Lean.Parser.Term.doSeq := ⟨seq'⟩
      `(do $tsSeq)

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
  IO.println s!"testSimple1: {repr r}"  -- some 42

def double (n : Nat) : Nat := n * 2

def testSimple2 : IO Nat :=
  mut_do[double]
    let x ← pure 21
    return x

#eval do
  let r ← testSimple2
  assert! r == 42
  IO.println s!"testSimple2: {repr r}"  -- 42

def testSimple3 (xs : List Nat) : IO (Option Nat) :=
  mut_do[Option.some]
    for x in xs do
      if x > 10 then
        return x
    return 0

#eval do
  let r ← testSimple3 [3, 5, 15, 20]
  assert! r == some 15
  IO.println s!"testSimple3 (match): {repr r}"  -- some 15
  let r2 ← testSimple3 [1, 2, 3]
  assert! r2 == some 0
  IO.println s!"testSimple3 (no match): {repr r2}"  -- some 0

end SimpleTests

-- ============================================================
-- Tests: full form with mutable binders
-- ============================================================

section MutTests

/-- Single mutable var. `count` starts at 0, gets incremented twice.
    Continuation packs the final count with the return value. -/
def testMut1 : IO (Nat × String) :=
  let count := 0
  let k := fun (count : Nat) (msg : String) => (count, msg)
  mut_do[k; count : Nat]
    count := count + 1
    count := count + 1
    return "done"

#eval do
  let r ← testMut1
  assert! r == (2, "done")
  IO.println s!"testMut1: {repr r}"  -- (2, "done")

/-- Two mutable vars. -/
def testMut2 : IO (Nat × Nat × String) :=
  let x := 1
  let y := 2
  let k := fun ((x, y) : Nat × Nat) (msg : String) => (x, y, msg)
  mut_do[k; x : Nat, y : Nat]
    x := x + 10
    y := y + 20
    return "hello"

#eval do
  let r ← testMut2
  assert! r == (11, 22, "hello")
  IO.println s!"testMut2: {repr r}"  -- (11, 22, "hello")

/-- Mutable var with early return from a loop. -/
def testMut3 (threshold : Nat) : IO (Nat × Bool) :=
  let acc := 0
  let k := fun (acc : Nat) (found : Bool) => (acc, found)
  mut_do[k; acc : Nat]
    for i in [0:5] do
      acc := acc + i
      if acc > threshold then
        return true
    return false

#eval do
  -- 0+0+1+2+3+4 = 10, never exceeds 100
  let r1 ← testMut3 100
  assert! r1.2 == false
  assert! r1.1 == 10
  IO.println s!"testMut3 (no early): {repr r1}"  -- (10, false)
  -- 0+0+1+2 = 3, then +3 = 6 > 3, early return
  let r2 ← testMut3 3
  assert! r2.2 == true
  IO.println s!"testMut3 (early): {repr r2}"

/-- Three mutable vars. -/
def testMut4 : IO (Nat × String × Bool × Unit) :=
  let a := 0
  let b := "hello"
  let c := false
  let k := fun ((a, b, c) : Nat × String × Bool) (u : Unit) => (a, b, c, u)
  mut_do[k; a : Nat, b : String, c : Bool]
    a := a + 42
    b := b ++ " world"
    c := !c
    return ()

#eval do
  let r ← testMut4
  assert! r == (42, "hello world", true, ())
  IO.println s!"testMut4: {repr r}"  -- (42, "hello world", true, ())

/-- Mutable var with conditional mutation. -/
def testMut5 (xs : List Nat) : IO (Nat × Nat × Nat) :=
  let sum := 0
  let count := 0
  let k := fun ((sum, count) : Nat × Nat) (max : Nat) => (sum, count, max)
  mut_do[k; sum : Nat, count : Nat]
    let mut max := 0
    for x in xs do
      sum := sum + x
      count := count + 1
      if x > max then
        max := x
    return max

#eval do
  let r ← testMut5 [3, 7, 1, 9, 2]
  assert! r == (22, 5, 9)
  IO.println s!"testMut5: {repr r}"  -- (22, 5, 9)

end MutTests

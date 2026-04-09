import Lean
open Lean

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
-- Syntax scanning
-- ============================================================

partial def collectIdents : Syntax → NameSet
  | .ident _ _ n _ => NameSet.empty.insert n
  | .node _ _ args => args.foldl (fun acc a => acc.merge (collectIdents a)) NameSet.empty
  | _ => NameSet.empty

def containsAnyOf (stx : Syntax) (names : NameSet) : Bool :=
  let idents := collectIdents stx
  names.any fun n => idents.contains n

partial def replaceIdent (stx : Syntax) (name : Name) (replacement : Syntax) : Syntax :=
  match stx with
  | .ident _ _ n _ => if n == name then replacement else stx
  | .node info kind args => .node info kind (args.map (replaceIdent · name replacement))
  | other => other

partial def substOnce (stx : Syntax) (m : NameMap Syntax) : Syntax :=
  match stx with
  | .ident _ _ n _ => match m.find? n with | some repl => repl | none => stx
  | .node info kind args => .node info kind (args.map (substOnce · m))
  | other => other

partial def inlineMutDeps (stx : Syntax) (m : NameMap Syntax) (fuel : Nat := 20) : Syntax :=
  if fuel == 0 then stx
  else
    let stx' := substOnce stx m
    if toString stx' == toString stx then stx
    else inlineMutDeps stx' m (fuel - 1)

partial def findMutVar (stx : Syntax) (mutVars : NameSet) : Option Name :=
  match stx with
  | .ident _ _ n _ => if mutVars.contains n then some n else none
  | .node _ _ args => args.findSome? (findMutVar · mutVars)
  | _ => none

def resolveAccessor (expr : Syntax) (mutVars : NameSet) (inlineMap : NameMap Syntax)
    : MacroM (Name × TSyntax `term) := do
  let inlined := inlineMutDeps expr inlineMap
  match findMutVar inlined mutVars with
  | some mutName =>
    if inlined.isIdent && inlined.getId == mutName then
      return (mutName, ← `(id))
    else
      let freshVar := mkIdent `_mv
      let body := replaceIdent inlined mutName freshVar
      let bodyTerm : TSyntax `term := ⟨body⟩
      let freshId : TSyntax `ident := freshVar
      return (mutName, ← `(fun $freshId => $bodyTerm))
  | none =>
    Macro.throwError s!"mut_call: no mutable variable found in expression after inlining"

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

/-- Build a `let name := rhs` doSeqItem by creating a template and replacing parts. -/
def mkLetItem (name : TSyntax `ident) (rhs : Syntax) : MacroM Syntax := do
  let helper ← `(do let _placeholder := (); pure ())
  let item := helper.raw[1][0][0]  -- first doSeqItem
  -- item[0] = doLet node
  let doLet := item[0]
  -- doLet[2] = letDecl, letDecl[0] = letIdDecl
  let letDecl := doLet[2]
  let letIdDecl := letDecl[0]
  -- letIdDecl: [letId[ident], null, null, ":=", rhs]
  -- Replace the ident inside letId
  let letId := letIdDecl[0]
  let newLetId := match letId with
    | .node info kind _ => Syntax.node info kind #[name.raw]
    | other => other
  let letIdDecl := letIdDecl.setArg 0 newLetId
  -- Replace the rhs (index 4)
  let letIdDecl := letIdDecl.setArg 4 rhs
  let letDecl := letDecl.setArg 0 letIdDecl
  let doLet := doLet.setArg 2 letDecl
  let item := item.setArg 0 doLet
  return item

-- ============================================================
-- Let binding analysis
--
-- From syntax dump, doLet structure is:
--   NODE[doLet]
--     ATOM "let"
--     NODE[null] []                       -- [1] may contain "mut" atom
--     NODE[letDecl]                       -- [2]
--       NODE[letIdDecl]
--         NODE[letId]                     -- [0] wrapper around the ident
--           IDENT "name"
--         NODE[null] []                   -- [1] optional binders
--         NODE[null] []                   -- [2] optional type
--         ATOM ":="                       -- [3]
--         <rhs expr>                      -- [4]
-- ============================================================

private def isMutAtom : Syntax → Bool
  | .atom _ val => val == "mut"
  | _ => false

/-- Find the first ident in a syntax tree. -/
private partial def findFirstIdent : Syntax → Option Name
  | .ident _ _ n _ => some n
  | .node _ _ args => args.findSome? findFirstIdent
  | _ => none

/-- Extract (name, rhs, isMut) from a doLet doElem. -/
def extractLetInfo (doElem : Syntax) : Option (Name × Syntax × Bool) := Id.run do
  unless doElem.isOfKind ``Lean.Parser.Term.doLet do return none
  let args := doElem.getArgs
  unless args.size ≥ 3 do return none
  -- args[1] = null node that may contain "mut"
  let hasMut := match args[1]! with
    | .node _ _ subArgs => subArgs.any isMutAtom
    | _ => false
  -- args[2] = letDecl
  let letDecl := args[2]!
  unless letDecl.getArgs.size ≥ 1 do return none
  let letIdDecl := letDecl[0]
  unless letIdDecl.isOfKind ``Lean.Parser.Term.letIdDecl do return none
  let idDeclArgs := letIdDecl.getArgs
  -- idDeclArgs[0] = letId (contains the ident)
  -- idDeclArgs[4] = rhs (after letId, null, null, ":=")
  unless idDeclArgs.size ≥ 5 do return none
  let some name := findFirstIdent idDeclArgs[0]! | return none
  let rhs := idDeclArgs[4]!
  return some (name, rhs, hasMut)

-- ============================================================
-- mut_call detection and parsing
-- ============================================================

private partial def hasMutCallAtom : Syntax → Bool
  | .atom _ val => val == "mut_call"
  | .node _ _ args => args.any hasMutCallAtom
  | _ => false

private def isMutCallNode (doElem : Syntax) : Bool :=
  hasMutCallAtom doElem

/-- Parse a mut_call doElem: extract (mutExprs, resultVar, funcExpr). -/
private def parseMutCall (doElem : Syntax) : Option (Array Syntax × Syntax × Syntax) :=
  match doElem with
  | .node _ _ args => Id.run do
    let mut inBracket := false
    let mut mutExprs : Array Syntax := #[]
    let mut resultVar : Option Syntax := none
    let mut pastArrow := false
    let mut funcExpr : Option Syntax := none
    for arg in args do
      match arg with
      | .atom _ "[" => inBracket := true
      | .atom _ "]" => inBracket := false
      | .atom _ "←" => pastArrow := true
      | _ =>
        if inBracket then
          if !arg.isAtom then
            match arg with
            | .node _ _ subArgs =>
              for sub in subArgs do
                if !sub.isAtom then mutExprs := mutExprs.push sub
            | _ => mutExprs := mutExprs.push arg
        else if pastArrow then
          if funcExpr.isNone && !arg.isAtom then
            funcExpr := some arg
        else
          if arg.isIdent && resultVar.isNone then
            resultVar := some arg
    match resultVar, funcExpr with
    | some rv, some fe => some (mutExprs, rv, fe)
    | _, _ => none
  | _ => none

/-- Expand a mut_call doElem using scope info. Returns a replacement doSeqItem. -/
def expandMutCallWithScope (doElem : Syntax) (mutVars : NameSet) (inlineMap : NameMap Syntax)
    : MacroM (Option Syntax) := do
  unless isMutCallNode doElem do return none
  let some (mutExprs, resultVar, funcExpr) := parseMutCall doElem | return none
  let v : TSyntax `ident := ⟨resultVar⟩
  let f : TSyntax `term := ⟨funcExpr⟩
  let mut baseVars : Array (TSyntax `ident) := #[]
  let mut accessors : Array (TSyntax `term) := #[]
  for expr in mutExprs do
    let (mutName, acc) ← resolveAccessor expr mutVars inlineMap
    baseVars := baseVars.push (mkIdent mutName)
    accessors := accessors.push acc
  let mut allIdents : Array (TSyntax `ident) := #[v]
  for bv in baseVars do
    allIdents := allIdents.push bv
  let pat ← mkTupleStx (allIdents.map (·.raw))
  let mut callExpr : TSyntax `term := f
  for i in [:baseVars.size] do
    let bvTerm : TSyntax `term := ⟨baseVars[i]!.raw⟩
    let accTerm := accessors[i]!
    callExpr ← `($callExpr $bvTerm $accTerm)
  let item ← mkLetBindItem pat.raw callExpr.raw
  return some item

-- ============================================================
-- Unified rewriting (mutual recursion)
-- ============================================================

mutual

partial def processDoSeqItems (items : Array Syntax) (mutVars : NameSet)
    (inlineMap : NameMap Syntax) (mutVarNames : Array Syntax)
    : MacroM (Array Syntax) := do
  let mut result : Array Syntax := #[]
  let mut mvs := mutVars
  let mut imap := inlineMap
  -- Track the order of inline map entries so we re-emit in the right order
  let mut imapOrder : Array Name := #[]
  for item in items do
    let doElem := item[0]
    -- Try mut_call expansion with scope info
    match ← expandMutCallWithScope doElem mvs imap with
    | some expandedItem =>
      result := result.push expandedItem
      -- Re-emit all mut-dependent let bindings after the mutation
      -- so they reflect the updated state
      for name in imapOrder do
        if let some rhs := imap.find? name then
          let letItem ← mkLetItem (mkIdent name) rhs
          result := result.push letItem
    | none =>
      -- Check for let bindings to track scope
      match extractLetInfo doElem with
      | some (name, _rhs, true) =>
        -- let mut: add to mut vars
        mvs := mvs.insert name
        let rewritten ← rewriteNode mvs imap mutVarNames item
        result := result.push rewritten
      | some (name, rhs, false) =>
        -- normal let: track if it depends on mut vars
        let allDep := mvs.merge (NameSet.ofList (imap.toList.map (·.1)))
        if containsAnyOf rhs allDep then
          imap := imap.insert name rhs
          imapOrder := imapOrder.push name
        let rewritten ← rewriteNode mvs imap mutVarNames item
        result := result.push rewritten
      | none =>
        let rewritten ← rewriteNode mvs imap mutVarNames item
        result := result.push rewritten
  return result

partial def rewriteNode (mutVars : NameSet) (inlineMap : NameMap Syntax)
    (mutVarNames : Array Syntax) : Syntax → MacroM Syntax
  | .node info kind args => do
    if kind == ``Lean.Parser.Term.doReturn && args.size == 2 then
      let nullNode := args[1]!
      match nullNode with
      | .node nullInfo nullKind nullArgs =>
        if nullArgs.size > 0 then
          let innerExpr ← rewriteNode mutVars inlineMap mutVarNames nullArgs[0]!
          let innerTerm : TSyntax `term := ⟨innerExpr⟩
          let allElems := #[innerTerm.raw] ++ mutVarNames
          let tup ← mkTupleStx allElems
          return .node info kind (args.set! 1
            (Syntax.node nullInfo nullKind (nullArgs.set! 0 tup.raw)))
        else
          let unit ← `(())
          let allElems := #[unit.raw] ++ mutVarNames
          let tup ← mkTupleStx allElems
          return .node info kind (args.set! 1
            (Syntax.node SourceInfo.none `null #[tup.raw]))
      | _ => return .node info kind args
    else if kind == ``Lean.Parser.Term.doSeqIndent then
      match args with
      | #[.node nullInfo nullKind items] =>
        let newItems ← processDoSeqItems items mutVars inlineMap mutVarNames
        return .node info kind #[Syntax.node nullInfo nullKind newItems]
      | _ =>
        let newArgs ← args.mapM (rewriteNode mutVars inlineMap mutVarNames)
        return .node info kind newArgs
    else
      let newArgs ← args.mapM (rewriteNode mutVars inlineMap mutVarNames)
      return .node info kind newArgs
  | other => return other

end

end MutDo

-- ============================================================
-- Syntax
-- ============================================================

syntax mutBinder := ident " : " term

syntax:lead "mut" "[" mutBinder,+ "]" doSeq : term
syntax:lead "mut_call" "[" term,+ "]" ident " ← " term : doElem
syntax:lead "let" ident "←" term "⟦" term+ "⟧" : doElem

-- ============================================================
-- Macro rules
-- ============================================================

macro_rules
  | `(mut[ $binders,* ] $seq) => do
    let binders := binders.getElems
    let mut varNames : Array (TSyntax `ident) := #[]
    let mut varTypes : Array (TSyntax `term) := #[]
    let mut initMutVars : NameSet := {}
    for b in binders do
      let name : TSyntax `ident := ⟨b.raw[0]⟩
      let ty : TSyntax `term := ⟨b.raw[2]⟩
      varNames := varNames.push name
      varTypes := varTypes.push ty
      initMutVars := initMutVars.insert name.getId
    let varNamesSyntax : Array Syntax := varNames.map (·.raw)
    let seq' ← MutDo.rewriteNode initMutVars {} varNamesSyntax (seq : Syntax)
    let mut letMutItems : Array Syntax := #[]
    for i in [:varNames.size] do
      let item ← MutDo.mkLetMutItem varNames[i]! varTypes[i]!
      letMutItems := letMutItems.push item
    let bodyItems := MutDo.getDoSeqItems seq'
    let allItems := letMutItems ++ bodyItems
    let newSeq : TSyntax `Lean.Parser.Term.doSeq :=
      ⟨MutDo.mkDoSeqIndent seq' allItems⟩
    `(do $newSeq)

/-- Standalone mut_call fallback for use outside mut[] blocks. -/
macro_rules
  | `(doElem| mut_call[ $mutExprs,* ] $v:ident ← $f:term) => do
    let mut baseVars : Array (TSyntax `ident) := #[]
    let mut accessors : Array (TSyntax `term) := #[]
    for expr in mutExprs.getElems do
      if expr.raw.isIdent then
        baseVars := baseVars.push ⟨expr.raw⟩
        accessors := accessors.push (← `(id))
      else
        Macro.throwError "mut_call outside mut[]: complex expressions need scope info. Use inside a mut[] block."
    let mut allIdents : Array (TSyntax `ident) := #[v]
    for bv in baseVars do
      allIdents := allIdents.push bv
    let pat ← MutDo.mkTupleStx (allIdents.map (·.raw))
    let mut callExpr : TSyntax `term := f
    for i in [:baseVars.size] do
      let bvTerm : TSyntax `term := ⟨baseVars[i]!.raw⟩
      let accTerm := accessors[i]!
      callExpr ← `($callExpr $bvTerm $accTerm)
    let item ← MutDo.mkLetBindItem pat.raw callExpr.raw
    let doElem : TSyntax `doElem := ⟨item[0]⟩
    return doElem

-- ============================================================
-- Tests: mut basics
-- ============================================================

section MutTests

def testMut1 : IO (String × Nat) :=
  let count := 0
  mut[count : Nat]
    count := count + 1
    count := count + 1
    return "done"

#eval do
  let r ← testMut1
  assert! r == ("done", 2)
  IO.println s!"testMut1: {repr r}"

def testMut2 : IO (String × Nat × Nat) :=
  let x := 1
  let y := 2
  mut[x : Nat, y : Nat]
    x := x + 10
    y := y + 20
    return "hello"

#eval do
  let r ← testMut2
  assert! r == ("hello", 11, 22)
  IO.println s!"testMut2: {repr r}"

def testMut3 (threshold : Nat) : IO (Bool × Nat) :=
  let acc := 0
  mut[acc : Nat]
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

end MutTests

-- ============================================================
-- Tests: simple mut_call
-- ============================================================

section SimpleCallTests

def increment (amount : Nat) (count : Nat) (_k : Nat → Nat) : IO (String × Nat) :=
  mut[count : Nat]
    count := count + amount
    return s!"incremented by {amount}"

def doubleM (x : Nat) (_k : Nat → Nat) : IO (Unit × Nat) :=
  mut[x : Nat]
    x := x * 2
    return ()

#eval do
  let r ← increment 5 10 id
  assert! r == ("incremented by 5", 15)
  IO.println s!"increment direct: {repr r}"

def testCall1 : IO (String × Nat) :=
  let count := 0
  mut[count : Nat]
    mut_call[count] msg ← increment 5
    return msg

#eval do
  let r ← testCall1
  assert! r == ("incremented by 5", 5)
  IO.println s!"testCall1: {repr r}"

def testCall2 : IO ((String × String) × Nat) :=
  let count := 0
  mut[count : Nat]
    mut_call[count] msg1 ← increment 3
    mut_call[count] msg2 ← increment 7
    return (msg1, msg2)

#eval do
  let r ← testCall2
  assert! r == (("incremented by 3", "incremented by 7"), 10)
  IO.println s!"testCall2: {repr r}"

def testCall3 : IO (Unit × Nat) :=
  let x := 5
  mut[x : Nat]
    mut_call[x] u1 ← doubleM
    mut_call[x] u2 ← doubleM
    return ()

#eval do
  let r ← testCall3
  assert! r == ((), 20)
  IO.println s!"testCall3: {repr r}"

end SimpleCallTests

-- ============================================================
-- Tests: accessor + inline
-- ============================================================

section InlineTests

/-- Read a field from base via accessor. Returns (value, base unchanged). -/
def readField (base : Nat × Nat) (k : Nat × Nat → Nat) : IO (Nat × Nat × Nat) := do
  pure (k base, base)

/-- Set a field in base via accessor. The accessor tells us which field to read;
    we set that field to `newVal`. Since we know it's a Nat × Nat, we check
    which field the accessor points to. -/
def setField (newVal : Nat) (base : Nat × Nat) (k : Nat × Nat → Nat) : IO (Unit × Nat × Nat) := do
  -- Figure out which field k points to by testing
  let testA := k (1, 0)
  let testB := k (0, 1)
  if testA == 1 then
    -- k selects fst
    pure ((), (newVal, base.2))
  else if testB == 1 then
    -- k selects snd
    pure ((), (base.1, newVal))
  else
    -- fallback: just return unchanged
    pure ((), base)

/-- Direct accessor: Prod.fst state -/
def testInline1 : IO (Nat × Nat × Nat) :=
  let state := (10, 20)
  mut[state : Nat × Nat]
    mut_call[Prod.fst state] val ← readField
    return val

#eval do
  let r ← testInline1
  assert! r == (10, 10, 20)
  IO.println s!"testInline1: {repr r}"

/-- Accessor via let that depends on mut var. -/
def testInline2 : IO (Nat × Nat × Nat) :=
  let state := (10, 20)
  mut[state : Nat × Nat]
    let derived := Prod.fst state
    mut_call[derived] val ← readField
    return val

#eval do
  let r ← testInline2
  assert! r == (10, 10, 20)
  IO.println s!"testInline2: {repr r}"

/-- Chained let inlining. -/
def testInline3 : IO (Nat × Nat × Nat) :=
  let state := (10, 20)
  mut[state : Nat × Nat]
    let pair := state
    let fstVal := Prod.fst pair
    mut_call[fstVal] val ← readField
    return val

#eval do
  let r ← testInline3
  assert! r == (10, 10, 20)
  IO.println s!"testInline3: {repr r}"

/-- SET fst to 99 via direct accessor, confirm state changes. -/
def testSet1 : IO (Unit × Nat × Nat) :=
  let state := (10, 20)
  mut[state : Nat × Nat]
    mut_call[Prod.fst state] u ← setField 99
    return ()

#eval do
  let r ← testSet1
  -- state.fst should be 99, snd unchanged
  assert! r == ((), 99, 20)
  IO.println s!"testSet1: {repr r}"

/-- SET snd to 42 via accessor. -/
def testSet2 : IO (Unit × Nat × Nat) :=
  let state := (10, 20)
  mut[state : Nat × Nat]
    mut_call[Prod.snd state] u ← setField 42
    return ()

#eval do
  let r ← testSet2
  assert! r == ((), 10, 42)
  IO.println s!"testSet2: {repr r}"

/-- SET via let-inlined accessor. -/
def testSet3 : IO (Unit × Nat × Nat) :=
  let state := (10, 20)
  mut[state : Nat × Nat]
    let fstAccessor := Prod.fst state
    mut_call[fstAccessor] u ← setField 77
    return ()

#eval do
  let r ← testSet3
  assert! r == ((), 77, 20)
  IO.println s!"testSet3: {repr r}"

/-- SET fst then SET snd — two mutations in sequence. -/
def testSet4 : IO (Unit × Nat × Nat) :=
  let state := (10, 20)
  mut[state : Nat × Nat]
    mut_call[Prod.fst state] u1 ← setField 100
    mut_call[Prod.snd state] u2 ← setField 200
    return ()

#eval do
  let r ← testSet4
  assert! r == ((), 100, 200)
  IO.println s!"testSet4: {repr r}"

/-- SET via chained let inlining, then read to confirm. -/
def testSet5 : IO (Nat × Nat × Nat) :=
  let state := (10, 20)
  mut[state : Nat × Nat]
    let pair := state
    let fstVal := Prod.fst pair
    IO.println fstVal -- 10
    mut_call[fstVal] u ← setField 55
    IO.println fstVal -- 55
    -- Read after mutation — should see updated value
    mut_call[Prod.fst state] val ← readField
    return val

#eval do
  let r ← testSet5
  assert! r == (55, 55, 20)
  IO.println s!"testSet5: {repr r}"

end InlineTests

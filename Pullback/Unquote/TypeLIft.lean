import Lean

universe u v w t

/-! # TypeLift: automatic universe cumulativity -/

class TypeLift (A : Type u) (B : outParam (Type w)) where
  up   : A → B
  down : B → A
  roundtrip : ∀ a, down (up a) = a

instance : TypeLift.{u, max u w} A (ULift.{max u w, u} A) where
  up   := ULift.up
  down := ULift.down
  roundtrip _ := rfl

instance : TypeLift.{u, u} A A where
  up   := id
  down := id
  roundtrip _ := rfl

instance typeLiftFun [TypeLift.{u, t} A A'] [TypeLift.{v, t} B B']
    : TypeLift (A → B) (A' → B') where
  up   f := fun a' => TypeLift.up (f (TypeLift.down a'))
  down f := fun a  => TypeLift.down (f (TypeLift.up a))
  roundtrip f := by funext a; simp [TypeLift.roundtrip]

def typeLift [TypeLift.{u, w} A B] (a : A) : B := TypeLift.up a
def typeUnlift [TypeLift.{u, w} A B] (b : B) : A := TypeLift.down b
def typeLiftFn {A : Type u} {B : Type v} {A' : Type w} {B' : Type w}
    [TypeLift A A'] [TypeLift B B']
    (f : A → B) : A' → B' :=
  fun a' => TypeLift.up (f (TypeLift.down a'))

/-! ## Deriving handler -/

namespace TypeLift.Deriving

open Lean Elab Command Term Meta Parser.Term

private def getCtorShortName (ctorName : Name) : Name :=
  ctorName.replacePrefix ctorName.getPrefix .anonymous

private def mkLiftArm (env : Environment) (ctorName : Name) (liftFn : TSyntax `term)
    : CommandElabM (TSyntax ``matchAlt) := do
  let some (.ctorInfo ctorVal) := env.find? ctorName
    | throwError "not a constructor: {ctorName}"
  let shortName := getCtorShortName ctorName
  let ctor := mkIdent shortName
  let fieldCount := ctorVal.numFields
  if fieldCount == 0 then
    `(matchAltExpr| | .$ctor:ident => .$ctor:ident)
  else
    let fieldNames ← (Array.range fieldCount).mapM fun i =>
      pure (mkIdent (Name.mkSimple s!"x{i}"))
    let liftedFields ← fieldNames.mapM fun x => `($liftFn $x)
    `(matchAltExpr| | .$ctor:ident $fieldNames* => .$ctor:ident $liftedFields*)

private def mkRoundtripArm (env : Environment) (ctorName : Name)
    : CommandElabM (TSyntax ``matchAlt) := do
  let some (.ctorInfo ctorVal) := env.find? ctorName
    | throwError "not a constructor: {ctorName}"
  let shortName := getCtorShortName ctorName
  let ctor := mkIdent shortName
  let fieldCount := ctorVal.numFields
  if fieldCount == 0 then
    `(matchAltExpr| | .$ctor:ident => rfl)
  else
    let wildcards ← (Array.range fieldCount).mapM fun i =>
      pure (mkIdent (Name.mkSimple s!"_x{i}"))
    `(matchAltExpr| | .$ctor:ident $wildcards* => by simp [TypeLift.up, TypeLift.down, TypeLift.roundtrip])

def mkTypeLiftHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then return false
  let declName := declNames[0]!
  let env ← getEnv
  let some (.inductInfo indVal) := env.find? declName | return false

  -- Get parameter names
  let paramNames ← liftTermElabM do
    forallTelescopeReducing indVal.type fun xs _ => do
      xs.mapM fun x => do
        let ldecl ← x.fvarId!.getDecl
        return ldecl.userName

  let paramIdents := paramNames.map mkIdent
  let paramIdents' := paramNames.map fun n =>
    mkIdent (Name.mkSimple (n.toString ++ "'"))

  -- Build [TypeLift α α'] binders for each param pair
  let mut instBinders : Array (TSyntax ``bracketedBinder) := #[]
  for (p, p') in paramIdents.zip paramIdents' do
    instBinders := instBinders.push (← `(bracketedBinder| [TypeLift $p $p']))

  let typeName := mkIdent declName
  let srcType ← `($typeName $paramIdents*)
  let tgtType ← `($typeName $paramIdents'*)

  -- For recursive types, we define up/down as recursive functions
  -- that call themselves on recursive fields and TypeLift.up/down on others
  let upName := mkIdent (declName ++ `typeLiftUp)
  let downName := mkIdent (declName ++ `typeLiftDown)

  -- Build match arms using the recursive helper names
  let mut upArms : Array (TSyntax ``matchAlt) := #[]
  let mut downArms : Array (TSyntax ``matchAlt) := #[]
  let mut rtArms : Array (TSyntax ``matchAlt) := #[]

  for ctorName in indVal.ctors do
    let some (.ctorInfo ctorVal) := env.find? ctorName
      | throwError "not a constructor: {ctorName}"
    let shortName := getCtorShortName ctorName
    let ctor := mkIdent shortName
    let fieldCount := ctorVal.numFields

    if fieldCount == 0 then
      upArms := upArms.push (← `(matchAltExpr| | .$ctor:ident => .$ctor:ident))
      downArms := downArms.push (← `(matchAltExpr| | .$ctor:ident => .$ctor:ident))
      rtArms := rtArms.push (← `(matchAltExpr| | .$ctor:ident => rfl))
    else
      let fieldNames ← (Array.range fieldCount).mapM fun i =>
        pure (mkIdent (Name.mkSimple s!"x{i}"))
      let rtFieldNames ← (Array.range fieldCount).mapM fun i =>
        pure (mkIdent (Name.mkSimple s!"_x{i}"))

      -- For each field, check if it's a recursive occurrence of the type being defined
      -- by inspecting the constructor type
      let mut upFields : Array (TSyntax `term) := #[]
      let mut downFields : Array (TSyntax `term) := #[]
      let ctorType := ctorVal.type
      let mut ty := ctorType
      -- Skip parameters
      for _ in [:indVal.numParams] do
        ty := ty.bindingBody!
      -- Now walk the fields
      for i in [:fieldCount] do
        let fieldType := ty.bindingDomain!
        ty := ty.bindingBody!
        let x := fieldNames[i]!
        -- Check if this field's type is an application of the inductive being defined
        let isRecursive := fieldType.getAppFn.isConstOf declName
        if isRecursive then
          upFields := upFields.push (← `($upName $x))
          downFields := downFields.push (← `($downName $x))
        else
          upFields := upFields.push (← `(TypeLift.up $x))
          downFields := downFields.push (← `(TypeLift.down $x))

      upArms := upArms.push (← `(matchAltExpr| | .$ctor:ident $fieldNames* => .$ctor:ident $upFields*))
      downArms := downArms.push (← `(matchAltExpr| | .$ctor:ident $fieldNames* => .$ctor:ident $downFields*))
      let upSimpLemma : TSyntax ``Lean.Parser.Tactic.simpLemma ← `(Lean.Parser.Tactic.simpLemma| $upName:ident)
      let downSimpLemma : TSyntax ``Lean.Parser.Tactic.simpLemma ← `(Lean.Parser.Tactic.simpLemma| $downName:ident)
      rtArms := rtArms.push (← `(matchAltExpr| | .$ctor:ident $rtFieldNames* => by simp [TypeLift.up, TypeLift.down, TypeLift.roundtrip, $upSimpLemma, $downSimpLemma]))

  let rtName := mkIdent (declName ++ `typeLiftRoundtrip)

  -- Build roundtrip match arms that use the recursive roundtrip for recursive fields
  let mut rtArms2 : Array (TSyntax ``matchAlt) := #[]
  for ctorName in indVal.ctors do
    let some (.ctorInfo ctorVal) := env.find? ctorName
      | throwError "not a constructor: {ctorName}"
    let shortName := getCtorShortName ctorName
    let ctor := mkIdent shortName
    let fieldCount := ctorVal.numFields

    if fieldCount == 0 then
      rtArms2 := rtArms2.push (← `(matchAltExpr| | .$ctor:ident => rfl))
    else
      let fieldNames ← (Array.range fieldCount).mapM fun i =>
        pure (mkIdent (Name.mkSimple s!"x{i}"))

      -- Check which fields are recursive
      let mut ty := ctorVal.type
      for _ in [:indVal.numParams] do
        ty := ty.bindingBody!

      let mut congArgs : Array (TSyntax `term) := #[]
      let mut hasRecursive := false
      for i in [:fieldCount] do
        let fieldType := ty.bindingDomain!
        ty := ty.bindingBody!
        let x := fieldNames[i]!
        let isRecursive := fieldType.getAppFn.isConstOf declName
        if isRecursive then
          hasRecursive := true
          congArgs := congArgs.push (← `($rtName $x))
        else
          congArgs := congArgs.push (← `(TypeLift.roundtrip $x))

      if hasRecursive then
        let upSimpLemma : TSyntax ``Lean.Parser.Tactic.simpLemma ← `(Lean.Parser.Tactic.simpLemma| $upName:ident)
        let downSimpLemma : TSyntax ``Lean.Parser.Tactic.simpLemma ← `(Lean.Parser.Tactic.simpLemma| $downName:ident)
        let rtSimpLemma : TSyntax ``Lean.Parser.Tactic.simpLemma ← `(Lean.Parser.Tactic.simpLemma| $rtName:ident)
        rtArms2 := rtArms2.push (← `(matchAltExpr| | .$ctor:ident $fieldNames* => by simp [$upSimpLemma, $downSimpLemma, TypeLift.roundtrip, $rtSimpLemma]))
      else
        let upSimpLemma : TSyntax ``Lean.Parser.Tactic.simpLemma ← `(Lean.Parser.Tactic.simpLemma| $upName:ident)
        let downSimpLemma : TSyntax ``Lean.Parser.Tactic.simpLemma ← `(Lean.Parser.Tactic.simpLemma| $downName:ident)
        rtArms2 := rtArms2.push (← `(matchAltExpr| | .$ctor:ident $fieldNames* => by simp [$upSimpLemma, $downSimpLemma, TypeLift.roundtrip]))

  let upBody ← `(fun $upArms:matchAlt*)
  let downBody ← `(fun $downArms:matchAlt*)

  let cmdUp ← `(
    def $upName $[$instBinders]* : $srcType → $tgtType := $upBody
  )
  let cmdDown ← `(
    def $downName $[$instBinders]* : $tgtType → $srcType := $downBody
  )
  let cmdRt ← `(
    @[simp] theorem $rtName $[$instBinders]* : (x : $srcType) → $downName ($upName x) = x $rtArms2:matchAlt*
  )
  let cmdInst ← `(
    instance $[$instBinders]* : TypeLift $srcType $tgtType where
      up := $upName
      down := $downName
      roundtrip := $rtName
  )
  elabCommand cmdUp
  elabCommand cmdDown
  elabCommand cmdRt
  elabCommand cmdInst
  return true

initialize registerDerivingHandler ``TypeLift mkTypeLiftHandler

end TypeLift.Deriving

/-! ## Context -/

def Ctx.{uu} := List (Type uu)

namespace Ctx
def nil.{uu} : Ctx.{uu} := []
def cons.{uu} (A : Type uu) (ctx : Ctx.{uu}) : Ctx.{uu} := A :: ctx
def lift (ctx : Ctx.{u}) : Ctx.{max u v} :=
  List.map (ULift.{max u v, u} ·) ctx
def append (ctx₁ : Ctx.{u}) (ctx₂ : Ctx.{v}) : Ctx.{max u v} :=
  List.append (ctx₁.lift) (ctx₂.lift)
end Ctx

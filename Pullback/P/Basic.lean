import Lean

open Lean

inductive PType (BaseType : Type) where
| ofBase : BaseType → PType BaseType
| fun : PType BaseType → PType BaseType → PType BaseType

/-
`Typed α A` means that each element `a` of `α` can be `A` typed (uniquely assigned a type `T : A`)
-/
class Typed (α A : Type) where
  type : α → A

class BasedType (BaseType : Type) where
  valueType : BaseType → Type

def BaseConst (BaseType : Type) [BasedType BaseType] := Σ (x : BaseType), BasedType.valueType x

class Dialect (dialect : (BaseType : Type) → Type) where
  typed : (BaseType : Type) → [BasedType BaseType] → Typed (dialect BaseType) (PType BaseType)

inductive PExpr (Const BaseType : Type) [Typed Const (PType BaseType)] where
| const : Const → PExpr Const BaseType
| letE (var : Name) (val : PExpr Const BaseType) (body : PExpr Const BaseType) : PExpr Const BaseType
| var (name : Name) : PExpr Const BaseType
| app (f : PExpr Const BaseType) (arg : PExpr Const BaseType)
| lam (varName : Name) (varType : BaseType) (body : PExpr Const BaseType) : PExpr Const BaseType

instance {BaseType Const : Type} [Typed Const (PType BaseType)] : Typed (PExpr Const BaseType) (PType BaseType) := sorry

instance {dialect : (BaseType : Type) → Type} [Dialect dialect] {BaseType : Type} [BasedType BaseType] : Typed (dialect BaseType) (PType BaseType) :=
  Dialect.typed BaseType

instance {BaseType : Type} [BasedType BaseType] {dialect : (BaseType : Type) → Type} [Dialect dialect] : Typed (PExpr (dialect BaseType) BaseType) (PType BaseType) :=
  inferInstance

def PExpr.interp : sorry := sorry

inductive PDo (Const BaseType : Type) [Typed Const (PType BaseType)] where

/-
  adds structured control flow (if statements and loops) to `dialect`
-/
def Dialect.scf (dialect : (BaseType : Type) → Type) : (BaseType : Type) → Type := sorry

instance {dialect : (BaseType : Type) → Type} [Dialect dialect] : Dialect (Dialect.scf dialect) := sorry

#check ToExpr
def PDo.toExpr (dialect : (BaseType : Type) → Type) (BaseType : Type) [BasedType BaseType] [Dialect dialect] :
  PDo (dialect BaseType) BaseType → PExpr (Dialect.scf dialect BaseType) BaseType := sorry

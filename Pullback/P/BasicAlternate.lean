import Lean

open Lean

class BasedType (α : Type) where
  valueType : α → Type

class Typed (α : Type) (A : outParam Type) where
  type : α → A

def natFamilyFromFin {n : Nat} (cs : Fin n → Type) : Nat → Type
| m =>
    if h : m < n then
      cs ⟨m, h⟩
    else if hn : n = 0 then
      PUnit
    else
      cs ⟨0, Nat.pos_of_ne_zero hn⟩

mutual
inductive PExpr (BaseConst : Nat → Type) (BaseType : Type) : Nat → List BaseType → Type where
| var {n : Nat} {ctx : List BaseType} (i : Fin ctx.length) :
    PExpr BaseConst BaseType n ctx
| const {n : Nat} {ctx : List BaseType} :
    BaseConst n → PExpr BaseConst BaseType n ctx
| app {n : Nat} {ctx : List BaseType} :
    PExpr BaseConst BaseType n ctx →
    PExpr BaseConst BaseType n ctx →
    PExpr BaseConst BaseType n ctx
| lift {n : Nat} {ctx : List BaseType} :
    PType BaseConst BaseType n ctx →
    PExpr BaseConst BaseType (n + 1) ctx

inductive PType (BaseConst : Nat → Type) (BaseType : Type) : Nat → List BaseType → Type where
| atom {n : Nat} {ctx : List BaseType} :
    BaseType → PType BaseConst BaseType n ctx
| fun {n : Nat} {ctx : List BaseType} :
    PType BaseConst BaseType n ctx →
    PType BaseConst BaseType n ctx →
    PType BaseConst BaseType n ctx
| fromExpr {n : Nat} {ctx : List BaseType} :
    PExpr BaseConst BaseType n ctx →
    PType BaseConst BaseType n ctx
end

namespace PType

def beq {BaseConst : Nat → Type} {BaseType : Type} [∀ n, BEq (BaseConst n)] [BEq BaseType] :
    {n : Nat} → {ctx : List BaseType} →
    PType BaseConst BaseType n ctx → PType BaseConst BaseType n ctx → Bool
| _, _, .atom a, .atom b => a == b
| _, _, .fun a₁ b₁, .fun a₂ b₂ => a₁.beq a₂ && b₁.beq b₂
| _, _, .fromExpr _, .fromExpr _ => true
| _, _, _, _ => false

end PType

namespace PExpr

def beq {BaseConst : Nat → Type} {BaseType : Type} [∀ n, BEq (BaseConst n)] [BEq BaseType] :
    {n : Nat} → {ctx : List BaseType} →
    PExpr BaseConst BaseType n ctx → PExpr BaseConst BaseType n ctx → Bool
| _, _, .var a, .var b => a == b
| _, _, .const a, .const b => a == b
| _, _, .app f₁ x₁, .app f₂ x₂ => f₁.beq f₂ && x₁.beq x₂
| _, _, .lift a, .lift b => PType.beq a b
| _, _, _, _ => false

end PExpr

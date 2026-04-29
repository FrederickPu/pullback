import Pullback.P.Basic
import Pullback.P.Syntax

open Lean

@[reducible]
def NDArray (α : Type u) : List Nat → Type u
| [] => α
| d :: ds => Fin d → NDArray α ds


inductive TensorBaseType
| float
| tensor (shape : List Nat)
deriving DecidableEq

instance : BasedType TensorBaseType where
  valueType
  | .float => Float
  | .tensor s => NDArray Float s

abbrev T := PType TensorBaseType

#check (ptype{b(.float) -> b(.float)} : T)

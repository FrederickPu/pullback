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


#check (ptype{b(.float) -> b(.float) -> b(.float)} : T)
#check (PType.ofBase TensorBaseType.float).fun ((PType.ofBase TensorBaseType.float).fun (PType.ofBase TensorBaseType.float))


inductive LinalgConst
| float (f : Float)
| matmul (m n k : Nat)
| relu

instance : Typed LinalgConst T where
  type
  | .float _ => .ofBase .float
  | .relu => .fun (.ofBase .float) (.ofBase .float)
  | .matmul m n k =>
      .fun (.ofBase (.tensor [m, k]))
        (.fun (.ofBase (.tensor [k, n]))
          (.ofBase (.tensor [m, n])))

instance : Typed LinalgConst T where
  type
  | .float _ => .ofBase .float
  | .relu => .fun (.ofBase .float) (.ofBase .float)
  | .matmul m n k =>
      .fun (.ofBase (.tensor [m, k]))
        (.fun (.ofBase (.tensor [k, n]))
          (.ofBase (.tensor [m, n])))

#check (pexpr{fun x : b(.tensor [2, 3]) => fun y : b(.tensor [3, 5]) => c(.matmul 2 3 5) x y} : PExpr LinalgConst TensorBaseType)
#check PExpr.lam `x (PType.ofBase (TensorBaseType.tensor [2, 3]))
  ((PExpr.lam `y (PType.ofBase (TensorBaseType.tensor [3, 5]))
        ((PExpr.const (LinalgConst.matmul 2 3 5)).app (PExpr.var `x))).app
    (PExpr.var `y))

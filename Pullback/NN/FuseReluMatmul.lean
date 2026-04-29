import Mathlib
import Lean
import Pullback.P.Basic

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

inductive LinalgConst
| float (f : Float)
| matmul (m n k : Nat)
| relu
-- deriving DecidableEq

inductive SCFConst
| float (f : Float)
| add
| mul
| relu
| foldl (n : Nat)
-- deriving DecidableEq

instance : Typed LinalgConst T where
  type
  | .float _ => .ofBase .float
  | .relu => .fun (.ofBase .float) (.ofBase .float)
  | .matmul m n k =>
      .fun (.ofBase (.tensor [m, k]))
        (.fun (.ofBase (.tensor [k, n]))
          (.ofBase (.tensor [m, n])))

instance : Typed SCFConst T where
  type
  | .float _ => .ofBase .float
  | .add =>
      .fun (.ofBase .float)
        (.fun (.ofBase .float) (.ofBase .float))
  | .mul =>
      .fun (.ofBase .float)
        (.fun (.ofBase .float) (.ofBase .float))
  | .relu =>
      .fun (.ofBase .float) (.ofBase .float)
  | .foldl n =>
      .fun (.fun (.ofBase .float)
                 (.fun (.ofBase .float)
                       (.ofBase .float)))
        (.fun (.ofBase (.tensor [n]))
          (.fun (.ofBase .float)
            (.ofBase .float)))

abbrev LinalgExpr := PExpr LinalgConst TensorBaseType
abbrev SCFExpr := PExpr SCFConst TensorBaseType

def relu (x : Float) : Float :=
  max x 0

def matmul {m n k : Nat}
  (A : Fin m → Fin k → Float)
  (B : Fin k → Fin n → Float)
  : Fin m → Fin n → Float :=
fun i j =>
  Fin.foldl k (fun acc t => acc + A i t * B t j) 0

instance : Interp TensorBaseType LinalgConst where
  interp c :=
    match c with
    | .float f => f
    | .relu => relu
    | .matmul _ _ _ => matmul

def add (a b : Float) : Float := a + b
def mul (a b : Float) : Float := a * b
def foldl {n : Nat}
  (f : Float → Float → Float)
  (x : NDArray Float [n])
  (init : Float) : Float :=
Fin.foldl (n := n)
  (fun acc i => f acc (x i))
  init

instance : Interp TensorBaseType SCFConst where
  interp
  | .float f => f
  | .add => add
  | .mul => mul
  | .relu => relu
  | .foldl _ => foldl

def lower : LinalgExpr → SCFExpr
| .const c =>
    match c with
    | .float f => (.const (.float f))
    | .relu => .const SCFConst.relu
    | .matmul _ _ _ => .const (SCFConst.foldl 0)
| .var x => .var x
| .app (.const .relu)
       (.app (.app (.const (.matmul m n k)) A) B) =>
    let A' := lower A
    let B' := lower B
    .app
      (.app
        (.app (.const (SCFConst.foldl k))
          (.lam `acc (.ofBase .float)
            (.lam `t (.ofBase .float)
              (.app (.const SCFConst.relu)
                (.app
                  (.app (.const SCFConst.add)
                    (.var `acc))
                  (.app
                    (.app (.const SCFConst.mul)
                      (.app A' (.var `t)))
                    (.app B' (.var `t))))))))
        A')
      (.const (.float 0))
| .app (.app (.const (.matmul m n k)) A) B =>
    let A' := lower A
    let B' := lower B
    .app
      (.app
        (.app (.const (SCFConst.foldl k))
          -- function: acc t => acc + A i t * B t j
          (.lam `acc (.ofBase .float)
            (.lam `t (.ofBase .float)
              (.app
                (.app (.const SCFConst.add)
                  (.var `acc))
                (.app
                  (.app (.const SCFConst.mul)
                        (.app A' (.var `t)))
                  (.app B' (.var `t)))))))
        A')
      (.const (.float 0))
| .app f x =>
    .app (lower f) (lower x)
| .lam n t b =>
    .lam n t (lower b)
| .letE n v b =>
    .letE n (lower v) (lower b)

theorem inferType_lower (vars : VarMap TensorBaseType) : (e : LinalgExpr) → (he : (e.inferType vars).isSome) →
  e.inferType vars = (lower e).inferType vars := sorry

theorem interp_lower (vars : VarMap TensorBaseType) : (e : LinalgExpr) → (he : (e.inferType vars).isSome) →
  cast (by grind [inferType_lower]) ((lower e).interp vars (by grind [inferType_lower])) = e.interp vars (by grind) := by sorry

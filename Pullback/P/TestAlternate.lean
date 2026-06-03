import Pullback.P.Basic
import Pullback.P.Syntax

inductive BaseConst : Nat → Type
| zero : BaseConst 0
| succ : BaseConst 0
| nil : BaseConst 0
| cons : BaseConst 0
| tensor : BaseConst 0
| relu : BaseConst 0
| matmul : BaseConst 0
deriving BEq

inductive TensorBaseType
| t0
| t1
deriving BEq

def ctx0 : List TensorBaseType := [TensorBaseType.t0]

def e0 : PExpr BaseConst TensorBaseType 0 ctx0 := .var ⟨0, by simp [ctx0]⟩

def e1 : PExpr BaseConst TensorBaseType 0 ctx0 := .const BaseConst.nil

def t0 : PType BaseConst TensorBaseType 0 ctx0 := .atom TensorBaseType.t1

def e2 : PExpr BaseConst TensorBaseType 1 ctx0 := .lift t0

def t1 : PType BaseConst TensorBaseType 1 ctx0 := .fromExpr e2

def fam : Fin 2 → Type
| ⟨0, _⟩ => Nat
| ⟨1, _⟩ => Bool

def famNat : Nat → Type := natFamilyFromFin fam

def one : PExpr BaseConst TensorBaseType 0 ctx0 :=
  .app (.const BaseConst.succ) (.const BaseConst.zero)

def two : PExpr BaseConst TensorBaseType 0 ctx0 :=
  .app (.const BaseConst.succ) one

def shape2 : PExpr BaseConst TensorBaseType 0 ctx0 :=
  .app (.app (.const BaseConst.cons) one)
    (.app (.app (.const BaseConst.cons) two) (.const BaseConst.nil))

def tensor2 : PType BaseConst TensorBaseType 0 ctx0 :=
  .fromExpr (.app (.const BaseConst.tensor) shape2)

def tensor3 : PType BaseConst TensorBaseType 0 ctx0 :=
  .fromExpr (.app (.const BaseConst.tensor)
    (.app (.app (.const BaseConst.cons) two)
      (.app (.app (.const BaseConst.cons) (.app (.const BaseConst.succ) two)) (.const BaseConst.nil))))

def tensorMatmul : PType BaseConst TensorBaseType 0 ctx0 :=
  .fun tensor2 (.fun tensor3 (.fromExpr (.app (.const BaseConst.tensor)
    (.app (.app (.const BaseConst.cons) one)
      (.app (.app (.const BaseConst.cons) (.app (.const BaseConst.succ) two)) (.const BaseConst.nil))))))

#check e0
#check e1
#check t0
#check t1
#check e2
#check famNat 0
#check famNat 7
#check one
#check two
#check shape2
#check tensor2
#check tensor3
#check tensorMatmul

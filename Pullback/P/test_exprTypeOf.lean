import Pullback.P.Basic

namespace ExprTypeOfTest

private instance : BasedType Nat := ⟨fun _ => Nat⟩
private instance : Typed Unit (PType Nat) := ⟨fun _ => .ofBase 0⟩

open PExpr
open RawPExpr

/--
info: some (PType.ofBase 0) : Option (PType ℕ)
-/
#guard_msgs (info) in
#check exprTypeOf (.const () : RawPExpr Unit Nat) in []

/--
info: some (PType.ofBase 0) : Option (PType ℕ)
-/
#guard_msgs (info) in
#check exprTypeOf (.var `x : RawPExpr Unit Nat) in [(`x, .ofBase 0)]

/--
info: some ((PType.ofBase 0).fun (PType.ofBase 0)) : Option (PType ℕ)
-/
#guard_msgs (info) in
#check exprTypeOf (.lam `x (.ofBase 0) (.var `x) : RawPExpr Unit Nat) in []

/--
info: some (PType.ofBase 0) : Option (PType ℕ)
-/
#guard_msgs (info) in
#check exprTypeOf (.app (.lam `x (.ofBase 0) (.var `x)) (.const ()) : RawPExpr Unit Nat) in []

/--
info: some (PType.ofBase 0) : Option (PType ℕ)
-/
#guard_msgs (info) in
#check exprTypeOf (.letE `x (.const ()) (.var `x) : RawPExpr Unit Nat) in []

end ExprTypeOfTest

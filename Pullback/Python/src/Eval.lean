import Init
import Lean
import Pullback.Python.src.Data.Dict.Basic
import Pullback.Python.src.Syntax

namespace Python

inductive Value where
  | int   : Int → Value
  | bool  : Bool → Value
  | str   : String → Value
  | list  : List Value → Value
  | dict  : List (String × Value) → Value
  | none  : Value
deriving Repr, BEq, Inhabited

structure Env where
  get : String → Value

namespace Env

def init (i : Value) : Env where
  get _ := i

def set (x : String) (v : Value) (σ : Env) : Env where
  get y := if x == y then v else σ.get y


@[simp]
theorem get_init : (Env.init v).get x = v := by rfl

@[simp]
theorem get_set_same {σ : Env} : (σ.set x v).get x = v := by
  simp [get, set]

@[simp]
theorem get_set_different {σ : Env} : x ≠ y → (σ.set x v).get y = σ.get y := by
  intros
  simp [get, set, *]

end Env

def eval (σ : Env) : Expr → Value
  | Expr.constInt n => Value.int n
  | Expr.constBool b => Value.bool b
  | Expr.constStr s => Value.str s
  | Expr.var str => σ.get str
  | Expr.plus e₁ e₂ =>
    match eval σ e₁, eval σ e₂ with
    | Value.int n₁, Value.int n₂ => Value.int (n₁ + n₂)
    | _, _ => Value.none
  | Expr.equal e₁ e₂ =>
    Value.bool (eval σ e₁ == eval σ e₂)
  | Expr.len e =>
    match eval σ e with
    | Value.str s => Value.int s.length
    | Value.list l => Value.int l.length
    | _ => Value.none
  | Expr.concat e₁ e₂ =>
    match eval σ e₁, eval σ e₂ with
    | Value.str s₁, Value.str s₂ => Value.str (s₁ ++ s₂)
    | Value.list l₁, Value.list l₂ => Value.list (l₁ ++ l₂)
    | _, _ => Value.none
  | Expr.emptyDict => Value.dict []
  | Expr.lookup e_dict e_key =>
    match eval σ e_dict, eval σ e_key with
    | Value.dict d, Value.str k =>
      let raw : Dict Value := d
      match raw.find k with
      | some v => v
      | none => Value.none
    | _, _ => Value.none

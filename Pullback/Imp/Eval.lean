import Pullback.Imp.Syntax

namespace Imp

structure Ctx where
  (map : String → Value)

def Ctx.init : Ctx := { map := fun _ => 0 }

variable (σ : Ctx)

def Ctx.get (s : String) : Value :=
  σ.map s

def Ctx.set (s : String) (v : Value) : Ctx :=
  { map := fun s' => if s = s' then v else σ.get s }

@[simp]
theorem Ctx.get_set_same (s : String) (v : Value) : (σ.set s v).get s = v := by
  simp only [Ctx.get, Ctx.set, ↓reduceIte]

def eval (σ : Ctx) : Expr → Value
  | .const v => v
  | .lt x y =>
    if eval σ x < eval σ y then 1 else 0
  | .add x y => eval σ x + eval σ y
  | .var x => σ.get x

#check eval Ctx.init (.add (.const 1) (.const 2))

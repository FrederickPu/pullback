import Pullback.SSA.Basic

open Lean

inductive SSAVal where
  | const : SSAConst → SSAVal
  | closure : (n : Nat) → ((e : SSAExpr) → e.size ≤ n → SSAVal) → SSAVal
  | error : SSAVal

abbrev ValueMap := Array (Name × SSAVal)

def ValueMap.get' (env : ValueMap) (name : Name) : SSAVal :=
  match env.findLast? (·.1 == name) with
  | some (_, v) => v
  | none => .error

def SSAExpr.eval' (n : Nat) (env : ValueMap) (e : SSAExpr) (he : e.size ≤ n)
    (k : SSAVal → SSAVal) : SSAVal :=
  match e with
  | .const c => k (.const c)
  | .var name => k (env.get' name)
  | .letE name val body =>
      have hsz : 1 + val.size + body.size ≤ n := by simp [SSAExpr.size] at he; exact he
      val.eval' (n - 1) env (by omega) fun v =>
        body.eval' (n - 1) (env.push (name, v)) (by omega) k
  | .lam varName _varType body =>
      have hsz : 1 + body.size ≤ n := by simp [SSAExpr.size] at he; exact he
      k (.closure (n - 1) fun argExpr harg =>
        argExpr.eval' (n - 1) env harg fun argVal =>
          body.eval' (n - 1) (env.push (varName, argVal)) (by omega) id)
  | .app f x =>
      have hsz : 1 + f.size + x.size ≤ n := by simp [SSAExpr.size] at he; exact he
      f.eval' (n - 1) env (by omega) fun fVal =>
        match fVal with
        | .closure m fn =>
            if h : x.size ≤ m then k (fn x h)
            else .error
        | _ => .error

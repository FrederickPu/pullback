/- be able to do mutual recursion (and regular recursion) in a controlled cps quotable way -/
/- mutual version -/
mutual
  def f (n : Nat) : Nat :=
    if n = 0 then 1 else 1 -  g (n - 1)

  def g (n : Nat) : Nat :=
    if n = 0 then 0 else 1 - f (n - 1)
end

/- CPS version: each function takes n, and a continuation that can call
   any of the m functions on a smaller value -/
def f' (n : Nat) (call : Fin 2 → Fin n → Nat) : Nat :=
  if h : n = 0 then 1 else 1 - call 1 ⟨n - 1, by omega⟩

def g' (n : Nat) (call : Fin 2 → Fin n → Nat) : Nat :=
  if h : n = 0 then 0 else 1 - call 0 ⟨n - 1, by omega⟩

/- General mkJoint: takes m functions, each of type (n : Nat) → (Fin m → Fin n → Nat) → Nat -/
def mkJoint
    {m : Nat}
    (bodies : Fin m → (n : Nat) → (Fin m → Fin n → Nat) → Nat)
    (role : Fin m)
    (n : Nat) : Nat :=
  bodies role n (fun r ⟨k, hk⟩ => mkJoint bodies r k)
termination_by n
decreasing_by exact hk

def bodies : Fin 2 → (n : Nat) → (Fin 2 → Fin n → Nat) → Nat
  | ⟨0, _⟩ => f'
  | ⟨1, _⟩ => g'
  | ⟨n+2, h⟩ => absurd h (by omega)

def mkF := mkJoint (m := 2) bodies 0
def mkG := mkJoint (m := 2) bodies 1

example : mkF 0 = f 0 := by native_decide
example : mkF 2 = f 2 := by native_decide
example : mkF 3 = f 3 := by native_decide
example : mkF 10 = f 10 := by native_decide

example : mkG 0 = g 0 := by native_decide
example : mkG 1 = g 1 := by native_decide
example : mkG 2 = g 2 := by native_decide
example : mkG 3 = g 3 := by native_decide
example : mkG 10 = g 10 := by native_decide

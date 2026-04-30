import Mathlib
import Lean
import Pullback.P.Basic
import Pullback.P.Syntax

open Lean

@[reducible]
def NDArray (α : Type u) : List Nat → Type u
| [] => α
| d :: ds => Fin d → NDArray α ds

def NDArray.map {α : Type u} {β : Type v} (f : α → β) : {shape : List Nat} → NDArray α shape → NDArray β shape
| [] => f
| _::l => fun x => fun i => NDArray.map f (shape := l) (x i)

def scfFor {α}
  {Ts : List Type}
  (range : Std.Legacy.Range)
  (iterArgs : DVector Ts)
  (step : Nat → DVector Ts → (DVector Ts → α) → α)
  (k : DVector Ts → α)
  : α :=
let rec
  loop (i : Nat) (state : DVector Ts) : α :=
    if h : i < range.stop then
      step i state fun state' => loop (i + range.step) state'
    else
      k state
  termination_by range.stop - i
  decreasing_by
    have : range.step > 0 := range.step_pos
    omega
loop range.start iterArgs


inductive LinalgBaseType
| float
| tensor (shape : List Nat)
deriving DecidableEq

instance : BasedType LinalgBaseType where
  valueType
  | .float => Float
  | .tensor s => NDArray Float s

abbrev T := PType LinalgBaseType

inductive SCFBaseType
| float
| fin (n : Nat)
deriving DecidableEq

instance : BasedType SCFBaseType where
  valueType
  | .float => Float
  | .fin n => Fin n

abbrev S := PType SCFBaseType

-- the scf type corresponding to `.tensor shape`
def LinalgBaseType.tensor_toscf : (shape : List Nat) → S
| [] => ptype{b(.float)}
| a::l => ptype{b(.fin a) -> `(tensor_toscf l)}

def LinalgBaseType.toSCF : LinalgBaseType → S
| .float => .ofBase .float
| .tensor shape => tensor_toscf shape

def T.toS : T → S
| .ofBase b => b.toSCF
| .fun a b => .fun (T.toS a) (T.toS b)
| .prod alpha beta => .prod (T.toS alpha) (T.toS beta)

theorem LinalgBaseType.tensor_toscf_type_eq : (shape : List Nat) → (ptype{b(.tensor shape)} : T).type = (tensor_toscf shape).type
| [] => rfl
| a::l => by
  simp [PType.type, BasedType.valueType, NDArray, tensor_toscf, ← tensor_toscf_type_eq l]

inductive LinalgConst
| float (f : Float)
| matmul (m n k : Nat)
| relu (shape : List Nat)
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
  | .relu (shape : List Nat) => .fun (.ofBase (.tensor shape)) (.ofBase (.tensor shape))
  | .matmul m n k =>
      .fun (.ofBase (.tensor [m, k]))
        (.fun (.ofBase (.tensor [k, n]))
          (.ofBase (.tensor [m, n])))

instance : Typed SCFConst S where
  type
  | .float _ => ptype{b(.float)}
  | .add => ptype{b(.float) -> b(.float) -> b(.float)}
  | .mul => ptype{b(.float) -> b(.float) -> b(.float)}
  | .relu => ptype{b(.float) -> b(.float)}
  | .foldl n => ptype{
    (b(.float) -> b(.float) -> b(.float)) ->
    (b(.fin n) -> b(.float)) ->
    b(.float) -> b(.float)}

abbrev LinalgExpr := PExpr LinalgConst LinalgBaseType
abbrev SCFExpr := PExpr SCFConst SCFBaseType

def relu (x : Float) : Float :=
  max x 0

def matmul {m n k : Nat}
  (A : Fin m → Fin k → Float)
  (B : Fin k → Fin n → Float)
  : Fin m → Fin n → Float :=
fun i j =>
  Fin.foldl k (fun acc t => acc + A i t * B t j) 0

instance : Interp LinalgBaseType LinalgConst where
  interp c :=
    match c with
    | .float f => f
    | .relu _ => NDArray.map relu
    | .matmul _ _ _ => matmul

def add (a b : Float) : Float := a + b
def mul (a b : Float) : Float := a * b
def foldl {n : Nat}
  (f : Float → Float → Float)
  (x : Fin n → Float)
  (init : Float) : Float :=
Fin.foldl (n := n)
  (fun acc i => f acc (x i))
  init

instance : Interp SCFBaseType SCFConst where
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
    | .relu _ => .const SCFConst.relu
    | .matmul _ _ _ => .const (SCFConst.foldl 0) -- dummy value
| .var x => .var x
| .app (.const (.relu _))
       (.app (.app (.const (.matmul m n k)) A) B) =>
    let A' := lower A
    let B' := lower B
    pexpr{fun i : b(.fin m) => fun j : b(.fin n) =>
      c(.foldl k) (fun acc : b(.float) => fun t : b(.fin k) => (c(.add) acc) ((c(.mul) ((`(A') i) t)) ((`(B') t) j)))
    }
| .app (.app (.const (.matmul m n k)) A) B =>
    let A' := lower A
    let B' := lower B
    pexpr{fun i : b(.fin m) => fun j : b(.fin n) =>
      c(.foldl k) (fun acc : b(.float) => fun t : b(.fin k) => c(.relu) ((c(.add) acc) ((c(.mul) ((`(A') i) t)) ((`(B') t) j))))
    }
| .app f x =>
    .app (lower f) (lower x)
| .lam n t b =>
    .lam n (T.toS t) (lower b)
| .letE n v b =>
    .letE n (lower v) (lower b)

theorem SCFExpr.foldl_eq_matmul {m n k : Nat} {vars : VarMap LinalgBaseType} (A B : LinalgExpr) (hA : A.inferType vars = PType.ofBase (LinalgBaseType.tensor [m, k])) (hB : B.inferType vars = PType.ofBase (LinalgBaseType.tensor [k, n]))
  :
  matmul (m := m) (n := n) (k := k) (cast (by simp [hA, PType.type, BasedType.valueType, NDArray]) (A.interp vars sorry sorry)) (cast (by simp [hB, PType.type, BasedType.valueType, NDArray]) (B.interp vars sorry sorry)) = (pexpr{
      fun i : b(.fin m) => fun j : b(.fin n) =>
      c(.foldl k) (fun acc : b(.float) => fun t : b(.fin k) => c(.relu) ((c(.add) acc) ((c(.mul) ((`(A') i) t)) ((`(B') t) j))))
    } : SCFExpr).interp vars sorry sorry := sorry

theorem Map.get_isSome_iff_any {α : Type} [DecidableEq α] {β : Type} (vars : Map α β) (key : α) :
    (vars.get key).isSome ↔ vars.any (·.1 = key) := by
    simp only [get, Array.findLast?, Option.isSome_map, Array.find?_isSome, Array.mem_reverse,
      decide_eq_true_eq, Prod.exists, exists_and_right, exists_eq_right, Array.any_eq_true']

theorem Map.get_map {α : Type} [DecidableEq α] {β γ : Type} (vars : Map α β) (f : β → γ) (x : α): Option.map f (Map.get vars x) = Map.get (Array.map (fun x => (x.1, f x.2)) vars) x := sorry

theorem inferType_lower (vars : VarMap LinalgBaseType) : (e : LinalgExpr) → (he : (e.inferType vars).isSome) → (heVal : ((e.inferType vars).get he).funCodom?.isNone) →
  (e.inferType vars).map T.toS = (lower e).inferType (vars.map (fun x => (x.1, T.toS x.2)))
| .const (.float f) => by
   simp [PExpr.inferType, Typed.type, lower, T.toS, LinalgBaseType.toSCF]
| .const (.matmul _ _ _) => by
  simp [PExpr.inferType, Typed.type, PType.funCodom?]
| .var x => by
  simp [PExpr.inferType, Map.get_map, Option.isSome_iff_exists, lower]
| (.app (.app (.const (.matmul m n k)) A) B) => by
  intro he heVal
  clear heVal
  simp [PExpr.inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff, Typed.type] at he
  have hA : A.inferType vars = PType.ofBase (LinalgBaseType.tensor [m, k]) := by
    grind [PType.funDom?]
  have hB : B.inferType vars = PType.ofBase (LinalgBaseType.tensor [k, n]) := by
    grind [PType.funDom?, PType.funCodom?]
  have : PExpr.inferType vars (((PExpr.const (LinalgConst.matmul m n k)).app A).app B) = PType.ofBase (TensorBaseType.tensor [m, n]) := by
    simp [PType.funDom?, PType.funCodom?, PExpr.inferType, Typed.type]
    grind
  rw [this]
  simp [lower]
  symm
  have : (PExpr.lam `acc (PType.ofBase TensorBaseType.float)
                (PExpr.lam `t (PType.ofBase TensorBaseType.float)
                  (((PExpr.const SCFConst.add).app (PExpr.var `acc)).app
                    (((PExpr.const SCFConst.mul).app (PExpr.app (lower A) (PExpr.var `t))).app
                      (PExpr.app (lower B) (PExpr.var `t)))))).inferType vars = sorry := sorry

  sorry
| _ => sorry

-- theorem interp_lower (vars : VarMap TensorBaseType) : (e : LinalgExpr) → (he : (e.inferType vars).isSome) →
--   cast (by grind [inferType_lower]) ((lower e).interp vars (by grind [inferType_lower])) = e.interp vars (by grind) := by sorry

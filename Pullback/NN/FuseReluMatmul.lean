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

theorem LinalgBaseType.type_toSCF : ∀ l : LinalgBaseType, BasedType.valueType l = l.toSCF.type
| .float => rfl
| .tensor shape => by simp [toSCF, ← tensor_toscf_type_eq, PType.type]

def T.type_toS : ∀ t : T, t.type = t.toS.type
| .ofBase b => by simp [PType.type, LinalgBaseType.type_toSCF, toS]
| .fun a b => by simp [PType.type, toS, type_toS]
| .prod alpha beta => by simp [PType.type, toS, type_toS]

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

instance : Typed SCFConst (PType SCFBaseType) where
  type
  | .float _ => ptype{b(.float)}
  | .add => ptype{b(.float) -> b(.float) -> b(.float)}
  | .mul => ptype{b(.float) -> b(.float) -> b(.float)}
  | .relu => ptype{b(.float) -> b(.float)}
  | .foldl n => ptype{
    (b(.float) -> b(.fin n) -> b(.float)) ->
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
def foldl (n : Nat)
  (f : Float → Fin n → Float)
  (init : Float) : Float :=
Fin.foldl (n := n)
  (fun acc i => f acc i)
  init

instance : Interp SCFBaseType SCFConst where
  interp
  | .float f => f
  | .add => add
  | .mul => mul
  | .relu => relu
  | .foldl n => foldl n

def lower
  : (ctx : List T) → {ty : T} →
    LinalgExpr ctx ty →
    SCFExpr (ctx.map T.toS) (T.toS ty)
| ctx, _, PExpr.const c => sorry
  -- match c with
  -- | .float f =>
  --   PExpr.const (SCFConst.float f)
  -- | .relu _ => sorry
  -- | .matmul m n k => sorry
| ctx, _, PExpr.letE (valT := valT) val body =>
  .letE (lower ctx val) (lower (valT::ctx) body)
| ctx, _, PExpr.var name =>
  let varScf : SCFExpr (ctx.map T.toS) _ := PExpr.var (Fin.cast (by simp) name)
  cast (by  simp) varScf
-- | ctx, _, .app (.const (LinalgConst.relu [m, n]) : LinalgExpr ctx (.fun (PType.ofBase (LinalgBaseType.tensor [m, n])) (PType.ofBase (LinalgBaseType.tensor [m, n])))) ((.app (argT := BT) (.app (argT := AT) (matmul') A) B) : LinalgExpr ctx (PType.ofBase (LinalgBaseType.tensor [m, n]))) =>
--   match matmul' with
--   | PExpr.const (LinalgConst.matmul m n k) => sorry
-- -- | .app (.const (.relu _))
-- --        (.app (.app (.const (.matmul m n k)) A) B) =>
-- --     let A' := lower A
-- --     let B' := lower B
-- --     pexpr{fun i : b(.fin m) => fun j : b(.fin n) =>
-- --       c(.foldl k) (fun acc : b(.float) => fun t : b(.fin k) => (c(.add) acc) ((c(.mul) ((`(A') i) t)) ((`(B') t) j)))
-- --     }

| ctx, _, PExpr.app (argT := argT) (ty := ty) (f : LinalgExpr _ _) x =>
  let defaultVal := (lower ctx (ty := .fun argT ty) f).app (lower ctx x)
  match hx : x with
  | (.app (argT := BT) (.app (argT := AT) (g) A) B) =>
    let temp := (AT.fun (BT.fun argT))
    let temp' := argT.fun ty
    let g' : PExpr LinalgConst LinalgBaseType ctx temp := g
    let f' : PExpr LinalgConst LinalgBaseType ctx temp' := f
    match hA : AT, hB : BT with
    | (.ofBase (.tensor [m, k])), (.ofBase (.tensor [k', n])) =>
      have htemp : temp = (PType.ofBase (LinalgBaseType.tensor [m, k])).fun ((PType.ofBase (LinalgBaseType.tensor [k', n])).fun argT) := by
        simp [temp, hA, hB]
      match hg': g' with
      | .const (LinalgConst.matmul m' n' k'') =>
        have : PType.ofBase (LinalgBaseType.tensor [k', n]) = PType.ofBase (LinalgBaseType.tensor [k, n]) := by
          grind [Typed.type, instTypedLinalgConstT]
        let B := cast (congrArg _ this) B
        have : temp = (PType.ofBase (LinalgBaseType.tensor [m, k])).fun ((PType.ofBase (LinalgBaseType.tensor [k, n])).fun argT) := by
          grind [Typed.type, instTypedLinalgConstT]
        let matmul' := cast (congrArg _ this) g'
        let A' := lower ctx A
        let B' := lower ctx B
        let womp : PExpr.RawPExpr SCFConst SCFBaseType := rpexpr{fun A' : `((T.toS (PType.ofBase (LinalgBaseType.tensor [m, k])))) => fun B' : `((T.toS (PType.ofBase (LinalgBaseType.tensor [k, n])))) => fun i : b(.fin m) => fun j : b(.fin n) =>
          c(.relu) (c(.foldl k) (fun acc : b(.float) => fun t : b(.fin k) => (c(.add) acc) (c(.mul) (A' i t) (B' t j))) c(.float 0))
        }
        have hargT : argT = PType.ofBase (LinalgBaseType.tensor [m, n]) := by
          have q : temp = (Typed.type (LinalgConst.matmul m' n' k'')) := by grind
          simp [Typed.type] at q
          grind
        have hwomp : (PExpr.RawPExpr.inferType [] womp).isSome := by
          simp [womp, T.toS, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf, PExpr.RawPExpr.inferType, Typed.type]
        have htemp' : temp' = (PType.ofBase (LinalgBaseType.tensor [m, n])).fun ty := by grind
        match hf' : f' with
        | (.const (.relu [m'', n''])) =>
          let womp' : SCFExpr [] (
      (((PType.ofBase (SCFBaseType.fin m)).fun
            ((PType.ofBase (SCFBaseType.fin k)).fun (PType.ofBase SCFBaseType.float))).fun
        (((PType.ofBase (SCFBaseType.fin k)).fun
              ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float))).fun
          ((PType.ofBase (SCFBaseType.fin m)).fun
            ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float)))))) := cast (by {
                simp [womp, T.toS, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf, PExpr.RawPExpr.inferType, T.toS, SCFExpr]
              }) (womp.toPExpr [] hwomp)
          -- TODO :: add tactic for drafting simped values by expanding stuff automatically
    --       have : womp.inferType [] = sorry := by {
    --         simp [womp, T.toS, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf, PExpr.RawPExpr.inferType, Typed.type]
    --         /-
    --            some
    --   (((PType.ofBase (SCFBaseType.fin m)).fun
    --         ((PType.ofBase (SCFBaseType.fin k)).fun (PType.ofBase SCFBaseType.float))).fun
    --     (((PType.ofBase (SCFBaseType.fin k)).fun
    --           ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float))).fun
    --       ((PType.ofBase (SCFBaseType.fin m)).fun
    --         ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float))))) =
    -- sorry
    --         -/
    --       }
          have hty : ty = PType.ofBase (LinalgBaseType.tensor [m, n]) := by
            grind [Typed.type, instTypedLinalgConstT]
          cast (by simp [T.toS, this, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf, hty]) (((PExpr.lift womp').app A').app B')
        | _ => defaultVal
      | _ => defaultVal
    | _, _ => defaultVal
  | _ => defaultVal
| ctx, _, PExpr.lam varType body =>
  PExpr.lam (T.toS varType) (lower (varType::ctx) body)
| _, _, PExpr.lift (ctx := ctx) (ctx' := ctx') e => cast (by simp) <| PExpr.lift (ctx := ctx.map T.toS) (ctx' := ctx'.map T.toS) (lower ctx e)
-- termination_by ctx ty e => sizeOf e
-- decreasing_by {
--   all_goals simp; omega

-- }

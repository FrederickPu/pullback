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



def ctxS (ctxL : List (Name × T)) := ctxL.map (fun (x, v) => (x, T.toS v))

open PExpr

def reluSCF {ctx} : (shape : List Nat) → {x : RawPExpr SCFConst SCFBaseType // HasType ctx x (.fun (LinalgBaseType.tensor_toscf shape) (LinalgBaseType.tensor_toscf shape))}
| [] => ⟨(RawPExpr.const SCFConst.relu), by infer_instance⟩
| a::l =>
  let ⟨reluL, hreluL⟩ := reluSCF (ctx := ctx) l
  -- note: can think of the quoted `reluL'` as being a placeholder fo the actual reluL this way inferType will have nice reduction rules wihtout needing to use `hreluL` which can be unstable for simp
  -- (we use a similar trick for matmulrelufuse case and matmul case of `lowerRaw`)
  let outAux : RawPExpr SCFConst SCFBaseType :=
    rpexpr{fun reluL' : `(ptype{`(LinalgBaseType.tensor_toscf l) ->
    `(LinalgBaseType.tensor_toscf l)}) => fun x : `(ptype{b(.fin a) -> `(LinalgBaseType.tensor_toscf l)}) => fun i : b(.fin a) => reluL' (x i)}
  have houtAux : HasType ctx outAux ((PType.fun (LinalgBaseType.tensor_toscf l) (LinalgBaseType.tensor_toscf l)).fun
      (((PType.ofBase (SCFBaseType.fin a)).fun (LinalgBaseType.tensor_toscf l)).fun
        ((PType.ofBase (SCFBaseType.fin a)).fun (LinalgBaseType.tensor_toscf l)))) := by
    apply HasType.mk
    simp [outAux, RawPExpr.inferType]
  ⟨outAux.app reluL, by infer_instance⟩

/-
  todo :: make a general purpose lowering functions that takes in a Const.lower along with a `preprocess : RawPExpr → (k : RawPExpr → RawPExpr) → Option RawPExpr`
  (use the continutation passing recursor pattern) function
  - it will lower the expr normally and call Const.lower for the const lowering
  - and preprocosses will return some if non trivial lowering is done (not just const, ie optimizaiton pass eg: FuseReluMatmul)

  todo:: add faifullness of lowering condition to subtype property (ie interping the lowered result gives the same result and interping the original)
-/
def lowerRaw : (ctxL : List (Name × T)) → (ty : T) → (e : RawPExpr LinalgConst LinalgBaseType) →
  [h : HasType ctxL e ty] → {x : RawPExpr SCFConst SCFBaseType // HasType (ctxS ctxL) x (T.toS ty)}
| ctx, ty, .app (.const (.relu shape)) (.app (.app (.const (.matmul m n k)) A) B), ⟨he⟩ =>
  have ⟨hshape, hA, hB, hty⟩ : shape = [m, n] ∧
    HasType ctx A (PType.ofBase (LinalgBaseType.tensor [m, k])) ∧
    HasType ctx B (PType.ofBase (LinalgBaseType.tensor [k, n])) ∧
    ty = PType.ofBase (LinalgBaseType.tensor [m, n]) := by
    simp only [RawPExpr.inferType, Option.pure_def, Option.bind_eq_bind, Option.bind_fun_none,
      Option.bind_some, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq,
      ↓existsAndEq, true_and, and_true, PType.ofBase.injEq, LinalgBaseType.tensor.injEq] at he
    grind [HasType]
  let ⟨A', ⟨hA'⟩⟩ := lowerRaw ctx (PType.ofBase (LinalgBaseType.tensor [m, k])) A
  let ⟨B', hB'⟩ := lowerRaw ctx (PType.ofBase (LinalgBaseType.tensor [k, n])) B
  let outAux : RawPExpr SCFConst SCFBaseType := rpexpr{
    fun A' : `((T.toS (PType.ofBase (LinalgBaseType.tensor [m, k])))) => fun B' : `((T.toS (PType.ofBase (LinalgBaseType.tensor [k, n])))) =>
    fun i : b(.fin m) => fun j : b(.fin n) =>
      c(.relu) (c(.foldl k) (fun acc : b(.float) => fun t : b(.fin k) => (c(.add) acc) (c(.mul) (A' i t) (B' t j))) c(.float 0))
    }
  have : HasType (ctxS ctx) outAux ((((PType.ofBase (SCFBaseType.fin m)).fun
            ((PType.ofBase (SCFBaseType.fin k)).fun (PType.ofBase SCFBaseType.float))).fun
        (((PType.ofBase (SCFBaseType.fin k)).fun
              ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float))).fun
          ((PType.ofBase (SCFBaseType.fin m)).fun
            ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float)))))) := by
    apply HasType.mk
    simp [RawPExpr.inferType, outAux, T.toS, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf, PExpr.RawPExpr.inferType, T.toS, ctxS, Typed.type]
  let out := (outAux.app A').app B'
  have hA' : HasType (ctxS ctx) A' ((PType.ofBase (SCFBaseType.fin m)).fun
        ((PType.ofBase (SCFBaseType.fin k)).fun (PType.ofBase SCFBaseType.float))) := by
    simp only [T.toS, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf] at hA'
    grind [HasType]
  have hB' : HasType (ctxS ctx) B' ((PType.ofBase (SCFBaseType.fin k)).fun
        ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float))) := by
    simp only [T.toS, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf] at hB'
    grind [HasType]
  have hout : HasType (ctxS ctx) out (T.toS (PType.ofBase (LinalgBaseType.tensor [m, n]))) := by
    simp only [T.toS, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf]
    infer_instance
  ⟨out, by rw [hty]; infer_instance⟩
| ctx, ty, .const c, ⟨he⟩ =>
  match c with
  | .float f => ⟨.const (SCFConst.float f), (by {
    apply HasType.mk
    simp only [RawPExpr.inferType, Typed.type, Option.some.injEq] at he
    simp [RawPExpr.inferType, Typed.type, ← he, T.toS, LinalgBaseType.toSCF]
  })⟩
  | .relu shape =>
    have hty : ty = .fun (.ofBase (LinalgBaseType.tensor shape)) (.ofBase (LinalgBaseType.tensor shape)) := by
      simp only [RawPExpr.inferType, Typed.type, Option.some.injEq] at he
      grind
    let ⟨out, hout⟩ := reluSCF (ctx := (ctxS ctx)) shape
    ⟨out, by {
      simp only [hty, T.toS, LinalgBaseType.toSCF]
      grind
    }⟩
  | .matmul m n k =>
    have hty : ty = .fun (PType.ofBase (LinalgBaseType.tensor [m, k])) (.fun (PType.ofBase (LinalgBaseType.tensor [k, n])) (PType.ofBase (LinalgBaseType.tensor [m, n]))) := by
      simp only [RawPExpr.inferType, Typed.type, Option.some.injEq] at he
      grind
    let out : RawPExpr SCFConst SCFBaseType := rpexpr{
    fun A' : `((T.toS (PType.ofBase (LinalgBaseType.tensor [m, k])))) => fun B' : `((T.toS (PType.ofBase (LinalgBaseType.tensor [k, n])))) =>
    fun i : b(.fin m) => fun j : b(.fin n) =>
      (c(.foldl k) (fun acc : b(.float) => fun t : b(.fin k) => (c(.add) acc) (c(.mul) (A' i t) (B' t j))) c(.float 0))
    }
    have : RawPExpr.inferType (ctxS ctx) out = ((((PType.ofBase (SCFBaseType.fin m)).fun
          ((PType.ofBase (SCFBaseType.fin k)).fun (PType.ofBase SCFBaseType.float))).fun
      (((PType.ofBase (SCFBaseType.fin k)).fun
            ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float))).fun
        ((PType.ofBase (SCFBaseType.fin m)).fun
          ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float)))))) := by
      simp [RawPExpr.inferType, out, T.toS, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf, PExpr.RawPExpr.inferType, T.toS, ctxS, Typed.type]
    ⟨out, (by {
      apply HasType.mk
      rw [this]
      simp [hty, T.toS, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf]
    })⟩
| ctx, ty, .letE name val body, ⟨he⟩ =>
  have hvalT : (val.inferType ctx).isSome := by
    grind [RawPExpr.inferType, Option.bind_eq_some_iff]
  have ⟨hval, hbody⟩ :
    HasType ctx val ((val.inferType ctx).get hvalT) ∧
      HasType ((name, (RawPExpr.inferType ctx val).get hvalT) :: ctx) body ty := by
    grind [HasType, RawPExpr.inferType, Option.bind_eq_some_iff]
  let ⟨val', hval'⟩ := lowerRaw ctx ((RawPExpr.inferType ctx val).get hvalT) val
  let ⟨body', hbody'⟩ := lowerRaw ((name, (val.inferType ctx).get hvalT)::ctx) ty body
  ⟨.letE name val' body', by {
    have : (ctxS ((name, (RawPExpr.inferType ctx val).get hvalT) :: ctx)) = ((name, T.toS ((RawPExpr.inferType ctx val).get hvalT))) :: (ctxS ctx) := by rfl
    rw [this] at hbody'
    infer_instance
  }⟩
| ctx, ty, .app f x, ⟨he⟩ =>
  have hf : (f.inferType ctx).isSome := by
    grind [RawPExpr.inferType, Option.bind_eq_some_iff]
  let fT := (f.inferType ctx).get hf
  match hfT : fT with
  | .fun dom codom =>
    have ⟨hcodom, hx⟩ : codom = ty ∧ (x.inferType ctx) = dom := by
      simp [RawPExpr.inferType, Option.bind_eq_some_iff] at he
      obtain ⟨fT', hfT', xT, hxT, H⟩ := he
      have : fT' = fT := by grind
      rw [this, hfT] at H
      grind
    have : HasType ctx f (dom.fun codom) := by
      grind [HasType]
    have : HasType ctx x dom := by
      grind [HasType]
    let ⟨f', hf'⟩ := lowerRaw ctx (.fun dom codom) f
    let ⟨x', hx'⟩ := lowerRaw ctx dom x
    ⟨f'.app x', by {
      have : T.toS (dom.fun codom) = (T.toS dom).fun (T.toS codom) := rfl
      rw [this, hcodom] at hf'
      infer_instance
    }⟩
  | .ofBase b  | .prod alpha beta => by
    apply False.elim
    have : (RawPExpr.inferType ctx f) = fT := by grind
    simp [hfT, RawPExpr.inferType, this] at he
| ctx, ty, .lam name varType body, ⟨he⟩ =>
  match hty : ty with
  | .fun dom codom =>
    have : HasType ((name, varType) :: ctx) body codom := by
      simp only [RawPExpr.inferType, Option.map_eq_some_iff, PType.fun.injEq,
        exists_eq_right_right] at he
      grind [HasType]
    let ⟨body', hbody'⟩ := lowerRaw ((name, varType)::ctx) codom body
    have hlam : HasType (ctxS ctx) (RawPExpr.lam name (T.toS varType) body') (T.toS (dom.fun codom)) := by {
      have : (ctxS ((name, varType) :: ctx)) = (name, T.toS varType)::(ctxS ctx) := rfl
      rw [this] at hbody'
      simp [T.toS]
      grind [HasType, RawPExpr.inferType]
    }
    ⟨.lam name (T.toS varType) body', hlam⟩
  | .ofBase b  | .prod alpha beta => by
    apply False.elim
    simp [RawPExpr.inferType] at he
| ctx, ty, .var name, ⟨he⟩ =>
  have hvar : HasType (ctxS ctx) (RawPExpr.var name) ty.toS := by
    apply HasType.mk
    simp only [RawPExpr.inferType, Option.map_eq_some_iff, Prod.exists, exists_eq_right] at he
    simp only [RawPExpr.inferType, Option.map_eq_some_iff, Prod.exists, exists_eq_right]
    obtain ⟨a, ha⟩ := he
    use a
    simp only [ctxS, List.find?_map, Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists,
      ↓existsAndEq, true_and]
    use ty
    simp only [and_true]
    rw [← ha]
    rfl
  ⟨.var name, hvar⟩

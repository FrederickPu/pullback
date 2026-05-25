import Mathlib
import Lean
import Pullback.P.Basic
import Pullback.P.Syntax
import Pullback.P.RawPExpr
import Pullback.P.HEq

open Lean

@[reducible]
def NDArray (α : Type u) : List Nat → Type u
| [] => α
| d :: ds => Fin d → NDArray α ds

def NDArray.map {α : Type u} {β : Type v} (f : α → β) : {shape : List Nat} → NDArray α shape → NDArray β shape
| [] => f
| _::l => fun x => fun i => NDArray.map f (shape := l) (x i)

@[simp] theorem NDArray.map_nil {α β : Type*} (f : α → β) (x : NDArray α []) :
    NDArray.map f x = f x := rfl

@[simp] theorem NDArray.map_cons {α β : Type*} (f : α → β) {d ds} (g : NDArray α (d :: ds)) (i : Fin d) :
    NDArray.map f g i = NDArray.map f (g i) := rfl

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
@[reducible]
def LinalgBaseType.tensor_toscf : (shape : List Nat) → S
| [] => ptype{b(.float)}
| a::l => ptype{b(.fin a) -> `(tensor_toscf l)}

@[reducible]
def LinalgBaseType.toSCF : LinalgBaseType → S
| .float => .ofBase .float
| .tensor shape => tensor_toscf shape


@[reducible]
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
    simp [outAux, RawPExpr.inferType, List.findFinIdx?, List.findFinIdx?.go]
  ⟨outAux.app reluL, by infer_instance⟩

example {m n k : Nat} : ((RawPExpr.const (LinalgConst.matmul m n k) : RawPExpr LinalgConst LinalgBaseType).toPExpr [] (by simp [RawPExpr.inferType])).interp (cast (by simp [DVector]) Unit.unit) = matmul := by
  rfl

theorem wee {m n k : Nat} : (rpexpr{fun A : b(.tensor [m, k]) => fun B : b(.tensor [k, n]) => c(.relu [m, n]) (c(.matmul m n k) A B)} : RawPExpr LinalgConst LinalgBaseType).inferType [] = sorry := by {
  sorry
}
example {m n k : Nat} :
  let : HasType []
    (RawPExpr.lam `A (PType.ofBase (LinalgBaseType.tensor [m, k]))
      (RawPExpr.lam `B (PType.ofBase (LinalgBaseType.tensor [k, n]))
        ((RawPExpr.const (LinalgConst.relu [m, n])).app
          (((RawPExpr.const (LinalgConst.matmul m n k)).app (RawPExpr.var `A)).app (RawPExpr.var `B)))))
    ((PType.ofBase (LinalgBaseType.tensor [m, k])).fun
      ((PType.ofBase (LinalgBaseType.tensor [k, n])).fun (PType.ofBase (LinalgBaseType.tensor [m, n])))) := sorry
  ((rpexpr{fun A : b(.tensor [m, k]) => fun B : b(.tensor [k, n]) => c(.relu [m, n]) (c(.matmul m n k) A B)} : RawPExpr LinalgConst LinalgBaseType).toPExpr' [] (((PType.ofBase (LinalgBaseType.tensor [m, k])).fun
      ((PType.ofBase (LinalgBaseType.tensor [k, n])).fun (PType.ofBase (LinalgBaseType.tensor [m, n])))))).interp (cast (by simp [DVector]) Unit.unit) = fun A : (NDArray Float [m, k]) => fun B : NDArray Float [k, n] => NDArray.map relu (matmul A B)  := by
  simp only [List.map_nil, ↓reduce_toPExpr', List.map_cons, RawPExpr.toPExpr'_var, List.length_cons,
    List.length_nil, Nat.reduceAdd, Fin.cast_eq_self]
  rfl

-- todo :: have a nice definition/command elaborator that automatically gives you the inferType theorem when you declar the rpexpr
-- (this will require fixing some of the reflexivity issues with inferType)
@[reducible] def matmulReluSCF (m n k : Nat) : RawPExpr SCFConst SCFBaseType := rpexpr{
    fun A' : `((T.toS (PType.ofBase (LinalgBaseType.tensor [m, k])))) => fun B' : `((T.toS (PType.ofBase (LinalgBaseType.tensor [k, n])))) =>
    fun i : b(.fin m) => fun j : b(.fin n) =>
      c(.relu) (c(.foldl k) (fun acc : b(.float) => fun t : b(.fin k) => (c(.add) acc) (c(.mul) (A' i t) (B' t j))) c(.float 0))
    }

@[reducible] def reluMatmulRaw (m n k : Nat) : RawPExpr LinalgConst LinalgBaseType := rpexpr{
  fun A : b(.tensor [m, k]) =>
  fun B : b(.tensor [k, n]) =>
    c(.relu [m, n]) (c(.matmul m n k) A B)
}

-- todo :: modify inferType so that rfl can close this
-- (it should be possible since `m n k` are parametric arguments so you never check against them or have any unfold steps that depend on their value)
theorem inferType_matmulReluSCF {ctx : List (Name × S)} {m n k} : RawPExpr.inferType ctx (matmulReluSCF m n k) = ((((PType.ofBase (SCFBaseType.fin m)).fun
            ((PType.ofBase (SCFBaseType.fin k)).fun (PType.ofBase SCFBaseType.float))).fun
        (((PType.ofBase (SCFBaseType.fin k)).fun
              ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float))).fun
          ((PType.ofBase (SCFBaseType.fin m)).fun
            ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float)))))) := by
  simp [RawPExpr.inferType, T.toS, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf,
    PExpr.RawPExpr.inferType, T.toS, Typed.type, List.findFinIdx?, List.findFinIdx?.go]

instance instHasType_matmulReluSCF {ctx : List (Name × S)} {m n k : ℕ} :
    HasType ctx (matmulReluSCF m n k)
      ((((PType.ofBase (SCFBaseType.fin m)).fun ((PType.ofBase (SCFBaseType.fin k)).fun (PType.ofBase SCFBaseType.float))).fun
        (((PType.ofBase (SCFBaseType.fin k)).fun ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float))).fun
          ((PType.ofBase (SCFBaseType.fin m)).fun ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float)))))) :=
  HasType.mk inferType_matmulReluSCF

instance instHasType_reluMatmul
    {ctx : List (Name × T)} {m n k : ℕ}
    {A B : RawPExpr LinalgConst LinalgBaseType}
    [HasType ctx A (PType.ofBase (LinalgBaseType.tensor [m, k]))]
    [HasType ctx B (PType.ofBase (LinalgBaseType.tensor [k, n]))] :
    HasType ctx
        ((RawPExpr.const (LinalgConst.relu [m, n])).app
          (((RawPExpr.const (LinalgConst.matmul m n k)).app A).app B))
        (PType.ofBase (LinalgBaseType.tensor [m, n])) := by
  apply HasType.mk
  simp only [RawPExpr.inferType, Option.pure_def, Option.bind_eq_bind, Option.bind_fun_none,
    Option.bind_some, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq,
    ↓existsAndEq, true_and, and_true]
  grind [HasType]

instance instHasType_matmulReluSCFApp
    {ctx : List (Name × S)} {m n k : ℕ}
    {A' B' : RawPExpr SCFConst SCFBaseType}
    [hA' : HasType ctx A' (T.toS (PType.ofBase (LinalgBaseType.tensor [m, k])))]
    [hB' : HasType ctx B' (T.toS (PType.ofBase (LinalgBaseType.tensor [k, n])))] :
    HasType ctx (((matmulReluSCF m n k).app A').app B')
        (T.toS (PType.ofBase (LinalgBaseType.tensor [m, n]))) := by
  have hA'_exp : HasType ctx A'
      ((PType.ofBase (SCFBaseType.fin m)).fun
        ((PType.ofBase (SCFBaseType.fin k)).fun (PType.ofBase SCFBaseType.float))) := by
    simp only [T.toS, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf] at hA'
    grind [HasType]
  have hB'_exp : HasType ctx B'
      ((PType.ofBase (SCFBaseType.fin k)).fun
        ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float))) := by
    simp only [T.toS, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf] at hB'
    grind [HasType]
  simp only [T.toS, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf]
  infer_instance

set_option maxHeartbeats 2000000

set_option pp.parens true

@[reducible]
private def reluMatmulTy (m n k : Nat) : T :=
  (PType.ofBase (LinalgBaseType.tensor [m, k])).fun
    ((PType.ofBase (LinalgBaseType.tensor [k, n])).fun
      (PType.ofBase (LinalgBaseType.tensor [m, n])))

@[reducible]
private def matmulReluSCFTy (m n k : Nat) : S :=
  (((PType.ofBase (SCFBaseType.fin m)).fun
      ((PType.ofBase (SCFBaseType.fin k)).fun (PType.ofBase SCFBaseType.float))).fun
    (((PType.ofBase (SCFBaseType.fin k)).fun
        ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float))).fun
      ((PType.ofBase (SCFBaseType.fin m)).fun
        ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float)))))

private theorem reluMatmulRaw_generatedPartial_isSome
    {ctx : List (Name × T)} {m n k : Nat} :
    (RawPExpr.Partial.generatedPartial? ctx (reluMatmulTy m n k)
      (reluMatmulRaw m n k)).isSome := by
  interpvc [reluMatmulRaw, reluMatmulTy]

private theorem reluMatmulRaw_hasType
    {ctx : List (Name × T)} {m n k : Nat} :
    HasType ctx (reluMatmulRaw m n k) (reluMatmulTy m n k) := by
  apply HasType.mk
  simp [RawPExpr.inferType, reluMatmulTy, Typed.type,
    List.findFinIdx?, List.findFinIdx?.go]

private theorem matmulReluSCF_generatedPartial_isSome
    {ctx : List (Name × S)} {m n k : Nat} :
    (RawPExpr.Partial.generatedPartial? ctx (matmulReluSCFTy m n k)
      (matmulReluSCF m n k)).isSome := by
  interpvc [matmulReluSCFTy, matmulReluSCF, T.toS,
    LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf]

private theorem lowerRaw_reluMatmul_correct_partial
    {ctx : List (Name × T)}
    {m n k : ℕ}
    {A B : RawPExpr LinalgConst LinalgBaseType}
    {A' B' : RawPExpr SCFConst SCFBaseType}
    (hA : HasType ctx A (PType.ofBase (LinalgBaseType.tensor [m, k])))
    (hB : HasType ctx B (PType.ofBase (LinalgBaseType.tensor [k, n])))
    (hA' : HasType (ctxS ctx) A' (T.toS (PType.ofBase (LinalgBaseType.tensor [m, k]))))
    (hB' : HasType (ctxS ctx) B' (T.toS (PType.ofBase (LinalgBaseType.tensor [k, n]))))
    (hcorrA :
      (fun args => interp args
        (RawPExpr.toPExprElab ctx (PType.ofBase (LinalgBaseType.tensor [m, k])) A)) ≍
      fun args => interp args
        (RawPExpr.toPExprElab (ctxS ctx)
          (T.toS (PType.ofBase (LinalgBaseType.tensor [m, k]))) A'))
    (hcorrB :
      (fun args => interp args
        (RawPExpr.toPExprElab ctx (PType.ofBase (LinalgBaseType.tensor [k, n])) B)) ≍
      fun args => interp args
        (RawPExpr.toPExprElab (ctxS ctx)
          (T.toS (PType.ofBase (LinalgBaseType.tensor [k, n]))) B')) :
    (fun args => interp args
      (RawPExpr.Partial.generatedApp2
        (ctxRaw := ctx)
        (arg₁ := PType.ofBase (LinalgBaseType.tensor [m, k]))
        (arg₂ := PType.ofBase (LinalgBaseType.tensor [k, n]))
        (out := PType.ofBase (LinalgBaseType.tensor [m, n]))
        (reluMatmulRaw m n k)
        (reluMatmulRaw_generatedPartial_isSome (ctx := ctx) (m := m) (n := n) (k := k))
        hA hB).toPExpr) ≍
    fun args => interp args
      (RawPExpr.Partial.generatedApp2
        (ctxRaw := ctxS ctx)
        (arg₁ := T.toS (PType.ofBase (LinalgBaseType.tensor [m, k])))
        (arg₂ := T.toS (PType.ofBase (LinalgBaseType.tensor [k, n])))
        (out := T.toS (PType.ofBase (LinalgBaseType.tensor [m, n])))
        (matmulReluSCF m n k)
        (matmulReluSCF_generatedPartial_isSome (ctx := ctxS ctx) (m := m) (n := n) (k := k))
        hA' hB').toPExpr := by
  interpvc [reluMatmulRaw, reluMatmulTy, matmulReluSCFTy, matmulReluSCF, T.toS,
    LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf]
  apply Function.hfunext
  · apply congrArg DVector
    induction ctx with
    | nil => rfl
    | cons hd tl ih =>
        cases hd
        simp [ctxS, T.type_toS]
  · intro args args' hargs
    have hAargs := congr_heq hcorrA hargs
    have hBargs := congr_heq hcorrB hargs
    rw [hAargs, hBargs]
    set AV := interp args'
      (RawPExpr.toPExprElab (ctxS ctx)
        (T.toS (PType.ofBase (LinalgBaseType.tensor [m, k]))) A')
    set BV := interp args'
      (RawPExpr.toPExprElab (ctxS ctx)
        (T.toS (PType.ofBase (LinalgBaseType.tensor [k, n]))) B')
    simp
    rfl

private theorem RawPExpr.toPExprElab_of_elab?_eq
    {Const BaseType : Type} [Typed Const (PType BaseType)] [DecidableEq BaseType]
    {ctxRaw : List (Name × PType BaseType)} {ty : PType BaseType}
    {e : RawPExpr Const BaseType}
    {pe : PExpr Const BaseType (ctxRaw.map (·.2)) ty}
    [HasType ctxRaw e ty]
    (h : RawPExpr.elab? ctxRaw e = some ⟨ty, pe⟩) :
    RawPExpr.toPExprElab ctxRaw ty e = pe := by
  unfold RawPExpr.toPExprElab
  split
  · rename_i ty' pe' hc
    have hs : Sigma.mk ty' pe' = Sigma.mk ty pe := Option.some.inj (hc.symm.trans h)
    cases hs
    rw [cast_eq]
  · rename_i hc
    rw [hc] at h
    simp at h

private theorem elab?_reluMatmulRaw_eq_generatedPartial
    {ctx : List (Name × T)} {m n k : ℕ} :
    RawPExpr.elab? ctx (reluMatmulRaw m n k) =
      some ⟨reluMatmulTy m n k,
        (RawPExpr.Partial.generatedPartial ctx (reluMatmulTy m n k)
          (reluMatmulRaw m n k)
          (reluMatmulRaw_generatedPartial_isSome (ctx := ctx) (m := m) (n := n) (k := k))).toPExpr⟩ := by
  simp [RawPExpr.elab?, RawPExpr.Partial.generatedPartial,
    RawPExpr.Partial.generatedPartial?, RawPExpr.Partial.partialOfRawWithLocalsAs?,
    RawPExpr.Partial.ofRawWithLocals?, RawPExpr.Partial.findVarWithLocals?,
    RawPExpr.Partial.toPExpr, reluMatmulRaw, reluMatmulTy, Typed.type,
    List.findFinIdx?, List.findFinIdx?.go, List.map_cons, List.length_cons,
    Nat.reduceAdd, Option.bind, Option.pure_def, dif_pos, cast_eq]
  congr <;> simp

private theorem elab?_matmulReluSCF_eq_generatedPartial
    {ctx : List (Name × S)} {m n k : ℕ} :
    RawPExpr.elab? ctx (matmulReluSCF m n k) =
      some ⟨matmulReluSCFTy m n k,
        (RawPExpr.Partial.generatedPartial ctx (matmulReluSCFTy m n k)
          (matmulReluSCF m n k)
          (matmulReluSCF_generatedPartial_isSome (ctx := ctx) (m := m) (n := n) (k := k))).toPExpr⟩ := by
  simp [RawPExpr.elab?, RawPExpr.Partial.generatedPartial,
    RawPExpr.Partial.generatedPartial?, RawPExpr.Partial.partialOfRawWithLocalsAs?,
    RawPExpr.Partial.ofRawWithLocals?, RawPExpr.Partial.findVarWithLocals?,
    RawPExpr.Partial.toPExpr, matmulReluSCF, matmulReluSCFTy, T.toS,
    LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf, Typed.type,
    List.findFinIdx?, List.findFinIdx?.go, List.map_cons, List.length_cons,
    Nat.reduceAdd, Fin.cast_eq_self, Option.bind, Option.pure_def, dif_pos, cast_eq]
  congr <;> simp

private theorem toPExprElab_reluMatmulRaw_eq_generatedPartial
    {ctx : List (Name × T)} {m n k : ℕ}
    [HasType ctx (reluMatmulRaw m n k) (reluMatmulTy m n k)] :
    RawPExpr.toPExprElab ctx (reluMatmulTy m n k) (reluMatmulRaw m n k) =
      (RawPExpr.Partial.generatedPartial ctx (reluMatmulTy m n k)
        (reluMatmulRaw m n k)
        (reluMatmulRaw_generatedPartial_isSome (ctx := ctx) (m := m) (n := n) (k := k))).toPExpr :=
  RawPExpr.toPExprElab_of_elab?_eq
    (h := elab?_reluMatmulRaw_eq_generatedPartial (ctx := ctx) (m := m) (n := n) (k := k))

private theorem toPExprElab_matmulReluSCF_eq_generatedPartial
    {ctx : List (Name × S)} {m n k : ℕ}
    [HasType ctx (matmulReluSCF m n k) (matmulReluSCFTy m n k)] :
    RawPExpr.toPExprElab ctx (matmulReluSCFTy m n k) (matmulReluSCF m n k) =
      (RawPExpr.Partial.generatedPartial ctx (matmulReluSCFTy m n k)
        (matmulReluSCF m n k)
        (matmulReluSCF_generatedPartial_isSome (ctx := ctx) (m := m) (n := n) (k := k))).toPExpr :=
  RawPExpr.toPExprElab_of_elab?_eq
    (h := elab?_matmulReluSCF_eq_generatedPartial (ctx := ctx) (m := m) (n := n) (k := k))

private theorem inferType_isSome_of_hasType
    {Const BaseType : Type} [Typed Const (PType BaseType)] [DecidableEq BaseType]
    {ctxRaw : List (Name × PType BaseType)} {e : RawPExpr Const BaseType}
    {ty : PType BaseType}
    (h : HasType ctxRaw e ty) :
    (RawPExpr.inferType ctxRaw e).isSome := by
  rw [h.hasType]
  simp

private theorem reluMatmulApp_isSome
    {ctx : List (Name × T)} {m n k : ℕ}
    {A B : RawPExpr LinalgConst LinalgBaseType}
    (hA : HasType ctx A (PType.ofBase (LinalgBaseType.tensor [m, k])))
    (hB : HasType ctx B (PType.ofBase (LinalgBaseType.tensor [k, n]))) :
    (RawPExpr.inferType ctx
      ((RawPExpr.const (LinalgConst.relu [m, n])).app
        (((RawPExpr.const (LinalgConst.matmul m n k)).app A).app B))).isSome := by
  letI := hA
  letI := hB
  exact inferType_isSome_of_hasType
    (inferInstance : HasType ctx
      ((RawPExpr.const (LinalgConst.relu [m, n])).app
        (((RawPExpr.const (LinalgConst.matmul m n k)).app A).app B))
      (PType.ofBase (LinalgBaseType.tensor [m, n])))

private theorem reluMatmulRawApp_isSome
    {ctx : List (Name × T)} {m n k : ℕ}
    {A B : RawPExpr LinalgConst LinalgBaseType}
    (hA : HasType ctx A (PType.ofBase (LinalgBaseType.tensor [m, k])))
    (hB : HasType ctx B (PType.ofBase (LinalgBaseType.tensor [k, n]))) :
    (RawPExpr.inferType ctx (((reluMatmulRaw m n k).app A).app B)).isSome := by
  letI := reluMatmulRaw_hasType (ctx := ctx) (m := m) (n := n) (k := k)
  letI := hA
  letI := hB
  exact inferType_isSome_of_hasType
    (inferInstance : HasType ctx (((reluMatmulRaw m n k).app A).app B)
      (PType.ofBase (LinalgBaseType.tensor [m, n])))

private theorem matmulReluSCFApp_isSome
    {ctx : List (Name × T)} {m n k : ℕ}
    {A' B' : RawPExpr SCFConst SCFBaseType}
    (hA' : HasType (ctxS ctx) A' (T.toS (PType.ofBase (LinalgBaseType.tensor [m, k]))))
    (hB' : HasType (ctxS ctx) B' (T.toS (PType.ofBase (LinalgBaseType.tensor [k, n])))) :
    (RawPExpr.inferType (ctxS ctx)
      (((matmulReluSCF m n k).app A').app B')).isSome := by
  letI := hA'
  letI := hB'
  exact inferType_isSome_of_hasType
    (inferInstance : HasType (ctxS ctx)
      (((matmulReluSCF m n k).app A').app B')
      (T.toS (PType.ofBase (LinalgBaseType.tensor [m, n]))))

private theorem interp_toPExpr_heq_generatedApp2
    {Const BaseType : Type} [BasedType BaseType] [Typed Const (PType BaseType)]
    [DecidableEq BaseType] [Interp BaseType Const]
    {ctxRaw : List (Name × PType BaseType)}
    {arg₁ arg₂ out : PType BaseType}
    {fRaw a b : RawPExpr Const BaseType}
    [HasType ctxRaw fRaw (arg₁.fun (arg₂.fun out))]
    (ha : HasType ctxRaw a arg₁) (hb : HasType ctxRaw b arg₂)
    (hf : (RawPExpr.Partial.generatedPartial? ctxRaw (arg₁.fun (arg₂.fun out)) fRaw).isSome)
    (hFgen : RawPExpr.toPExprElab ctxRaw (arg₁.fun (arg₂.fun out)) fRaw =
      (RawPExpr.Partial.generatedPartial ctxRaw (arg₁.fun (arg₂.fun out)) fRaw hf).toPExpr)
    (he : (RawPExpr.inferType ctxRaw ((fRaw.app a).app b)).isSome) :
    (fun args => interp args (RawPExpr.toPExpr ctxRaw ((fRaw.app a).app b) he)) ≍
    fun args => interp args
      (RawPExpr.Partial.generatedApp2
        (ctxRaw := ctxRaw) (arg₁ := arg₁) (arg₂ := arg₂) (out := out)
        fRaw hf ha hb).toPExpr := by
  letI := ha
  letI := hb
  have hfa : HasType ctxRaw (fRaw.app a) (arg₂.fun out) := inferInstance
  letI := hfa
  have hRaw := RawPExpr.interp_toPExpr_heq_toPExprElab
    (ctxRaw := ctxRaw) (e := (fRaw.app a).app b) (ty := out) he
  have hElab :
      RawPExpr.toPExprElab ctxRaw out ((fRaw.app a).app b) =
        (RawPExpr.Partial.generatedApp2
          (ctxRaw := ctxRaw) (arg₁ := arg₁) (arg₂ := arg₂) (out := out)
          fRaw hf ha hb).toPExpr := by
    rw [RawPExpr.toPExprElab_app
      (f := fRaw.app a) (a := b) (A := arg₂) (B := out)]
    rw [RawPExpr.toPExprElab_app
      (f := fRaw) (a := a) (A := arg₁) (B := arg₂.fun out)]
    simp [RawPExpr.Partial.toPExpr, hFgen]
  rw [hElab] at hRaw
  exact hRaw

/-- Correctness of the fused relu-matmul lowering:
given correct lowerings `A'` and `B'` of `A` and `B`, the lowered raw expression has
the same interpretation as the original raw `relu(matmul A B)` expression. -/
theorem lowerRaw_reluMatmul_correct
    {ctx : List (Name × T)}
    {m n k : ℕ}
    {A B : RawPExpr LinalgConst LinalgBaseType}
    {A' B' : RawPExpr SCFConst SCFBaseType}
    (hA : HasType ctx A (PType.ofBase (LinalgBaseType.tensor [m, k])))
    (hB : HasType ctx B (PType.ofBase (LinalgBaseType.tensor [k, n])))
    (hA' : HasType (ctxS ctx) A' (T.toS (PType.ofBase (LinalgBaseType.tensor [m, k]))))
    (hB' : HasType (ctxS ctx) B' (T.toS (PType.ofBase (LinalgBaseType.tensor [k, n]))))
    (hcorrA :
      (fun args => interp args
        (RawPExpr.toPExpr ctx A (inferType_isSome_of_hasType hA))) ≍
      fun args => interp args
        (RawPExpr.toPExpr (ctxS ctx) A' (inferType_isSome_of_hasType hA')))
    (hcorrB :
      (fun args => interp args
        (RawPExpr.toPExpr ctx B (inferType_isSome_of_hasType hB))) ≍
      fun args => interp args
        (RawPExpr.toPExpr (ctxS ctx) B' (inferType_isSome_of_hasType hB'))) :
    (fun args => interp args
      (RawPExpr.toPExpr ctx
        (((reluMatmulRaw m n k).app A).app B)
        (reluMatmulRawApp_isSome hA hB))) ≍
    fun args => interp args
      (RawPExpr.toPExpr (ctxS ctx)
        (((matmulReluSCF m n k).app A').app B')
        (matmulReluSCFApp_isSome hA' hB')) := by
  letI := hA
  letI := hB
  letI := hA'
  letI := hB'
  have hA_to_elab := RawPExpr.interp_toPExpr_heq_toPExprElab
    (ctxRaw := ctx) (e := A) (ty := PType.ofBase (LinalgBaseType.tensor [m, k]))
    (inferType_isSome_of_hasType hA)
  have hA'_to_elab := RawPExpr.interp_toPExpr_heq_toPExprElab
    (ctxRaw := ctxS ctx) (e := A')
    (ty := T.toS (PType.ofBase (LinalgBaseType.tensor [m, k])))
    (inferType_isSome_of_hasType hA')
  have hcorrA_elab :
      (fun args => interp args
        (RawPExpr.toPExprElab ctx (PType.ofBase (LinalgBaseType.tensor [m, k])) A)) ≍
      fun args => interp args
        (RawPExpr.toPExprElab (ctxS ctx)
          (T.toS (PType.ofBase (LinalgBaseType.tensor [m, k]))) A') := by
    exact hA_to_elab.symm.trans (hcorrA.trans hA'_to_elab)
  have hB_to_elab := RawPExpr.interp_toPExpr_heq_toPExprElab
    (ctxRaw := ctx) (e := B) (ty := PType.ofBase (LinalgBaseType.tensor [k, n]))
    (inferType_isSome_of_hasType hB)
  have hB'_to_elab := RawPExpr.interp_toPExpr_heq_toPExprElab
    (ctxRaw := ctxS ctx) (e := B')
    (ty := T.toS (PType.ofBase (LinalgBaseType.tensor [k, n])))
    (inferType_isSome_of_hasType hB')
  have hcorrB_elab :
      (fun args => interp args
        (RawPExpr.toPExprElab ctx (PType.ofBase (LinalgBaseType.tensor [k, n])) B)) ≍
      fun args => interp args
        (RawPExpr.toPExprElab (ctxS ctx)
          (T.toS (PType.ofBase (LinalgBaseType.tensor [k, n]))) B') := by
    exact hB_to_elab.symm.trans (hcorrB.trans hB'_to_elab)
  have hReluMatmulRaw : HasType ctx (reluMatmulRaw m n k) (reluMatmulTy m n k) := by
    exact reluMatmulRaw_hasType (ctx := ctx) (m := m) (n := n) (k := k)
  letI := hReluMatmulRaw
  have hMatmulReluSCF : HasType (ctxS ctx) (matmulReluSCF m n k) (matmulReluSCFTy m n k) := by
    apply HasType.mk
    interpvc [matmulReluSCFTy, matmulReluSCF, T.toS,
      LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf]
  letI := hMatmulReluSCF
  have hIn_to_partial := interp_toPExpr_heq_generatedApp2
    (ctxRaw := ctx)
    (arg₁ := PType.ofBase (LinalgBaseType.tensor [m, k]))
    (arg₂ := PType.ofBase (LinalgBaseType.tensor [k, n]))
    (out := PType.ofBase (LinalgBaseType.tensor [m, n]))
    (fRaw := reluMatmulRaw m n k) (a := A) (b := B)
    hA hB
    (reluMatmulRaw_generatedPartial_isSome (ctx := ctx) (m := m) (n := n) (k := k))
    (toPExprElab_reluMatmulRaw_eq_generatedPartial (ctx := ctx) (m := m) (n := n) (k := k))
    (reluMatmulRawApp_isSome hA hB)
  have hOut_to_partial := interp_toPExpr_heq_generatedApp2
    (ctxRaw := ctxS ctx)
    (arg₁ := T.toS (PType.ofBase (LinalgBaseType.tensor [m, k])))
    (arg₂ := T.toS (PType.ofBase (LinalgBaseType.tensor [k, n])))
    (out := T.toS (PType.ofBase (LinalgBaseType.tensor [m, n])))
    (fRaw := matmulReluSCF m n k) (a := A') (b := B')
    hA' hB'
    (matmulReluSCF_generatedPartial_isSome (ctx := ctxS ctx) (m := m) (n := n) (k := k))
    (toPExprElab_matmulReluSCF_eq_generatedPartial (ctx := ctxS ctx) (m := m) (n := n) (k := k))
    (matmulReluSCFApp_isSome hA' hB')
  exact hIn_to_partial.trans
    ((lowerRaw_reluMatmul_correct_partial hA hB hA' hB' hcorrA_elab hcorrB_elab).trans
      hOut_to_partial.symm)
/-
  todo :: make a general purpose lowering functions that takes in a Const.lower along with a `preprocess : RawPExpr → (k : RawPExpr → RawPExpr) → Option RawPExpr`
  (use the continutation passing recursor pattern) function
  - it will lower the expr normally and call Const.lower for the const lowering
  - and preprocosses will return some if non trivial lowering is done (not just const, ie optimizaiton pass eg: FuseReluMatmul)

  todo:: add faifullness of lowering condition to subtype property (ie interping the lowered result gives the same result and interping the original)
-/
def lowerRaw : (ctxL : List (Name × T)) → (ty : T) → (e : RawPExpr LinalgConst LinalgBaseType) →
  [HasType ctxL e ty] → {x : RawPExpr SCFConst SCFBaseType // HasType (ctxS ctxL) x (T.toS ty)}
| ctx, ty, .app (.const (.relu shape)) (.app (.app (.const (.matmul m n k)) A) B), ⟨he⟩ =>
  let e : RawPExpr LinalgConst LinalgBaseType := .app (.const (.relu shape)) (.app (.app (.const (.matmul m n k)) A) B)
  have ⟨_, hA, hB, hty⟩ : shape = [m, n] ∧
    HasType ctx A (PType.ofBase (LinalgBaseType.tensor [m, k])) ∧
    HasType ctx B (PType.ofBase (LinalgBaseType.tensor [k, n])) ∧
    ty = PType.ofBase (LinalgBaseType.tensor [m, n]) := by
    simp only [RawPExpr.inferType, Option.pure_def, Option.bind_eq_bind, Option.bind_fun_none,
      Option.bind_some, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq,
      ↓existsAndEq, true_and, and_true, PType.ofBase.injEq, LinalgBaseType.tensor.injEq] at he
    grind [HasType]
  have he' : HasType ctx e (PType.ofBase (LinalgBaseType.tensor [m, n])) := by
    apply HasType.mk
    simp only [e, RawPExpr.inferType, Option.pure_def, Option.bind_eq_bind, Option.bind_fun_none,
      Option.bind_some, Option.bind_eq_some_iff, Option.ite_none_right_eq_some, Option.some.injEq,
      ↓existsAndEq, true_and, and_true, PType.ofBase.injEq, LinalgBaseType.tensor.injEq]
    grind [HasType]
  let ⟨A', ⟨hA'⟩⟩ := lowerRaw ctx (PType.ofBase (LinalgBaseType.tensor [m, k])) A
  let ⟨B', hB'⟩ := lowerRaw ctx (PType.ofBase (LinalgBaseType.tensor [k, n])) B
  let outAux : RawPExpr SCFConst SCFBaseType := matmulReluSCF m n k
  have : HasType (ctxS ctx) outAux ((((PType.ofBase (SCFBaseType.fin m)).fun
            ((PType.ofBase (SCFBaseType.fin k)).fun (PType.ofBase SCFBaseType.float))).fun
        (((PType.ofBase (SCFBaseType.fin k)).fun
              ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float))).fun
          ((PType.ofBase (SCFBaseType.fin m)).fun
            ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float)))))) := by
    apply HasType.mk
    simp [RawPExpr.inferType, outAux, T.toS, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf, PExpr.RawPExpr.inferType, T.toS, ctxS, Typed.type, List.findFinIdx?, List.findFinIdx?.go]
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
      simp [RawPExpr.inferType, out, T.toS, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf, PExpr.RawPExpr.inferType, T.toS, ctxS, Typed.type, List.findFinIdx?, List.findFinIdx?.go]
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
| ctx, ty, .var name, he =>
  have hvar : HasType (ctxS ctx) (RawPExpr.var name) ty.toS := by
    have : HasVar (ctxS ctx) name ty.toS := by
      rw [PExpr.RawPExpr.HasType_iff_HasVar] at he
      simp [ctxS]
      apply PExpr.RawPExpr.HasVar_map
      grind [ctxS]
    infer_instance
  ⟨.var name, hvar⟩

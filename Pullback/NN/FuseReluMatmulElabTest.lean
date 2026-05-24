import Pullback.NN.FuseReluMatmul

open Lean
open PExpr

set_option linter.unusedSimpArgs false

namespace FuseReluMatmulElabTest

@[reducible]
def reluMatmulRaw (m n k : Nat) : RawPExpr LinalgConst LinalgBaseType := rpexpr{
  fun A : b(.tensor [m, k]) =>
  fun B : b(.tensor [k, n]) =>
    c(.relu [m, n]) (c(.matmul m n k) A B)
}

@[reducible]
def reluMatmulTy (m n k : Nat) : T :=
  (PType.ofBase (LinalgBaseType.tensor [m, k])).fun
    ((PType.ofBase (LinalgBaseType.tensor [k, n])).fun
      (PType.ofBase (LinalgBaseType.tensor [m, n])))

theorem inferType_reluMatmulRaw {ctx : List (Name × T)} {m n k : Nat} :
    RawPExpr.inferType ctx (reluMatmulRaw m n k) = some (reluMatmulTy m n k) := by
  simp [RawPExpr.inferType, reluMatmulRaw, reluMatmulTy, Typed.type,
    List.findFinIdx?, List.findFinIdx?.go]

instance instHasType_reluMatmulRaw {ctx : List (Name × T)} {m n k : Nat} :
    HasType ctx (reluMatmulRaw m n k) (reluMatmulTy m n k) :=
  HasType.mk inferType_reluMatmulRaw

@[reducible]
def matmulReluSCFTy (m n k : Nat) : S :=
  (((PType.ofBase (SCFBaseType.fin m)).fun
      ((PType.ofBase (SCFBaseType.fin k)).fun (PType.ofBase SCFBaseType.float))).fun
    (((PType.ofBase (SCFBaseType.fin k)).fun
        ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float))).fun
      ((PType.ofBase (SCFBaseType.fin m)).fun
        ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float)))))

@[reducible] def SF : S := PType.ofBase SCFBaseType.float
@[reducible] def SFin (n : Nat) : S := PType.ofBase (SCFBaseType.fin n)
@[reducible] def STensor2 (m n : Nat) : S :=
  T.toS (PType.ofBase (LinalgBaseType.tensor [m, n]))

abbrev SPartial (ctx : List (Name × S)) (ty : S) : Type :=
  RawPExpr.Partial (Const := SCFConst) (BaseType := SCFBaseType) ctx ty

@[reducible]
def partialOfRawWithLocalsAs? {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) (ty : PType BaseType)
    (e : RawPExpr Const BaseType) :
    Option (RawPExpr.Partial (Const := Const) (BaseType := BaseType) ctxRaw ty) :=
  match RawPExpr.Partial.ofRawWithLocals? ctxRaw [] e with
  | some ⟨ty', pe⟩ =>
      if h : ty' = ty then
        some (h ▸ pe)
      else
        none
  | none => none

@[reducible]
def generatedPartial? {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) (ty : PType BaseType)
    (e : RawPExpr Const BaseType) :
    Option (RawPExpr.Partial (Const := Const) (BaseType := BaseType) ctxRaw ty) :=
  partialOfRawWithLocalsAs? ctxRaw ty e

@[reducible]
def generatedPartial {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) (ty : PType BaseType)
    (e : RawPExpr Const BaseType) (h : (generatedPartial? ctxRaw ty e).isSome) :
    RawPExpr.Partial (Const := Const) (BaseType := BaseType) ctxRaw ty :=
  (generatedPartial? ctxRaw ty e).get h

@[reducible]
def partialApp2 {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    {ctxRaw : List (Name × PType BaseType)} {arg₁ arg₂ out : PType BaseType}
    (f : RawPExpr.Partial (Const := Const) (BaseType := BaseType) ctxRaw
      (arg₁.fun (arg₂.fun out)))
    {a b : RawPExpr Const BaseType}
    (ha : HasType ctxRaw a arg₁) (hb : HasType ctxRaw b arg₂) :
    RawPExpr.Partial (Const := Const) (BaseType := BaseType) ctxRaw out :=
  RawPExpr.Partial.app
    (RawPExpr.Partial.app f (RawPExpr.Partial.hole a ha))
    (RawPExpr.Partial.hole b hb)

@[reducible]
def matmulReluSCFPartialGenerated? (ctx : List (Name × S)) (m n k : Nat) :
    Option (SPartial ctx (matmulReluSCFTy m n k)) :=
  generatedPartial? ctx (matmulReluSCFTy m n k) (matmulReluSCF m n k)

theorem matmulReluSCFPartialGenerated_isSome (ctx : List (Name × S)) (m n k : Nat) :
    (matmulReluSCFPartialGenerated? ctx m n k).isSome := by
  simp [matmulReluSCFPartialGenerated?, generatedPartial?, partialOfRawWithLocalsAs?,
    RawPExpr.Partial.ofRawWithLocals?, RawPExpr.Partial.findVarWithLocals?,
    List.findFinIdx?, List.findFinIdx?.go, matmulReluSCFTy, matmulReluSCF, T.toS,
    LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf, Typed.type]

@[reducible]
def matmulReluSCFPartial (ctx : List (Name × S)) (m n k : Nat) :
    SPartial ctx (matmulReluSCFTy m n k) :=
  generatedPartial ctx (matmulReluSCFTy m n k) (matmulReluSCF m n k)
    (matmulReluSCFPartialGenerated_isSome ctx m n k)

@[reducible]
def matmulReluSCFAppPartial
    {ctx : List (Name × T)} {m n k : Nat}
    {A' B' : RawPExpr SCFConst SCFBaseType}
    (hA' : HasType (ctxS ctx) A' (STensor2 m k))
    (hB' : HasType (ctxS ctx) B' (STensor2 k n)) :
    SPartial (ctxS ctx) (STensor2 m n) :=
  partialApp2 (matmulReluSCFPartial (ctxS ctx) m n k) hA' hB'

/-- The generated partial skeleton is available with a generalized ambient context; no
handwritten `Partial` tree or explicit variable indices are needed at the call site. -/
example (ctx : List (Name × S)) (m n k : Nat) :
    (matmulReluSCFPartialGenerated? ctx m n k).isSome := by
  exact matmulReluSCFPartialGenerated_isSome ctx m n k

example
    {ctx : List (Name × T)} {m n k : Nat}
    {A' B' : RawPExpr SCFConst SCFBaseType}
    [hA' : HasType (ctxS ctx) A' (STensor2 m k)]
    [hB' : HasType (ctxS ctx) B' (STensor2 k n)] :
    SPartial (ctxS ctx) (STensor2 m n) :=
  matmulReluSCFAppPartial
    (ctx := ctx) (m := m) (n := n) (k := k) (A' := A') (B' := B') hA' hB'

/-- The canonical elaborator recovers the old closed relu-matmul simplification without
using the `reduce_toPExpr'` simproc. -/
example :
    ((reluMatmulRaw 2 5 3).toPExprElab [] (reluMatmulTy 2 5 3)).interp
      (cast (by simp [DVector]) Unit.unit)
    = fun A : NDArray Float [2, 3] =>
        fun B : NDArray Float [3, 5] =>
          NDArray.map relu (matmul A B) := by
  simp only [RawPExpr.toPExprElab, RawPExpr.elab?, reluMatmulRaw, reluMatmulTy,
    Typed.type, Interp.interp, PExpr.interp, List.findFinIdx?, List.findFinIdx?.go,
    List.map_nil, List.map_cons, List.length_cons, List.length_nil, Nat.reduceAdd,
    Fin.cast_eq_self, cast_eq, ↓DVector.reduceGet, ↓reduceIte, Option.bind,
    Option.pure_def, dif_pos]
  simp [Option.bind, PExpr.interp, Interp.interp, cast_eq, ↓reduceIte, dif_pos]
  rfl

/-- The fused SCF expression also unfolds through the canonical elaborator without the
custom `toPExpr'` simproc. -/
example :
    ((matmulReluSCF 2 5 3).toPExprElab [] (matmulReluSCFTy 2 5 3)).interp
      (cast (by simp [DVector]) Unit.unit)
    = fun A' : (T.toS (PType.ofBase (LinalgBaseType.tensor [2, 3]))).type =>
        fun B' : (T.toS (PType.ofBase (LinalgBaseType.tensor [3, 5]))).type =>
          fun i : Fin 2 =>
            fun j : Fin 5 =>
              relu (foldl 3
                (fun acc t => add acc (mul ((A' i) t) ((B' t) j)))
                0) := by
  simp only [RawPExpr.toPExprElab, RawPExpr.elab?, matmulReluSCF, matmulReluSCFTy, T.toS,
    LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf, Typed.type, Interp.interp,
    PExpr.interp, List.findFinIdx?, List.findFinIdx?.go, List.map_nil, List.map_cons,
    List.length_cons, List.length_nil, Nat.reduceAdd, Fin.cast_eq_self, cast_eq,
    ↓DVector.reduceGet, ↓reduceIte, Option.bind, Option.pure_def, dif_pos]
  simp [Option.bind, PExpr.interp, Interp.interp, cast_eq, ↓reduceIte, dif_pos]
  rfl

/-- Generated Linalg skeleton partial from the closed `reluMatmulRaw` `rpexpr{...}`. -/
@[reducible]
def reluMatmulPartialGenerated? (ctx : List (Name × T)) (m n k : Nat) :
    Option (RawPExpr.Partial (Const := LinalgConst) (BaseType := LinalgBaseType) ctx
      (reluMatmulTy m n k)) :=
  generatedPartial? ctx (reluMatmulTy m n k) (reluMatmulRaw m n k)

theorem reluMatmulPartialGenerated_isSome (ctx : List (Name × T)) (m n k : Nat) :
    (reluMatmulPartialGenerated? ctx m n k).isSome := by
  simp [reluMatmulPartialGenerated?, generatedPartial?, partialOfRawWithLocalsAs?,
    RawPExpr.Partial.ofRawWithLocals?, RawPExpr.Partial.findVarWithLocals?,
    List.findFinIdx?, List.findFinIdx?.go, reluMatmulRaw, reluMatmulTy, Typed.type]

example (ctx : List (Name × T)) (m n k : Nat) :
    (reluMatmulPartialGenerated? ctx m n k).isSome := by
  exact reluMatmulPartialGenerated_isSome ctx m n k

@[reducible]
def reluMatmulPartial (ctx : List (Name × T)) (m n k : Nat) :
    RawPExpr.Partial (Const := LinalgConst) (BaseType := LinalgBaseType) ctx (reluMatmulTy m n k) :=
  generatedPartial ctx (reluMatmulTy m n k) (reluMatmulRaw m n k)
    (reluMatmulPartialGenerated_isSome ctx m n k)

/-- Linalg open expression `relu(matmul A B)` as a `Partial` with typed holes for `A` and `B`. -/
@[reducible]
def reluMatmulAppPartial
    {ctx : List (Name × T)} {m n k : Nat}
    {A B : RawPExpr LinalgConst LinalgBaseType}
    (hA : HasType ctx A (PType.ofBase (LinalgBaseType.tensor [m, k])))
    (hB : HasType ctx B (PType.ofBase (LinalgBaseType.tensor [k, n]))) :
    RawPExpr.Partial (Const := LinalgConst) (BaseType := LinalgBaseType)
      ctx (PType.ofBase (LinalgBaseType.tensor [m, n])) :=
  partialApp2 (reluMatmulPartial ctx m n k) hA hB

/-- The Linalg open expression `relu(matmul A B)` unfolds structurally through
`Partial.toPExpr`, leaving only the typed holes for `A` and `B`. -/
theorem reluMatmulAppPartial_interp_eq
    {ctx : List (Name × T)} {m n k : Nat}
    {A B : RawPExpr LinalgConst LinalgBaseType}
    (hA : HasType ctx A (PType.ofBase (LinalgBaseType.tensor [m, k])))
    (hB : HasType ctx B (PType.ofBase (LinalgBaseType.tensor [k, n]))) :
    (fun args => interp args (reluMatmulAppPartial hA hB).toPExpr) =
    fun args => NDArray.map relu
      (matmul
        (interp args (RawPExpr.toPExprElab ctx (PType.ofBase (LinalgBaseType.tensor [m, k])) A))
        (interp args (RawPExpr.toPExprElab ctx (PType.ofBase (LinalgBaseType.tensor [k, n])) B))) := by
  funext args
  simp only [reluMatmulAppPartial, reluMatmulPartial, reluMatmulPartialGenerated?,
    partialApp2, generatedPartial, generatedPartial?, RawPExpr.Partial.toPExpr,
    PExpr.interp, Interp.interp, cast_eq]
  simp [partialOfRawWithLocalsAs?, RawPExpr.Partial.ofRawWithLocals?,
    RawPExpr.Partial.findVarWithLocals?, inferType_reluMatmulRaw, reluMatmulRaw,
    reluMatmulTy, Typed.type, List.findFinIdx?, List.findFinIdx?.go, List.map_nil, List.map_cons,
    List.length_cons, List.length_nil, Nat.reduceAdd, Fin.cast_eq_self, Option.bind,
    Option.pure_def, dif_pos, PExpr.interp, Interp.interp, cast_eq, ↓DVector.reduceGet]
  simp [RawPExpr.Partial.toPExpr, PExpr.interp, Interp.interp, cast_eq,
    PType.type, BasedType.valueType, ↓DVector.reduceGet]
  congr

/-- The SCF open expression unfolds structurally through `Partial.toPExpr`, exposing the
fused `relu (foldl ...)` normal form and leaving only the typed holes for `A'` and `B'`. -/
theorem matmulReluSCFAppPartial_interp_eq
    {ctx : List (Name × T)} {m n k : Nat}
    {A' B' : RawPExpr SCFConst SCFBaseType}
    (hA' : HasType (ctxS ctx) A' (STensor2 m k))
    (hB' : HasType (ctxS ctx) B' (STensor2 k n)) :
    (fun args => interp args (matmulReluSCFAppPartial hA' hB').toPExpr) =
    fun args => fun i : Fin m => fun j : Fin n =>
      relu (foldl k
        (fun acc t => add acc (mul
          (((interp args (RawPExpr.toPExprElab (ctxS ctx) (STensor2 m k) A')) i) t)
          (((interp args (RawPExpr.toPExprElab (ctxS ctx) (STensor2 k n) B')) t) j)))
        0) := by
  funext args
  simp only [matmulReluSCFAppPartial, matmulReluSCFPartial, matmulReluSCFPartialGenerated?,
    partialApp2, generatedPartial, generatedPartial?, RawPExpr.Partial.toPExpr,
    PExpr.interp, Interp.interp, cast_eq]
  simp [partialOfRawWithLocalsAs?, RawPExpr.Partial.ofRawWithLocals?,
    RawPExpr.Partial.findVarWithLocals?, matmulReluSCF, inferType_matmulReluSCF,
    matmulReluSCFTy, T.toS, LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf,
    Typed.type, List.findFinIdx?, List.findFinIdx?.go, List.map_nil, List.map_cons,
    List.length_cons, List.length_nil, Nat.reduceAdd, Fin.cast_eq_self, Option.bind,
    Option.pure_def, dif_pos, PExpr.interp, Interp.interp, cast_eq, ↓DVector.reduceGet]
  simp [RawPExpr.Partial.toPExpr, PExpr.interp, Interp.interp, cast_eq, ↓DVector.reduceGet,
    PType.type, BasedType.valueType, STensor2, T.toS, LinalgBaseType.toSCF,
    LinalgBaseType.tensor_toscf]
  funext i j
  congr

/-- Correctness of the fused relu-matmul lowering using the generated `Partial` pipeline:
given correct lowerings `A'` and `B'` of `A` and `B`, the generated SCF partial
correctly lowers the generated Linalg partial for `relu(matmul A B)`. -/
theorem lowerRaw_reluMatmul_correct_partial
    {ctx : List (Name × T)}
    {m n k : Nat}
    {A B : RawPExpr LinalgConst LinalgBaseType}
    {A' B' : RawPExpr SCFConst SCFBaseType}
    (hA : HasType ctx A (PType.ofBase (LinalgBaseType.tensor [m, k])))
    (hB : HasType ctx B (PType.ofBase (LinalgBaseType.tensor [k, n])))
    (hA' : HasType (ctxS ctx) A' (STensor2 m k))
    (hB' : HasType (ctxS ctx) B' (STensor2 k n))
    (hcorrA :
      (fun args => interp args
        (RawPExpr.toPExprElab ctx (PType.ofBase (LinalgBaseType.tensor [m, k])) A)) ≍
      fun args => interp args (RawPExpr.toPExprElab (ctxS ctx) (STensor2 m k) A'))
    (hcorrB :
      (fun args => interp args
        (RawPExpr.toPExprElab ctx (PType.ofBase (LinalgBaseType.tensor [k, n])) B)) ≍
      fun args => interp args (RawPExpr.toPExprElab (ctxS ctx) (STensor2 k n) B')) :
    (fun args => interp args
      (reluMatmulAppPartial (ctx := ctx) (m := m) (n := n) (k := k)
        (A := A) (B := B) hA hB).toPExpr) ≍
    fun args => interp args
      (matmulReluSCFAppPartial (ctx := ctx) (m := m) (n := n) (k := k)
        (A' := A') (B' := B') hA' hB').toPExpr := by
  rw [reluMatmulAppPartial_interp_eq hA hB]
  rw [matmulReluSCFAppPartial_interp_eq hA' hB']
  apply Function.hfunext
  · apply congrArg DVector
    induction ctx with
    | nil => rfl
    | cons hd tl ih =>
        cases hd
        simp [ctxS, T.type_toS, ih]
  · intro args args' hargs
    have hAargs := congr_heq hcorrA hargs
    have hBargs := congr_heq hcorrB hargs
    rw [hAargs, hBargs, heq_eq_eq]
    simp only [NDArray.map, matmul, foldl, add, mul]

end FuseReluMatmulElabTest

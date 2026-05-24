import Pullback.NN.FuseReluMatmul

open Lean
open PExpr

set_option linter.unusedSimpArgs false

namespace FuseReluMatmulElabTest

@[reducible, simp]
def reluMatmulRaw (m n k : Nat) : RawPExpr LinalgConst LinalgBaseType := rpexpr{
  fun A : b(.tensor [m, k]) =>
  fun B : b(.tensor [k, n]) =>
    c(.relu [m, n]) (c(.matmul m n k) A B)
}

@[reducible, simp]
def matmulReluSCFRaw (m n k : Nat) : RawPExpr SCFConst SCFBaseType :=
  matmulReluSCF m n k

@[reducible, simp]
private def reluMatmulTy (m n k : Nat) : T :=
  (PType.ofBase (LinalgBaseType.tensor [m, k])).fun
    ((PType.ofBase (LinalgBaseType.tensor [k, n])).fun
      (PType.ofBase (LinalgBaseType.tensor [m, n])))

@[reducible, simp]
private def matmulReluSCFTy (m n k : Nat) : S :=
  (((PType.ofBase (SCFBaseType.fin m)).fun
      ((PType.ofBase (SCFBaseType.fin k)).fun (PType.ofBase SCFBaseType.float))).fun
    (((PType.ofBase (SCFBaseType.fin k)).fun
        ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float))).fun
      ((PType.ofBase (SCFBaseType.fin m)).fun
        ((PType.ofBase (SCFBaseType.fin n)).fun (PType.ofBase SCFBaseType.float)))))

@[reducible, simp]
private def STensor2 (m n : Nat) : S :=
  T.toS (PType.ofBase (LinalgBaseType.tensor [m, n]))

attribute [local simp] matmulReluSCF T.toS LinalgBaseType.toSCF LinalgBaseType.tensor_toscf

@[reducible]
private def partialOfRawWithLocalsAs? {Const BaseType : Type} [Typed Const (PType BaseType)]
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
private def generatedPartial? {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) (ty : PType BaseType)
    (e : RawPExpr Const BaseType) :
    Option (RawPExpr.Partial (Const := Const) (BaseType := BaseType) ctxRaw ty) :=
  partialOfRawWithLocalsAs? ctxRaw ty e

@[reducible]
private def generatedPartial {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    (ctxRaw : List (Name × PType BaseType)) (ty : PType BaseType)
    (e : RawPExpr Const BaseType) (h : (generatedPartial? ctxRaw ty e).isSome) :
    RawPExpr.Partial (Const := Const) (BaseType := BaseType) ctxRaw ty :=
  (generatedPartial? ctxRaw ty e).get h

@[reducible]
private def generatedApp2 {Const BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType]
    {ctxRaw : List (Name × PType BaseType)} {arg₁ arg₂ out : PType BaseType}
    (fRaw : RawPExpr Const BaseType)
    (hf : (generatedPartial? ctxRaw (arg₁.fun (arg₂.fun out)) fRaw).isSome)
    {a b : RawPExpr Const BaseType}
    (ha : HasType ctxRaw a arg₁) (hb : HasType ctxRaw b arg₂) :
    RawPExpr.Partial (Const := Const) (BaseType := BaseType) ctxRaw out :=
  RawPExpr.Partial.app
    (RawPExpr.Partial.app
      (generatedPartial ctxRaw (arg₁.fun (arg₂.fun out)) fRaw hf)
      (RawPExpr.Partial.hole a ha))
    (RawPExpr.Partial.hole b hb)

macro "interpvc" : tactic => `(tactic|
  (simp [generatedApp2, generatedPartial, generatedPartial?, partialOfRawWithLocalsAs?,
    RawPExpr.Partial.ofRawWithLocals?, RawPExpr.Partial.findVarWithLocals?,
    RawPExpr.Partial.toPExpr, PExpr.interp, Interp.interp, List.findFinIdx?,
    List.findFinIdx?.go, List.map_nil, List.map_cons, List.length_cons, List.length_nil,
    Nat.reduceAdd, Fin.cast_eq_self, Option.bind, Option.pure_def, dif_pos, cast_eq,
    ↓DVector.reduceGet, PType.type, BasedType.valueType, Typed.type, T.toS,
    LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf]
    <;> try (funext i j) <;> try congr)
)

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
    (generatedApp2
      (ctxRaw := ctx)
      (arg₁ := PType.ofBase (LinalgBaseType.tensor [m, k]))
      (arg₂ := PType.ofBase (LinalgBaseType.tensor [k, n]))
      (out := PType.ofBase (LinalgBaseType.tensor [m, n]))
      (reluMatmulRaw m n k)
      (by interpvc)
      hA hB).toPExpr) ≍
  fun args => interp args
    (generatedApp2
      (ctxRaw := ctxS ctx)
      (arg₁ := STensor2 m k)
      (arg₂ := STensor2 k n)
      (out := STensor2 m n)
      (matmulReluSCFRaw m n k)
      (by interpvc)
      hA' hB').toPExpr := by
  interpvc
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
    simp [NDArray.map, matmul, foldl, add, mul, STensor2, T.toS,
      LinalgBaseType.toSCF, LinalgBaseType.tensor_toscf, PType.type, BasedType.valueType,
      cast_eq]
    rfl

end FuseReluMatmulElabTest

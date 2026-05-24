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

instance instHasType_reluMatmulRaw {m n k : Nat} :
    HasType [] (reluMatmulRaw m n k) (reluMatmulTy m n k) := by
  inferHasType

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
def matmulReluSCFPartialGenerated? (ctx : List (Name × S)) (m n k : Nat) :
    Option (SPartial ctx (matmulReluSCFTy m n k)) :=
  RawPExpr.Partial.ofRawAsSplit? ctx (matmulReluSCFTy m n k) (matmulReluSCF m n k)

@[reducible]
def matmulReluSCFPartial (ctx : List (Name × S)) (m n k : Nat) :
    SPartial ctx (matmulReluSCFTy m n k) :=
  (RawPExpr.Partial.ofRawAsSplit? ctx (matmulReluSCFTy m n k) (matmulReluSCF m n k)).get (by
    simp [RawPExpr.Partial.ofRawAsSplit?, RawPExpr.Partial.ofRawWithLocals?,RawPExpr.Partial.findVarWithLocals?, List.findFinIdx?, List.findFinIdx?.go, Typed.type])

@[reducible]
def matmulReluSCFAppPartial
    {ctx : List (Name × T)} {m n k : Nat}
    {A' B' : RawPExpr SCFConst SCFBaseType}
    (hA' : HasType (ctxS ctx) A' (STensor2 m k))
    (hB' : HasType (ctxS ctx) B' (STensor2 k n)) :
    SPartial (ctxS ctx) (STensor2 m n) :=
  RawPExpr.Partial.app
    (RawPExpr.Partial.app
      (matmulReluSCFPartial (ctxS ctx) m n k)
      (RawPExpr.Partial.hole A' hA'))
    (RawPExpr.Partial.hole B' hB')

/-- The generated partial skeleton is available with a generalized ambient context; no
handwritten `Partial` tree or explicit variable indices are needed at the call site. -/
example (ctx : List (Name × S)) (m n k : Nat) :
    (matmulReluSCFPartialGenerated? ctx m n k).isSome := by
  simp [matmulReluSCFPartialGenerated?]
  simp [RawPExpr.Partial.ofRawAsSplit?, RawPExpr.Partial.ofRawWithLocals?,RawPExpr.Partial.findVarWithLocals?, List.findFinIdx?, List.findFinIdx?.go, Typed.type]

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

end FuseReluMatmulElabTest

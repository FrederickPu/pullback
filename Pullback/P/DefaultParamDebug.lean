import Pullback.P.RawPExpr
import Pullback.NN.FuseReluMatmul

open PExpr RawPExpr

#check reduce_toPExpr'
-- Proper test: relu takes tensor [m,n] -> tensor [m,n]
-- matmul m n k takes tensor [m,k] -> tensor [k,n] -> tensor [m,n]
example {m n k : Nat} :
  let ctx := [(`B, PType.ofBase (LinalgBaseType.tensor [k, n])), (`A, PType.ofBase (LinalgBaseType.tensor [m, k]))]
  let matmulAB := ((RawPExpr.const (LinalgConst.matmul m n k)).app (RawPExpr.var `A)).app (RawPExpr.var `B)
  let f := RawPExpr.const (LinalgConst.relu [m, n])
  -- have : HasType ctx matmulAB (PType.ofBase (LinalgBaseType.tensor [m, n])) := by simp [f, matmulAB, ctx];  inferHasType;
  have : HasType ctx (f.app matmulAB) (PType.ofBase (LinalgBaseType.tensor [m, n])) := by simp [f, matmulAB, ctx]; inferHasType
  (RawPExpr.app f matmulAB).toPExpr' ctx (PType.ofBase (LinalgBaseType.tensor [m, n]))
  =
  sorry := by
  extract_lets ctx matmulAB f this1
  simp [↓reduce_toPExpr']
  sorry

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
  simp [↓reduce_toPExpr']
  rfl

import Pullback.P.Basic
import Pullback.NN.FuseReluMatmul

open Lean Meta Simp

open Lean Meta Elab Term PrettyPrinter

open PExpr RawPExpr

#check Term.mkConst
def exprTypeOfMeta (e vars : Expr) : MetaM (Expr × Expr) := do
  let varsStx ← delab vars
  let eStx ← delab e
  let stx ←
    `(term|
      (PExpr.RawPExpr.inferType $varsStx $eStx).get
        (by simp [PExpr.RawPExpr.inferType,
                  List.findFinIdx?,
                  List.findFinIdx?.go,
                  Typed.type]))
  let term ←
    TermElabM.run' do
      elabTerm stx none

  let ty ← simpExpr term
    [`PExpr.RawPExpr.inferType,
     `List.findFinIdx?,
     `List.findFinIdx?.go,
     `Typed.type]

  let stxTy ← delab ty
  let hasTypeStx ←
    `(term|
      ((by inferHasType) : HasType $varsStx $eStx $stxTy))

  let proof ← TermElabM.run' do
    elabTermAndSynthesize hasTypeStx none

  return (ty, proof)

open Lean Meta Elab Tactic

partial def annotateRawPExpr (e vars : Expr) : TacticM Unit := do
  let rec go (e : Expr) (visited : Std.HashSet Expr) :
      TacticM (Std.HashSet Expr) := do
    if visited.contains e then
      return visited
    let visited := visited.insert e

    IO.println "bruh"

    -- let (ty, proof) ← liftMetaM do
    --   exprTypeOfMeta e vars

    -- let proofStx ← delab proof
    -- let varsStx ← delab vars
    -- let eStx ← delab e
    -- let eTypeStx ← delab (← Meta.inferType e)
    -- let tyStx ← delab ty

    -- let hName ← mkFreshUserName `ht
    -- withMainContext do
    --   evalTactic (← `(tactic|
    --     have $(mkIdent hName) : HasType $varsStx ($eStx : $eTypeStx) $tyStx := $proofStx
    --   ))

    match e with
    | Expr.app f a => do
        let visited ← go f visited
        let visited ← go a visited
        return visited
    | _ =>
        return visited

  let _ ← go e {}
  return ()

elab "annotate_raw" e:term "in" vars:term : tactic => do
  withMainContext do
    let eExpr ← Lean.Elab.Term.elabTerm e none
    let varsExpr ← Lean.Elab.Term.elabTerm vars none
    annotateRawPExpr eExpr varsExpr

/-- Term elaborator that delegates to `exprTypeOfMeta`. -/
elab "exprTypeOf'" e:term "in" vars:term : term => do

  -- turn syntax into Expr
  let eExpr ← elabTerm e none
  let varsExpr ← elabTerm vars none

  -- call your MetaM function
  let r ← exprTypeOfMeta eExpr varsExpr

  logInfo r.2

  -- return result as term
  return r.1

variable {m n k : Nat}
#check exprTypeOf (((RawPExpr.const (LinalgConst.matmul m n k)).app (RawPExpr.var `A)).app (RawPExpr.var `B) : RawPExpr LinalgConst LinalgBaseType) in [(`B, PType.ofBase (LinalgBaseType.tensor [k, n])), (`A, PType.ofBase (LinalgBaseType.tensor [m, k]))]
/-
PType.ofBase (LinalgBaseType.tensor [m, n]) : PType LinalgBaseType
-/
#check exprTypeOf' (((RawPExpr.const (LinalgConst.matmul m n k)).app (RawPExpr.var `A)).app (RawPExpr.var `B) : RawPExpr LinalgConst LinalgBaseType) in [(`B, PType.ofBase (LinalgBaseType.tensor [k, n])), (`A, PType.ofBase (LinalgBaseType.tensor [m, k]))]
/-
Unknown constant `RawPExpr.inferType`
-/

-- #check PExpr.RawPExpr.app
-- /-
-- {Const BaseType : Type} → PExpr.RawPExpr Const BaseType → PExpr.RawPExpr Const BaseType → PExpr.RawPExpr Const BaseType
-- -/
-- #check @PExpr.RawPExpr.toPExpr'
-- /-
-- @PExpr.RawPExpr.toPExpr' : {BaseType Const : Type} →
--   [inst : DecidableEq BaseType] →
--     [inst_1 : Typed Const (PType BaseType)] →
--       (ctxRaw : List (Name × PType BaseType)) →
--         (ty : PType BaseType) →
--           (e : PExpr.RawPExpr Const BaseType) →
--             [PExpr.HasType ctxRaw e ty] → PExpr Const BaseType (List.map (fun x => x.2) ctxRaw) ty
-- -/
-- simproc ↓ [simp, seval] reduce_toPExpr' (PExpr.RawPExpr.toPExpr' _ _ (PExpr.RawPExpr.app _ _)) := fun e => do
--   logInfo m!"start"
--   let_expr eouter@PExpr.RawPExpr.toPExpr' BaseType Const hd ht ctxRaw ty ee inst ← e | return .continue
--   let_expr eapp@PExpr.RawPExpr.app _ _ f x ← ee | return .continue
--   let inferX := mkApp (mkConst ``PExpr.RawPExpr.inferType)
--                       #[mkConst ``ctxRaw, x] -- NOTE: ctxRaw is already Expr in e, see below fix

--   let r ← simp inferX
--   let xty ←
--   return .continue

open PExpr RawPExpr HasType Lean Meta Simp

variable {Const Const' BaseType BaseType'} [DecidableEq BaseType] [BasedType BaseType] [BasedType BaseType'] [DecidableEq BaseType'] [Typed Const (PType BaseType)] [Typed Const' (PType BaseType')]
variable [Interp BaseType Const] [Interp BaseType' Const']

@[simp]
theorem toPExpr'_app'
    {ctx : List (Name × PType BaseType)}
    {f a : RawPExpr Const BaseType}
    (A : PType BaseType)
    (B : PType BaseType)
    [hf : HasType ctx f (A.fun B)] [ha : HasType ctx a A] :
  (RawPExpr.app f a).toPExpr' ctx B
  =
  PExpr.app
    (f.toPExpr' ctx (A.fun B))
    (a.toPExpr' ctx A) := by
simp only [toPExpr']
rw! (castMode := .all) [hf.1]
simp [ha.1]
  -- get thing expr for f from lctx
  -- get expr for ctx from lctx
  -- exprTypeOfMeta
sorry


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
  let x := ((RawPExpr.app f matmulAB) : RawPExpr LinalgConst LinalgBaseType)
  /-
  failed to synthesize
  Typed ?m.101 (PType ?m.106)
  -/
  annotate_raw ((RawPExpr.app f matmulAB) : RawPExpr LinalgConst LinalgBaseType) in ctx
  -- rw [toPExpr'_app']

-- Proper test: relu takes tensor [m,n] -> tensor [m,n]
-- matmul m n k takes tensor [m,k] -> tensor [k,n] -> tensor [m,n]
example {m n k : Nat} :
  let ctx := [(`B, PType.ofBase (LinalgBaseType.tensor [k, n])), (`A, PType.ofBase (LinalgBaseType.tensor [m, k]))]
  let matmulAB := ((RawPExpr.const (LinalgConst.matmul m n k)).app (RawPExpr.var `A)).app (RawPExpr.var `B)
  let f := RawPExpr.const (LinalgConst.relu [m, n])
  have : HasType ctx matmulAB (PType.ofBase (LinalgBaseType.tensor [m, n])) := by simp [f, matmulAB, ctx];  inferHasType;
  have : HasType ctx (f.app matmulAB) (PType.ofBase (LinalgBaseType.tensor [m, n])) := by simp [f, matmulAB, ctx]; inferHasType
  (RawPExpr.app f matmulAB).toPExpr' ctx (PType.ofBase (LinalgBaseType.tensor [m, n]))
  =
  PExpr.app
    (f.toPExpr' ctx (PType.fun (PType.ofBase (LinalgBaseType.tensor [m, n])) (PType.ofBase (LinalgBaseType.tensor [m, n]))))
    (matmulAB.toPExpr' ctx (PType.ofBase (LinalgBaseType.tensor [m, n]))) := by
  simp only [toPExpr'_app]
  sorry

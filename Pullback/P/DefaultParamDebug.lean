import Pullback.P.Basic
import Pullback.NN.FuseReluMatmul

open Lean Meta Simp

open Lean Meta Elab Term PrettyPrinter

open PExpr RawPExpr

#check Term.mkConst
def inferHasType (e vars : Expr) : MetaM (Expr × Expr) := do
  let e ← zetaReduce e
  let vars ← zetaReduce vars

  let inferTypeApp ← mkAppM ``PExpr.RawPExpr.inferType #[vars, e]
  let inferTypeApp ← instantiateMVars inferTypeApp

  -- Build isSome proof via tactic (same as `by simp [...]` in the original)
  let isSomeTy ← mkEq (← mkAppM ``Option.isSome #[inferTypeApp]) (mkConst ``Bool.true)
  let isSomeMvar ← mkFreshExprMVar (some isSomeTy)
  let _ ← TermElabM.run' do
    let remaining ← Lean.Elab.Tactic.run isSomeMvar.mvarId! do
      Lean.Elab.Tactic.evalTactic (← `(tactic| simp [PExpr.RawPExpr.inferType, List.findFinIdx?, List.findFinIdx?.go, Typed.type]))
    if !remaining.isEmpty then
      throwError "isSome simp left unsolved goals"

  -- Build the full `Option.get inferTypeApp proof` term, then simpExpr the whole thing
  let getApp ← mkAppOptM ``Option.get #[none, inferTypeApp, isSomeMvar]
  let ty ← simpExpr getApp
    [`PExpr.RawPExpr.inferType, `List.findFinIdx?, `List.findFinIdx?.go, `Typed.type]

  -- HasType proof via synthInstance
  let hasTypeTy ← mkAppM ``HasType #[vars, e, ty]
  let mvar ← mkFreshExprMVar (some hasTypeTy)
  let remaining ← TermElabM.run' do
    Lean.Elab.Tactic.run mvar.mvarId! do
      Lean.Elab.Tactic.evalTactic (← `(tactic| inferHasType))
  if !remaining.isEmpty then
    let goalStrs ← remaining.mapM fun g => do
      let fmt ← Meta.ppGoal g
      return fmt.pretty
    throwError "inferHasType left unsolved goals:\n{goalStrs.foldl (· ++ "\n---\n" ++ ·) ""}"
  let proof ← instantiateMVars mvar
  return (hasTypeTy, proof)

open Lean Meta Elab Tactic

partial def annotateRawPExpr (e vars : Expr) : TacticM Unit := do
  let rec go (e : Expr) (visited : Std.HashSet Expr) :
      TacticM (Std.HashSet Expr) := do
    if visited.contains e then
      return visited
    let visited := visited.insert e

    -- Check if e has type RawPExpr before annotating
    let eType ← liftMetaM do Meta.inferType e
    let isRawPExpr := eType.isAppOf ``PExpr.RawPExpr

    if isRawPExpr then
      let (ty, proof) ← liftMetaM do inferHasType e vars
      let goal ← getMainGoal
      let goal' ← goal.assert `hasType ty proof
      let (_, goal') ← goal'.intro1P
      replaceMainGoal [goal']

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
elab "exprHasType" e:term "in" vars:term : term => do

  -- turn syntax into Expr
  let eExpr ← elabTerm e none
  let varsExpr ← elabTerm vars none

  -- call your MetaM function
  let r ← inferHasType eExpr varsExpr

  -- logInfo r.2

  -- return result as term
  return r.1

variable {m n k : Nat}
#check exprTypeOf (((RawPExpr.const (LinalgConst.matmul m n k)).app (RawPExpr.var `A)).app (RawPExpr.var `B) : RawPExpr LinalgConst LinalgBaseType) in [(`B, PType.ofBase (LinalgBaseType.tensor [k, n])), (`A, PType.ofBase (LinalgBaseType.tensor [m, k]))]
/-
PType.ofBase (LinalgBaseType.tensor [m, n]) : PType LinalgBaseType
-/
#check exprHasType (((RawPExpr.const (LinalgConst.matmul m n k)).app (RawPExpr.var `A)).app (RawPExpr.var `B) : RawPExpr LinalgConst LinalgBaseType) in [(`B, PType.ofBase (LinalgBaseType.tensor [k, n])), (`A, PType.ofBase (LinalgBaseType.tensor [m, k]))]
-- isSome simp left unsolved goalsLean 4
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
  annotate_raw ((RawPExpr.app f matmulAB) : RawPExpr LinalgConst LinalgBaseType) in [(`B, PType.ofBase (LinalgBaseType.tensor [k, n])), (`A, PType.ofBase (LinalgBaseType.tensor [m, k]))]
  simp

  /-
  failed to synthesize
  Typed ?m.101 (PType ?m.106)
  -/
  -- annotate_raw ((RawPExpr.app f matmulAB) : RawPExpr LinalgConst LinalgBaseType) in ctx
  -- rw [toPExpr'_app']

-- -- Proper test: relu takes tensor [m,n] -> tensor [m,n]
-- -- matmul m n k takes tensor [m,k] -> tensor [k,n] -> tensor [m,n]
-- example {m n k : Nat} :
--   let ctx := [(`B, PType.ofBase (LinalgBaseType.tensor [k, n])), (`A, PType.ofBase (LinalgBaseType.tensor [m, k]))]
--   let matmulAB := ((RawPExpr.const (LinalgConst.matmul m n k)).app (RawPExpr.var `A)).app (RawPExpr.var `B)
--   let f := RawPExpr.const (LinalgConst.relu [m, n])
--   have : HasType ctx matmulAB (PType.ofBase (LinalgBaseType.tensor [m, n])) := by simp [f, matmulAB, ctx];  inferHasType;
--   have : HasType ctx (f.app matmulAB) (PType.ofBase (LinalgBaseType.tensor [m, n])) := by simp [f, matmulAB, ctx]; inferHasType
--   (RawPExpr.app f matmulAB).toPExpr' ctx (PType.ofBase (LinalgBaseType.tensor [m, n]))
--   =
--   PExpr.app
--     (f.toPExpr' ctx (PType.fun (PType.ofBase (LinalgBaseType.tensor [m, n])) (PType.ofBase (LinalgBaseType.tensor [m, n]))))
--     (matmulAB.toPExpr' ctx (PType.ofBase (LinalgBaseType.tensor [m, n]))) := by
--   simp only [toPExpr'_app]
--   sorry

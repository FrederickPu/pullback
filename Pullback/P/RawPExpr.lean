import Pullback.P.Basic

namespace PExpr
namespace RawPExpr

open Lean

variable {BaseType Const} [DecidableEq BaseType] [Typed Const (PType BaseType)]

instance instHasType_const (ctxRaw : List (Name × PType BaseType)) (c : Const) :
  HasType ctxRaw (RawPExpr.const c : RawPExpr Const BaseType) (Typed.type c) :=
  ⟨by simp [inferType]⟩

instance instHasType_lam (ctxRaw : List (Name × PType BaseType)) (x : Name) (argT bodyT : PType BaseType)
    (body : RawPExpr Const BaseType) [HasType ((x, argT)::ctxRaw) body bodyT] :
  HasType ctxRaw (RawPExpr.lam x argT body : RawPExpr Const BaseType) (PType.fun argT bodyT) :=
  ⟨by
    have hbody : inferType ((x, argT) :: ctxRaw) body = some bodyT :=
      HasType.hasType (ctxRaw := ((x, argT) :: ctxRaw)) (e := body) (ty := bodyT)
    simp [inferType, hbody]
  ⟩

instance instHasType_letE (ctxRaw : List (Name × PType BaseType)) (x : Name)
    (v body : RawPExpr Const BaseType) (vT bodyT : PType BaseType)
    [HasType ctxRaw v vT] [HasType ((x, vT)::ctxRaw) body bodyT] :
  HasType ctxRaw (RawPExpr.letE x v body : RawPExpr Const BaseType) bodyT :=
  ⟨by
    have hv : inferType ctxRaw v = some vT :=
      HasType.hasType (ctxRaw := ctxRaw) (e := v) (ty := vT)
    have hbody : inferType ((x, vT) :: ctxRaw) body = some bodyT :=
      HasType.hasType (ctxRaw := ((x, vT) :: ctxRaw)) (e := body) (ty := bodyT)
    simp [inferType, hv, hbody]
  ⟩

instance instHasType_app (ctxRaw : List (Name × PType BaseType)) (dom codom : PType BaseType) (f x : RawPExpr Const BaseType) [HasType ctxRaw f (PType.fun dom codom)] [HasType ctxRaw x dom] :
  HasType ctxRaw (RawPExpr.app f x) codom :=
  ⟨by simp [inferType]; grind [HasType]⟩

instance instHasVar_head {ctx : List (Name × PType BaseType)} {name : Name} {ty : PType BaseType} :
    HasVar ((name, ty) :: ctx) name ty :=
  ⟨by grind⟩

theorem hasVar_cons {ctx : List (Name × PType BaseType)} {name name' : Name} {ty ty' : PType BaseType}
    (h : HasVar ctx name ty) (hne : name' ≠ name) :
    HasVar ((name', ty') :: ctx) name ty :=
  ⟨by grind [h.1]⟩

theorem HasType_iff_HasVar {ctxRaw : List (Name × PType BaseType)} {x : Name} {ty : PType BaseType} :
    HasType ctxRaw (RawPExpr.var x : RawPExpr Const BaseType) ty ↔ HasVar ctxRaw x ty := by
  sorry

theorem HasVar_map {BaseType' : Type} (f : PType BaseType → PType BaseType')
    {ctx : List (Name × PType BaseType)} {name : Name} {ty : PType BaseType}
    (h : HasVar ctx name ty) :
    HasVar (ctx.map (fun x => (x.1, f x.2))) name (f ty) :=
  ⟨by sorry
  ⟩

instance instHasType_var {ctx : List (Name × PType BaseType)} {name : Name}
  {ty : PType BaseType} [hv : HasVar ctx name ty] :
    HasType ctx (RawPExpr.var name : RawPExpr Const BaseType) ty :=
  ⟨by
    {
      have := hv.1
      rw [List.find?_eq_some_iff_getElem] at this
      simp [List.findFinIdx?_eq_some_iff, inferType, Option.bind_eq_some_iff]
      obtain ⟨i, hi, H⟩ := this.2
      use ⟨i, hi⟩
      grind
    }⟩

@[simp]
theorem inferType_of_hasType
    {ctx : List (Name × PType BaseType)} {e : RawPExpr Const BaseType} {ty : PType BaseType}
    [h : HasType ctx e ty] : e.inferType ctx = ty :=
  h.hasType

macro "inferHasType" : tactic =>
  `(tactic| (apply HasType.mk; simp [RawPExpr.inferType, List.findFinIdx?, List.findFinIdx?.go, Typed.type]))

syntax "inferHasVar" : tactic

elab_rules : tactic
  | `(tactic| inferHasVar) => do
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact instHasVar_head))
      return
    catch _ => pure ()
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply hasVar_cons))
    Lean.Elab.Tactic.evalTactic (← `(tactic| inferHasVar))
    Lean.Elab.Tactic.evalTactic (← `(tactic| decide))


open Lean Meta Expr Elab Term Tactic Core IO LibrarySuggestions
open Lean Meta Elab Tactic Simp in
open Lean Meta
/-- Simplify an expression using the given lemmas -/
def simpExpr (e : Expr) (defns : List Name) : MetaM Expr := do
  let cfg : Lean.Meta.Simp.Config := {
    zeta := true
    beta := true
    eta := true
    iota := true
    proj := true
    decide := true
    contextual := false
    arith := false
  }
  let ctx ← Meta.mkSimpContext (simpOnly := false) cfg

  let mut simpTheorems := ctx.simpTheorems
  if simpTheorems.isEmpty then
    simpTheorems := #[]

  -- 🔥 KEY CHANGE HERE
  for name in defns do
    simpTheorems ← simpTheorems.modifyM 0 fun thms0 =>
      thms0.addDeclToUnfold name

  let ctx := ctx.setSimpTheorems simpTheorems
  let result ← Meta.simp e ctx
  return result.1.expr

open Lean Meta Elab Tactic Simp
/-- Term elaborator that returns `RawPExpr.inferType vars e` unevaluated (no simplification). -/
elab "exprTypeOf" e:term "in" vars:term : term => do
  let stx ← `((RawPExpr.inferType $vars $e).get (by simp [RawPExpr.inferType, List.findFinIdx?, List.findFinIdx?.go, Typed.type]))
  let e ← Lean.Elab.Term.elabTerm stx none
  simpExpr e [`PExpr.RawPExpr.inferType, `List.findFinIdx?, `List.findFinIdx?.go, `Typed.type]

@[simp]
theorem toPExpr'_app
    {ctx : List (Name × PType BaseType)}
    {f a : RawPExpr Const BaseType}
    {A : PType BaseType}
    {B : PType BaseType}
    (hf : HasType ctx f (A.fun B) := by inferHasType) (ha : HasType ctx a A := by inferHasType) :
  (RawPExpr.app f a).toPExpr' ctx B
  =
  PExpr.app
    (f.toPExpr' ctx (A.fun B))
    (a.toPExpr' ctx A) := by
simp [RawPExpr.toPExpr', RawPExpr.toPExpr]
rw! (castMode := .all) [hf.1]
simp

@[simp]
theorem toPExpr'_const
    {ctx : List (Name × PType BaseType)}
    {ty : PType BaseType}
    (c : Const)
    [h : HasType ctx (RawPExpr.const c : RawPExpr Const BaseType) ty] :
  (RawPExpr.const c : RawPExpr Const BaseType).toPExpr' ctx ty
  = PExpr.const c (ty := ty) (hty := by simpa [RawPExpr.inferType] using h.hasType) := by
  have hty : Typed.type c = ty := by simpa [RawPExpr.inferType] using h.hasType
  subst hty; rfl

@[simp]
theorem toPExpr'_lam
    {ctx : List (Name × PType BaseType)}
    {x : Name} {argT bodyT : PType BaseType}
    {body : RawPExpr Const BaseType}
    (hbody : HasType ((x, argT) :: ctx) body bodyT := by inferHasType) :
  (RawPExpr.lam x argT body : RawPExpr Const BaseType).toPExpr' ctx (.fun argT bodyT)
  = PExpr.lam argT (body.toPExpr' ((x, argT) :: ctx) bodyT) := by
simp [RawPExpr.toPExpr', RawPExpr.toPExpr]
rw! (castMode := .all) [hbody.1]
simp

@[simp]
theorem toPExpr'_letE
    {ctx : List (Name × PType BaseType)}
    {x : Name} {v body : RawPExpr Const BaseType}
    {vT bodyT : PType BaseType}
    (hv : HasType ctx v vT := by inferHasType) (hbody : HasType ((x, vT) :: ctx) body bodyT := by inferHasType) :
  (RawPExpr.letE x v body : RawPExpr Const BaseType).toPExpr' ctx bodyT
  = PExpr.letE (v.toPExpr' ctx vT) (body.toPExpr' ((x, vT) :: ctx) bodyT) := by
simp [RawPExpr.toPExpr', RawPExpr.toPExpr]
rw! (castMode := .all) [hv.1, hbody.1]
grind

@[simp]
theorem toPExpr'_var
    {ctx : List (Name × PType BaseType)}
    {name : Name} {ty : PType BaseType}
    (hv : HasVar ctx name ty := by inferHasVar) :
  (RawPExpr.var name : RawPExpr Const BaseType).toPExpr' ctx ty
  = PExpr.var (Fin.cast (by grind) ((ctx.findFinIdx? (·.1 == name)).get (by grind [HasVar]))) ty (by {
    have := hv.1
    sorry
  }) := by
  simp [RawPExpr.toPExpr', RawPExpr.toPExpr]
  grind [HasVar]

variable {Const' BaseType'} [BasedType BaseType] [BasedType BaseType'] [DecidableEq BaseType'] [Typed Const' (PType BaseType')]
variable [Interp BaseType Const] [Interp BaseType' Const']

example
  {ctx : List (Name × PType BaseType)} {ty : PType BaseType} (args : DVector (ctx.map (·.2.type)))
  {e : RawPExpr Const BaseType} {e' : RawPExpr Const' BaseType'}
  (f : PType BaseType → PType BaseType') (hf : ∀ ty : PType BaseType, ty.type = (f ty).type)
  (he : HasType ctx e ty := by inferHasType) (he' : HasType (ctx.map (fun (x, v) => (x, f v))) e' (f ty) := by inferHasType)
  (E : ty.type) (E' : (f ty).type)
  (He : (e.toPExpr' ctx ty).interp (cast (by grind) args) = E)
  (He' : (e'.toPExpr' (ctx.map (fun (x, t) => (x, f t))) (f ty)).interp (cast sorry args) = E')
  (H : E ≍ E') :
    let harg := by
      apply congrArg
      simp
      grind
    (e.toPExpr ctx (by grind [HasType])).interp (cast (by grind) args) = cast (by simp [he.1, he'.1, hf]) ((e'.toPExpr (ctx.map (fun (x, t) => (x, f t))) (by grind [HasType])).interp (cast harg args)) := sorry

end RawPExpr
end PExpr

namespace PExpr
namespace RawPExpr

open Lean Meta Simp
open Lean Meta Elab Term PrettyPrinter

-- `BaseType`, `Const` are the type universe args; `instDecidable` is `DecidableEq BaseType`;
-- `instTyped` is `Typed Const (PType BaseType)`.  These must come from the surrounding
-- `toPExpr'` application so that instance synthesis never needs to rediscover them.
def inferHasType (e vars : Expr) (BaseType Const instDecidable instTyped : Expr) : MetaM (Expr × Expr) := do
  let e ← zetaReduce e
  let vars ← zetaReduce vars

  -- inferType : {Const BaseType} [DecidableEq BaseType] [Typed Const (PType BaseType)] ctxRaw → e → Option _
  let inferTypeApp ← mkAppOptM ``PExpr.RawPExpr.inferType
    #[some Const, some BaseType, some instDecidable, some instTyped, some vars, some e]
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
    [`PExpr.RawPExpr.inferType, `List.findFinIdx?, `List.findFinIdx?.go]

  -- HasType : {Const BaseType} [Typed Const (PType BaseType)] [DecidableEq BaseType] ctxRaw e ty
  let hasTypeTy ← mkAppOptM ``HasType
    #[some Const, some BaseType, some instTyped, some instDecidable, some vars, some e, some ty]
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
  -- Return (ty, proof) where ty : PType BaseType and proof : HasType ctxRaw e ty
  return (ty, proof)

end RawPExpr
end PExpr

open Lean Meta Simp
open Lean Meta Elab Term PrettyPrinter
open PExpr RawPExpr HasType Lean Meta Simp

-- Helper: build `(name, ty) :: ctxRaw` as a Lean Expr.
private def mkExtCtx (name ty ctxRaw : Expr) : MetaM Expr := do
  let pair ← mkAppM ``Prod.mk #[name, ty]
  mkAppM ``List.cons #[pair, ctxRaw]

simproc ↓ [simp, seval] reduce_toPExpr' (_) := fun e => do
  let fn := e.getAppFn
  unless fn.isConstOf ``PExpr.RawPExpr.toPExpr' do return .continue
  let args := e.getAppArgs
  -- toPExpr' args: BaseType, Const, [Typed], [DecidableEq], ctxRaw, ty, e, [HasType]
  let ⟨[BaseType, Const, instTyped, instDecidable, ctxRaw, _ty, ee, _he]⟩ := args | return .continue
  let fn2  := ee.getAppFn
  let args2 := ee.getAppArgs
  -- All RawPExpr constructors have (Const BaseType) as first two implicit args,
  -- so getAppArgs gives [Const, BaseType, field₁, field₂?, ...].
  -- Theorems (toPExpr'_*) are in a section with variable order [DecidableEq BaseType] [Typed ...],
  -- so instDecidable and instTyped are swapped relative to toPExpr' itself.

  -- Note: only lemmas that involve binders need to be handled directly by the simproc
  if fn2.isConstOf ``PExpr.RawPExpr.app then
    -- args2 = [Const, BaseType, f, x]
    let f := args2[2]!
    let x := args2[3]!
    let (argTy, xProof) ← inferHasType x ctxRaw BaseType Const instDecidable instTyped
    let (fTy,   fProof) ← inferHasType f ctxRaw BaseType Const instDecidable instTyped
    let fToPExpr ← mkAppOptM ``PExpr.RawPExpr.toPExpr'
      #[some BaseType, some Const, some instTyped, some instDecidable, some ctxRaw, some fTy, some f, some fProof]
    let xToPExpr ← mkAppOptM ``PExpr.RawPExpr.toPExpr'
      #[some BaseType, some Const, some instTyped, some instDecidable, some ctxRaw, some argTy, some x, some xProof]
    let result   ← mkAppM ``PExpr.app #[fToPExpr, xToPExpr]
    let eqProof  ← mkAppM ``toPExpr'_app #[fProof, xProof]
    return .visit { expr := result, proof? := some eqProof }
  else if fn2.isConstOf ``PExpr.RawPExpr.const then
    -- args2 = [Const, BaseType, c]
    let c := args2[2]!
    let (ty, hProof) ← inferHasType ee ctxRaw BaseType Const instDecidable instTyped
    let eqProof ← mkAppOptM ``PExpr.RawPExpr.toPExpr'_const
      #[some BaseType, some Const, some instDecidable, some instTyped,
        some ctxRaw, some ty, some c, some hProof]
    let result := (← inferType eqProof).appArg!
    return .visit { expr := result, proof? := some eqProof }
  else if fn2.isConstOf ``PExpr.RawPExpr.lam then
    -- args2 = [Const, BaseType, varName, argT, body]
    let varName := args2[2]!
    let argT    := args2[3]!
    let body    := args2[4]!
    let extCtx  ← mkExtCtx varName argT ctxRaw
    let (bodyTy, hbodyProof) ← inferHasType body extCtx BaseType Const instDecidable instTyped
    -- toPExpr'_lam args: BaseType, Const, [DecidableEq], [Typed], ctx, x, argT, bodyT, body, hbody
    let eqProof ← mkAppOptM ``toPExpr'_lam
      #[some BaseType, some Const, some instDecidable, some instTyped,
        some ctxRaw, some varName, some argT, some bodyTy, some body, some hbodyProof]
    let result := (← inferType eqProof).appArg!
    return .visit { expr := result, proof? := some eqProof }
  else if fn2.isConstOf ``PExpr.RawPExpr.letE then
    -- args2 = [Const, BaseType, varName, v, body]
    let varName := args2[2]!
    let v       := args2[3]!
    let body    := args2[4]!
    let (vTy, hvProof) ← inferHasType v ctxRaw BaseType Const instDecidable instTyped
    let extCtx  ← mkExtCtx varName vTy ctxRaw
    let (bodyTy, hbodyProof) ← inferHasType body extCtx BaseType Const instDecidable instTyped
    -- toPExpr'_letE args: BaseType, Const, [DecidableEq], [Typed], ctx, x, v, body, vT, bodyT, hv, hbody
    let eqProof ← mkAppOptM ``toPExpr'_letE
      #[some BaseType, some Const, some instDecidable, some instTyped,
        some ctxRaw, some varName, some v, some body, some vTy, some bodyTy,
        some hvProof, some hbodyProof]
    let result := (← inferType eqProof).appArg!
    return .visit { expr := result, proof? := some eqProof }
  else if fn2.isConstOf ``PExpr.RawPExpr.var then
    -- var case can be handled by the var simp lemma
    return .continue
  else
    return .continue

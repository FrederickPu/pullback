import Lean
import Pullback.SSA.VarMap

open Lean

inductive PExpr where
| var (n : Name) : PExpr
| lam (binderName : Name) (binderType : PExpr) (body : PExpr) : PExpr
| forallE (binderName : Name) (binderType : PExpr) (body : PExpr) : PExpr
| app (f x : PExpr) : PExpr
| sort : PExpr
deriving DecidableEq

def PExpr.subst (name : Name) : PExpr → (replacement : PExpr) → PExpr
  | .var n, replacement => if n == name then replacement else .var n
  | .lam bn bt body, replacement =>
    if bn == name then .lam bn (bt.subst name replacement) body
    else .lam bn (bt.subst name replacement) (body.subst name replacement)
  | .forallE bn bt body, replacement =>
    if bn == name then .forallE bn (bt.subst name replacement) body
    else .forallE bn (bt.subst name replacement) (body.subst name replacement)
  | .app f x, replacement => .app (f.subst name replacement) (x.subst name replacement)
  | .sort, _ => .sort

partial def PExpr.betaReduce : PExpr → PExpr
  | .app (.lam name _ body) x => (body.subst name x).betaReduce
  | .app f x => .app f.betaReduce x.betaReduce
  | .forallE n t b => .forallE n t.betaReduce b.betaReduce
  | .lam n t b => .lam n t.betaReduce b.betaReduce
  | e => e

def PExpr.isWhnf : PExpr → Prop
  | .var _ => True
  | .sort => True
  | .lam _ binderType body => binderType.isWhnf ∧ body.isWhnf
  | .forallE _ binderType body => binderType.isWhnf ∧ body.isWhnf
  | .app f x =>
      f.isWhnf ∧ x.isWhnf ∧
      match f with
      | .lam _ _ _ => False
      | _ => True

theorem PExpr.isWhnf_lam_iff (name : Name) (binderType body : PExpr) :
    (PExpr.lam name binderType body).isWhnf ↔ binderType.isWhnf ∧ body.isWhnf := by
  rfl

theorem PExpr.isWhnf_forallE_iff (name : Name) (binderType body : PExpr) :
    (PExpr.forallE name binderType body).isWhnf ↔ binderType.isWhnf ∧ body.isWhnf := by
  rfl

theorem PExpr.isWhnf_app_iff (f x : PExpr) :
    (PExpr.app f x).isWhnf ↔
      f.isWhnf ∧ x.isWhnf ∧
      (match f with
      | .lam _ _ _ => False
      | _ => True) := by
  rfl

theorem PExpr.isWhnf_lam_binder (name : Name) (binderType body : PExpr)
    (h : (PExpr.lam name binderType body).isWhnf) : binderType.isWhnf :=
  (PExpr.isWhnf_lam_iff name binderType body).1 h |>.1

theorem PExpr.isWhnf_lam_body (name : Name) (binderType body : PExpr)
    (h : (PExpr.lam name binderType body).isWhnf) : body.isWhnf :=
  (PExpr.isWhnf_lam_iff name binderType body).1 h |>.2

theorem PExpr.isWhnf_forallE_binder (name : Name) (binderType body : PExpr)
    (h : (PExpr.forallE name binderType body).isWhnf) : binderType.isWhnf :=
  (PExpr.isWhnf_forallE_iff name binderType body).1 h |>.1

theorem PExpr.isWhnf_forallE_body (name : Name) (binderType body : PExpr)
    (h : (PExpr.forallE name binderType body).isWhnf) : body.isWhnf :=
  (PExpr.isWhnf_forallE_iff name binderType body).1 h |>.2

theorem PExpr.isWhnf_app_fun (f x : PExpr) (h : (PExpr.app f x).isWhnf) : f.isWhnf :=
  (PExpr.isWhnf_app_iff f x).1 h |>.1

theorem PExpr.isWhnf_app_arg (f x : PExpr) (h : (PExpr.app f x).isWhnf) : x.isWhnf :=
  (PExpr.isWhnf_app_iff f x).1 h |>.2.1

def PExpr.inferType (vars : Map Name PExpr) : PExpr → Option PExpr
| .var name => vars.get name
| .sort => none
| .lam name type body => do
  let .sort ← type.inferType vars | none
  let bodyType ← body.inferType (vars.push (name, type))
  return .forallE name type bodyType
| .forallE name type body => do
  let .sort ← type.inferType vars | none
  let .sort ← body.inferType (vars.push (name, type)) | none
  return .sort
| .app f x => do
  let .forallE name binderType bodyType ← f.inferType vars | none
  let xType ← x.inferType vars
  guard (xType == binderType)
  return bodyType.subst name x

universe uu

inductive TypeWhnf : Type (uu + 1) where
  | ret : Type uu → TypeWhnf
  | ext : (dom : Type uu) → (dom → TypeWhnf) → TypeWhnf

instance : Inhabited TypeWhnf := ⟨.ret PUnit⟩

namespace TypeWhnf
def toType : TypeWhnf.{uu} → Type uu
  | .ret T => T
  | .ext dom rest => (x : dom) → (rest x).toType
end TypeWhnf

@[simp] theorem TypeWhnf.toType_ret (T : Type uu) : (TypeWhnf.ret T).toType = T := rfl

@[simp] theorem TypeWhnf.toType_ext (dom : Type uu) (rest : dom → TypeWhnf.{uu}) :
  TypeWhnf.toType (TypeWhnf.ext dom rest) = ((x : dom) → TypeWhnf.toType (rest x)) := by
  rfl

structure TypedVal where
  whnf : TypeWhnf.{uu}
  val : whnf.toType

instance : Inhabited (TypedVal) := ⟨⟨.ret PUnit, PUnit.unit⟩⟩

def Ctx := Array (Name × TypedVal.{uu})

namespace Ctx
def empty : Ctx.{uu} := #[]
def push (ctx : Ctx.{uu}) (name : Name) (e : TypedVal.{uu}) : Ctx.{uu} :=
  Array.push ctx (name, e)
def get (ctx : Ctx.{uu}) (name : Name) : Option (TypedVal.{uu}) :=
  (ctx.reverse.find? (·.1 == name)).map (·.2)

def aligned (vars : Map Name PExpr) (ctx : Ctx.{uu}) : Prop :=
  ∀ name, (vars.get name).isSome → (ctx.get name).isSome

theorem aligned_push (vars : Map Name PExpr) (ctx : Ctx.{uu})
    (h : aligned vars ctx) (name : Name) (binderType : PExpr) (tv : TypedVal.{uu}) :
    aligned (vars.push (name, binderType)) (ctx.push name tv) := by
  sorry
end Ctx

theorem PExpr.inferType_forallE_eq_sort_or_none (vars : Map Name PExpr) (name : Name) (binderType bodyType : PExpr) :
  (forallE name binderType bodyType).inferType vars = some .sort ∨ (forallE name binderType bodyType).inferType vars = none := sorry

theorem PExpr.welltyped_lam_iff (vars : Map Name PExpr) (name : Name)
    (binderType body : PExpr) :
    ((PExpr.lam name binderType body).inferType vars).isSome ∧ (PExpr.lam name binderType body).inferType vars ≠ some .sort ↔
      (binderType.inferType vars = some .sort) ∧
      (body.inferType (vars.push (name, binderType))).isSome := by
  sorry

theorem PExpr.inferType_lam_ne_sort (vars : Map Name PExpr) (name : Name) (binderType body : PExpr) :
  ((PExpr.lam name binderType body).inferType vars) ≠ some .sort := sorry

theorem PExpr.welltyped_forallE_iff (vars : Map Name PExpr) (name : Name)
    (binderType body : PExpr) :
    ((PExpr.forallE name binderType body).inferType vars) = some .sort ↔
      (binderType.inferType vars = some .sort) ∧
      (body.inferType (vars.push (name, binderType))).isSome := by
  sorry

theorem PExpr.welltyped_sort_app_iff (vars : Map Name PExpr) (f x : PExpr) :
    ((PExpr.app f x).inferType vars) = some .sort ↔
      ∃ name binderType bodyType,
        f.inferType vars = some (.forallE name binderType bodyType) ∧
        x.inferType vars = some binderType := by
  sorry

theorem PExpr.welltyped_app_iff (vars : Map Name PExpr) (f x : PExpr) :
    ((PExpr.app f x).inferType vars).isSome ∧ ((PExpr.app f x).inferType vars) ≠ some .sort ↔
      ∃ name binderType body,
        f.inferType vars = some (.lam name binderType body) ∧
        x.inferType vars = some binderType := by
  sorry

theorem PExpr.inferType_app_eq_sort_imp_sort (vars : Map Name PExpr) (f x : PExpr) :
  (f.app x).inferType vars = some .sort → f.inferType vars = some .sort := sorry
/-! ## interp

Returns Sum:
- inl whnf : type mode result (a TypeWhnf)
- inr tv   : value mode result (a TypedVal)

isType flag determines which branch.
-/

def PExpr.interp (isType : Bool) (vars : Map Name PExpr)
  (ctx : Ctx.{uu}) (halign : Ctx.aligned vars ctx)
    : (e : PExpr) → e.isWhnf → (if isType then e.inferType vars = some .sort else (e.inferType vars).isSome ∧ (e.inferType vars) ≠ some .sort) → (if isType then TypeWhnf.{uu} else TypedVal.{uu})
  | .sort, _hwhnf, he =>
    match isType with
    | true => by simp [inferType] at he
    | false => by simp [inferType] at he
  | .var name, _hwhnf, he =>
    match isType with
    | true =>
      match h : ctx.get name with
      | some x => x.whnf
      | none => by {
        have hctx : (ctx.get name).isSome := halign name (by grind [inferType])
        simp [h] at hctx
      }
    | false =>
      match h : ctx.get name with
      | some x => x
      | none => by {
        have hctx : (ctx.get name).isSome := halign name (by simpa using he.1)
        simp [h] at hctx
      }
  | .forallE name binderType body, hwhnf, he =>
    match isType with
    | true =>
      have heForall : (PExpr.forallE name binderType body).inferType vars = some .sort := by
        simpa using he
      have hBinder : binderType.inferType vars = some .sort := by
        rcases (PExpr.welltyped_forallE_iff vars name binderType body).1 heForall with ⟨hBinder, _⟩
        exact hBinder
      have hBody : (body.inferType (vars.push (name, binderType))) = some .sort := by
        cases hty : body.inferType (vars.push (name, binderType)) with
        | none =>
          simp [PExpr.inferType, hBinder, hty] at heForall
        | some ty =>
          cases ty <;> simp [PExpr.inferType, hBinder, hty] at heForall
          simp
      let domWhnf := PExpr.interp true vars ctx halign binderType (by
        exact PExpr.isWhnf_forallE_binder name binderType body hwhnf) (by
        simp [hBinder])
      let dom := domWhnf.toType
      (TypeWhnf.ext dom (fun v =>
          let vars' := vars.push (name, binderType)
          let ctx' := ctx.push name ⟨TypeWhnf.ret dom, v⟩
          (PExpr.interp true vars' ctx'
            (Ctx.aligned_push vars ctx halign name binderType ⟨TypeWhnf.ret dom, v⟩)
            body
            (by
              exact PExpr.isWhnf_forallE_body name binderType body hwhnf)
            hBody)))
    | false => by
      apply False.elim
      simp [inferType] at he
      have := he.1
      simp at this
      option_elim
      have hdolift' : dolift = sort := by
        apply by_contra
        intro H
        simp at this
      simp [hdolift'] at this
      option_elim
      have : dolift = sort := by
        apply by_contra
        intro H
        simp at this
      grind
  | .lam name binderType body, hwhnf, he =>
    match isType with
    | true => by
        apply False.elim
        simp only [↓reduceIte, inferType, Option.pure_def, Option.bind_eq_bind] at he
        option_elim
        cases em (dolift = sort) with
        | inl hl =>
          simp only [hl] at he
          option_elim
          simp at he
        | inr hr => simp at he
    | false =>
      have hBinder : binderType.inferType vars = some .sort := by
        rcases (PExpr.welltyped_lam_iff vars name binderType body).1 he with ⟨hBinder, _⟩
        exact hBinder
      let vars' := vars.push (name, binderType)
      have hBody : (body.inferType vars').isSome ∧ (body.inferType vars') ≠ some .sort := by
        rcases (PExpr.welltyped_lam_iff vars name binderType body).1 he with x
        -- todo :: use submap lemma
        sorry
      let domWhnf := PExpr.interp true vars ctx halign binderType (by
        exact PExpr.isWhnf_lam_binder name binderType body hwhnf) (by
        simp [hBinder])
      let dom := domWhnf.toType
      let whnf := TypeWhnf.ext dom (fun v =>
          let ctx' := ctx.push name ⟨TypeWhnf.ret dom, v⟩
          let bodyTv := PExpr.interp false vars' ctx'
            (Ctx.aligned_push vars ctx halign name binderType ⟨TypeWhnf.ret dom, v⟩)
            body
            (by
              exact PExpr.isWhnf_lam_body name binderType body hwhnf)
            hBody
          bodyTv.whnf)
        let val : whnf.toType := fun v =>
          let ctx' := ctx.push name ⟨TypeWhnf.ret dom, v⟩
          let bodyTv := PExpr.interp false vars' ctx'
            (Ctx.aligned_push vars ctx halign name binderType ⟨TypeWhnf.ret dom, v⟩)
            body
            (by
              exact PExpr.isWhnf_lam_body name binderType body hwhnf)
            hBody
          bodyTv.val
        ⟨whnf, val⟩
  | .app f x, hwhnf, he =>
    -- Atomic application path: head is a variable looked up in the aligned context.
    match f with
    | .var fname =>
      match isType with
      | true =>
        have hFSort : (PExpr.var fname).inferType vars = some .sort := by
          have hAppSort : (PExpr.app (.var fname) x).inferType vars = some .sort := by
            simpa using he
          exact PExpr.inferType_app_eq_sort_imp_sort vars (.var fname) x hAppSort
        have hVarGet : vars.get fname = some .sort := by
          simpa [PExpr.inferType] using hFSort
        have hctxSome : (ctx.get fname).isSome := by
          apply halign fname
          simp [hVarGet]
        match hget : ctx.get fname with
        | some fTv =>
          match fTv.whnf with
          | TypeWhnf.ext dom rest =>
            let xTv := PExpr.interp false vars ctx halign x (by
              exact PExpr.isWhnf_app_arg (.var fname) x hwhnf) (by
              sorry)
            let xVal : dom := cast sorry xTv.val
            rest xVal
          | _ => by
            apply False.elim
            sorry
        | none => by
          have : False := by simp [hget] at hctxSome
          exact False.elim this
      | false =>
        have hFNonSort : ((PExpr.var fname).inferType vars).isSome ∧ (PExpr.var fname).inferType vars ≠ some .sort := by
          sorry
        let fTv := PExpr.interp false vars ctx halign (.var fname) (by
          trivial) hFNonSort
        match fTv.whnf with
        | TypeWhnf.ext dom rest =>
          let xTv := PExpr.interp false vars ctx halign x (by
            exact PExpr.isWhnf_app_arg (.var fname) x hwhnf) (by
            sorry)
          let xVal : dom := cast sorry xTv.val
          let fVal : (v : dom) → (rest v).toType := cast sorry fTv.val
          ⟨rest xVal, fVal xVal⟩
        | _ => by
          apply False.elim
          sorry
    | _ =>
      by
        apply False.elim
        -- Under the atomic-application invariant, app heads are variables.
        sorry

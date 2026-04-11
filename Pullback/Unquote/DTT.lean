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

def TypeWhnf.Aligned (vars : Map Name PExpr) (ctx : Ctx.{uu}) : TypeWhnf.{uu} → PExpr → Prop
  | .ret _, .sort => Ctx.aligned vars ctx
  | w, .var name =>
      ∃ tv, ctx.get name = some tv ∧ w = tv.whnf
  | .ext dom rest, .forallE name binderType body =>
      Ctx.aligned vars ctx ∧
      binderType.inferType vars = some .sort ∧
      (body.inferType (vars.push (name, binderType))).isSome ∧
      ∀ v : dom, TypeWhnf.Aligned (vars.push (name, binderType))
        (ctx.push name ⟨TypeWhnf.ret dom, v⟩) (rest v) body
  | _, _ => False

theorem TypeWhnf.aligned_var_iff {vars : Map Name PExpr} {ctx : Ctx.{uu}} {name : Name} {w : TypeWhnf.{uu}} :
    TypeWhnf.Aligned vars ctx w (PExpr.var name) ↔ ∃ tv, ctx.get name = some tv ∧ w = tv.whnf := by
  simp [TypeWhnf.Aligned]

def TypedVal.Aligned (vars : Map Name PExpr) (ctx : Ctx.{uu}) (tv : TypedVal.{uu}) (e : PExpr) : Prop :=
  ∃ ty : PExpr, e.inferType vars = some ty ∧ TypeWhnf.Aligned vars ctx tv.whnf ty

def Ctx.alignedTy (vars : Map Name PExpr) (ctx : Ctx.{uu}) : Prop :=
  ∀ name ty, vars.get name = some ty →
    ∃ tv, ctx.get name = some tv ∧ TypeWhnf.Aligned vars ctx tv.whnf ty

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

def TypeWhnfAligned (vars : Map Name PExpr) (ctx : Ctx.{uu}) (e : PExpr) : Type (uu + 1) :=
  {w : TypeWhnf.{uu} // TypeWhnf.Aligned vars ctx w e}

def TypedValAligned (vars : Map Name PExpr) (ctx : Ctx.{uu}) (e : PExpr) : Type (uu + 1) :=
  {tv : TypedVal.{uu} // TypedVal.Aligned vars ctx tv e}

namespace TypeWhnfAligned

def mk {vars : Map Name PExpr} {ctx : Ctx.{uu}} {e : PExpr}
    (w : TypeWhnf.{uu}) (h : TypeWhnf.Aligned vars ctx w e) : TypeWhnfAligned vars ctx e :=
  ⟨w, h⟩

def whnf {vars : Map Name PExpr} {ctx : Ctx.{uu}} {e : PExpr}
    (a : TypeWhnfAligned vars ctx e) : TypeWhnf.{uu} :=
  a.1

def aligned {vars : Map Name PExpr} {ctx : Ctx.{uu}} {e : PExpr}
    (a : TypeWhnfAligned vars ctx e) : TypeWhnf.Aligned vars ctx a.whnf e :=
  a.2

@[simp] theorem whnf_mk {vars : Map Name PExpr} {ctx : Ctx.{uu}} {e : PExpr}
    (w : TypeWhnf.{uu}) (h : TypeWhnf.Aligned vars ctx w e) :
    (mk w h).whnf = w := rfl

@[simp] theorem aligned_mk {vars : Map Name PExpr} {ctx : Ctx.{uu}} {e : PExpr}
    (w : TypeWhnf.{uu}) (h : TypeWhnf.Aligned vars ctx w e) :
    (mk w h).aligned = h := rfl

-- Constructors matching TypeWhnf.Aligned patterns
def ofSort {vars : Map Name PExpr} {ctx : Ctx.{uu}}
    (halign : Ctx.aligned vars ctx) : TypeWhnfAligned vars ctx .sort :=
  ⟨TypeWhnf.ret PUnit, halign⟩

def ofVar {vars : Map Name PExpr} {ctx : Ctx.{uu}} {name : Name}
    (tv : TypedVal.{uu})
    (h : ctx.get name = some tv) : TypeWhnfAligned vars ctx (.var name) :=
  { val := tv.whnf
    property := TypeWhnf.aligned_var_iff.mpr ⟨tv, h, rfl⟩ }

def ofForallE {vars : Map Name PExpr} {ctx : Ctx.{uu}}
    {name : Name} {binderType body : PExpr}
    {dom : Type uu} (rest : dom → TypeWhnf.{uu})
    (halign : Ctx.aligned vars ctx)
    (hBinder : binderType.inferType vars = some .sort)
    (hBody : (body.inferType (vars.push (name, binderType))).isSome)
    (hRest : ∀ v : dom, TypeWhnf.Aligned (vars.push (name, binderType))
      (ctx.push name ⟨TypeWhnf.ret dom, v⟩) (rest v) body) :
    TypeWhnfAligned vars ctx (.forallE name binderType body) :=
  ⟨TypeWhnf.ext dom rest, ⟨halign, hBinder, hBody, hRest⟩⟩

@[simp] theorem whnf_ofSort {vars : Map Name PExpr} {ctx : Ctx.{uu}}
    (halign : Ctx.aligned vars ctx) :
    (ofSort halign).whnf = TypeWhnf.ret PUnit := rfl

@[simp] theorem whnf_ofForallE {vars : Map Name PExpr} {ctx : Ctx.{uu}}
    {name : Name} {binderType body : PExpr}
    {dom : Type uu} (rest : dom → TypeWhnf.{uu})
    (halign : Ctx.aligned vars ctx)
    (hBinder : binderType.inferType vars = some .sort)
    (hBody : (body.inferType (vars.push (name, binderType))).isSome)
    (hRest : ∀ v : dom, TypeWhnf.Aligned (vars.push (name, binderType))
      (ctx.push name ⟨TypeWhnf.ret dom, v⟩) (rest v) body) :
    (ofForallE rest halign hBinder hBody hRest).whnf = TypeWhnf.ext dom rest := rfl

end TypeWhnfAligned

namespace TypedValAligned

def mk {vars : Map Name PExpr} {ctx : Ctx.{uu}} {e : PExpr}
    (tv : TypedVal.{uu}) (h : TypedVal.Aligned vars ctx tv e) : TypedValAligned vars ctx e :=
  ⟨tv, h⟩

def tv {vars : Map Name PExpr} {ctx : Ctx.{uu}} {e : PExpr}
    (a : TypedValAligned vars ctx e) : TypedVal.{uu} :=
  a.1

def aligned {vars : Map Name PExpr} {ctx : Ctx.{uu}} {e : PExpr}
    (a : TypedValAligned vars ctx e) : TypedVal.Aligned vars ctx a.tv e :=
  a.2

def whnf {vars : Map Name PExpr} {ctx : Ctx.{uu}} {e : PExpr}
    (a : TypedValAligned vars ctx e) : TypeWhnf.{uu} :=
  a.tv.whnf

def val {vars : Map Name PExpr} {ctx : Ctx.{uu}} {e : PExpr}
    (a : TypedValAligned vars ctx e) : a.whnf.toType :=
  a.tv.val

@[simp] theorem tv_mk {vars : Map Name PExpr} {ctx : Ctx.{uu}} {e : PExpr}
    (tv : TypedVal.{uu}) (h : TypedVal.Aligned vars ctx tv e) :
    (mk tv h).tv = tv := rfl

@[simp] theorem aligned_mk {vars : Map Name PExpr} {ctx : Ctx.{uu}} {e : PExpr}
    (tv : TypedVal.{uu}) (h : TypedVal.Aligned vars ctx tv e) :
    (mk tv h).aligned = h := rfl

@[simp] theorem whnf_mk {vars : Map Name PExpr} {ctx : Ctx.{uu}} {e : PExpr}
    (tv : TypedVal.{uu}) (h : TypedVal.Aligned vars ctx tv e) :
    (mk tv h).whnf = tv.whnf := rfl

@[simp] theorem val_mk {vars : Map Name PExpr} {ctx : Ctx.{uu}} {e : PExpr}
    (tv : TypedVal.{uu}) (h : TypedVal.Aligned vars ctx tv e) :
    (mk tv h).val = tv.val := rfl

-- Constructor for variable lookup in value mode
def ofVar_val {vars : Map Name PExpr} {ctx : Ctx.{uu}} {name : Name}
    (x : TypedVal.{uu})
    (_hctx : ctx.get name = some x)
    (ty : PExpr)
    (htype : vars.get name = some ty)
    (halign : TypeWhnf.Aligned vars ctx x.whnf ty) :
    TypedValAligned vars ctx (.var name) :=
  { val := x
    property := ⟨ty, htype, halign⟩ }

end TypedValAligned

/-! ## interp

Returns Sum:
- inl whnf : type mode result (a TypeWhnf)
- inr tv   : value mode result (a TypedVal)

isType flag determines which branch.
-/

def PExpr.interp (isType : Bool) (vars : Map Name PExpr)
  (ctx : Ctx.{uu}) (halign : Ctx.aligned vars ctx)
    : (e : PExpr) →
      (if isType then e.inferType vars = some .sort else (e.inferType vars).isSome ∧ (e.inferType vars) ≠ some .sort) →
      (if isType then TypeWhnfAligned vars ctx e else TypedValAligned vars ctx e)
  | .sort, he =>
    match isType with
    | true =>
      TypeWhnfAligned.ofSort halign
    | false => by
      apply False.elim
      simp [inferType] at he
  | .var name, he =>
    match isType with
    | true =>
      match h : ctx.get name with
      | some x =>
        ⟨x.whnf, TypeWhnf.aligned_var_iff.mpr ⟨x, h, rfl⟩⟩
      | none => by {
        have hctx : (ctx.get name).isSome := halign name (by grind [inferType])
        simp [h] at hctx
      }
    | false =>
      match h : ctx.get name with
      | some x =>
        match htype : vars.get name with
        | some ty =>
          TypedValAligned.ofVar_val x h ty htype (by sorry)
        | none => by
          have : (vars.get name).isSome := by simpa using he.1
          simp [htype] at this
      | none => by {
        have hctx : (ctx.get name).isSome := halign name (by simpa using he.1)
        simp [h] at hctx
      }
  | .forallE name binderType body, he =>
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
      let domWhnf := (PExpr.interp true vars ctx halign binderType (by
        simp [hBinder])).1
      let dom := domWhnf.toType
      ⟨TypeWhnf.ext dom (fun v =>
          let vars' := vars.push (name, binderType)
          let ctx' := ctx.push name ⟨TypeWhnf.ret dom, v⟩
          (PExpr.interp true vars' ctx'
            (Ctx.aligned_push vars ctx halign name binderType ⟨TypeWhnf.ret dom, v⟩)
            body
            hBody).1), by
        sorry⟩
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
  | .lam name binderType body, he =>
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
      let domWhnf := (PExpr.interp true vars ctx halign binderType (by
        simp [hBinder])).1
      let dom := domWhnf.toType
      let whnf := TypeWhnf.ext dom (fun v =>
          let ctx' := ctx.push name ⟨TypeWhnf.ret dom, v⟩
          let bodyTv := (PExpr.interp false vars' ctx'
            (Ctx.aligned_push vars ctx halign name binderType ⟨TypeWhnf.ret dom, v⟩)
            body
            hBody).1
          bodyTv.whnf)
        let val : whnf.toType := fun v =>
          let ctx' := ctx.push name ⟨TypeWhnf.ret dom, v⟩
          let bodyTv := (PExpr.interp false vars' ctx'
            (Ctx.aligned_push vars ctx halign name binderType ⟨TypeWhnf.ret dom, v⟩)
            body
            hBody).1
          bodyTv.val
        ⟨⟨whnf, val⟩, by
          sorry⟩
  | .app f x, he =>
    match isType with
    | true =>
      have hFSort : f.inferType vars = some .sort := by
        have hAppSort : (PExpr.app f x).inferType vars = some .sort := by
          simpa using he
        exact PExpr.inferType_app_eq_sort_imp_sort vars f x hAppSort
      let fWhnf := (PExpr.interp true vars ctx halign f hFSort).1
      match fWhnf with
      | TypeWhnf.ext dom rest =>
        let xTv := (PExpr.interp false vars ctx halign x (by
          sorry)).1
        let xVal : dom := cast sorry xTv.val
        ⟨rest xVal, by
          sorry⟩
      | _ => by
        apply False.elim
        sorry
    | false =>
      have hF : (f.inferType vars).isSome ∧ f.inferType vars ≠ some .sort := by
        sorry
      let fTv := (PExpr.interp false vars ctx halign f hF).1
      match fTv.whnf with
      | TypeWhnf.ext dom rest =>
        let xTv := (PExpr.interp false vars ctx halign x (by
          sorry)).1
        let xVal : dom := cast sorry xTv.val
        let fVal : (v : dom) → (rest v).toType := cast sorry fTv.val
        ⟨⟨rest xVal, fVal xVal⟩, by
          sorry⟩
      | _ => by
        apply False.elim
        sorry

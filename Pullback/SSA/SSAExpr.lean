import Pullback.SSA.VarMap


theorem SSAExpr.inferType_eq_of_vars_submap (vars₁ vars₂ : VarMap) (hvars : vars₁.submap vars₂) : (expr : SSAExpr) → (expr.inferType vars₁).isSome → expr.inferType vars₁ = expr.inferType vars₂
| const c => by simp [inferType]
| letE varname val body => by
    simp only [inferType]
    intro H
    simp [Option.isSome_iff_exists, Option.bind_eq_some_iff] at H
    rw [← inferType_eq_of_vars_submap vars₁ vars₂ hvars val]
    obtain ⟨bodyT, valT, hvalT, hbodyT⟩ := H
    simp [hvalT, hbodyT]
    have := inferType_eq_of_vars_submap (vars₁.push (varname, valT)) (vars₂.push (varname, valT)) (Map.push_submap_push _ _ hvars _ _) body (by grind)
    grind
    grind
| lam varname type body => by
    simp only [inferType]
    intro H
    simp [Option.isSome_iff_exists, Option.bind_eq_some_iff] at H
    obtain ⟨bodyT, hbodyT⟩ := H
    simp [hbodyT]
    have := inferType_eq_of_vars_submap (vars₁.push (varname, type)) (vars₂.push (varname, type)) (Map.push_submap_push _ _ hvars _ _) body (by grind)
    grind
| app f x => by
    simp only [inferType]
    intro H
    simp [Option.isSome_iff_exists, Option.bind_eq_some_iff] at H
    obtain ⟨finaltype, ftype, hftype, xtype, hxtype, hfinaltype⟩ := H
    have cruxf := inferType_eq_of_vars_submap vars₁ vars₂ hvars f (by grind)
    have cruxx := inferType_eq_of_vars_submap vars₁ vars₂ hvars x (by grind)
    simp [hftype, hxtype, ← cruxf, ← cruxx]
| var name => by
    simp only [inferType]
    intro H
    simp only [Option.isSome_iff_exists] at H
    obtain ⟨type, htype⟩ := H
    simp only [Map.submap, Array.any_eq_true, decide_eq_true_eq, Set.setOf_subset_setOf,
      forall_exists_index] at hvars
    have := Map.get_eq_some_imp_any _ _  _ htype
    simp only [Array.any_eq_true, decide_eq_true_eq] at this
    obtain ⟨i, hi, Hi⟩ := this
    grind only

open Lean

theorem SSAExpr.inferType_push_eq_of_hygenic (vars : VarMap) (newvar : Name) (newVarType : SSAType) (hHygenic : ¬ vars.any (·.1 = newvar)) : (expr : SSAExpr) → (expr.inferType vars).isSome → expr.inferType (vars.push (newvar, newVarType)) = expr.inferType vars
| const c => by simp [inferType]
| letE varName val body => by
    intro H
    simp only [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff] at H
    obtain ⟨bodyT, valT, hvalT, hbodyT⟩ := H
    have crux1 := inferType_push_eq_of_hygenic vars newvar newVarType hHygenic val (Option.isSome_of_mem hvalT)
    simp [inferType, hvalT, crux1]
    symm
    apply SSAExpr.inferType_eq_of_vars_submap
    simp [Map.submap]
    apply And.intro
    grind
    intro name hName
    have := Map.get_push (α := Name) (β := SSAType)
    simp at this
    simp [this]
    cases em (varName = name) with
    | inl hl =>
        simp [hl]
    | inr hr =>
        simp [hr]
        simp [Map.get, Array.findLast?, Array.find?_eq_some_iff_getElem]
        grind
    grind
| lam varname type body => by
    intro H
    simp only [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff, Option.some.injEq,
      ↓existsAndEq, and_true] at H
    obtain ⟨bodyT, hbodyT⟩ := H
    simp only [inferType, hbodyT, Option.bind_some, Option.bind_eq_some_iff, Option.some.injEq,
      SSAType.fun.injEq, true_and, exists_eq_right]
    symm
    rw [← hbodyT]
    apply SSAExpr.inferType_eq_of_vars_submap
    simp [Map.submap]
    apply And.intro
    grind
    intro name hName
    have := Map.get_push (α := Name) (β := SSAType)
    simp at this
    simp [this]
    cases em (varname = name) with
    | inl hl =>
        simp [hl]
    | inr hr =>
        simp [hr]
        simp [Map.get, Array.findLast?, Array.find?_eq_some_iff_getElem]
        grind
    grind
| app f x => by
    intro H
    simp only [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff] at H
    obtain ⟨finaltype, ftype, hftype, xtype, hxtype, Hfinal⟩ := H
    simp only [inferType, hftype, hxtype, Option.bind_some]
    have cruxf := inferType_push_eq_of_hygenic vars newvar newVarType hHygenic f (Option.isSome_of_mem hftype)
    have cruxx := inferType_push_eq_of_hygenic vars newvar newVarType hHygenic x (Option.isSome_of_mem hxtype)
    simp only [cruxf, hftype, cruxx, hxtype, Option.bind_some]
| var name => by
    intro H
    simp only [inferType, Option.isSome_iff_exists] at H
    have := Map.get_push (α := Name) (β := SSAType)
    simp at this
    simp [inferType, this]
    obtain ⟨t, ht⟩ := H
    have := Map.get_eq_some_imp_any _ _ _ ht
    simp only [Array.any_eq_true, decide_eq_true_eq] at this
    simp at hHygenic
    grind

namespace SSAExpr

/-- Any fuel ≥ e.size gives the same result as exactly e.size fuel. -/
lemma reduceAux_fuel_sufficient
    (env : Array (Name × Option SSAExpr)) (e : SSAExpr) (n : Nat)
    (h : e.size ≤ n) :
    e.reduceAux env n = e.reduceAux env e.size := by
  induction e generalizing env n with
  | const c =>
    simp [reduceAux]
  | var name =>
    simp [reduceAux]
  | lam varName varType body =>
    simp [reduceAux]
  | letE name val body ih_val ih_body =>
    sorry
  | app f x f_ih x_ih => sorry

/-- The fuel threading in reduceAux never produces something bigger than the input,
    provided env entries are bounded by `bound`. -/
lemma reduceAux_size_le
    (env : Array (Name × Option SSAExpr)) (bound : Nat)
    (henv : ∀ i : Fin env.size, ∀ e', env[i].2 = some e' → e'.size ≤ bound)
    (e e': SSAExpr) (n : Nat) (he : e.size ≤ bound)
    (h : e.reduceAux env n = some e') :
    e'.size ≤ bound := by
  induction e generalizing env n e' with
  | const c => simp [reduceAux] at h; subst h; simpa [size]
  | lam varName varType body => simp [reduceAux] at h; subst h; simpa [size]
  | var name => sorry
  | letE name val body ih_val ih_body => sorry
  | app f x ih_f ih_x => sorry

lemma reduce_size_le
    (env : Array (Name × Option SSAExpr))
    (e e' : SSAExpr)
    (henv : ∀ i : Fin env.size, ∀ e', env[i].2 = some e' → e'.size ≤ e.size)
    (h : e.reduce env = some e') :
    e'.size ≤ e.size := by
  apply reduceAux_size_le env e.size henv e e' e.size (le_refl _)
  simpa [reduce] using h


lemma reduceAux_eq_reduce (env : Array (Name × Option SSAExpr)) (e : SSAExpr) (n : Nat)
    (h : e.size ≤ n) :
    e.reduceAux env n = e.reduce env :=
  reduceAux_fuel_sufficient env e n h

/-!
## Elimination rules for `reduce`

Each theorem corresponds to one pattern-match arm of `reduceAux`.
Hypotheses are stated purely in terms of `reduce` (no fuel).
-/

@[simp]
theorem reduce_const (env : Array (Name × Option SSAExpr)) (c : SSAConst) :
    SSAExpr.reduce env (.const c) = some (.const c) := by
  simp [reduce, reduceAux, size]

@[simp]
theorem reduce_lam (env : Array (Name × Option SSAExpr))
    (varName : Name) (varType : SSAType) (body : SSAExpr) :
    SSAExpr.reduce env (.lam varName varType body) = some (.lam varName varType body) := by
  simp [reduce, reduceAux, size]

theorem reduce_var_bound (env : Array (Name × Option SSAExpr)) (name : Name) (x : SSAExpr)
    (h : env.findLast? (·.1 == name) = some (name, some x)) :
    SSAExpr.reduce env (.var name) = some x := by
  simp [reduce, reduceAux, size, h]

theorem reduce_var_free (env : Array (Name × Option SSAExpr)) (name : Name)
    (h : env.findLast? (·.1 == name) = some (name, none)) :
    SSAExpr.reduce env (.var name) = some (.var name) := by
  simp [reduce, reduceAux, size, h]

theorem reduce_var_notFound (env : Array (Name × Option SSAExpr)) (name : Name)
    (h : env.findLast? (·.1 == name) = none) :
    SSAExpr.reduce env (.var name) = none := by
  simp [reduce, reduceAux, size, h]

theorem reduce_letE_none (env : Array (Name × Option SSAExpr))
    (name : Name) (val body : SSAExpr)
    (h : SSAExpr.reduce env val = none) :
    SSAExpr.reduce env (.letE name val body) = none := by
  have : (letE name val body).size = val.size + body.size  + 1 := by grind [size]
  grind [reduce, reduceAux,reduceAux_eq_reduce]

theorem reduce_letE_ok (env : Array (Name × Option SSAExpr))
    (name : Name) (val body : SSAExpr)
    (val' body' : SSAExpr)
    (hv : SSAExpr.reduce env val = some val')
    (hb : SSAExpr.reduce (env.push (name, some val')) body = some body') :
    SSAExpr.reduce env (.letE name val body) = some body' := by
  have : (letE name val body).size = (val.size + body.size) + 1 := by grind [size]
  grind only [reduce, reduceAux, = Option.bind_apply, = Option.bind_some, reduceAux_eq_reduce]

theorem Array.findLast?_eq_some_imp_any_fst_eq {α β : Type} [BEq α]
    (args : Array (α × β)) (n : α) (x : β) :
    args.findLast? (fun p => p.1 == n) = some (n, x) → args.any (·.1 == n) = true := by
    intro h
    simp [Array.findLast?, Array.find?_eq_some_iff_getElem] at h ⊢
    grind

theorem Array.findLast?_eq_some_imp_any_fst_eq' {α β : Type} [BEq α]
    (args : Array (α × β)) (n : α) (x : α × β) :
    args.findLast? (fun p => p.1 == n) = some x → args.any (·.1 == n) = true := by
    intro h
    simp [Array.findLast?, Array.find?_eq_some_iff_getElem] at h ⊢
    grind


theorem reduce_app_beta (env : Array (Name × Option SSAExpr))
    (f x : SSAExpr)
    (henv : ∀ i : Fin env.size, ∀ e', env[i].2 = some e' → e'.size ≤ (f.app x).size)
    (varName : Name) (varType : SSAType) (lamBody : SSAExpr)
    (x' result : SSAExpr)
    (hf : SSAExpr.reduce env f = some (.lam varName varType lamBody))
    (hx : SSAExpr.reduce env x = some x')
    (hb : SSAExpr.reduce (env.push (varName, some x')) lamBody = some result) :
    SSAExpr.reduce env (.app f x) = some result := by
  have : (f.app x).size = (f.size + x.size) + 1 := by grind [size]
  simp [reduce, this]
  match h : f with
  | lam varName' varType' body =>
    simp [reduceAux]
    rw [reduceAux_eq_reduce _ _ _ (by grind [size]), hx]
    simp
    rw [reduceAux_eq_reduce _ _ _ (by grind [size])]
    simp [reduce, reduceAux] at hf
    grind
  | .const c =>
    simp [reduce, reduceAux] at hf
  | .letE varName' val body =>
    have : (letE varName' val body).size  = val.size + body.size + 1 := by grind [size]
    simp [reduce, this, reduceAux] at hf
    rw [reduceAux_eq_reduce _ _ _ (by grind [size])] at hf
    option_elim
    simp [reduceAux]
    rw [reduceAux_eq_reduce _ _ _ (by grind [size])]
    simp [hdolift]
    rw [reduceAux_eq_reduce _ _ _ (by grind [size])]
    rw [reduceAux_eq_reduce _ _ _ (by grind [size])] at hf
    simp [hf]
    rw [reduceAux_eq_reduce _ _ _ (by grind [size])]
    simp [hx]
    rw [reduceAux_eq_reduce _ _ _ (by {
        simp [size]
        have : (lam varName varType lamBody).size ≤ body.size := sorry -- reduce_size_le _ _ _ _ _ hf
        grind [size]
    })]
    grind
  | .var name =>
    simp [reduce, reduceAux] at hf
    option_elim
    match hh: dolift.2 with
    | some q =>
        simp [hh] at hf
        simp [reduceAux, hdolift, hh, hf]
        rw [reduceAux_eq_reduce _ _ _ (by grind [size]), hx]
        simp
        rw [reduceAux_eq_reduce _ _ _ (by {
            have := Array.findLast?_eq_some_imp_any_fst_eq' env _ _ hdolift
            simp only [Array.any_eq_true, beq_iff_eq] at this
            obtain ⟨i, hi, Hi⟩ := this
            specialize henv ⟨i, by omega⟩ q (by {
                simp
                sorry
            })
            have := henv
            grind [size]
        }), hb]
    | none =>
        simp [hh] at hf
   | .app g q =>
     have : (g.app q).size = g.size + q.size + 1 := by grind [size]
     simp [reduce, this, reduceAux] at hf
     rw [reduceAux_eq_reduce _ _ _ (by grind)] at hf
     option_elim
     simp [reduceAux]
     rw [reduceAux_eq_reduce _ _ _ (by grind)]
     simp [hdolift]
     match dolift with
     | lam varName' varType' body' =>
        simp at hf
        option_elim
        simp
        have : (lam varName' varType' body').size ≤ g.size := sorry
        rw [reduceAux_eq_reduce _ _ _ (by grind)]
        rw [reduceAux_eq_reduce _ _ _ (by grind [size])] at hf
        rw [reduceAux_eq_reduce _ _ _ (by grind)] at hdolift
        simp [hdolift]
        rw [reduceAux_eq_reduce _ _ _ (by grind [size])]
        simp [hf]
        rw [reduceAux_eq_reduce _ _ _ (by grind), hx]
        simp
        have : (lam varName varType lamBody).size ≤ body'.size := sorry
        rw [reduceAux_eq_reduce _ _ _ (by grind [size])]
        grind
      | .const c =>
        simp at hf
      | app _ _ =>
        simp at hf
      | letE _ _ _ =>
        simp at hf
      | var _ =>
        simp at hf

theorem reduce_app_not_lam (env : Array (Name × Option SSAExpr))
    (f x : SSAExpr)
    (hf : ∀ varName varType body, SSAExpr.reduce env f ≠ some (.lam varName varType body)) :
    SSAExpr.reduce env (.app f x) = app f x := by
  unfold reduce
  sorry

theorem reduce_app_arg_none (env : Array (Name × Option SSAExpr))
    (f x : SSAExpr)
    (varName : Name) (varType : SSAType) (lamBody : SSAExpr)
    (hf : SSAExpr.reduce env f = some (.lam varName varType lamBody))
    (hx : SSAExpr.reduce env x = none) :
    SSAExpr.reduce env (.app f x) = none := by
  unfold reduce
  simp only [size, reduceAux]
  sorry

end SSAExpr

theorem SSAExpr.eval_ifthenelse_app
    (args : Array (Name × SSAConst))
    (ty : SSAType)
    (cond t e : SSAExpr) :
    (SSAExpr.app (SSAExpr.app (SSAExpr.app (.const (.ifthenelse ty)) cond) t) e).eval args =
        (do
            let c ← cond.eval args
            let tv ← t.eval args
            let ev ← e.eval args
            pure (if c != SSAConst.ofBase (.int (0 : Int)) then tv else ev)) := by
    sorry

theorem SSAExpr.eval_letE_push_of_eval
    (args : Array (Name × SSAConst))
    (name : Name)
    (val body : SSAExpr)
    (v : SSAConst)
    (hval : val.eval args = some v) :
    (SSAExpr.letE name val body).eval args = body.eval (args.push (name, v)) := by
    unfold SSAExpr.eval
    sorry


theorem SSAExpr.eval_letE
    (args : Array (Name × SSAConst))
    (name : Name)
    (val body : SSAExpr)
    (v : SSAConst)
    (hval : val.eval args = some v) :
    (SSAExpr.letE name val body).eval args = body.eval (args.push (name, v)) := by
    exact SSAExpr.eval_letE_push_of_eval args name val body v hval

/-
  letE does nothing if the variable is already bound in the body expression
-/
theorem SSAExpr.eval_letE_bv
    (args : Array (Name × SSAConst))
    (name : Name)
    (val body : SSAExpr)
    (hval : (val.eval args).isSome)
    (hbody : (body.eval args).isSome) :
    (SSAExpr.letE name val body).eval args = body.eval args :=
    sorry
theorem SSAExpr.eval_var (args : ArgMap) (name : Name) :
    (SSAExpr.var name).eval args = Map.get args name := by
    sorry

theorem SSAExpr.eval_app
    (args : ArgMap)
    (varName : Name) (varType : SSAType) (body x : SSAExpr)
    (xv : SSAConst)
    (hx : x.eval args = some xv)
    (hdom : varType = xv.inferType) :
    (SSAExpr.app (.lam varName varType body) x).eval args =
        body.eval (args.push (varName, xv)) := by
    sorry

theorem SSAExpr.eval_isSome_inferType_eq (vars : VarMap) (args : Array (Name × SSAConst))
    (expr : SSAExpr) (v : SSAConst)
    (heval : expr.eval args = some v) :
        expr.inferType vars = some v.inferType := by
    sorry

theorem SSAExpr.eval_isSome_inferType (vars : VarMap) (args : Array (Name × SSAConst))
    (expr : SSAExpr) (v : SSAConst)
    (heval : expr.eval args = some v) :
        (expr.inferType vars).isSome := by
    sorry

theorem SSAExpr.inferType_eq_some_inferType!_of_isSome (vars : VarMap) : (expr : SSAExpr) →(expr.inferType vars).isSome → expr.inferType vars = expr.inferType! vars
| const base => by simp only [inferType, Option.isSome_some, inferType!, imp_self]
| letE name val body => by
    intro h
    simp only [inferType] at h
    option_elim
    simp [inferType, inferType!, hvalType, h]
    have := inferType_eq_some_inferType!_of_isSome (Array.push vars (name, valType)) body (by simp [h])
    have := inferType_eq_some_inferType!_of_isSome vars val (by grind)
    grind
| var name => by
    intro h
    simp only [inferType] at h
    option_elim
    simp [inferType, inferType!, h]
| app f x => by
    intro h
    simp only [inferType] at h
    option_elim
    have := inferType_eq_some_inferType!_of_isSome vars f (by grind)
    match hh : (f.inferType! vars).funDom? with
    | some codom =>
        grind [inferType, inferType!]
    | none =>
        grind
| lam varName varType body => by
    intro h
    simp only [inferType] at h
    option_elim
    have := inferType_eq_some_inferType!_of_isSome (Array.push vars (varName, varType)) body (by grind)
    grind [inferType, inferType!]

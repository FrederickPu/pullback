import Lean
import Mathlib.Logic.ExistsUnique
import Mathlib.Data.Fin.Tuple.Basic
import Pullback.SSA.Tactic

open Lean

inductive SSABaseType where
| float : SSABaseType
| int : SSABaseType
| unit : SSABaseType
deriving DecidableEq

inductive SSAType where
| ofBase : SSABaseType → SSAType
| fun : SSAType → SSAType → SSAType
| prod : SSAType → SSAType → SSAType
deriving DecidableEq

-- returns domain of function type if the type is a function type
def SSAType.funDom? : SSAType → Option SSAType
| .fun α _ => α
| _ => none

theorem SSAType.funDom?_eq_some_iff (f : SSAType) (dom : SSAType): f.funDom? = some dom → ∃ β, f = .fun dom β := by
    intro h
    match f with
    | .fun α β =>
        grind [funDom?]
    | ofBase _ => simp [funDom?] at h
    | prod α β => simp [funDom?] at h

-- returns codomain of function type if the type is a function type
def SSAType.funCodom? : SSAType → Option SSAType
| .fun _ β => β
| _ => none

inductive SSAConst where
/- use Rat instead of Float for underlying value since Float is opaque -/
| ofFloat : Rat → SSAConst
| ofInt : Int → SSAConst
| ofUnit : Unit → SSAConst
| loop (ty out : SSAType) : SSAConst
| prod (α β : SSAType) : SSAConst
| prod₁ (α β : SSAType) : SSAConst
| prod₂ (α β : SSAType) : SSAConst
| ifthenelse (ty : SSAType) : SSAConst
/-prop stuff-/
| eq (ty : SSABaseType) : SSAConst
| and : SSAConst
| or: SSAConst
deriving DecidableEq

inductive SSAExpr where
| const : SSAConst → SSAExpr
| letE (var : Name) (val : SSAExpr) (body : SSAExpr) : SSAExpr
| var (name : Name) : SSAExpr
| app (f : SSAExpr) (arg : SSAExpr)
| lam (varName : Name) (varType : SSAType) (body : SSAExpr) : SSAExpr
deriving Inhabited, DecidableEq

abbrev VarMap := Array (Name × SSAType)

def Fin.last' {n : Nat} [NeZero n] : Fin n :=
    match h :  n with
    | (k + 1) => Fin.last k
    | 0 => by {
        apply False.elim
        expose_names
        rw [h] at inst
        simp at inst
    }

def Fin.val_last'_eq {n : Nat} [NeZero n] : (Fin.last' (n := n)).val = n - 1 := by
    cases n with
    | succ k => simp [last']
    | zero => grind only

def Fin.le_last' {n : Nat} [NeZero n] : ∀ i : Fin n, i ≤ (Fin.last' (n := n)) := by
    cases n with
    | succ k =>
        intro i
        have : i.val ≤ (last' : Fin (k + 1)).val := by
            simp only [val_last'_eq, Nat.add_one_sub_one]
            have := i.isLt
            grind only
        exact this
    | zero => grind only

def Array.findLast? {α : Type u} (p : α → Bool) (as : Array α) : Option α := as.reverse.find? p

def Array.findLastFinIdx? {α : Type u} (p : α → Bool) (as : Array α) : Option (Fin as.size) := Option.map (fun res => have : NeZero as.size := ⟨by {
    have := res.isLt
    grind
}⟩;
Fin.last' - Fin.cast (size_reverse) res) (as.reverse.findFinIdx? p)

def Array.get (map : VarMap) (key : Name) : Option SSAType :=
    map.findLast? (·.1 = key) |>.map (·.2)

#check Array.find?_eq_some_iff_getElem


def SSAConst.inferType : SSAConst → SSAType
| ofFloat _ => .ofBase .float
| ofInt _ => .ofBase .int
| ofUnit _ => .ofBase .unit
| loop ty out => .fun (ty) <|
        .fun (.fun (ty) (.fun (.fun ty out) out))
        out

    -- the step function takes in a kcontinue continuation and returns ty (loop in CPS form)
| prod α β => .fun α (.fun β (.prod α β))
| prod₁ α β => .fun (.prod α β) α
| prod₂ α β => .fun (.prod α β) β
| ifthenelse ty => .fun (.ofBase .int) (.fun ty (.fun ty ty))
| eq ty => .fun (.ofBase ty) (.fun (.ofBase ty) (.ofBase .int))
| and => .fun (.ofBase .int) (.fun (.ofBase .int) (.ofBase .int))
| or => .fun (.ofBase .int) (.fun (.ofBase .int) (.ofBase .int))

/-
    none is returned the input expr doesn't typecheck
-/
def SSAExpr.inferType (vars : VarMap) : SSAExpr → Option SSAType
| const base => base.inferType
| letE name val body =>
    (val.inferType vars).bind <|
        fun valType => body.inferType (vars.push ⟨name, valType⟩)
| var name => vars.get name
| app f arg =>
    f.inferType vars |>.bind
    fun fType =>
    arg.inferType vars |>.bind
    fun argType =>
    fType.funDom? |>.bind
    fun dom =>
        if dom = argType then
            fType.funCodom?
        else
            none
| lam name varType body => body.inferType (vars.push (name, varType)) |>.bind (fun bodyType => SSAType.fun varType bodyType)

def SSAExpr.inferType! (vars : VarMap) : SSAExpr → SSAType
| const base => base.inferType
| letE varname val body => body.inferType! (vars.push (varname, val.inferType! vars))
| var name => (vars.get name).getD
    (.ofBase .unit) -- dummy value this is failure case
| app f _ => ((f.inferType! vars).funCodom?).getD
    (.ofBase .unit) -- dummy value this is failure case
| lam varName varType body => .fun varType (body.inferType! (vars.push (varName, varType)))

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


example (vars : VarMap) (expr : SSAExpr) : (expr.inferType vars).isSome ↔ expr.inferType vars = expr.inferType! vars := by
    apply Iff.intro
    exact fun a => SSAExpr.inferType_eq_some_inferType!_of_isSome vars expr a
    intro h
    grind only [= Option.isSome_some]

def SSABaseType.type : SSABaseType → Type
| float => Rat
| int => Int
| unit => Unit

def SSAType.type : SSAType → Type
| .ofBase baseTy => baseTy.type
| .fun α β => α.type → β.type
| prod α β => α.type × β.type

#check Nat × Int × Int
def DVector : List Type → Type
| [] => Unit
| α::l => α × DVector l

def DVector.cons {L: List Type} {α : Type} : α → DVector L → DVector (α::L)
| a, l => (a, l)

def DVector.push : {L: Array Type} → {α : Type} → DVector L.toList → α → DVector (L.push α).toList
| ⟨[]⟩, α, _, a => (a, ())
| ⟨l::ls⟩, α, (x, xs), a => DVector.cons x <| DVector.push xs a

/-
    recursive structure follows List.get exactly
-/
def DVector.get : {L : List Type} → (v : DVector L) → (i : Fin L.length) → L.get i
| .cons _ _, (a, _), ⟨0, _⟩ => a
| .cons _ _, (_, as), ⟨Nat.succ i, h⟩ => DVector.get as ⟨i, Nat.le_of_succ_le_succ h⟩

theorem Array.find?_eq_getElem_findFinIdx? {α : Type u} (xs : Array α) (p : α → Bool) :
      xs.find? p = (xs.findFinIdx? p).map (xs[·]) := by
    rcases xs with ⟨xs⟩; ext
    simp [List.findFinIdx?_eq_pmap_findIdx?, List.findIdx?_eq_fst_find?_zipIdx,
        List.find?_eq_some_iff_getElem]
    constructor
    · rintro ⟨_, _, _, rfl, _⟩; grind
    · grind

#check ForIn
def SSA.loop {α β : Type u} {m : Type u → Type v} [Monad m] [Inhabited α] (init : α) (step : α → (α → m β) → m β) : m β := sorry

lemma SSA.loop_unfold {α β : Type u} {m : Type u → Type v} [Monad m] [Inhabited α]
    (init : α) (step : α → (α → m β) → m β) :
    SSA.loop init step = step init (fun x => SSA.loop x step) := sorry

private def SSABaseType.decEq : (ty : SSABaseType) → DecidableEq ty.type
| float => by
    simp [SSABaseType.type]
    infer_instance
| int => by
    simp [SSABaseType.type]
    infer_instance
| unit => by
    simp [SSABaseType.type]
    infer_instance

instance (ty : SSABaseType) : DecidableEq (SSAType.ofBase ty).type := by
    simp [SSAType.type]
    exact SSABaseType.decEq ty

private def SSABaseType.inhabit : (ty : SSABaseType) → ty.type
| int => (0 : Int)
| float => (0 : Rat)
| unit => ()

instance {ty : SSABaseType} : Inhabited (SSAType.ofBase ty).type := by
    simp [SSAType.type]
    exact ⟨SSABaseType.inhabit ty⟩

instance {ty : SSAType} : Inhabited ty.type := sorry

def SSAConst.interp : (e : SSAConst) → (e.inferType).type
| ofFloat f => f
| ofInt i => i
| ofUnit () => ()
| ifthenelse ty => fun c t e => if (cast (by simp [SSAType.type, SSABaseType.type]) c : Int) != 0 then t else e
| loop ty out => SSA.loop (m := Id)
| prod α β => (@Prod.mk α.type β.type)
| prod₁ α β => fun ab => ab.1
| prod₂ α β => fun ab => ab.2
| eq ty => fun t₁ t₂ => if t₁ = t₂ then (1:Int) else (0:Int)
| or => fun x y => if x != (0: Int) || y != (0:Int) then (1:Int) else (0:Int)
| and => fun x y => if x != (0 : Int) && y != (0 : Int) then (1 : Int) else (0 : Int)

theorem SSAExpr.welltyped_app_iff (vars : VarMap) (f x : SSAExpr) : ((f.app x).inferType vars).isSome ↔ (do pure ((← f.inferType vars).funDom? = (← x.inferType vars))) = some True := by
    simp only [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff, SSAType.funDom?,
      Option.pure_def, Option.bind_eq_bind, Option.some.injEq, eq_iff_iff, iff_true]
    sorry

theorem SSAExpr.welltyped_letE_of_welltyped_val_body
        (vars : VarMap) (name : Name) (val body : SSAExpr) (valT : SSAType)
        (hval : val.inferType vars = some valT)
        (hbody : (body.inferType (vars.push (name, valT))).isSome) :
        ((SSAExpr.letE name val body).inferType vars).isSome := by
        simp [SSAExpr.inferType, hval, hbody]

theorem SSAExpr.welltyped_letE_iff
        (vars : VarMap) (name : Name) (val body : SSAExpr) :
        ((SSAExpr.letE name val body).inferType vars).isSome ↔
            ∃ valT,
                val.inferType vars = some valT ∧
                (body.inferType (vars.push (name, valT))).isSome := by
        constructor
        · intro h
          rcases Option.isSome_iff_exists.mp h with ⟨bodyT, hlet⟩
          simp [SSAExpr.inferType, Option.bind_eq_some_iff] at hlet
          rcases hlet with ⟨valT, hval, hbody⟩
          exact ⟨valT, hval, Option.isSome_iff_exists.mpr ⟨bodyT, hbody⟩⟩
        · intro h
          rcases h with ⟨valT, hval, hbody⟩
          exact SSAExpr.welltyped_letE_of_welltyped_val_body vars name val body valT hval hbody

theorem SSAExpr.inferType_letE_app (vars : VarMap) (name : Name) (val : SSAExpr) (f a : SSAExpr) :
    (SSAExpr.letE name val (f.app a)).inferType! vars = ((SSAExpr.letE name val f).app (.letE name val a)).inferType! vars := by
    rfl

theorem SSAType.type_fun_eq_dom_codom (ftype : SSAType) (dom codom : SSAType) : ftype.funDom? = dom → ftype.funCodom? = codom → ftype = .fun dom codom := sorry

theorem SSAType.dom_isSome_iff_codom_isSome (ftype : SSAType) : ftype.funDom?.isSome ↔ ftype.funCodom?.isSome := sorry

def SSAExpr.interp (vars : VarMap) : (e : SSAExpr) → (he : e.inferType vars |>.isSome) → DVector (Array.toList (vars.map (·.2.type))) → (Option.get (e.inferType vars) he).type
| .const base, he, _ => base.interp
| .letE name val body, he, ctx =>
    match hh : val.inferType vars with
    | some valType => cast (by simp [inferType, hh]) <| body.interp (vars.push ⟨name, valType⟩) (by {
        simp [inferType, Option.isSome_bind] at he
        grind only [= Option.any_some]
    }) (cast (by {
        simp [Array.map_push, hh]
    }) <| ctx.push (val.interp vars (by simp [hh]) ctx))
    | none => by {
        simp [inferType, Option.isSome_bind] at he
        grind only [= Option.any_none]
    }
| var name, he, ctx =>
    match h : (vars.findLastFinIdx? (·.1 == name)) with
    | some x => cast (by {
        simp [inferType, Array.get] at he
        calc
            _ = ((Array.findLast? (fun x => decide (x.fst = name)) vars).get he).2.type := by {
                have : x = (some x).get rfl := rfl
                rw [this]
                simp [← h]
                congr
                simp only [Array.findLast?, Array.findLastFinIdx?]
                simp [Array.find?_eq_getElem_findFinIdx?]
                congr
                rw [Fin.val_cast, Fin.sub_val_of_le]
                simp [Fin.val_last'_eq]
                grind
                have : NeZero (Array.size vars) := ⟨by {
                    have := x.isLt
                    grind
                }⟩
                exact Fin.le_last' _
            }
            _ = _ := by {
                simp [Array.findLast?, inferType, Array.get]
            }

    }) (ctx.get (Fin.cast (by {
        simp only [Array.toList_map, List.length_map, Array.length_toList]
    }) x))
    | none => by {
        simp only [inferType, Array.get, Array.findLast?, Option.isSome_map] at he
        simp only [Array.findLastFinIdx?, Option.map_eq_none_iff] at h
        grind only [= Option.isSome_none, = Array.find?_eq_none, = Array.findFinIdx?_eq_none_iff,
          = Array.size_reverse]
    }
| app f arg, he, ctx =>
    match hfType : f.inferType vars with
    | some fType =>
        match hdom : fType.funDom?, hcodom : fType.funCodom? with
        | some dom, some codom =>
            if hdom' : (fType.funDom? = some dom) then
                cast (by {
                    rw [welltyped_app_iff] at he
                    option_elim
                    expose_names
                    simp only [inferType, hfType, hdolift, Option.bind_some, hdom]
                    grind
                }) <|
                (cast (β := dom.type → codom.type) (by {
                    simp [inferType, Option.isSome_bind, Option.any_eq_true_iff_get] at he
                    have : inferType vars f = some (.fun dom codom) := by
                        rw [hfType, SSAType.type_fun_eq_dom_codom fType dom codom hdom hcodom]
                    simp [this, SSAType.type]
                }) <| f.interp vars (by grind [inferType]) ctx) (cast (β := dom.type) (by {
                    simp only [inferType] at he
                    option_elim
                    grind [SSAType.funCodom?, SSAType.funDom?]
                }) <| arg.interp vars (by {
                    simp only [inferType, Option.isSome_bind, Option.any_eq_true_iff_get] at he
                    grind only
                }) ctx)
            else
                (by grind)
        | some dom, none => (by grind [SSAType.dom_isSome_iff_codom_isSome])
        | none, some dom => (by grind [SSAType.dom_isSome_iff_codom_isSome])
        | none, none => (by {
            apply False.elim
            simp only [inferType, hfType, Option.bind_some] at he
            option_elim
            simp only [Option.ite_none_right_eq_some] at he
            grind
        })
    | none => by simp [inferType, hfType] at he
| lam name valType body, he, ctx => cast (by {
    simp [inferType, Option.isSome_bind] at he
    simp [inferType, SSAType.type]
}) <|
    fun val : valType.type => (body.interp (vars.push ⟨name, valType⟩) (by {
        simp [inferType, Option.isSome_bind] at he
        grind
    }) (cast (by simp) <| ctx.push val))


def SSAExpr.interp! (vars : VarMap) : (e : SSAExpr) → DVector (Array.toList (vars.map (·.2.type))) → (match e.inferType vars with
| some ty => ty.type
| none => Unit) := fun e ctx =>
    match he : e.inferType vars with
    | some ty => cast (by simp only [he, Option.get_some]) (e.interp vars (by simp [he]) ctx)
    | none => ()

def mkMutTuple : VarMap → SSAExpr × SSAType
| ⟨[]⟩ => (.const (SSAConst.ofUnit ()), .ofBase .unit)
| ⟨[(name, type)]⟩ => (.var name, type)
| ⟨(name, type)::b::l⟩ =>
    let (rightExpr, rightType) := mkMutTuple ⟨(b::l)⟩;
    (.app (.app (.const (.prod type rightType)) (.var name)) rightExpr, .prod type rightType)
termination_by as => as.size

theorem SSAExpr.inferType_mkMutTuple (vars : VarMap) : (mutVars : VarMap) → (h' : ∀ x ∈ mutVars, vars.get x.1 = x.2) → (mkMutTuple mutVars).fst.inferType vars = (mkMutTuple mutVars).snd
| ⟨[]⟩ => by simp [inferType, mkMutTuple, SSAConst.inferType]
| ⟨[(name, type)]⟩ => by
    simp only [List.mem_toArray,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq, mkMutTuple, inferType, imp_self]
| ⟨(name, type)::b::l⟩ => by
    simp
    intro h1 h2 h3
    have := inferType_mkMutTuple vars ⟨b::l⟩ (by grind)
    simp [inferType, mkMutTuple, this, h1, SSAConst.inferType, SSAType.funDom?, SSAType.funCodom?]
termination_by as => as.size

def destructMutTuple (tupleName : Name) : VarMap → SSAExpr → SSAExpr
| ⟨[]⟩, body => body
| ⟨[(name, _)]⟩, body => .letE name (.var tupleName) body
| ⟨(name, type)::b::l⟩, body =>
    let (_, rightTupleType) := mkMutTuple ⟨b::l⟩
    .letE name (.app (.const (.prod₁ type rightTupleType)) (.var tupleName)) (.letE tupleName (.app (.const (.prod₂ type rightTupleType)) (.var tupleName)) (destructMutTuple tupleName ⟨b::l⟩ body))
termination_by as _ => as.size

theorem SSAExpr.inferType_destructMutTuple (vars : VarMap) (name : Name): (mutVars : VarMap) → (h' : ∀ x ∈ mutVars, vars.get x.1 = x.2) → (body : SSAExpr) → (destructMutTuple name mutVars body).inferType vars = body.inferType (vars ++ mutVars):= sorry

/- todo :: should be able to prove termination by showing that each name will have a maximal number of prefix occurances in the mutvars varmap -/
private partial def freshNameAux (vars : Array Name) (baseName : Name) (idx : Nat) : Name :=
    if vars.any (· == baseName.appendIndexAfter idx) then
        freshNameAux vars baseName (idx + 1)
    else
        baseName.appendIndexAfter idx
/-
    for fixed mutVars, if baseName1 and baseName2 don't share a prefix then freshName will give different fresh names.
-/
def freshName (vars : Array Name) (baseName : Name) : Name :=
    if vars.any (· == baseName) then
        freshNameAux vars baseName 1
    else
        baseName

theorem freshName_hygenic (vars : Array Name) (baseName : Name) : ∀ var ∈ vars, var ≠ freshName vars baseName := sorry

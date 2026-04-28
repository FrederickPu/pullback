import Lean
import Mathlib.Logic.ExistsUnique
import Mathlib.Data.Fin.Tuple.Basic
import Pullback.SSA.Tactic
import Pullback.Shallow.Fix

open Lean

/-- `BasedType α` means each element of α maps to a runtime Type -/
class BasedType (α : Type) where
  valueType : α → Type

/-- `Typed α A` means each element of α can be assigned a type in A -/
class Typed (α A : Type) where
  type : α → A

inductive PType (BaseType : Type) where
| ofBase : BaseType → PType BaseType
| fun : PType BaseType → PType BaseType → PType BaseType
| prod : PType BaseType → PType BaseType → PType BaseType
deriving DecidableEq

namespace PType

def funDom? {BaseType : Type} : PType BaseType → Option (PType BaseType)
| .fun α _ => α
| _ => none

def funCodom? {BaseType : Type} : PType BaseType → Option (PType BaseType)
| .fun _ β => β
| _ => none

theorem funDom?_eq_some_iff {BaseType : Type} (f : PType BaseType) (dom : PType BaseType):
    f.funDom? = some dom → ∃ β, f = .fun dom β := by
  intro h
  match f with
  | .fun α β => simp [funDom?] at h; exact ⟨β, h ▸ rfl⟩
  | ofBase _ => simp [funDom?] at h
  | prod α β => simp [funDom?] at h

theorem funCodom?_eq_some_iff {BaseType : Type} (f : PType BaseType) (codom : PType BaseType):
    f.funCodom? = some codom → ∃ α, f = .fun α codom := by
  intro h
  match f with
  | .fun α β => simp [funCodom?] at h; exact ⟨α, h ▸ rfl⟩
  | ofBase _ => simp [funCodom?] at h
  | prod α β => simp [funCodom?] at h

/-- Interpret a PType as a runtime Type, given a mapping on base types -/
def type {BaseType : Type} [BasedType BaseType] : PType BaseType → Type
| .ofBase baseTy => BasedType.valueType baseTy
| .fun α β => α.type → β.type
| .prod α β => α.type × β.type

end PType

theorem PType.type_fun_eq_dom_codom {BaseType : Type} (ftype : PType BaseType) (dom codom : PType BaseType) :
    ftype.funDom? = some dom → ftype.funCodom? = some codom → ftype = .fun dom codom := by
  intro hdom hcodom
  match ftype with
  | .fun α β =>
    simp [PType.funDom?] at hdom
    simp [PType.funCodom?] at hcodom
    exact hdom ▸ hcodom ▸ rfl
  | ofBase _ => simp [PType.funDom?] at hdom
  | prod α β => simp [PType.funDom?] at hdom

theorem PType.dom_isSome_iff_codom_isSome {BaseType : Type} (ftype : PType BaseType) :
    ftype.funDom?.isSome ↔ ftype.funCodom?.isSome := by
  match ftype with
  | .fun α β => simp [PType.funDom?, PType.funCodom?]
  | ofBase _ => simp [PType.funDom?, PType.funCodom?]
  | prod α β => simp [PType.funDom?, PType.funCodom?]

/-- `Interp BaseType Const` gives a runtime value for each typed constant. -/
class Interp (BaseType : Type) (Const : Type) [BasedType BaseType] [Typed Const (PType BaseType)] where
  interp : ∀ c : Const, PType.type (BaseType := BaseType) (Typed.type (α := Const) (A := PType BaseType) c)

abbrev Map (α : Type) (β : Type) := Array (α × β)

abbrev VarMap (BaseType : Type) := Map Name (PType BaseType)

namespace Map

def Array.findLast? {α : Type} (p : α → Bool) (as : Array α) : Option α := as.reverse.find? p

def get {α β : Type} [DecidableEq α] (map : Map α β) (key : α) : Option β :=
    Array.findLast? (·.1 = key) map |>.map (·.2)

def keys {α β : Type} [DecidableEq α] (x : Map α β) := x.map (·.1)

def uniqueKeys {α β : Type} [DecidableEq α] (x : Map α β) : Prop :=
  (x.keys.toList).Nodup

end Map

def Fin.last' {n : Nat} [NeZero n] : Fin n :=
  match h : n with
  | k + 1 => Fin.last k
  | 0 => by
      apply False.elim
      expose_names
      rw [h] at inst
      simp at inst

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

def Array.findLastFinIdx? {α : Type u} (p : α → Bool) (as : Array α) : Option (Fin as.size) :=
  Option.map (fun res => have : NeZero as.size := ⟨by {
    have := res.isLt
    grind
  }⟩;
  Fin.last' - Fin.cast (Array.size_reverse) res) (as.reverse.findFinIdx? p)
namespace P

inductive Expr (Const BaseType : Type) [Typed Const (PType BaseType)] where
| const : Const → Expr Const BaseType
| letE (var : Name) (val : Expr Const BaseType) (body : Expr Const BaseType) : Expr Const BaseType
| var (name : Name) : Expr Const BaseType
| app (f : Expr Const BaseType) (arg : Expr Const BaseType)
| lam (varName : Name) (varType : PType BaseType) (body : Expr Const BaseType) : Expr Const BaseType
deriving DecidableEq

/-- DVector is a heterogeneous tuple indexed by a list of types -/
def DVector : List Type → Type
| [] => Unit
| α::l => α × DVector l

def Array.findLast? {α : Type u} (p : α → Bool) (as : Array α) : Option α := as.reverse.find? p

def Array.pushSome {α : Type u} (as : Array α) (a : Option α) : Array α :=
    as ++ a.toArray

namespace DVector

def cons {L: List Type} {α : Type} : α → DVector L → DVector (α::L)
| a, dv => (a, dv)

def push {L: Array Type} {α : Type} (dv : DVector L.toList) (a : α) : DVector (L.push α).toList :=
  match L with
  | ⟨[]⟩ => (a, ())
  | ⟨l::ls⟩ =>
      let (x, xs) := dv
      (x, push xs a)

def get : {L : List Type} → (v : DVector L) → (i : Fin L.length) → L.get i
| _::_, (va, _), ⟨0, _⟩ => va
| _::_, (_, dv), ⟨i+1, h⟩ => get dv ⟨i, Nat.lt_of_succ_lt_succ h⟩

end DVector

/-- Helper function to extend context by adding a binding value -/
def addToContext {L : Array Type} (dv : DVector L.toList) (α : Type) (x : α) :
    DVector ((L.push α).toList) :=
  DVector.push dv x

theorem Array.toList_push {α : Type} (as : Array α) (a : α) : (as.push a).toList = as.toList ++ [a] := by
  simp [Array.push]

theorem Array.map_push {α β : Type} (as : Array α) (f : α → β) (a : α) :
    (as.push a).map f = (as.map f).push (f a) := by
  simp [Array.push]

theorem PType.type_fun_eq {BaseType : Type} [BasedType BaseType] (dom codom : PType BaseType) :
    (.fun dom codom : PType BaseType).type = (dom.type → codom.type) := rfl

theorem Array.findLast?_map {α β : Type u} (f : α → β) (p : β → Bool) (as : Array α) :
    Array.findLast? p (as.map f) = (Array.findLast? (p ∘ f) as).map f := by
  simp only [findLast?]
  rcases as with ⟨xs⟩
  simp [← List.map_reverse, List.find?_map]

theorem Array.find?_eq_getElem_findFinIdx? {α : Type u} (xs : Array α) (p : α → Bool) :
      xs.find? p = (xs.findFinIdx? p).map (xs[·]) := by
    rcases xs with ⟨xs⟩; ext
    simp [List.findFinIdx?_eq_pmap_findIdx?, List.findIdx?_eq_fst_find?_zipIdx,
        List.find?_eq_some_iff_getElem]
    constructor
    · rintro ⟨_, _, _, rfl, _⟩; grind
    · grind

def Expr.inferType {Const : Type} {BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType] [DecidableEq (PType BaseType)]
    (vars : VarMap BaseType) : Expr Const BaseType → Option (PType BaseType)
| .const c => some (Typed.type c)
| .letE name val body =>
    (val.inferType vars).bind fun valType =>
      body.inferType (vars.push ⟨name, valType⟩)
| .var name => Map.get vars name
| .app f arg =>
    f.inferType vars |>.bind fun fType =>
    arg.inferType vars |>.bind fun argType =>
    fType.funDom? |>.bind fun dom =>
      if dom = argType then fType.funCodom? else none
| .lam name varType body =>
    body.inferType (vars.push (name, varType)) |>.bind fun bodyType =>
      some (.fun varType bodyType)

theorem PType.funCodom?_isSome_eq_funDom?_isSome {BaseType} : (x : PType BaseType) → (x.funCodom?.isSome = x.funDom?.isSome)
| .ofBase b => by rfl
| .prod T1 T2 => by rfl
| .fun dom codom => by rfl

theorem Expr.welltyped_app_iff {Const : Type} {BaseType : Type} [Typed Const (PType BaseType)]
    [DecidableEq BaseType] [DecidableEq (PType BaseType)]
    (vars : VarMap BaseType) (f x : Expr Const BaseType) :
    ((f.app x).inferType vars).isSome ↔ (do pure ((← f.inferType vars).funDom? = (← x.inferType vars))) = some True := by
  simp [inferType, Option.isSome_iff_exists, Option.bind_eq_some_iff]
  have : ∀ x : PType BaseType, x.funCodom?.isSome = x.funDom?.isSome :=
    fun x =>
      PType.funCodom?_isSome_eq_funDom?_isSome x
  grind [Option.isSome_iff_exists]


def Expr.interp {Const : Type} {BaseType : Type} [Typed Const (PType BaseType)]
    [BasedType BaseType] [Interp BaseType Const] [DecidableEq BaseType] [DecidableEq (PType BaseType)]
    (vars : VarMap BaseType) : (e : Expr Const BaseType) →
    (he : (e.inferType vars).isSome) →
    DVector (Array.toList (vars.map (·.2.type))) →
    (Option.get (e.inferType vars) he).type
| .const c, _, _ => Interp.interp (BaseType := BaseType) (Const := Const) c
| .letE name val body, he, ctx =>
    match hh : val.inferType vars with
    | some valType =>
        have hbody : (body.inferType (vars.push ⟨name, valType⟩)).isSome = true := by
          simpa [Expr.inferType, hh] using he
        cast (by simp [Expr.inferType, hh]) <|
          body.interp (vars.push ⟨name, valType⟩) hbody
            (cast (by simp [hh]) <| ctx.push (val.interp vars (by simp [hh]) ctx))
    | none => by
        simp [Expr.inferType, Option.isSome_bind] at he
        grind only [= Option.any_none]
| .var name, he, ctx =>
    match h : Array.findLastFinIdx? (fun x => x.1 == name) vars with
    | some x =>
        have hfind : (Map.Array.findLast? (fun x => decide (x.fst = name)) vars).isSome = true := by
          simp only [inferType, Map.get, Option.isSome_map] at he
          exact he
        cast (by
          simp [Expr.inferType, Map.get]
          calc
              _ = ((Map.Array.findLast? (fun x => decide (x.fst = name)) vars).get hfind).2.type := by
                have : x = (some x).get rfl := rfl
                rw [this]
                simp [← h]
                congr
                simp only [Map.Array.findLast?, Array.findLastFinIdx?]
                simp [Array.find?_eq_getElem_findFinIdx?]
                congr
                rw [Fin.val_cast, Fin.sub_val_of_le]
                simp [Fin.val_last'_eq]
                grind
                have : NeZero (Array.size vars) := ⟨by
                  have := x.isLt
                  grind
                ⟩
                exact Fin.le_last' _
              _ = _ := by
                simp [Map.Array.findLast?]
        ) (ctx.get (Fin.cast (by
          simp only [Array.toList_map, List.length_map, Array.length_toList]
        ) x))
    | none => by
        simp only [inferType, Map.get, Map.Array.findLast?, Option.isSome_map] at he
        simp only [Array.findLastFinIdx?, Option.map_eq_none_iff] at h
        grind only [= Option.isSome_none, = Array.find?_eq_none, = Array.findFinIdx?_eq_none_iff,
          = Array.size_reverse]
| .app f arg, he, ctx =>
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
                        rw [hfType, PType.type_fun_eq_dom_codom fType dom codom hdom hcodom]
                    simp [this, PType.type]
                }) <| f.interp vars (by grind [inferType]) ctx) (cast (β := dom.type) (by {
                    simp only [inferType] at he
                    option_elim
                    grind [PType.funCodom?, PType.funDom?]
                }) <| arg.interp vars (by {
                    simp only [inferType, Option.isSome_bind, Option.any_eq_true_iff_get] at he
                    grind only
                }) ctx)
            else
                (by grind)
        | some dom, none => (by grind [PType.dom_isSome_iff_codom_isSome])
        | none, some dom => (by grind [PType.dom_isSome_iff_codom_isSome])
        | none, none => (by {
            apply False.elim
            simp only [inferType, hfType, Option.bind_some] at he
            option_elim
            grind
        })
    | none => by simp [inferType, hfType] at he
| .lam name valType body, he, ctx =>
    cast (by simp [Expr.inferType, PType.type]) <|
      fun val : valType.type =>
        body.interp (vars.push ⟨name, valType⟩) (by
          simp [Expr.inferType, Option.isSome_bind] at he
          grind
        ) (cast (by simp) <| ctx.push val)

def Expr.interp! {Const : Type} {BaseType : Type} [Typed Const (PType BaseType)]
    [BasedType BaseType] [Interp BaseType Const] [DecidableEq BaseType] [DecidableEq (PType BaseType)]
    (vars : VarMap BaseType) :
    (e : Expr Const BaseType) → DVector (Array.toList (vars.map (·.2.type))) →
    (match e.inferType vars with
    | some ty => ty.type
    | none => Unit) := fun e ctx =>
    match he : e.inferType vars with
    | some ty => cast (by simp only [he, Option.get_some]) (e.interp vars (by simp [he]) ctx)
    | none => ()

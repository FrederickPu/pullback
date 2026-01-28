import Mathlib

/-
  `NDMatrix α shape` is a numpy ndarray with shape `shape` and elements from `α`
-/
@[reducible]
def NDMatrix (α : Type u) : List Nat → Type u
| [] => α
| (a::l) => Fin a → NDMatrix α l

def NDMatrix.map {α : Type u} (f : α → α) : {shape : List Nat} → NDMatrix α shape → NDMatrix α shape
| [] => f
| _::l => fun x => fun i => NDMatrix.map f (shape := l) (x i)

def NDMatrix.sum {α : Type u} [Zero α] [Add α] : {shape : List Nat} → NDMatrix α shape → α
| [] => id
| _::l => fun x => Fin.sum (fun i => NDMatrix.sum (shape := l) (x i))

def NDMatrix.entrywise {α : Type u} (f : α → α → α) : {shape : List Nat} → NDMatrix α shape → NDMatrix α shape → NDMatrix α shape
| [] => f
| _::l =>
  fun x y =>
    fun i => NDMatrix.entrywise f (shape := l) (x i) (y i)

instance instNonempty {α : Type u} [Nonempty α] : {shape : List Nat} → Nonempty (NDMatrix α shape)
  | [] => inferInstance
  | _ :: shape => letI := instNonempty (α := α) (shape := shape); inferInstance

instance {α : Type u} [Sub α] {shape : (List Nat)} : Sub (NDMatrix α shape) := ⟨NDMatrix.entrywise (· - · : α → α → α)⟩


instance {α : Type u} [Mul α] {shape : (List Nat)} : Mul (NDMatrix α shape) := ⟨NDMatrix.entrywise (· * · : α → α → α)⟩

instance{α : Type u} [Sub α] : Sub (NDMatrix α [0]) := by infer_instance


def List.shapesize (shape : List Nat) :  Nat := List.foldr (· * ·) 1 shape

def NN (α : Type u) (shape₁ shape₂ : List Nat) := NDMatrix α shape₁ → NDMatrix α shape₂

theorem Function.comp_invFun {α : Sort u} {β} [Nonempty α] (f : α → β) (hf : Function.Surjective f) : f ∘ Function.invFun f = id := by sorry

def NN.implBy {α : Type u} [Nonempty α] {shape₁ shape₂ : List Nat} (nn :  NN α shape₁ shape₂) (view₁ : NDMatrix α shape₁ → Vector α shape₁.shapesize) (view₂ : NDMatrix α shape₂ → Vector α shape₂.shapesize) (impl : Vector α shape₁.shapesize → Vector α shape₂.shapesize) : Prop := nn = (Function.invFun view₂) ∘ impl ∘ view₁

notation:50 nn " ⊧[" view₁ "," view₂ "] " impl:max =>
  NN.implBy nn view₁ view₂ impl

theorem NN.comp_implBy {α : Type u} [Nonempty α] {shape₁ shape₂ shape₃ : List Nat} (nn₁ :  NN α shape₁ shape₂) (nn₂ : NN α shape₂ shape₃) (view₁ : NDMatrix α shape₁ → Vector α shape₁.shapesize) (view₂ : NDMatrix α shape₂ → Vector α shape₂.shapesize) (hview₂ : Function.Surjective view₂) (view₃ : _) (impl₁ : Vector α shape₁.shapesize → Vector α shape₂.shapesize) (impl₂ : Vector α shape₂.shapesize → Vector α shape₃.shapesize) : nn₁ ⊧[view₁, view₂] impl₁ → nn₂ ⊧[view₂, view₃] impl₂ → (nn₂ ∘ nn₁) ⊧[view₁, view₃] (impl₂ ∘ impl₁) := by
  unfold implBy
  intro h1 h2
  rw [h1, h2]
  calc
    _ = Function.invFun view₃ ∘ impl₂ ∘ (view₂ ∘ Function.invFun view₂) ∘ impl₁ ∘ view₁ := by simp [Function.comp_assoc]
    _ = Function.invFun view₃ ∘ impl₂ ∘ id ∘ impl₁ ∘ view₁ := by
      grind [Function.comp_invFun]

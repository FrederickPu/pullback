import Pullback.Python.src.Eval

namespace Python

/-- interpret a runtime `Value` as a Lean `Bool`  -/
def toBool : Value → Bool
  | Value.int n   => n ≠ 0
  | Value.bool b  => b
  | _             => false     -- strings, lists, none all count as “false” here


inductive BigStep :  Env → Stmt → Env → Prop
  | skip : BigStep σ (python { skip; }) σ
  | seq : BigStep σ s₁ σ' → BigStep σ' s₂ σ'' → BigStep σ (.seq s₁ s₂) σ''
  | assign: BigStep σ (.assign x e) (σ.set x (eval σ e))
  | ifTrue  : ∀ {σ σ' e s₁ s₂},
      toBool (eval σ e) = true →
      BigStep σ s₁ σ' →
      BigStep σ (Stmt.ifThenElse e s₁ s₂) σ'
  | ifFalse : ∀ {σ σ'' e s₁ s₂},
      toBool (eval σ e) = false →
      BigStep σ s₂ σ'' →
      BigStep σ (Stmt.ifThenElse e s₁ s₂) σ''


/-- Skip doesn't affect state -/
theorem BigStep.skip_pre_eq_post : BigStep σ (python {skip;}) σ' ↔ (σ = σ') := by
  constructor
  . intro h
    cases h
    rfl
  . intro heq
    rw [heq]
    apply BigStep.skip

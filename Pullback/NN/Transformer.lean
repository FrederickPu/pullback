import Mathlib
import Pullback.NN.Basic

noncomputable section

variable {l d : Nat} (ε : ℝ)

def mean (x : NDMatrix ℝ [d]) : ℝ :=
  (1 / d•1) * Fin.sum (fun i => x i)

def var (x : NDMatrix ℝ [d]) : ℝ :=
  (1 / d) * Fin.sum (fun i : Fin d => (x i - mean x) ^ 2)

def rms (x : NDMatrix ℝ [d]) : ℝ :=
  Real.sqrt ((1 / d) * Fin.sum (fun i : Fin d => (x i) ^ 2))

def layerNorm
  (γ β : NDMatrix ℝ [d]) : NN ℝ [d] [d] := fun x =>
    fun i =>
      ((x i - mean x) / Real.sqrt (var x + ε)) * γ i + β i

def biasNorm
  (γ β : NDMatrix ℝ [d]) : NN ℝ [d] [d] := fun x =>
    fun i =>
      x i / (rms (x - β)) * Real.exp (γ i)

/-
 attention for a single query
 TODO :: add softmax and multiplication by values
-/
def attention (keys : Array (NDMatrix ℝ [d])) (query : NDMatrix ℝ [d]) : Array ℝ := keys.map (fun key => (key * query).sum)

#check Matrix.mulᵣ
#check Matrix.transpose
#check Array.getElem?_append

/-
  batches attention computation across all keys from the given token sequence
-/
def attentionSeqBatch (keys : NDMatrix ℝ [l, d]) (queries : NDMatrix ℝ [l, d]) : NDMatrix ℝ [l, l] := Matrix.mulᵣ queries (Matrix.transpose keys)


theorem attention_eq_get_attentionSeqBatch (keys queries : Array (NDMatrix ℝ [d])) (h : keys.size = queries.size):
  ∀ i : Fin queries.size, ∀ j : Fin queries.size, (attention keys (queries[i]))[j]'(by simp [attention, h]) = (attentionSeqBatch (fun i : Fin queries.size => keys[i]) (queries[·])) i j := by
  intro i j
  simp [attention, attentionSeqBatch, Matrix.transpose, Matrix.mulᵣ, dotProduct, HMul.hMul, Mul.mul, NDMatrix.sum, Finset.sum, List.sum]
  apply congr
  rfl
  rw [List.ofFn_eq_map]
  simp only [List.map_inj_left, List.mem_finRange, forall_const]
  intro idx
  have : (keys[↑j] idx) *  (queries[↑i] idx) = (queries[↑i] idx)  * (keys[↑j] idx) := by ring
  exact this

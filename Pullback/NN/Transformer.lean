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

def NDMatrix.softmax : NDMatrix EReal [d] → NDMatrix ℝ [d] := sorry

#check Array.mapFinIdx
open EReal ENNReal
#check EReal

def List.softmax (l : List EReal) : List ℝ := List.ofFn (NDMatrix.softmax l.get)

def Array.softmax (l : Array EReal) : Array ℝ := l.toList.softmax.toArray

theorem womp (vals : Array ℝ) (i : Fin vals.size) : ∀ j, j ≤ i → (NDMatrix.softmax ((vals.mapFinIdx (fun j (x:ℝ) h => (if j ≤ i then x else ∞ : EReal))).toList.get) ⟨j, by {
  sorry
}⟩) = (vals.map (fun x : ℝ => (x : EReal))).softmax[j]' sorry := sorry

/-
 attention for a single query
 TODO :: add softmax and multiplication by values
-/
def attention (keys : Array (NDMatrix ℝ [d])) (query : NDMatrix ℝ [d]) : Array ℝ := Array.softmax (keys.map (fun key => (key * query).sum))

#check Matrix.mulᵣ
#check Matrix.transpose
#check Array.getElem?_append

/-
  batches attention computation across all keys from the given token sequence
-/
def attentionSeqBatch (keys : NDMatrix ℝ [l, d]) (queries : NDMatrix ℝ [l, d]) : NDMatrix ℝ [l, l] := (NDMatrix.broadcastMap (NDMatrix.softmax)) (NDMatrix.map (fun x : ℝ => (x : EReal)) (NDMatrix.instMul.mul (NDMatrix.triu l) (Matrix.mulᵣ queries (Matrix.transpose keys))))


theorem attention_eq_get_attentionSeqBatch (keys queries : Array (NDMatrix ℝ [d])) (h : keys.size = queries.size):
  ∀ i : Fin queries.size, ∀ j : Fin queries.size, (hij : j ≤ i) → (attention (keys.take (i + 1)) (queries[i]))[j]'(by simp [attention, h, hij, Array.softmax, List.softmax]) = (attentionSeqBatch (fun i : Fin queries.size => keys[i]) (queries[·])) i j := by
  intro i j hij
  simp [attention, attentionSeqBatch, NDMatrix.sum, Matrix.mulᵣ, dotProduct, Finset.sum, List.ofFn_eq_map, NDMatrix.broadcastMap, NDMatrix.broadcastMapAux]
  unfold NDMatrix.triu
  simp [Mul.mul, NDMatrix.entrywise, Array.softmax]
  sorry

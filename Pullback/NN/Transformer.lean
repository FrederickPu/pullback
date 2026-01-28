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

-- /-
--   batches attention computation across all keys from the given token sequence
-- -/
-- def attentionSeqBatch (keys : NDMatrix ℝ [l, d]) (queries : NDMatrix ℝ [l, d]) : NDMatrix ℝ [l, l] := queries.transpose.matmul keys

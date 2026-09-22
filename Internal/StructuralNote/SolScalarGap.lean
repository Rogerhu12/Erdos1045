import EventualExact.PressureSupport

namespace StructuralNote.SolScalarGap

open Erdos1045.EventualExact FourierMultiplier FiniteBox PressureSupport
open scoped BigOperators
noncomputable section

def potentialAverage {n : ℕ} (q : Fin n → ℝ) : ℝ :=
  (∑ i, |operator n q i|) / n

def V {n : ℕ} (q : Fin n → ℝ) : ℝ := normalizedBoxEnergy (operator n) q

/-- The scalar gap in Lemma 7.1, with the manuscript normalization. -/
def G {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ) : ℝ :=
  B hm + V q - amplitude (2 * m) * potentialAverage q

theorem gap_nonneg {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ) :
    0 ≤ G hm q := by
  have h := box_support hm q
  have hn : (0 : ℝ) < (2 * m : ℕ) := by positivity
  simp only [G, V, potentialAverage, normalizedBoxEnergy, boxEnergy,
    Fintype.card_fin] at h ⊢
  field_simp at h ⊢
  linarith

theorem vertex_gap_le_deficit {m : ℕ} (hm : 0 < m) (s : SignPattern hm) :
    G hm (vertex (amplitude (2 * m)) s) ≤
      B hm - V (vertex (amplitude (2 * m)) s) := by
  let f := vertex (amplitude (2 * m)) s
  let A := amplitude (2 * m)
  have hn : (0 : ℝ) < (2 * m : ℕ) := by positivity
  have hterm (i : Fin (2 * m)) : f i * operator (2 * m) f i ≤
      A * |operator (2 * m) f i| := by
    have hf : |f i| = A := vertex_abs (amplitude_pos (by omega)).le s i
    calc
      _ ≤ |f i * operator (2 * m) f i| := le_abs_self _
      _ = |f i| * |operator (2 * m) f i| := abs_mul _ _
      _ = _ := by rw [hf]
  have hs : (∑ i : Fin (2 * m), f i * operator (2 * m) f i) ≤
      ∑ i : Fin (2 * m), A * |operator (2 * m) f i| :=
    Finset.sum_le_sum (fun i _ => hterm i)
  rw [← Finset.mul_sum] at hs
  simp only [G, V, potentialAverage, normalizedBoxEnergy, boxEnergy,
    Fintype.card_fin]
  field_simp
  dsimp only [f, A] at hs ⊢
  simp only [finitePairing] at hs ⊢
  linarith

end
end StructuralNote.SolScalarGap

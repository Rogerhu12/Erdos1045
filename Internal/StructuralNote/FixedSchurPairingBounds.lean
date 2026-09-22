import EventualExact.SchurOperatorBounds

/-! The mixed L2/L1 estimate for the difference of normal-error pairings. -/

namespace StructuralNote.FixedSchurPairingBounds

open Erdos1045.EventualExact SchurLiftBounds
open scoped BigOperators

noncomputable section

theorem normalized_pairing_cauchy {n : ℕ} (hn : 0 < n) (f g : Fin n → ℝ) :
    |finitePairing f g / n| ≤ Real.sqrt (meanSquare f) * Real.sqrt (meanSquare g) := by
  have hs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j => |f j|) (fun j => |g j|)
  simp only [sq_abs] at hs
  have ha : |finitePairing f g| ≤ ∑ j, |f j| * |g j| := by
    simpa only [finitePairing, abs_mul] using Finset.abs_sum_le_sum_abs (fun j => f j * g j) Finset.univ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_div, abs_of_pos hnR]
  apply (div_le_div_of_nonneg_right (ha.trans hs) hnR.le).trans_eq
  simp only [meanSquare, Real.sqrt_div' _ hnR.le, div_mul_div_comm, Real.mul_self_sqrt hnR.le]

theorem normalized_pairing_sup {n : ℕ} (hn : 0 < n) (f e : Fin n → ℝ) {G : ℝ}
    (hf : ∀ j, |f j| ≤ G) :
    |finitePairing f e / n| ≤ G * (∑ j, |e j|) / n := by
  have hs : |finitePairing f e| ≤ G * ∑ j, |e j| := by
    unfold finitePairing
    rw [Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hf j) (abs_nonneg _)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [abs_div, abs_of_pos hnR]
  exact div_le_div_of_nonneg_right hs hnR.le

theorem pairing_difference (n : ℕ) (g g' e e' : Fin n → ℝ) :
    finitePairing g e / n - finitePairing g' e' / n =
      finitePairing (g - g') e / n + finitePairing g' (e - e') / n := by
  simp only [finitePairing, Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

theorem error_pairing_difference_le {n : ℕ} (hn : 0 < n)
    (g g' e e' : Fin n → ℝ) {G : ℝ} (hg' : ∀ j, |g' j| ≤ G) :
    |finitePairing g e / n - finitePairing g' e' / n| ≤
      Real.sqrt (meanSquare (g - g')) * Real.sqrt (meanSquare e) +
        G * (∑ j, |e j - e' j|) / n := by
  rw [pairing_difference]
  exact (abs_add_le _ _).trans (add_le_add (normalized_pairing_cauchy hn (g - g') e)
    (normalized_pairing_sup hn g' (e - e') hg'))

end
end StructuralNote.FixedSchurPairingBounds

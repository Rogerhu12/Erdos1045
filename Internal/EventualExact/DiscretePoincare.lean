import EventualExact.DiscreteEnergyBounds

/-! The general mean-zero Poincare inequality for the actual pair energy. -/

noncomputable section
open scoped BigOperators

namespace Erdos1045.EventualExact.DiscreteEnergy

open Complex FourierMultiplier FiniteFourierLift SchurSpectrum

theorem mean_zero_poincare {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ)
    (hmean : ∑ j, c j = 0) :
    ((n : ℝ) - 1) / 2 * (∑ j, normSq (c j)) ≤ pairEnergy (by omega) c := by
  let : NeZero n := ⟨by omega⟩
  have hzero : coefficient c 0 = 0 := by rw [coefficient_zero, hmean, zero_div]
  have hp (p : Fin n) : ((n : ℝ) - 1) * normSq (coefficient c p) ≤
      weight n p * normSq (coefficient c p) := by
    by_cases hp0 : p = 0
    · simp [hp0, hzero]
    have hpv : p.val ≠ 0 := Fin.val_ne_zero_iff.mpr hp0
    have hlo : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p.val by omega)
    have hhi : (p : ℝ) + 1 ≤ n := by exact_mod_cast p.isLt
    have hw : (n : ℝ) - 1 ≤ weight n p := by
      unfold weight
      nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (by linarith : 0 ≤ (n : ℝ) - p - 1)]
    exact mul_le_mul_of_nonneg_right hw (normSq_nonneg _)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hp p)
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (n : ℝ) / 2)
  rw [pairEnergy_spectrum, parseval (by omega)]
  calc
    _ = (n : ℝ) / 2 * ∑ p : Fin n, ((n : ℝ) - 1) * normSq (coefficient c p) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := hm

theorem sum_normSq_le_pairEnergy {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ)
    (hmean : ∑ j, c j = 0) :
    (∑ j, normSq (c j)) ≤ 2 / ((n : ℝ) - 1) * pairEnergy (by omega) c := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) - 1 := by linarith
  have h := mean_zero_poincare hn c hmean
  apply (le_of_mul_le_mul_left ?_ hpos)
  field_simp
  linarith

end Erdos1045.EventualExact.DiscreteEnergy

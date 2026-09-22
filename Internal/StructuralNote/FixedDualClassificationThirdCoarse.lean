import StructuralNote.FixedDualClassificationStepEnergy
import StructuralNote.FixedDualClassificationMultiplierLimit

/-! The coarse third-harmonic test for the actual normalized profile. This
closes the large-defect branch of Lemma 8.1 directly from Parseval. -/

namespace StructuralNote.FixedDualClassificationThirdCoarse

open Real Complex Filter Erdos1045.EventualExact FourierMultiplier SchurLiftBounds FiniteBox
open FixedDualClassificationStep FixedDualClassificationStepEnergy
open FixedDualClassificationParseval FixedDualClassificationOddSpectrum
open FixedDualClassificationSignedCutoff FixedDualClassificationMultiplierLimit
open scoped BigOperators ComplexConjugate
noncomputable section

theorem profileCoefficient_neg {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (scale : ℝ) (p : ℤ) :
    profileCoefficient (stepProfile q scale) (-p) =
      conj (profileCoefficient (stepProfile q scale) p) := by
  rw [profileCoefficient_eq hn, profileCoefficient_eq hn]
  simp only [Int.cast_neg, neg_mul, neg_div, sinc_neg, signedMidpointCoefficient_neg,
    map_mul, Complex.conj_ofReal]

theorem positive_bessel_half {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (scale : ℝ) (P : ℕ) :
    ∑ k ∈ Finset.range P, ‖profileCoefficient (stepProfile q scale) (2 * k + 1)‖ ^ 2 ≤
      scale ^ 2 * meanSquare q / 2 := by
  classical
  have hinj : Set.InjOn (fun k : ℤ => 2 * k + 1) (signedCutoff P) := by
    intro a _ b _ h
    dsimp only at h
    omega
  have h := profileCoefficient_bessel hn q scale ((signedCutoff P).image (fun k : ℤ => 2 * k + 1))
  rw [Finset.sum_image hinj, sum_signedCutoff] at h
  have he : (∑ k ∈ Finset.range P,
      (‖profileCoefficient (stepProfile q scale) (2 * (k : ℤ) + 1)‖ ^ 2 +
        ‖profileCoefficient (stepProfile q scale) (2 * Int.negSucc k + 1)‖ ^ 2)) =
      2 * ∑ k ∈ Finset.range P, ‖profileCoefficient (stepProfile q scale) (2 * k + 1)‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hi : (2 * Int.negSucc k + 1 : ℤ) = -(2 * (k : ℤ) + 1) := by omega
    rw [hi, profileCoefficient_neg hn, norm_conj]
    ring
  rw [he] at h
  have hm : scale ^ 2 * (∑ j, q j ^ 2) / n = scale ^ 2 * meanSquare q := by
    unfold meanSquare
    ring
  rw [hm] at h
  linarith

theorem positiveWeight_coarse (k : ℕ) :
    positiveWeight k ≤ (1 / 6 : ℝ) + if k = 1 then 1 / 12 else 0 := by
  by_cases hk0 : k = 0
  · subst k
    norm_num [positiveWeight, kernelCoefficient, naturalKernelCoefficient]
  by_cases hk1 : k = 1
  · subst k
    norm_num [positiveWeight, kernelCoefficient, naturalKernelCoefficient]
  simp only [positiveWeight, kernelCoefficient, naturalKernelCoefficient, if_neg hk0, if_neg hk1, add_zero]
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 6)).mpr
  have hden : 0 < 4 * ((k : ℝ) + 1) := by positivity
  field_simp
  linarith

theorem continuousEnergy_coarse {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (scale : ℝ) :
    continuousEnergy q scale ≤ scale ^ 2 * meanSquare q / 12 +
      ‖profileCoefficient (stepProfile q scale) 3‖ ^ 2 / 12 := by
  apply (energy_summable hn q scale).tsum_le_of_sum_range_le
  intro P
  have hsum : (∑ k ∈ Finset.range P, energyTerm q scale k) ≤
      (1 / 6 : ℝ) * (∑ k ∈ Finset.range P, ‖profileCoefficient (stepProfile q scale) (2 * k + 1)‖ ^ 2) +
        ‖profileCoefficient (stepProfile q scale) 3‖ ^ 2 / 12 := by
    calc
      _ ≤ ∑ k ∈ Finset.range P,
          ((1 / 6 : ℝ) * ‖profileCoefficient (stepProfile q scale) (2 * k + 1)‖ ^ 2 +
            if k = 1 then ‖profileCoefficient (stepProfile q scale) 3‖ ^ 2 / 12 else 0) := by
        apply Finset.sum_le_sum
        intro k _
        have hw := mul_le_mul_of_nonneg_right (positiveWeight_coarse k)
          (sq_nonneg ‖profileCoefficient (stepProfile q scale) (2 * k + 1)‖)
        unfold energyTerm
        by_cases hk : k = 1
        · subst k
          norm_num only [Nat.cast_one, mul_one, show (2 : ℤ) + 1 = 3 by norm_num, if_pos rfl, ite_true] at hw ⊢
          nlinarith
        · simpa only [if_neg hk, add_zero, zero_mul] using hw
      _ ≤ _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq']
        split_ifs <;> nlinarith [sq_nonneg ‖profileCoefficient (stepProfile q scale) 3‖]
  have hb := positive_bessel_half hn q scale P
  linarith

theorem normalized_square_mass_le {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ Q hm) : profileScale (2 * m) ^ 2 * meanSquare q ≤ (Real.pi / 2) ^ 2 := by
  have hA := amplitude_pos (n := 2 * m) (by omega)
  have h := mul_le_mul_of_nonneg_left
    (meanSquare_le_of_bound (by omega) q hA.le hq.2) (sq_nonneg (profileScale (2 * m)))
  have he : profileScale (2 * m) ^ 2 * amplitude (2 * m) ^ 2 = (Real.pi / 2) ^ 2 := by
    unfold profileScale
    field_simp
  exact h.trans_eq he

/-- The actual energy threshold excludes third-coefficient defect at least 4/25. -/
theorem normalized_third_coarse {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ Q hm) (hV : (531 : ℝ) / 2000 < continuousEnergy q (profileScale (2 * m))) :
    (21 : ℝ) / 25 < ‖profileCoefficient (stepProfile q (profileScale (2 * m))) 3‖ := by
  have hc := continuousEnergy_coarse (by omega) q (profileScale (2 * m))
  have hs := normalized_square_mass_le hm q hq
  have hpi : Real.pi < 22 / 7 := by linarith [pi_lt_d4]
  by_contra! h
  have hn := norm_nonneg (profileCoefficient (stepProfile q (profileScale (2 * m))) 3)
  have hsq := (sq_le_sq₀ hn (by norm_num : (0 : ℝ) ≤ 21 / 25)).mpr h
  nlinarith [pi_pos]

end
end StructuralNote.FixedDualClassificationThirdCoarse

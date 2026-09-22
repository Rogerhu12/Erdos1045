import StructuralNote.HessianReferencePotential
import StructuralNote.RelativeDenominator

/-! Uniform comparison of the actual velocity Hessian denominators with the
regular reference denominators, at the scale of the chord energy. -/

namespace StructuralNote.HessianDenominator

open Erdos1045 Erdos1045.EventualExact Complex SchurSpectrum
open LogDiscriminantHessian HessianReferencePotential AngularObjectiveCurvature
open scoped BigOperators
noncomputable section

theorem ratio_square_difference_bound {a b c : ℂ} {δ : ℝ} (ha : a ≠ 0)
    (hδ : δ ≤ 1 / 2) (hrelative : ‖b / a - 1‖ ≤ δ) :
    ‖(c / b) ^ 2 - (c / a) ^ 2‖ ≤ 10 * δ * ‖c / a‖ ^ 2 := by
  let e := b / a - 1
  have he : ‖e‖ ≤ 1 / 2 := hrelative.trans hδ
  have hb : b ≠ 0 := by
    intro hz
    simp only [hz, zero_div, zero_sub, norm_neg, norm_one] at hrelative
    linarith
  have hr : c / b = (c / a) / (1 + e) := by
    dsimp [e]
    rw [show 1 + (b / a - 1) = b / a by ring]
    field_simp
  rw [hr]
  change ‖RelativeDenominator.correction (c / a) e‖ ≤ _
  rw [RelativeDenominator.correction_identity, norm_mul, norm_pow]
  have hf := (RelativeDenominator.factor_bound he).trans
    (mul_le_mul_of_nonneg_left hrelative (by norm_num : (0 : ℝ) ≤ 10))
  nlinarith only [mul_le_mul_of_nonneg_left hf (sq_nonneg ‖c / a‖)]

theorem quadratic_denominator_bound {n : ℕ} (w z v : Fin n → ℂ) {δ : ℝ}
    (hw : Function.Injective w) (hδ : δ ≤ 1 / 2)
    (hrelative : ∀ i j, i ≠ j → ‖(z i - z j) / (w i - w j) - 1‖ ≤ δ) :
    |quadratic z v - quadratic w v| ≤
      10 * δ * (∑ i, ∑ j, ‖(v i - v j) / (w i - w j)‖ ^ 2) := by
  have hp (i j : Fin n) :
      |(((v i - v j) / (z i - z j)) ^ 2).re - (((v i - v j) / (w i - w j)) ^ 2).re| ≤
        10 * δ * ‖(v i - v j) / (w i - w j)‖ ^ 2 := by
    by_cases hij : i = j
    · subst j
      simp
    · have hh := (abs_re_le_norm
        (((v i - v j) / (z i - z j)) ^ 2 - ((v i - v j) / (w i - w j)) ^ 2)).trans
        (ratio_square_difference_bound (sub_ne_zero.mpr (hw.ne hij)) hδ (hrelative i j hij))
      simpa only [sub_re] using hh
  have hs := (Finset.abs_sum_le_sum_abs
    (fun i => ∑ j, ((((v i - v j) / (z i - z j)) ^ 2).re -
      (((v i - v j) / (w i - w j)) ^ 2).re)) Finset.univ).trans
    (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hp i j))))
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have he : quadratic z v - quadratic w v =
      -((∑ i, ∑ j, (((v i - v j) / (z i - z j)) ^ 2).re) -
        (∑ i, ∑ j, (((v i - v j) / (w i - w j)) ^ 2).re)) := by
    unfold quadratic
    ring
  rw [he, abs_neg]
  exact hs

theorem regular_denominator_bound {n : ℕ} (hn : 0 < n) (z v : Fin n → ℂ) {δ : ℝ}
    (hw : Function.Injective (root n)) (hδ : δ ≤ 1 / 2)
    (hrelative : ∀ i j, i ≠ j → ‖(z i - z j) / (root n i - root n j) - 1‖ ≤ δ) :
    |quadratic z v - quadratic (root n) v| ≤ 20 * δ * pairEnergy hn v := by
  have hs := quadratic_denominator_bound (root n) z v hw hδ hrelative
  have he : (∑ i, ∑ j, ‖(v i - v j) / (root n i - root n j)‖ ^ 2) =
      2 * pairEnergy hn v := by
    rw [pairEnergy_eq_chord_sum]
    simp only [norm_div, div_pow, normSq_eq_norm_sq, root]
    ring
  rw [he] at hs
  nlinarith only [hs]

end
end StructuralNote.HessianDenominator

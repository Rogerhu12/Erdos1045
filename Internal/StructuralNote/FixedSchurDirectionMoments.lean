import StructuralNote.FixedSchurRotatedCoefficients
import EventualExact.DiscretePoincare

/-! Direction estimates on the full grid. These depend on the actual pair
energy of the direction, with no smallness or chart-domain premise. -/

namespace StructuralNote.FixedSchurDirectionMoments

open Complex Erdos1045.EventualExact SchurSpectrum SchurLiftBounds
open FourierMultiplier FiniteFourierLift SchurLift DiscreteEnergy
open CommonClosureEnergy CommonFiberDerivativeEnergy EdgeCoordinates
open FixedSchurData CommonFiberNormalProjectionScaled FixedSchurNormalInnerEnergy
open scoped BigOperators

noncomputable section

theorem difference_meanSquare_le {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ) :
    meanSquare (fun j => ‖difference hn v j‖) ≤ 8 * Real.pi ^ 2 * pairEnergy hn v / (n : ℝ) ^ 3 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he := difference_energy_le hn v
  simp only [normSq_eq_norm_sq] at he
  have hs : (∑ j, ‖difference hn v j‖ ^ 2) ≤
      8 * Real.pi ^ 2 * pairEnergy hn v / (n : ℝ) ^ 2 := by
    exact (le_div_iff₀ (sq_pos_of_pos hnR)).2 (by nlinarith only [he])
  exact (div_le_div_of_nonneg_right hs hnR.le).trans_eq (by ring)

theorem difference_pointwise_sq_le {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ) (j : Fin n) :
    ‖difference hn v j‖ ^ 2 ≤ 8 * Real.pi ^ 2 * pairEnergy hn v / (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he := difference_energy_le hn v
  simp only [normSq_eq_norm_sq] at he
  have hj := Finset.single_le_sum (s := Finset.univ) (f := fun k => ‖difference hn v k‖ ^ 2)
    (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  apply (le_div_iff₀ (sq_pos_of_pos hnR)).2
  have hmul := (mul_le_mul_of_nonneg_left hj (sq_nonneg (n : ℝ))).trans he
  simpa only [mul_comm] using hmul

theorem angleDifference_meanSquare_le {n : ℕ} (hn : 0 < n) (η : Fin n → ℝ) :
    meanSquare (angleDifference hn η) ≤
      8 * Real.pi ^ 2 * pairEnergy hn (fun j => (η j : ℂ)) / (n : ℝ) ^ 3 := by
  have h := difference_meanSquare_le hn (fun j => (η j : ℂ))
  simpa only [meanSquare, difference, ← ofReal_sub, norm_real, Real.norm_eq_abs, sq_abs,
    angleDifference] using h

theorem angleDifference_pointwise_sq_le {n : ℕ} (hn : 0 < n) (η : Fin n → ℝ) (j : Fin n) :
    angleDifference hn η j ^ 2 ≤
      8 * Real.pi ^ 2 * pairEnergy hn (fun j => (η j : ℂ)) / (n : ℝ) ^ 2 := by
  simpa only [difference, ← ofReal_sub, norm_real, Real.norm_eq_abs, sq_abs, angleDifference] using
    difference_pointwise_sq_le hn (fun j => (η j : ℂ)) j

theorem angleAverage_meanSquare_le {n : ℕ} (hn : 2 ≤ n) (η : Fin n → ℝ)
    (hmean : ∑ j, (η j : ℂ) = 0) :
    meanSquare (angleAverage (by omega) η) ≤
      4 * pairEnergy (by omega) (fun j => (η j : ℂ)) / (n : ℝ) ^ 2 := by
  have hs := average_square_sum hn η
  have hp := mean_zero_poincare hn (fun j => (η j : ℂ)) hmean
  simp only [normSq_ofReal, ← pow_two] at hp
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsum : 0 ≤ ∑ j, η j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbound : (n : ℝ) * ∑ j, η j ^ 2 ≤
      4 * pairEnergy (by omega) (fun j => (η j : ℂ)) := by nlinarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hsumle : (∑ j, η j ^ 2) ≤
      4 * pairEnergy (by omega) (fun j => (η j : ℂ)) / n :=
    (le_div_iff₀ hnpos).2 (by linarith only [hbound])
  exact (div_le_div_of_nonneg_right (hs.trans hsumle) hnpos.le).trans_eq (by ring)

theorem angleAverage_pointwise_sq_le {n : ℕ} (hn : 2 ≤ n) (η : Fin n → ℝ)
    (hmean : ∑ j, (η j : ℂ) = 0) (j : Fin n) :
    angleAverage (by omega) η j ^ 2 ≤
      12 * Real.log (n : ℝ) / (n : ℝ) ^ 2 *
        pairEnergy (by omega) (fun j => (η j : ℂ)) := by
  have hj := DiscreteSobolev.pointwise_sq_le hn (fun j => (η j : ℂ)) hmean j
  have hk := DiscreteSobolev.pointwise_sq_le hn (fun j => (η j : ℂ)) hmean (successor (by omega) j)
  simp only [norm_real, Real.norm_eq_abs, sq_abs] at hj hk
  unfold angleAverage
  nlinarith [sq_nonneg (η j - η (successor (by omega) j))]

theorem tangent_abs_le_scale_difference {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → ℂ) (j : Fin n) :
    |tangent (by omega) v j| ≤ scale n * ‖difference (by omega) v j‖ := by
  have hsin := (SignedPressureRemainder.reciprocal_sine_le hn).1
  have href : ‖difference (by omega) (fun k => character n 1 k) j‖ =
      2 * Real.sin (Real.pi / n) := by
    rw [reference_difference]
    simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_I, norm_frame]
    rw [abs_of_pos hsin]
    ring
  calc
    |tangent (by omega) v j| = |((n : ℂ) * edgeRatio (by omega) v j).re| := by
      simp only [tangent, mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
    _ ≤ ‖(n : ℂ) * edgeRatio (by omega) v j‖ := abs_re_le_norm _
    _ = scale n * ‖difference (by omega) v j‖ := by
      rw [norm_mul, norm_natCast, edgeRatio_eq_difference, norm_div, href]
      unfold scale
      ring

theorem tangent_meanSquare_le {n : ℕ} (hn : 2 ≤ n) (v : Fin n → ℂ) :
    meanSquare (tangent (by omega) v) ≤ (Real.pi ^ 2 / 2) * n * pairEnergy (by omega) v := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs := scale_bounds hn
  have hA := pairEnergy_nonneg (by omega) v
  have hdom := meanSquare_domination (tangent (by omega) v)
    (fun j => ‖difference (by omega) v j‖) hs.1.le (fun j => by
      simpa only [abs_of_nonneg (norm_nonneg _)] using tangent_abs_le_scale_difference hn v j)
  calc
    _ ≤ scale n ^ 2 * meanSquare (fun j => ‖difference (by omega) v j‖) := hdom
    _ ≤ ((n : ℝ) ^ 2 / 4) ^ 2 *
        (8 * Real.pi ^ 2 * pairEnergy (by omega) v / (n : ℝ) ^ 3) := by
      exact mul_le_mul (pow_le_pow_left₀ hs.1.le hs.2 2)
        (difference_meanSquare_le (by omega) v) (by unfold meanSquare; positivity) (sq_nonneg _)
    _ = _ := by field_simp; ring

theorem tangent_pointwise_sq_le {n : ℕ} (hn : 2 ≤ n) (v : Fin n → ℂ) (j : Fin n) :
    tangent (by omega) v j ^ 2 ≤
      (Real.pi ^ 2 / 2) * (n : ℝ) ^ 2 * pairEnergy (by omega) v := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs := scale_bounds hn
  have hA := pairEnergy_nonneg (by omega) v
  have hj := pow_le_pow_left₀ (abs_nonneg _) (tangent_abs_le_scale_difference hn v j) 2
  rw [sq_abs, mul_pow] at hj
  calc
    _ ≤ scale n ^ 2 * ‖difference (by omega) v j‖ ^ 2 := hj
    _ ≤ ((n : ℝ) ^ 2 / 4) ^ 2 *
        (8 * Real.pi ^ 2 * pairEnergy (by omega) v / (n : ℝ) ^ 2) :=
      mul_le_mul (pow_le_pow_left₀ hs.1.le hs.2 2)
        (difference_pointwise_sq_le (by omega) v j) (sq_nonneg _) (sq_nonneg _)
    _ = _ := by field_simp; ring

end
end StructuralNote.FixedSchurDirectionMoments

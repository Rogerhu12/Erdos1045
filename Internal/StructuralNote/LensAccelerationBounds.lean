import StructuralNote.LensIncrementDerivatives

/-! Pointwise bounds for the full lens acceleration, with its implicit
second-height derivative separated from the direct source. -/

namespace StructuralNote.LensAccelerationBounds

open Erdos1045.EventualExact Complex LensClosure LensIncrementDerivatives
noncomputable section

theorem height_ge_one {t : ℝ} (ht : |t| ≤ 1) : 1 ≤ Lens.height t := by
  have hs : t ^ 2 ≤ 1 := by nlinarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
  exact Real.one_le_sqrt.mpr (by linarith)

theorem slope_abs_le {t : ℝ} (ht : |t| ≤ 1) : |heightSlope t| ≤ 1 := by
  have hh := height_ge_one ht
  rw [heightSlope, abs_div, abs_neg, abs_of_pos (by linarith : 0 < Lens.height t)]
  exact (div_le_one (by linarith)).mpr (ht.trans hh)

theorem curvature_abs_le {t : ℝ} (ht : |t| ≤ 1) : |heightCurvature t| ≤ 4 := by
  have hh := height_ge_one ht
  have hc : 1 ≤ Lens.height t ^ 3 := one_le_pow₀ hh
  have hp : 0 < Lens.height t ^ 3 := by positivity
  rw [heightCurvature, abs_div, abs_of_nonpos (by norm_num : (-4 : ℝ) ≤ 0), neg_neg,
    abs_of_pos hp]
  exact (div_le_iff₀ hp).mpr (by linarith)

theorem bodyVelocity_bound {l σ t u : ℝ} (hσ : |σ| ≤ 1) (ht : |t| ≤ 1) :
    ‖bodyVelocity l σ t u‖ ≤ 2 * |u| + |l| := by
  have hs := slope_abs_le ht
  calc
    _ ≤ |σ| * |heightSlope t * u - l| + |u| := by
      simpa only [bodyVelocity, norm_real, Real.norm_eq_abs, norm_mul, norm_I,
        mul_one, abs_mul] using norm_add_le
          ((σ * (heightSlope t * u - l) : ℝ) : ℂ) ((u : ℂ) * I)
    _ ≤ |heightSlope t * u - l| + |u| :=
      add_le_add (mul_le_of_le_one_left (abs_nonneg _) hσ) le_rfl
    _ ≤ (|heightSlope t| * |u| + |l|) + |u| := by
      gcongr
      simpa only [abs_mul] using abs_sub (heightSlope t * u) l
    _ ≤ _ := by nlinarith [abs_nonneg u]

theorem bodyAcceleration_zero_bound {ll σ t u : ℝ} (hσ : |σ| ≤ 1) (ht : |t| ≤ 1) :
    ‖bodyAcceleration ll σ t u 0‖ ≤ 4 * u ^ 2 + |ll| := by
  have hc := curvature_abs_le ht
  simp only [bodyAcceleration, ofReal_zero, mul_zero, zero_mul, add_zero, norm_real,
    Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ |heightCurvature t * u ^ 2 - ll| := mul_le_of_le_one_left (abs_nonneg _) hσ
    _ ≤ |heightCurvature t * u ^ 2| + |ll| := abs_sub _ _
    _ = |heightCurvature t| * u ^ 2 + |ll| := by rw [_root_.abs_mul, abs_of_nonneg (sq_nonneg u)]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hc (sq_nonneg u)) le_rfl

theorem increment_source_bound {α L σ t a l u ll : ℝ} (hσ : |σ| ≤ 1) (ht : |t| ≤ 1) :
    ‖incrementAcceleration α L σ t a l u 0 ll 0‖ ≤
      a ^ 2 * ‖body L σ t‖ + 4 * |a| * |u| + 2 * |a| * |l| + 4 * u ^ 2 + |ll| := by
  have hv := bodyVelocity_bound (l := l) (u := u) hσ ht
  have ha := bodyAcceleration_zero_bound (ll := ll) (u := u) hσ ht
  calc
    _ ≤ ‖(-(a : ℂ) ^ 2) * body L σ t‖ +
        ‖2 * (a : ℂ) * I * bodyVelocity l σ t u‖ + ‖bodyAcceleration ll σ t u 0‖ := by
      rw [incrementAcceleration, norm_mul, norm_unit, one_mul]
      simp only [ofReal_zero, zero_mul, zero_sub]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = a ^ 2 * ‖body L σ t‖ + 2 * |a| * ‖bodyVelocity l σ t u‖ +
        ‖bodyAcceleration ll σ t u 0‖ := by
      simp only [norm_mul, norm_neg, norm_pow, norm_real, Real.norm_eq_abs, sq_abs,
        norm_ofNat, norm_I, mul_one]
    _ ≤ a ^ 2 * ‖body L σ t‖ + 2 * |a| * (2 * |u| + |l|) + (4 * u ^ 2 + |ll|) := by
      gcongr
    _ = _ := by ring

end
end StructuralNote.LensAccelerationBounds

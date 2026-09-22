import StructuralNote.CommonClosureDifference

/-! Pointwise and total-variation bounds for changing the sign word at a common parameter. -/

namespace StructuralNote.CommonClosureDifference

open Erdos1045.EventualExact Erdos1045.EventualExact.LensClosure
open Complex Set Metric
open scoped BigOperators
noncomputable section

theorem tangent_norm_le_two {α s t : ℝ} (hs : |s| ≤ 1) (ht : |t| ≤ 1) :
    ‖tangent α s t‖ ≤ 2 := by
  have h := tangent_error (α := α) (μ := α) hs ht
  simp only [sub_self, abs_zero, zero_add] at h
  have hh := norm_le_norm_sub_add (tangent α s t) (unit α * I)
  simp only [norm_mul, norm_unit, norm_I, mul_one] at hh
  linarith

theorem increment_height_lipschitz (α L : ℝ) {s x y : ℝ}
    (hs : |s| ≤ 1) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    ‖increment α L s x - increment α L s y‖ ≤ 2 * |x - y| := by
  have hc : Convex ℝ (Icc (-1 : ℝ) 1) := convex_Icc _ _
  have h := hc.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := increment α L s) (f' := tangent α s) (C := (2 : ℝ))
    (fun z hz => (increment_hasDerivAt α L s (by nlinarith [hz.1, hz.2])).hasDerivWithinAt)
    (fun z hz => tangent_norm_le_two hs (abs_le.mpr hz))
    (abs_le.mp hy) (abs_le.mp hx)
  simpa only [Real.norm_eq_abs] using h

theorem height_parameter_difference {m : ℕ} (t : Fin m → ℝ) (ξ η : ℂ) (j : Fin m) :
    |heightParameter t ξ j - heightParameter t η j| ≤ ‖ξ - η‖ := by
  have he : heightParameter t ξ j - heightParameter t η j =
      harmonicFunctional (midpoint m j) (ξ - η) := by
    simp only [heightParameter, map_sub]
    ring
  rw [he]
  exact harmonicFunctional_le_norm _ _

theorem increment_common_parameter_bound {m : ℕ} (α L s r t : Fin m → ℝ)
    {ξ η : ℂ} (hs : ∀ j, |s j| ≤ 1)
    (hξ : ∀ j, |heightParameter t ξ j| ≤ 1)
    (hη : ∀ j, |heightParameter t η j| ≤ 1) (j : Fin m) :
    ‖increment (α j) (L j) (s j) (heightParameter t ξ j) -
      increment (α j) (L j) (r j) (heightParameter t η j)‖ ≤
        2 * ‖ξ - η‖ + |s j - r j| * |Lens.width (L j) (heightParameter t η j)| := by
  calc
    _ ≤ ‖increment (α j) (L j) (s j) (heightParameter t ξ j) -
          increment (α j) (L j) (s j) (heightParameter t η j)‖ +
        ‖increment (α j) (L j) (s j) (heightParameter t η j) -
          increment (α j) (L j) (r j) (heightParameter t η j)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * |heightParameter t ξ j - heightParameter t η j| +
        |s j - r j| * |Lens.width (L j) (heightParameter t η j)| := by
      rw [increment_word_difference_norm]
      exact add_le_add (increment_height_lipschitz _ _ (hs j) (hξ j) (hη j)) le_rfl
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
      (height_parameter_difference t ξ η j) (by norm_num : (0 : ℝ) ≤ 2)) le_rfl

/-- Away from the changed sites, only the small change of the closure root contributes. -/
theorem increment_difference_off_support {m : ℕ} (α L s r t : Fin m → ℝ)
    {ξ η : ℂ} (hs : ∀ j, |s j| ≤ 1)
    (hξ : ∀ j, |heightParameter t ξ j| ≤ 1)
    (hη : ∀ j, |heightParameter t η j| ≤ 1) (j : Fin m) (hagree : s j = r j) :
    ‖increment (α j) (L j) (s j) (heightParameter t ξ j) -
      increment (α j) (L j) (r j) (heightParameter t η j)‖ ≤ 2 * ‖ξ - η‖ := by
  simpa only [hagree, sub_self, abs_zero, zero_mul, add_zero] using
    increment_common_parameter_bound α L s r t hs hξ hη j

/-- The nonlinear correction preserves the total-variation scale of a sparse word change. -/
theorem increment_difference_sum {m : ℕ} (hm : 2 ≤ m) (α L s r t : Fin m → ℝ)
    {R w : ℝ} (hs : ∀ j, |s j| ≤ 1) (hr : ∀ j, |r j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |t j| + R ≤ 1 / 4)
    {ξ η : ℂ} (hξ : ‖ξ‖ ≤ R) (hη : ‖η‖ ≤ R)
    (hξz : closure α L s t ξ = 0) (hηz : closure α L r t η = 0)
    (J : Finset (Fin m)) (hagree : ∀ j, j ∉ J → s j = r j)
    (hwidth : ∀ j ∈ J, |Lens.width (L j) (heightParameter t η j)| ≤ w) :
    (∑ j, ‖increment (α j) (L j) (s j) (heightParameter t ξ j) -
      increment (α j) (L j) (r j) (heightParameter t η j)‖) ≤ 18 * J.card * w := by
  have hξt (j : Fin m) : |heightParameter t ξ j| ≤ 1 := by
    have h := ball_height_small α t hsmall (mem_closedBall_zero_iff.mpr hξ) j
    linarith [abs_nonneg (α j - midpoint m j)]
  have hηt (j : Fin m) : |heightParameter t η j| ≤ 1 := by
    have h := ball_height_small α t hsmall (mem_closedBall_zero_iff.mpr hη) j
    linarith [abs_nonneg (α j - midpoint m j)]
  have hd := root_sparse_word_difference hm α L s r t hs hr hsmall hξ hη hξz hηz J hagree hwidth
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  calc
    _ ≤ ∑ j, (2 * ‖ξ - η‖ + |s j - r j| *
        |Lens.width (L j) (heightParameter t η j)|) :=
      Finset.sum_le_sum (fun j _ => increment_common_parameter_bound α L s r t hs hξt hηt j)
    _ = 2 * m * ‖ξ - η‖ + ∑ j, |s j - r j| *
        |Lens.width (L j) (heightParameter t η j)| := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ 2 * m * ((8 * J.card / m : ℝ) * w) + 2 * J.card * w :=
      add_le_add (mul_le_mul_of_nonneg_left hd (by positivity))
        (sparse_word_source L s r t η J hs hr hagree hwidth)
    _ = _ := by field_simp; ring

end
end StructuralNote.CommonClosureDifference

import StructuralNote.FixedDualDerivativeBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-! Certified stationary primitive values, including the quadratic midpoint error. -/

namespace StructuralNote.FixedDualStationaryValues

open Real Set MeasureTheory FixedDualPrimitive FixedDualArithmetic FixedDualDerivativeBound
open scoped Interval
noncomputable section

theorem witness_difference_bound {b x y : ℝ} (hb : |b| ≤ 1)
    (hx : x ∈ Icc (3 / 50 : ℝ) (69 / 50)) (hy : y ∈ Icc (3 / 50 : ℝ) (69 / 50)) :
    |witness b x - witness b y| ≤ 26 * |x - y| := by
  have h := (convex_Icc (3 / 50 : ℝ) (69 / 50)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := witness b) (f' := witnessFirst b) (C := (26 : ℝ))
    (fun u hu => (witness_hasDerivAt b (show sin u ≠ 0 by
      have hs := sine_lower_on_table hu
      linarith)).hasDerivWithinAt)
    (fun u hu => by simpa only [Real.norm_eq_abs] using
      (witnessFirst_abs_lt_twenty_six hb hu).le) hy hx
  simpa only [Real.norm_eq_abs] using h

/-- Integrating a linear derivative bound gives the factor one half in the quadratic error. -/
theorem primitive_error_from_linear_bound {f g : ℝ → ℝ} {r t M : ℝ}
    (hc : ContinuousOn g (uIcc r t))
    (hd : ∀ x ∈ uIcc r t, HasDerivAt f (g x) x)
    (hb : ∀ x ∈ uIcc r t, |g x| ≤ M * |x - r|) :
    |f t - f r| ≤ M / 2 * (t - r) ^ 2 := by
  have hi := hc.intervalIntegrable (μ := volume)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [← he, ← Real.norm_eq_abs, intervalIntegral.norm_integral_eq_norm_integral_uIoc]
  have hbi : IntervalIntegrable (fun x => M * |x - r|) volume r t :=
    (continuous_const.mul (continuous_id.sub continuous_const).abs).intervalIntegrable _ _
  have hb' : ∀ᵐ x ∂volume.restrict (uIoc r t), ‖g x‖ ≤ M * |x - r| := by
    filter_upwards [self_mem_ae_restrict measurableSet_uIoc] with x hx
    simpa only [Real.norm_eq_abs] using hb x (uIoc_subset_uIcc hx)
  calc
    _ ≤ ∫ x in uIoc r t, M * |x - r| :=
      MeasureTheory.norm_integral_le_of_norm_le hbi.def' hb'
    _ = M * (|t - r| ^ 2 / 2) := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      have he := integral_pow_abs_sub_uIoc (a := r) (b := t) (n := 1)
      norm_num at he
      simpa only [sq_abs] using he
    _ = _ := by rw [sq_abs]; ring

theorem primitive_error_at_root {b r t : ℝ} (hb : |b| ≤ 1)
    (hr : r ∈ Icc (3 / 50 : ℝ) (69 / 50))
    (ht : t ∈ Icc (3 / 50 : ℝ) (69 / 50)) (hz : witness b r = 0) :
    |primitive b t - primitive b r| ≤ 13 * (t - r) ^ 2 := by
  have hsub : uIcc r t ⊆ Icc (3 / 50 : ℝ) (69 / 50) :=
    uIcc_subset_Icc hr ht
  have hc : ContinuousOn (witness b) (uIcc r t) := by
    intro x hx
    have hs := sine_lower_on_table (hsub hx)
    exact (witness_hasDerivAt b (by linarith)).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ uIcc r t, HasDerivAt (primitive b) (witness b x) x := by
    intro x hx
    have hs := sine_lower_on_table (hsub hx)
    exact primitive_hasDerivAt b (by linarith)
  have hb' : ∀ x ∈ uIcc r t, |witness b x| ≤ 26 * |x - r| := by
    intro x hx
    simpa only [hz, sub_zero] using witness_difference_bound hb (hsub hx) hr
  convert primitive_error_from_linear_bound hc hd hb' using 1
  norm_num

theorem table_root_midpoint_error (i : Fin 10) {r : ℝ}
    (hr : r ∈ Icc (left (rows i) : ℝ) (right (rows i) : ℝ))
    (hz : witness (signedParameter (rows i)) r = 0) :
    |primitive (signedParameter (rows i)) r -
      primitive (signedParameter (rows i)) (midpoint (rows i))| ≤ 13 / 40000 := by
  have hw := row_midpoint_width (rows i)
  have hwl : (midpoint (rows i) : ℝ) - (left (rows i) : ℝ) = 1 / 200 := by
    have he := congrArg (fun q : ℚ => (q : ℝ)) hw.1
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using he
  have hwr : (right (rows i) : ℝ) - (midpoint (rows i) : ℝ) = 1 / 200 := by
    have he := congrArg (fun q : ℚ => (q : ℝ)) hw.2.1
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using he
  have hm : (midpoint (rows i) : ℝ) ∈ Icc (left (rows i) : ℝ) (right (rows i) : ℝ) := by
    constructor <;> linarith
  obtain ⟨hb, hr'⟩ := table_row_domain i hr
  have he := primitive_error_at_root hb hr' (table_row_domain i hm).2 hz
  have hd : |(midpoint (rows i) : ℝ) - r| ≤ 1 / 200 := by
    rw [abs_le]
    constructor <;> linarith [hr.1, hr.2]
  rw [abs_sub_comm] at he
  have hs := sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 200) |>.mpr hd
  rw [sq_abs] at hs
  nlinarith only [he, hs]

/-- Each actual root in the certified interval has the enlarged primitive enclosure. -/
theorem table_root_primitive_enclosure (i : Fin 10) {r : ℝ}
    (hr : r ∈ Icc (left (rows i) : ℝ) (right (rows i) : ℝ))
    (hz : witness (signedParameter (rows i)) r = 0) :
    (primitiveLower (rows i) : ℝ) - 13 / 40000 < primitive (signedParameter (rows i)) r ∧
      primitive (signedParameter (rows i)) r < (primitiveUpper (rows i) : ℝ) + 13 / 40000 := by
  have hm := (FixedDualTable.certified_table i).2
  have he := abs_le.mp (table_root_midpoint_error i hr hz)
  dsimp [FixedDualTable.midpointBounds] at hm
  constructor <;> linarith [hm.1, hm.2]

end
end StructuralNote.FixedDualStationaryValues

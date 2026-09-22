import StructuralNote.FixedDualIntervals

/-! Actual midpoint primitive enclosures for the first and sixth rows of Appendix A. -/

namespace StructuralNote.FixedDualIntervals

open Real FixedDualPrimitive
noncomputable section

/-- Sound multiplication of a positive and a negative real interval. -/
theorem positive_negative_mul_bounds {x y xl xu yl yu : ℝ}
    (hx : xl ≤ x ∧ x ≤ xu) (hy : yl ≤ y ∧ y ≤ yu) (hxl : 0 ≤ xl) (hyu : yu ≤ 0) :
    xu * yl ≤ x * y ∧ x * y ≤ xl * yu := by
  constructor
  · calc
      xu * yl ≤ x * yl := mul_le_mul_of_nonpos_right hx.2 (hy.1.trans (hy.2.trans hyu))
      _ ≤ x * y := mul_le_mul_of_nonneg_left hy.1 (hxl.trans hx.1)
  · calc
      x * y ≤ xl * y := mul_le_mul_of_nonpos_right hx.1 (hy.2.trans hyu)
      _ ≤ xl * yu := mul_le_mul_of_nonneg_left hy.2 hxl

theorem positive_mul_bounds {x y xl xu yl yu : ℝ}
    (hx : xl ≤ x ∧ x ≤ xu) (hy : yl ≤ y ∧ y ≤ yu) (hxl : 0 ≤ xl) (hyl : 0 ≤ yl) :
    xl * yl ≤ x * y ∧ x * y ≤ xu * yu :=
  ⟨mul_le_mul hx.1 hy.1 hyl (hxl.trans hx.1),
    mul_le_mul hx.2 hy.2 (hyl.trans hy.1) ((hxl.trans hx.1).trans hx.2)⟩

theorem short_trigonometric_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x - x ^ 3 / 6 ≤ sin x ∧ sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 100 ∧
      1 - x ^ 2 / 2 ≤ cos x ∧ cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 * (5 / 96) := by
  have hs := sin_bound (show |x| ≤ 1 by rwa [abs_of_nonneg hx0])
  have hc := cos_bound (show |x| ≤ 1 by rwa [abs_of_nonneg hx0])
  rw [abs_of_nonneg hx0] at hs hc
  exact ⟨sin_ge_sub_cube hx0, by linarith [(abs_le.mp hs).2],
    one_sub_sq_div_two_le_cos, by linarith [(abs_le.mp hc).2]⟩

theorem midpoint_trigonometric_intervals :
    ((649542291 : ℝ) / 10000000000 ≤ sin (13 / 200) ∧
      sin (13 / 200) ≤ 649542408 / 10000000000) ∧
    ((9978875000 : ℝ) / 10000000000 ≤ cos (13 / 200) ∧
      cos (13 / 200) ≤ 9978884298 / 10000000000) ∧
    ((1937641875 : ℝ) / 10000000000 ≤ sin (39 / 200) ∧
      sin (39 / 200) ≤ 1937670071 / 10000000000) ∧
    ((9809875000 : ℝ) / 10000000000 ≤ cos (39 / 200) ∧
      cos (39 / 200) ≤ 9810628074 / 10000000000) := by
  have h1 := short_trigonometric_bounds (x := (13 : ℝ) / 200) (by norm_num) (by norm_num)
  have h3 := short_trigonometric_bounds (x := (39 : ℝ) / 200) (by norm_num) (by norm_num)
  norm_num at h1 h3
  rcases h1 with ⟨hs1, hs2, hc1, hc2⟩
  rcases h3 with ⟨ht1, ht2, hd1, hd2⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

theorem midpoint_log_interval :
    (-20419 : ℝ) / 10000 < log (2 * sin (13 / 200)) ∧
      log (2 * sin (13 / 200)) < -51 / 25 := by
  have hs := midpoint_trigonometric_intervals.1
  have hspos : 0 < sin ((13 : ℝ) / 200) := by linarith [hs.1]
  have h := scaled_log_bounds (by positivity : 0 < 2 * sin ((13 : ℝ) / 200))
  have hinv : (8 * (2 * sin ((13 : ℝ) / 200)))⁻¹ ≤
      (10000000000 / (16 * 649542291) : ℝ) := by
    calc
      _ ≤ (16 * (649542291 / 10000000000 : ℝ))⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le
          (by norm_num : (0 : ℝ) < 16 * (649542291 / 10000000000))
          (by linarith [hs.1] : 16 * (649542291 / 10000000000) ≤ 8 * (2 * sin ((13 : ℝ) / 200)))
      _ = _ := by norm_num
  constructor <;> linarith [h.1, h.2, hs.2]

/-- The two actual primitive enclosures at the common midpoint 13/200. -/
theorem first_and_sixth_primitive_enclosures :
    (1336 : ℝ) / 1000 < primitive (1 / 2) (13 / 200) ∧
      primitive (1 / 2) (13 / 200) < 1337 / 1000 ∧
    (1172 : ℝ) / 1000 < primitive 1 (13 / 200) ∧
      primitive 1 (13 / 200) < 1173 / 1000 := by
  obtain ⟨hs, hc, ht, hd⟩ := midpoint_trigonometric_intervals
  have hlog := midpoint_log_interval
  have hsl := positive_negative_mul_bounds hs ⟨hlog.1.le, hlog.2.le⟩ (by norm_num) (by norm_num)
  have hv : (31415926 / 10000000 - (13 : ℝ) / 100) / 2 ≤ Real.pi / 2 - 13 / 200 ∧
      Real.pi / 2 - 13 / 200 ≤ (31415927 / 10000000 - (13 : ℝ) / 100) / 2 := by
    constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]
  have hvc := positive_mul_bounds hv hc (by norm_num) (by norm_num)
  rcases hs with ⟨hs1, hs2⟩
  rcases ht with ⟨ht1, ht2⟩
  rcases hd with ⟨hd1, hd2⟩
  rcases hsl with ⟨hsl1, hsl2⟩
  rcases hvc with ⟨hvc1, hvc2⟩
  norm_num [primitive]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

end
end StructuralNote.FixedDualIntervals

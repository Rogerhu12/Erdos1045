import StructuralNote.FixedDualClassificationTanStrip

/-! A second coefficient estimate obtained directly from two removable difference quotients. -/

namespace StructuralNote.ThirdSchwarzCoefficient

open Complex Set Metric Filter
open scoped Topology
noncomputable section

theorem denominator_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - star a * z ≠ 0 := by
  have hm : ‖star a * z‖ < 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_right (norm_nonneg a) hz).trans_lt ha
  intro h
  have he : star a * z = 1 := by linear_combination -h
  rw [he, norm_one] at hm
  exact (lt_irrefl 1) hm

theorem disk_fraction_bound {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖(z - a) / (1 - star a * z)‖ ≤ 1 := by
  have he : normSq (1 - star a * z) - normSq (z - a) =
      (1 - normSq a) * (1 - normSq z) := by
    simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, one_re, one_im,
      star_def, conj_re, conj_im]
    ring
  have hsq : ‖z - a‖ ^ 2 ≤ ‖1 - star a * z‖ ^ 2 := by
    rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
    have ha2 : normSq a ≤ 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
    have hz2 : normSq z ≤ 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hz2)]
  rw [norm_div]
  apply (div_le_one (norm_pos_iff.mpr (denominator_ne_zero ha hz))).mpr
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem second_coefficient_bound {h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h (ball 0 1))
    (hb : ∀ z ∈ ball 0 1, ‖h z‖ ≤ 1) (hfirst : deriv h 0 = 0) :
    ‖deriv (dslope h 0) 0‖ ≤ 1 - ‖h 0‖ ^ 2 := by
  have hz0 : (0 : ℂ) ∈ ball 0 1 := by simp
  have hn : ball (0 : ℂ) 1 ∈ 𝓝 0 := ball_mem_nhds _ (by norm_num)
  have hdh := hd.differentiableAt hn
  have hdq : DifferentiableOn ℂ (dslope h 0) (ball 0 1) :=
    (Complex.differentiableOn_dslope hn).mpr hd
  have hq0 : dslope h 0 0 = 0 := by rw [dslope_same, hfirst]
  rcases (hb 0 hz0).eq_or_lt with ha | ha
  · have hc : EqOn h (Function.const ℂ (h 0)) (ball 0 1) :=
      Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball _ _).isPreconnected
        isOpen_ball hd hz0 (fun z hz => by change ‖h z‖ ≤ ‖h 0‖; rw [ha]; exact hb z hz)
    have hq : dslope h 0 =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hn] with z hz
      by_cases he : z = 0
      · simpa only [he] using hq0
      · rw [dslope_of_ne _ he, slope_def_module, hc hz]
        simp
    rw [Filter.EventuallyEq.deriv_eq hq, deriv_const, norm_zero, ha]
    norm_num
  · let H : ℂ → ℂ := fun z => (h z - h 0) / (1 - star (h 0) * h z)
    have hden (z : ℂ) (hz : z ∈ ball 0 1) : 1 - star (h 0) * h z ≠ 0 :=
      denominator_ne_zero ha (hb z hz)
    have hH : DifferentiableOn ℂ H (ball 0 1) := by
      exact (hd.sub_const _).div ((differentiableOn_const (c := (1 : ℂ))).sub (hd.const_mul _)) hden
    have hH0 : H 0 = 0 := by simp [H]
    have hHfirst : deriv H 0 = 0 := by
      have hp := (hdh.hasDerivAt.sub_const (h 0)).div
        ((hasDerivAt_const 0 (1 : ℂ)).sub (hdh.hasDerivAt.const_mul (star (h 0))))
        (hden 0 hz0)
      simpa [H, hfirst, Pi.div_def, Pi.sub_def] using hp.deriv
    have hHmap : MapsTo H (ball 0 1) (closedBall (H 0) 1) := by
      intro z hz
      simpa only [mem_closedBall, hH0, dist_zero_right, H] using
        disk_fraction_bound ha (hb z hz)
    have hQ : DifferentiableOn ℂ (dslope H 0) (ball 0 1) :=
      (Complex.differentiableOn_dslope hn).mpr hH
    have hQ0 : dslope H 0 0 = 0 := by rw [dslope_same, hHfirst]
    have hQmap : MapsTo (dslope H 0) (ball 0 1) (closedBall (dslope H 0 0) 1) := by
      intro z hz
      have h := Complex.norm_dslope_le_div_of_mapsTo_ball hH hHmap hz
      simpa only [mem_closedBall, hQ0, dist_zero_right, div_one] using h
    have hbound := Complex.norm_deriv_le_one_of_mapsTo_ball hQ hQmap (by norm_num : (0 : ℝ) < 1)
    have heq : dslope H 0 =ᶠ[𝓝 0]
        fun z => dslope h 0 z / (1 - star (h 0) * h z) := by
      filter_upwards [hn] with z hz
      by_cases he : z = 0
      · simp only [he, hQ0, hq0, zero_div]
      · simp only [dslope_of_ne _ he, slope_def_module, sub_zero, smul_eq_mul, hH0,
          H]
        ring
    have hratio := ((hdq.differentiableAt hn).hasDerivAt).div
      ((hasDerivAt_const 0 (1 : ℂ)).sub (hdh.hasDerivAt.const_mul (star (h 0))))
      (hden 0 hz0)
    have hratio' : deriv (dslope H 0) 0 =
        deriv (dslope h 0) 0 / (1 - star (h 0) * h 0) := by
      have hr := hratio.deriv
      simp only [Pi.div_def, Pi.sub_def] at hr
      rw [heq.deriv_eq, hr, hq0]
      simp only [zero_mul, sub_zero]
      field_simp
    rw [hratio', norm_div] at hbound
    have hreal : 1 - star (h 0) * h 0 = ((1 - ‖h 0‖ ^ 2 : ℝ) : ℂ) := by
      rw [star_def, mul_comm, Complex.mul_conj]
      simp only [normSq_eq_norm_sq, ofReal_sub, ofReal_one]
    have hpos : 0 < 1 - ‖h 0‖ ^ 2 := by nlinarith [norm_nonneg (h 0)]
    rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at hbound
    exact (div_le_one hpos).mp hbound

end
end StructuralNote.ThirdSchwarzCoefficient

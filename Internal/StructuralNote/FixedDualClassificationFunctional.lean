import StructuralNote.FixedDualNormBounds

/-! The two fixed planes for actual bounded measurable profiles. The potential
is the integral against the explicit kernel, not an assumed Fourier identity. -/

namespace StructuralNote.FixedDualClassificationFunctional

open Real Set MeasureTheory FixedDualPrimitive FixedDualIntegral FixedDualNormBounds
open FixedDualRootGeometry FixedDualRootSigns
noncomputable section

def cosineMoment (f : ℝ → ℝ) : ℝ := (∫ u in (0 : ℝ)..Real.pi, f u * cos (3 * u)) / Real.pi
def sineMoment (f : ℝ → ℝ) : ℝ := (∫ u in (0 : ℝ)..Real.pi, f u * sin (3 * u)) / Real.pi
def kernelPotential (f : ℝ → ℝ) : ℝ := (2 / Real.pi) * (∫ u in (0 : ℝ)..Real.pi, f u * kernel u)

theorem fixed_half_integrable :
    IntervalIntegrable (fun u => |witness (1 / 2) u|) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (fun u => |witness (-(1 / 2)) u|) volume 0 (Real.pi / 2) := by
  obtain ⟨p0, p1, p2, p3, p4⟩ := half_positions
  obtain ⟨s0, s1, s2, s3, s4, s5, s6⟩ := half_signs
  have hp := two_root_integral (1 / 2)
    (by linarith [p0.1] : 0 < root 0) (by linarith [p0.2, p1.1] : root 0 < root 1)
    (by linarith [p1.2, pi_gt_three] : root 1 < Real.pi / 2)
    (fun u hu => (s0 u hu).le) (fun u hu => (s1 u hu).le) (fun u hu => (s2 u hu).le)
  have hn := three_root_integral (-(1 / 2))
    (by linarith [p2.1] : 0 < root 2) (by linarith [p2.2, p3.1] : root 2 < root 3)
    (by linarith [p3.2, p4.1] : root 3 < root 4)
    (by linarith [p4.2, pi_gt_three] : root 4 < Real.pi / 2)
    (fun u hu => (s3 u hu).le) (fun u hu => (s4 u hu).le)
    (fun u hu => (s5 u hu).le) (fun u hu => (s6 u hu).le)
  exact ⟨hp.1, hn.1⟩

theorem kernel_intervalIntegrable : IntervalIntegrable kernel volume 0 Real.pi := by
  have hr : IntervalIntegrable (fun u => |witness (1 / 2) u|) volume (Real.pi / 2) Real.pi := by
    have h := (fixed_half_integrable.2.comp_sub_left Real.pi).symm
    simpa only [sub_zero, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring,
      witness_reflection, neg_neg, abs_neg] using h
  have ha := fixed_half_integrable.1.trans hr
  have hm : Measurable (witness (1 / 2)) := by unfold witness kernel; fun_prop
  have hw : IntervalIntegrable (witness (1 / 2)) volume 0 Real.pi :=
    (IntervalIntegrable.intervalIntegrable_norm_iff hm.aestronglyMeasurable).mp ha
  have hc : IntervalIntegrable (fun u : ℝ => cos (3 * u)) volume 0 Real.pi :=
    (continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hs : IntervalIntegrable (fun u : ℝ => sin (3 * u)) volume 0 Real.pi :=
    (continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  convert ((hc.add (hs.const_mul (1 / 2))).sub hw).div_const 2 using 1
  funext u
  unfold witness
  ring

theorem witness_intervalIntegrable (b : ℝ) : IntervalIntegrable (witness b) volume 0 Real.pi := by
  have hc : IntervalIntegrable (fun u : ℝ => cos (3 * u)) volume 0 Real.pi :=
    (continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hs : IntervalIntegrable (fun u : ℝ => sin (3 * u)) volume 0 Real.pi :=
    (continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  exact (hc.add (hs.const_mul b)).sub (kernel_intervalIntegrable.const_mul 2)

theorem bounded_profile_product {f h : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ u ∈ Icc 0 Real.pi, |f u| ≤ Real.pi / 2)
    (hh : IntervalIntegrable h volume 0 Real.pi) :
    IntervalIntegrable (fun u => f u * h u) volume 0 Real.pi := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le pi_pos.le] at hh ⊢
  apply hh.bdd_mul hf.aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with u hu
  simpa only [Real.norm_eq_abs] using hbox u hu

theorem fixed_functional_identity (b : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ u ∈ Icc 0 Real.pi, |f u| ≤ Real.pi / 2) :
    cosineMoment f + b * sineMoment f - kernelPotential f =
      (∫ u in (0 : ℝ)..Real.pi, f u * witness b u) / Real.pi := by
  have hc := bounded_profile_product (h := fun u => cos (3 * u)) hf hbox
    ((continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 Real.pi)
  have hs := bounded_profile_product (h := fun u => sin (3 * u)) hf hbox
    ((continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 Real.pi)
  have hk := bounded_profile_product hf hbox kernel_intervalIntegrable
  have he : (fun u => f u * witness b u) =
      fun u => f u * cos (3 * u) + b * (f u * sin (3 * u)) - 2 * (f u * kernel u) := by
    funext u
    unfold witness
    ring
  rw [he, intervalIntegral.integral_sub (hc.add (hs.const_mul b)) (hk.const_mul 2),
    intervalIntegral.integral_add hc (hs.const_mul b), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  unfold cosineMoment sineMoment kernelPotential
  ring

theorem fixed_functional_bound (b : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ u ∈ Icc 0 Real.pi, |f u| ≤ Real.pi / 2) :
    |cosineMoment f + b * sineMoment f - kernelPotential f| ≤ dualNorm b := by
  rw [fixed_functional_identity b hf hbox, abs_div, abs_of_pos pi_pos]
  have hb : IntervalIntegrable (fun u => (Real.pi / 2) * |witness b u|) volume 0 Real.pi :=
    (witness_intervalIntegrable b).abs.const_mul _
  have h := intervalIntegral.norm_integral_le_of_norm_le pi_pos.le
    (Filter.Eventually.of_forall fun u hu => show ‖f u * witness b u‖ ≤ (Real.pi / 2) * |witness b u| from by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hbox u ⟨hu.1.le, hu.2⟩) (abs_nonneg _)) hb
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at h
  apply (div_le_iff₀ pi_pos).mpr
  unfold dualNorm
  nlinarith

theorem two_fixed_supporting_planes {f : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ u ∈ Icc 0 Real.pi, |f u| ≤ Real.pi / 2) :
    |cosineMoment f + (1 / 2) * sineMoment f - kernelPotential f| < 9 / 10 ∧
      |cosineMoment f + sineMoment f - kernelPotential f| < 97 / 80 := by
  constructor
  · exact (fixed_functional_bound (1 / 2) hf hbox).trans_lt half_dualNorm_bound.2
  · simpa only [one_mul] using (fixed_functional_bound 1 hf hbox).trans_lt one_dualNorm_bound.2

end
end StructuralNote.FixedDualClassificationFunctional

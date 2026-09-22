import StructuralNote.FixedDualClassificationFunctional
import StructuralNote.FixedDualClassificationTrig

/-! The six-arc supporting-plane test for actual measurable box profiles. -/

namespace StructuralNote.FixedDualClassificationArc

open Real Set FixedDualPrimitive FixedDualIntegral FixedDualClassificationFunctional
open FixedDualClassificationTrig
noncomputable section

theorem dualNorm_neg (b : ℝ) : dualNorm (-b) = dualNorm b := by
  have h := intervalIntegral.integral_comp_sub_left (fun u => |witness b u|)
    (a := (0 : ℝ)) (b := Real.pi) Real.pi
  simp only [sub_self, sub_zero, witness_reflection, abs_neg] at h
  exact congrArg (fun x : ℝ => x / 2) h

/-- An actual kernel-integral potential is positive throughout either side of a positive lobe. -/
theorem profile_positive_arc {f : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ u ∈ Icc 0 Real.pi, |f u| ≤ Real.pi / 2)
    {r x : ℝ} (hr : (24 : ℝ) / 25 ≤ r) (hx : x ∈ Icc 0 (Real.pi / 2 - 3 / 8))
    (hc : cosineMoment f = r * cos x) (hs : |sineMoment f| = r * sin x) :
    (1 : ℝ) / 50 < kernelPotential f := by
  apply fixed_plane_sign_margin hr hx
  · by_cases hs0 : 0 ≤ sineMoment f
    · have h := (le_abs_self _).trans (fixed_functional_bound (1 / 2) hf hbox)
      rw [hc] at h
      rw [abs_of_nonneg hs0] at hs
      rw [hs] at h
      nlinarith only [h]
    · have h := (le_abs_self _).trans (fixed_functional_bound (-(1 / 2)) hf hbox)
      rw [dualNorm_neg, hc] at h
      rw [abs_of_nonpos (le_of_not_ge hs0)] at hs
      nlinarith only [h, hs]
  · by_cases hs0 : 0 ≤ sineMoment f
    · have h := (le_abs_self _).trans (fixed_functional_bound 1 hf hbox)
      rw [hc] at h
      rw [abs_of_nonneg hs0] at hs
      rw [hs] at h
      nlinarith only [h]
    · have h := (le_abs_self _).trans (fixed_functional_bound (-1) hf hbox)
      rw [show (-1 : ℝ) = -(1 : ℝ) by rfl, dualNorm_neg, hc] at h
      rw [abs_of_nonpos (le_of_not_ge hs0)] at hs
      nlinarith only [h, hs]

theorem profile_moments_neg (f : ℝ → ℝ) :
    cosineMoment (-f) = -cosineMoment f ∧ sineMoment (-f) = -sineMoment f ∧
      kernelPotential (-f) = -kernelPotential f := by
  simp only [cosineMoment, sineMoment, kernelPotential, Pi.neg_apply, neg_mul,
    intervalIntegral.integral_neg, neg_div, mul_neg, and_self]

/-- The corresponding negative lobe; no extremality or two-valued assumption is used. -/
theorem profile_negative_arc {f : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ u ∈ Icc 0 Real.pi, |f u| ≤ Real.pi / 2)
    {r x : ℝ} (hr : (24 : ℝ) / 25 ≤ r) (hx : x ∈ Icc 0 (Real.pi / 2 - 3 / 8))
    (hc : -cosineMoment f = r * cos x) (hs : |sineMoment f| = r * sin x) :
    kernelPotential f < -(1 / 50 : ℝ) := by
  have hbox' : ∀ u ∈ Icc 0 Real.pi, |(-f) u| ≤ Real.pi / 2 := by
    simpa only [Pi.neg_apply, abs_neg] using hbox
  have h := profile_positive_arc hf.neg hbox' hr hx
    (by simpa only [(profile_moments_neg f).1] using hc)
    (by simpa only [(profile_moments_neg f).2.1, abs_neg] using hs)
  rw [(profile_moments_neg f).2.2] at h
  linarith

end
end StructuralNote.FixedDualClassificationArc

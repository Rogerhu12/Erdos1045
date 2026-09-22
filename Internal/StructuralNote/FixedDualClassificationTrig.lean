import StructuralNote.FixedDualNormBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Actual trigonometric inequalities used by the two fixed supporting planes. -/

namespace StructuralNote.FixedDualClassificationTrig

open Real Set FixedDualIntegral FixedDualNormBounds
noncomputable section

theorem sine_le_cosine_first_octant {x : ℝ} (hx : x ∈ Icc 0 (Real.pi / 4)) :
    sin x ≤ cos x := by
  have hc := cos_le_cos_of_nonneg_of_le_pi hx.1
    (by linarith [pi_pos] : Real.pi / 4 ≤ Real.pi) hx.2
  have hs := sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [pi_pos, hx.1] : -(Real.pi / 2) ≤ x)
    (by linarith [pi_pos] : Real.pi / 4 ≤ Real.pi / 2) hx.2
  rw [cos_pi_div_four] at hc
  rw [sin_pi_div_four] at hs
  exact hs.trans hc

theorem first_plane_trigonometric {x : ℝ} (hx : x ∈ Icc 0 (Real.pi / 4)) :
    1 ≤ cos x + (1 / 2) * sin x := by
  have hs : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2, pi_pos])
  have hc : 0 ≤ cos x := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos, hx.1], by linarith [hx.2, pi_pos]⟩
  have hcs := sine_le_cosine_first_octant hx
  have hprod := mul_nonneg hs (sub_nonneg.mpr hcs)
  nlinarith [sin_sq_add_cos_sq x]

theorem sine_add_cosine_monotone : MonotoneOn (fun x : ℝ => sin x + cos x) (Icc 0 (Real.pi / 4)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (continuous_sin.add continuous_cos).continuousOn
  · intro x _
    exact (differentiable_sin.add differentiable_cos).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [((hasDerivAt_sin x).add (hasDerivAt_cos x)).deriv]
    have h := sine_le_cosine_first_octant ⟨hx.1.le, hx.2.le⟩
    linarith

theorem second_plane_trigonometric {x : ℝ}
    (hx : x ∈ Icc (Real.pi / 4) (Real.pi / 2 - 3 / 8)) :
    (129 : ℝ) / 100 ≤ cos x + sin x := by
  have ht : (3 : ℝ) / 8 ∈ Icc 0 (Real.pi / 4) := ⟨by norm_num, by linarith [pi_gt_three]⟩
  have hy : Real.pi / 2 - x ∈ Icc 0 (Real.pi / 4) := by
    constructor <;> linarith [hx.1, hx.2]
  have h := sine_add_cosine_monotone ht hy (by linarith [hx.2])
  dsimp only at h
  rw [sin_pi_div_two_sub, cos_pi_div_two_sub] at h
  have hs := sin_ge_sub_cube (x := (3 : ℝ) / 8) (by norm_num)
  have hc := one_sub_sq_div_two_le_cos (x := (3 : ℝ) / 8)
  norm_num at hs hc
  linarith

/-- The scalar six-arc margin, once the two actual supporting inequalities are available. -/
theorem fixed_plane_sign_margin {r x g : ℝ} (hr : (24 : ℝ) / 25 ≤ r)
    (hx : x ∈ Icc 0 (Real.pi / 2 - 3 / 8))
    (hhalf : r * (cos x + (1 / 2) * sin x) - dualNorm (1 / 2) ≤ g)
    (hone : r * (cos x + sin x) - dualNorm 1 ≤ g) : (1 : ℝ) / 50 < g := by
  by_cases hx4 : x ≤ Real.pi / 4
  · have h := FixedDualArithmetic.first_plane_margin hr half_dualNorm_bound.2
      (first_plane_trigonometric ⟨hx.1, hx4⟩) hhalf
    linarith
  · exact (FixedDualArithmetic.second_plane_margin hr one_dualNorm_bound.2
      (second_plane_trigonometric ⟨(lt_of_not_ge hx4).le, hx.2⟩) hone).2

end
end StructuralNote.FixedDualClassificationTrig

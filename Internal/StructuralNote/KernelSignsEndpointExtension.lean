import StructuralNote.KernelSignsEndpoints

/-! A fixed extension of the positive kernel interval past Real.pi/12. -/

namespace StructuralNote.KernelSignsEndpointExtension

open Real Filter Set FixedDualPrimitive KernelSignsEndpoints
open scoped Topology

theorem exists_positive_point_above_twelfth :
    ∃ θ : ℝ, Real.pi / 12 < θ ∧ θ < Real.pi / 2 ∧ 0 < kernel θ := by
  have hs : sin (Real.pi / 12) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (by linarith [pi_pos]) (by linarith [pi_pos])).ne'
  have hnear : ∀ᶠ t in 𝓝 (Real.pi / 12), t < Real.pi / 2 ∧ 0 < kernel t := by
    filter_upwards [gt_mem_nhds (show Real.pi / 12 < Real.pi / 2 by linarith [pi_pos]),
      (kernel_hasDerivAt hs).continuousAt.eventually (lt_mem_nhds kernel_pi_div_twelve_pos)]
      with t ht hk
    exact ⟨ht, hk⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  have hd : dist (Real.pi / 12 + ε / 2) (Real.pi / 12) < ε := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith
  exact ⟨Real.pi / 12 + ε / 2, by linarith, hball hd⟩

end StructuralNote.KernelSignsEndpointExtension

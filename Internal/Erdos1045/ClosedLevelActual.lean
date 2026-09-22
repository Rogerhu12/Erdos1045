import Erdos1045.ClosedLevel
import ExteriorLevelInverse
import Mathlib.Analysis.Convex.Topology

/-! The level-curve estimate follows from the actual Laurent model and the
ordinary exterior bijection. No separate level-analysis assumptions remain. -/

namespace Erdos1045.ExteriorClassical
open Complex Metric Set ExteriorReduction
noncomputable section

/-- The canonical Laurent coefficients identify the given map with its model
throughout the open exterior. The offset includes the linear Taylor term. -/
theorem ExteriorData.map_eq_model {n : ℕ} {z : Configuration.Points n}
    (d : ExteriorData z) {w : ℂ} (hw : w ∈ exteriorDisk) :
    d.map w = (d.offset - deriv d.model 0) + w * d.model w⁻¹ := by
  have hh := model_laurent_expansion d.model_analytic (d.offset - deriv d.model 0) hw
  rw [d.model_zero, sub_add_cancel] at hh
  simpa only [ExteriorData.map, ExteriorData.coefficient, laurent] using hh.symm

/-- Every map in the exterior-data interface satisfies the concrete
Cauchy--Bernstein--Walsh estimate already proved for exterior bijections. -/
theorem remainingLevelAnalysis_proved : RemainingLevelAnalysis where
  cauchy_bernstein_walsh := by
    intro n z d HF r h hr hh hsep p hp
    have hKclosed : IsClosed (hull z) := (Set.finite_range z).isClosed_convexHull ℝ
    have hboundary (w : ℂ) (hw : ‖w‖ = 1) : d.map w ∈ hull z := by
      apply hKclosed.frontier_subset
      rw [← HF.boundary_image]
      exact ⟨w, hw, rfl⟩
    have hsurj : ∀ v ∈ frontier (hull z), ∃ u : ℂ, ‖u‖ = 1 ∧ d.map u = v := by
      intro v hv
      rw [← HF.boundary_image] at hv
      exact hv
    exact cauchy_bernstein_walsh_of_bijective p (d.offset - deriv d.model 0)
      ⟨d.map 1, hboundary 1 (by simp)⟩ hKclosed d.model_analytic d.model_zero_ne
      HF.map_continuous (fun w hw => (HF.map_derivative w hw).differentiableAt.differentiableWithinAt)
      HF.map_bijective (fun _ hw => d.map_eq_model hw) hboundary hsurj hr hh hsep hp

#print axioms remainingLevelAnalysis_proved
end
end Erdos1045.ExteriorClassical

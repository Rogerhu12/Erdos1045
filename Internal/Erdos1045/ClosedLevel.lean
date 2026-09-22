import Erdos1045.ExteriorSeparation
import Erdos1045.ClosedInterpolation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace Erdos1045.ExteriorClassical

noncomputable section

/-- Polynomial mean value on the actual convex hull is an ordinary mathlib theorem. -/
theorem polynomial_mean_value_proved (n : ℕ) (z : Configuration.Points n)
    (p : Polynomial ℂ) (B : ℝ)
    (hB : ∀ x ∈ hull z, ‖p.derivative.eval x‖ ≤ B) :
    ∀ x ∈ hull z, ∀ y ∈ hull z, ‖p.eval x - p.eval y‖ ≤ B * ‖x - y‖ := by
  intro x hx y hy
  exact (convex_convexHull ℝ (Set.range z)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w _ => (p.hasDerivAt w).hasDerivWithinAt) hB hy hx

/-- Compatibility interface, constructed unconditionally in ClosedLevelActual. -/
structure RemainingLevelAnalysis : Prop where
  cauchy_bernstein_walsh : ∀ n (z : Configuration.Points n) (d : ExteriorData z),
    FaberIdentities d → ∀ r h : ℝ, 1 < r → 0 < h →
    (∀ u v : ℂ, ‖u‖ = r → ‖v‖ = 1 → h ≤ ‖d.map u - d.map v‖) →
    ∀ p : Polynomial ℂ, (∀ x ∈ hull z, ‖p.eval x‖ ≤ 1) →
      ∀ x ∈ hull z, ‖p.derivative.eval x‖ ≤ 2 * r ^ p.natDegree / h

theorem RemainingLevelAnalysis.toClassical (H : RemainingLevelAnalysis) : ClassicalLevelAnalysis where
  interpolation := fekete_interpolation_proved
  cauchy_bernstein_walsh := H.cauchy_bernstein_walsh
  polynomial_mean_value := polynomial_mean_value_proved

end
end Erdos1045.ExteriorClassical

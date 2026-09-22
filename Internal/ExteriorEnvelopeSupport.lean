import ExteriorEnvelopeCurve
import Erdos1045.ClosedHullSupport

/-! Distance to a finite convex hull controls every directional projection.
This supplies the support bound for the ordinary exterior-circle arc length. -/

namespace ExteriorReduction.ExteriorEnvelope

open Complex Metric Set
open Erdos1045.Configuration Erdos1045.HullGeometry
open scoped Topology
noncomputable section

theorem projection_lt_support_add_of_infDist_lt {n : ℕ} (z : Points n)
    (hn : (convexHull ℝ (range z)).Nonempty) {p : ℂ} {ε : ℝ}
    (hp : infDist p (convexHull ℝ (range z)) < ε) (t : ℝ) :
    (p * Complex.exp (-((t : ℂ) * I))).re < support z t + ε := by
  obtain ⟨w, hw, hpw⟩ := (infDist_lt_iff hn).mp hp
  have hproj := projection_le_support_of_mem_convexHull z hw t
  have hnorm : ((p - w) * Complex.exp (-((t : ℂ) * I))).re ≤ ‖p - w‖ := by
    calc
      _ ≤ ‖(p - w) * Complex.exp (-((t : ℂ) * I))‖ := re_le_norm _
      _ = ‖p - w‖ := by simp [Complex.norm_exp]
  have heq : (p * Complex.exp (-((t : ℂ) * I))).re =
      ((p - w) * Complex.exp (-((t : ℂ) * I))).re +
        (w * Complex.exp (-((t : ℂ) * I))).re := by
    rw [← Complex.add_re]
    congr 1
    ring
  rw [dist_eq_norm] at hpw
  rw [heq]
  linarith

theorem projection_le_support_add_of_infDist_lt {n : ℕ} (z : Points n)
    (hn : (convexHull ℝ (range z)).Nonempty) {p : ℂ} {ε : ℝ}
    (hp : infDist p (convexHull ℝ (range z)) < ε) (t : ℝ) :
    (p * Complex.exp (-((t : ℂ) * I))).re ≤ support z t + ε :=
  (projection_lt_support_add_of_infDist_lt z hn hp t).le

theorem rotatingProjection_le_support_of_infDist_lt {n : ℕ} (z : Points n)
    (hn : (convexHull ℝ (range z)).Nonempty) {γ : ℝ → ℂ} {θ : ℝ → ℝ}
    {s : Set ℝ} {ε : ℝ}
    (hclose : ∀ t ∈ s, infDist (γ t) (convexHull ℝ (range z)) < ε) :
    ∀ t ∈ s, (rotatingProjection γ θ t).re ≤ support z (θ t) + ε := by
  intro t ht
  exact projection_le_support_add_of_infDist_lt z hn (hclose t ht) (θ t)

theorem curve_length_le_hullPerimeter_of_infDist_lt {n : ℕ} (z : Points n)
    (hn : (convexHull ℝ (range z)).Nonempty)
    {γ : ℝ → ℂ} {θ v a : ℝ → ℝ} {ε : ℝ}
    (hγ : ∀ t, HasDerivAt γ (I * (v t : ℂ) * Complex.exp ((θ t : ℂ) * I)) t)
    (hθ : ∀ t, HasDerivAt θ (a t) t)
    (hv : Continuous v) (ha : Continuous a)
    (hperiod : rotatingProjection γ θ (2 * Real.pi) = rotatingProjection γ θ 0)
    (hθperiod : θ (2 * Real.pi) = θ 0 + 2 * Real.pi)
    (ha0 : ∀ t ∈ Icc 0 (2 * Real.pi), 0 ≤ a t)
    (hclose : ∀ t ∈ Icc 0 (2 * Real.pi),
      infDist (γ t) (convexHull ℝ (range z)) < ε) :
    (∫ t in (0 : ℝ)..2 * Real.pi, v t) ≤ hullPerimeter z + 2 * Real.pi * ε := by
  exact curve_length_le_support_integral (by positivity) hγ hθ hv ha hperiod hθperiod
    (support_continuous z) (support_periodic z) ha0
    (rotatingProjection_le_support_of_infDist_lt z hn hclose)

#print axioms projection_lt_support_add_of_infDist_lt
#print axioms curve_length_le_hullPerimeter_of_infDist_lt

end
end ExteriorReduction.ExteriorEnvelope

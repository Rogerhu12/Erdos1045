import OrderedBoundaryAngles
import LaurentBoundaryExtension
import Erdos1045.LocalConfiguration
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Finite boundary polygons are controlled by the lengths of exterior circles.
Only continuity of the boundary extension is used at radius one. -/

namespace ExteriorReduction

open Complex Metric Set Filter MeasureTheory
open Erdos1045.ExteriorBoundary Erdos1045.CyclicAngles Erdos1045.Configuration
open scoped Topology BigOperators
noncomputable section

theorem unit_two_pi_periodic : Function.Periodic unit (2 * Real.pi) := by
  intro t
  unfold unit
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The polygonal displacement of a periodic differentiable curve is at most
the integral of any continuous periodic upper bound for its speed. -/
theorem ordered_polygon_le_integral {n : ℕ} (hn : 2 ≤ n) (a : Angles n)
    {γ : ℝ → ℂ} {B : ℝ → ℝ} (hγ : Differentiable ℝ γ)
    (hperiod : Function.Periodic γ (2 * Real.pi)) (hB : Continuous B)
    (hBperiod : Function.Periodic B (2 * Real.pi))
    (hbound : ∀ t, ‖deriv γ t‖ ≤ B t) :
    boundaryLength (fun i : Fin n => γ (a.angle i)) ≤ ∫ t in 0..2 * Real.pi, B t := by
  let z : ℕ → ℂ := fun i => γ (a.angle i)
  have hz : Function.Periodic z n := by
    intro i
    dsimp [z]
    rw [a.period, hperiod]
  rw [← Erdos1045.LocalConfiguration.perimeter_eq_boundaryLength hn z hz]
  change (∑ i ∈ Finset.range n, ‖γ (a.angle (i + 1 : ℕ)) - γ (a.angle i)‖) ≤ _
  calc
    _ ≤ ∑ i ∈ Finset.range n, ∫ t in a.angle i..a.angle (i + 1 : ℕ), B t := by
      apply Finset.sum_le_sum
      intro i _
      apply norm_sub_le_integral_of_norm_deriv_le_of_le
        (a.increasing.monotone (by exact_mod_cast Nat.le_succ i))
        hγ.continuous.continuousOn hγ.differentiableOn
      · exact .of_forall fun t _ => hbound t
      · exact hB.intervalIntegrable _ _
    _ = ∫ t in a.angle 0..a.angle n, B t := by
      exact intervalIntegral.sum_integral_adjacent_intervals
        (a := fun i : ℕ => a.angle i) (fun _ _ => hB.intervalIntegrable _ _)
    _ = ∫ t in 0..2 * Real.pi, B t := by
      rw [show a.angle n = a.angle 0 + 2 * Real.pi by simpa using a.period 0]
      simpa using hBperiod.intervalIntegral_add_eq (a.angle 0) 0

def exteriorCircleLength (F : ℂ → ℂ) (r : ℝ) : ℝ :=
  ∫ t in 0..2 * Real.pi, ‖deriv F ((r : ℂ) * unit t)‖ * r

theorem exterior_circle_mem {r : ℝ} (hr : 1 < r) (t : ℝ) :
    (r : ℂ) * unit t ∈ exteriorDisk := by
  simpa [exteriorDisk, norm_mul, norm_unit, abs_of_pos (lt_trans zero_lt_one hr)] using hr

theorem exterior_circle_hasDerivAt {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F exteriorDisk) {r : ℝ} (hr : 1 < r) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F ((r : ℂ) * unit s))
      (deriv F ((r : ℂ) * unit t) * ((r : ℂ) * unit t * Complex.I)) t := by
  have hinner := ((Complex.hasDerivAt_exp ((t : ℂ) * Complex.I)).comp (t : ℂ)
    ((hasDerivAt_id (t : ℂ)).mul_const Complex.I)).const_mul (r : ℂ)
  have hout := ((hF _ (exterior_circle_mem hr t)).differentiableAt
    (exteriorDisk_isOpen.mem_nhds (exterior_circle_mem hr t))).hasDerivAt.comp (t : ℂ) hinner
  simpa [unit, mul_assoc] using hout.comp_ofReal

theorem exterior_polygon_le_circleLength {n : ℕ} (hn : 2 ≤ n) (a : Angles n)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F exteriorDisk) {r : ℝ} (hr : 1 < r) :
    boundaryLength (fun i : Fin n => F ((r : ℂ) * unit (a.angle i))) ≤
      exteriorCircleLength F r := by
  have hinner : Continuous (fun t : ℝ => (r : ℂ) * unit t) := by
    unfold unit
    fun_prop
  have hcont : Continuous (fun t : ℝ => ‖deriv F ((r : ℂ) * unit t)‖ * r) := by
    apply Continuous.mul_const
    apply Continuous.norm
    exact ((hF.analyticOnNhd exteriorDisk_isOpen).deriv.continuousOn.comp_continuous
      hinner (fun t => exterior_circle_mem hr t))
  apply ordered_polygon_le_integral hn a
    (fun t => (exterior_circle_hasDerivAt hF hr t).differentiableAt)
    (fun t => by rw [unit_two_pi_periodic]) hcont
    (fun t => by rw [unit_two_pi_periodic])
  intro t
  rw [(exterior_circle_hasDerivAt hF hr t).deriv]
  simp [norm_unit, abs_of_pos (lt_trans zero_lt_one hr)]

theorem boundary_polygon_radial_tendsto {n : ℕ} (a : Angles n) {F : ℂ → ℂ}
    (hF : ContinuousOn F closedExteriorDisk) :
    Tendsto (fun k => boundaryLength (fun i : Fin n =>
      F ((radialApproach k : ℂ) * unit (a.angle i)))) atTop
      (𝓝 (boundaryLength (fun i : Fin n => F (unit (a.angle i))))) := by
  unfold boundaryLength
  apply tendsto_finsetSum
  intro i _
  exact ((boundary_radial_tendsto hF (norm_unit (a.angle (finRotate n i)))).sub
    (boundary_radial_tendsto hF (norm_unit (a.angle i)))).norm

/-- An upper limit for exterior circle lengths bounds every finite polygon on
the continuous boundary. No boundary derivative is involved. -/
theorem boundary_polygon_le_of_radial_length_upper {n : ℕ} (hn : 2 ≤ n)
    (a : Angles n) {F : ℂ → ℂ} {P : ℝ}
    (hF : DifferentiableOn ℂ F exteriorDisk)
    (hboundary : ContinuousOn F closedExteriorDisk)
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      exteriorCircleLength F (radialApproach k) ≤ P + ε) :
    boundaryLength (fun i : Fin n => F (unit (a.angle i))) ≤ P := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  apply le_of_tendsto (boundary_polygon_radial_tendsto a hboundary)
  filter_upwards [hupper ε hε] with k hk
  exact (exterior_polygon_le_circleLength hn a hF (radialApproach_gt_one k)).trans hk

theorem boundary_polygon_le_of_circle_length_upper {n : ℕ} (hn : 2 ≤ n)
    (a : Angles n) {F : ℂ → ℂ} {P : ℝ}
    (hF : DifferentiableOn ℂ F exteriorDisk)
    (hboundary : ContinuousOn F closedExteriorDisk)
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[>] 1,
      exteriorCircleLength F r ≤ P + ε) :
    boundaryLength (fun i : Fin n => F (unit (a.angle i))) ≤ P := by
  apply boundary_polygon_le_of_radial_length_upper hn a hF hboundary
  intro ε hε
  have hrad : Tendsto radialApproach atTop (𝓝[>] (1 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨radialApproach_tendsto,
      .of_forall fun k => radialApproach_gt_one k⟩
  exact hrad.eventually (hupper ε hε)

theorem boundary_polygon_le_of_circle_length_tendsto {n : ℕ} (hn : 2 ≤ n)
    (a : Angles n) {F : ℂ → ℂ} {P : ℝ}
    (hF : DifferentiableOn ℂ F exteriorDisk)
    (hboundary : ContinuousOn F closedExteriorDisk)
    (hlimit : Tendsto (exteriorCircleLength F) (𝓝[>] 1) (𝓝 P)) :
    boundaryLength (fun i : Fin n => F (unit (a.angle i))) ≤ P := by
  apply boundary_polygon_le_of_circle_length_upper hn a hF hboundary
  intro ε hε
  filter_upwards [hlimit.eventually (gt_mem_nhds (lt_add_of_pos_right P hε))] with r hr
  exact hr.le

#print axioms ordered_polygon_le_integral
#print axioms exterior_polygon_le_circleLength
#print axioms boundary_polygon_le_of_circle_length_upper

end
end ExteriorReduction

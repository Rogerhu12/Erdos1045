import StructuralNote.MatchingActivityActiveConstraintCrossingResponse
import StructuralNote.MatchingActivityRadialObjectiveFirst

/-! Full row rank of the matching and selected-crossing constraint
differentials in the genuine closed lens chart. -/

namespace StructuralNote.MatchingActivityActiveGradientIndependence

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonTangentialParameters
open MatchingActivityRadialClosure MatchingActivityRadialGeometry MatchingActivityRadialPair
open MatchingActivityRadialIntegration MatchingActivityRadialConstraints
open MatchingActivityRadialFeasible MatchingActivityRadialPath MatchingActivityRadialVelocity
open MatchingActivityRadialObjectiveFirst
open MatchingActivityCrossingVariationGraph MatchingActivityCrossingVariationDerivative
open MatchingActivityActiveConstraintDifferentials
open MatchingActivityActiveConstraintCrossingResponse
open scoped BigOperators Topology ContDiff

noncomputable section

/-- Independence is stated directly for the ambient differentials of the
actual squared-distance constraints. -/
def ActiveConstraintDifferentialsIndependent {m : ℕ} (hm : 0 < m)
    (s : Fin m → ℝ) (x : Points (2 * m)) : Prop :=
  ∀ cM cX : Fin m → ℝ,
    (∀ U : Points (2 * m),
      (∑ j, cM j * edgeDifferential x U (matchingFirst j) (matchingSecond hm j)) +
      (∑ j, cX j * edgeDifferential x U
        (selectedFirst hm s j) (selectedSecond hm s j)) = 0) →
    cM = 0 ∧ cX = 0

theorem matching_radial_response {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (a : ℂ)
    (g : (Fin m → ℝ) → ℂ) (i j : Fin m)
    (hchart : IsFeasibleRadialChart (by omega) θ s ν r a g)
    (hθ : HalfPeriodic (by omega) (fun k => (θ k : ℂ)))
    (hpos : ∀ k, 0 < (pair (halfAngle (by omega) θ k)
      (r k) (r (nextIndex (by omega) k))).re)
    (ht : ∀ k, ν k ^ 2 < 4) :
    edgeDifferential
        (outwardPath (by omega) θ s ν r a g i 0)
        (directVelocity (by omega) θ i + centerVelocity (by omega) θ s ν r g i)
        (matchingFirst j) (matchingSecond (by omega) j) =
      if j = i then 8 * r j else 0 := by
  have hv (k : Fin (2 * m)) := outwardPath_hasDerivAt (show 0 < m by omega)
    θ s ν r a g i hchart hpos ht k
  have hc := matchingConstraint_hasDerivAt (show 0 < m by omega) j hv
  have hnear : Tendsto (radiusPath r i) (nhds 0) (nhds r) := by
    have hp := (radiusPath_contDiff r i).contDiffAt (x := (0 : ℝ))
    simpa only [radiusPath_zero] using hp.continuousAt.tendsto
  have hz := hnear.eventually hchart.2.2.2.1
  have heq : (λ t => matchingConstraint (by omega)
      (outwardPath (by omega) θ s ν r a g i t) j) =ᶠ[nhds (0 : ℝ)]
      (λ t => ‖(2 * radiusPath r i t j : ℝ)‖ ^ 2) := by
    filter_upwards [hz] with t hzt
    unfold matchingConstraint edgeConstraint matchingFirst matchingSecond outwardPath
    rw [norm_sub_rev, matching_distance (show 0 < m by omega) θ s ν
      (radiusPath r i t) (g (radiusPath r i t)) a hθ hzt,
      radiusFull_halfIndex]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hr := radiusPath_hasDerivAt r i j
  have hsquare := (hr.const_mul 2).norm_sq
  have hsquare' := hsquare.congr_of_eventuallyEq heq
  have hu := hc.unique hsquare'
  change edgeDifferential (outwardPath (by omega) θ s ν r a g i 0)
      (fun k => directVelocity (by omega) θ i k +
        MatchingActivityRadialVelocity.centerVelocity (by omega) θ s ν r g i k)
      (matchingFirst j) (matchingSecond (by omega) j) = _
  rw [hu]
  simp only [radiusPath_zero, Real.inner_apply]
  unfold radiusVelocity
  split_ifs <;> ring

theorem activeConstraintDifferentialsIndependent_of_chart {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (a : ℂ)
    (g : (Fin m → ℝ) → ℂ)
    (hchart : IsFeasibleRadialChart (by omega) θ s ν r a g)
    (hθ : HalfPeriodic (by omega) (fun k => (θ k : ℂ)))
    (hsend : ∀ k, s k = 1 ∨ s k = -1)
    (hpos : ∀ k, 0 < (pair (halfAngle (by omega) θ k)
      (r k) (r (nextIndex (by omega) k))).re)
    (hsmall : ∀ k, |radialPhase (by omega) θ r k - midpoint m k| + |ν k| ≤ 1 / 4)
    (hwidth : ∀ k, 0 < Lens.width (radialLength (by omega) θ r k) (ν k))
    (hrpos : ∀ k, 0 < r k) :
    ActiveConstraintDifferentialsIndependent (by omega) s
      (radialConfiguration (by omega) θ s ν r 0 a) := by
  intro cM cX hrel
  have ht (k : Fin m) : ν k ^ 2 < 4 := by
    have hb : |ν k| ≤ 1 / 4 := by
      linarith [hsmall k, abs_nonneg (radialPhase (by omega) θ r k - midpoint m k)]
    nlinarith [(abs_le.mp hb).1, (abs_le.mp hb).2]
  have hzero : closureFamily (parameters (by omega) θ s ν r) 0 = 0 := by
    simpa only [hchart.2.1] using hchart.2.2.2.1.self_of_nhds
  have hcX (i : Fin m) : cX i = 0 := by
    obtain ⟨ξ, hξ0, hξ, hz⟩ := exists_smooth_sigma_root hm θ s ν r i
      hchart.1 hsmall hzero
    let U := centerVelocity (by omega) θ s ν r ξ i
    have hM (j : Fin m) : edgeDifferential
        (radialConfiguration (by omega) θ s ν r 0 a) U
        (matchingFirst j) (matchingSecond (by omega) j) = 0 := by
      have hresp := matching_crossing_response_zero hm θ s ν r a i j ξ
        hθ hsmall hξ0 hξ hz
      simpa only [crossingPath, sigmaPath_zero, hξ0] using hresp
    have hX (j : Fin m) : edgeDifferential
        (radialConfiguration (by omega) θ s ν r 0 a) U
        (selectedFirst (by omega) s j) (selectedSecond (by omega) s j) =
        if j = i then
          2 * s j * Lens.height (ν j) *
            Lens.width (radialLength (by omega) θ r j) (ν j)
        else 0 := by
      have hresp := selected_crossing_response hm θ s ν r a i j ξ hθ hsend hsmall
        hwidth hξ0 hξ hz
      simpa only [crossingPath, sigmaPath_zero, hξ0] using hresp
    have hsum := hrel U
    simp_rw [hM, mul_zero, Finset.sum_const_zero, zero_add, hX] at hsum
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
    have hdiag := selected_crossing_response_diagonal_ne_zero hm θ s ν r i
      (hsend i) (ht i) (hwidth i)
    exact (mul_eq_zero.mp hsum).resolve_right hdiag
  have hcM (i : Fin m) : cM i = 0 := by
    let U := directVelocity (by omega) θ i + centerVelocity (by omega) θ s ν r g i
    have hM (j : Fin m) : edgeDifferential
        (radialConfiguration (by omega) θ s ν r 0 a) U
        (matchingFirst j) (matchingSecond (by omega) j) =
        if j = i then 8 * r j else 0 := by
      have hresp := matching_radial_response hm θ s ν r a g i j hchart hθ hpos ht
      simpa only [outwardPath, radiusPath_zero, hchart.2.1] using hresp
    have hsum := hrel U
    simp_rw [hM, hcX, zero_mul, Finset.sum_const_zero, add_zero] at hsum
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
    have hdiag : 8 * r i ≠ 0 := mul_ne_zero (by norm_num) (ne_of_gt (hrpos i))
    exact (mul_eq_zero.mp hsum).resolve_right hdiag
  constructor
  · funext i
    simpa only [Pi.zero_apply] using hcM i
  · funext i
    simpa only [Pi.zero_apply] using hcX i

end
end StructuralNote.MatchingActivityActiveGradientIndependence



import StructuralNote.MatchingActivityKKTActual
import StructuralNote.MatchingActivityActiveConstraintCrossingResponse
import StructuralNote.MatchingActivityRadialObjectiveFirst

/-! The genuine radial closure graph is tangent to every selected active
crossing constraint. -/

namespace StructuralNote.MatchingActivityKKTRadialResponse

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonTangentialParameters
open MatchingActivityRadialPair MatchingActivityRadialClosure MatchingActivityRadialGeometry
open MatchingActivityRadialIntegration MatchingActivityRadialConstraints
open MatchingActivityRadialFeasible MatchingActivityRadialPath MatchingActivityRadialVelocity
open MatchingActivityRadialObjectiveFirst
open MatchingActivityActiveConstraintDifferentials
open MatchingActivityActiveConstraintLensDerivative
open LensClosurePathDerivatives
open scoped BigOperators Topology ContDiff

noncomputable section

theorem selectedLensValue_endpoint {e L h : ℝ}
    (he : e = 1 ∨ e = -1) (hh : h ^ 2 ≤ 4) :
    selectedLensValue e L e h = 4 := by
  have hheight := Lens.height_sq hh
  rcases he with rfl | rfl
  · calc
      selectedLensValue 1 L 1 h = (L + Lens.width L h) ^ 2 + h ^ 2 := by
        simpa only [selectedLensValue, LensClosure.increment, Complex.ofReal_one, one_mul,
          mul_one, unit, Complex.ofReal_zero, zero_mul, Complex.exp_zero] using
            Lens.norm_sq_rotated_plus (norm_unit (0 : ℝ)) L (Lens.width L h) h
      _ = 4 := by simpa only [Lens.add_width] using hheight
  · calc
      selectedLensValue (-1) L (-1) h =
          (L - -Lens.width L h) ^ 2 + h ^ 2 := by
        simpa only [selectedLensValue, LensClosure.increment, Complex.ofReal_neg,
          Complex.ofReal_one, neg_mul, one_mul, mul_one, unit, Complex.ofReal_zero,
          zero_mul, Complex.exp_zero, sub_eq_add_neg] using
            Lens.norm_sq_rotated_minus (norm_unit (0 : ℝ)) L (-Lens.width L h) h
      _ = 4 := by simpa only [sub_neg_eq_add, Lens.add_width] using hheight

theorem selectedConstraint_radialConfiguration {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (a ξ : ℂ)
    (j : Fin m)
    (hθ : HalfPeriodic (by omega) (fun k => (θ k : ℂ)))
    (hz : closureFamily (parameters (by omega) θ s ν r) ξ = 0)
    (hs : s j = 1 ∨ s j = -1) :
    selectedConstraint (by omega) s
        (radialConfiguration (by omega) θ s ν r ξ a) j =
      selectedLensValue (s j) (radialLength (by omega) θ r j)
        (s j) (heightParameter ν ξ j) := by
  have hd : difference (by omega) (radialCenter (by omega) θ s ν r ξ)
      (CommonClosureEnergy.halfIndex j) = radialIncrement (by omega) θ s ν r ξ j := by
    rw [radialCenter_difference (by omega) θ s ν r ξ hz]
    exact repeatHalf_halfIndex (by omega) _ j
  have hc := radialCenter_halfPeriodic (by omega) θ s ν r ξ hz
  change ∀ k, radialCenter (by omega) θ s ν r ξ (halfTurn (by omega) k) =
    radialCenter (by omega) θ s ν r ξ k at hc
  rcases hs with hp | hn
  · have he : radialConfiguration (by omega) θ s ν r ξ a
          (successor (by omega) (CommonClosureEnergy.halfIndex j)) -
        radialConfiguration (by omega) θ s ν r ξ a
          (halfTurn (by omega) (CommonClosureEnergy.halfIndex j)) =
        (radialLength (by omega) θ r j : ℂ) *
            unit (radialPhase (by omega) θ r j) +
          radialIncrement (by omega) θ s ν r ξ j := by
      rw [← weighted_diameter_sum (by omega) θ r j, ← hd]
      simp only [radialConfiguration, vertices, radiusFull_halfTurn,
        diameterVector_halfTurn (by omega) θ hθ, hc, difference]
      ring
    simp only [selectedConstraint, selectedFirst, selectedSecond, hp, if_true,
      edgeConstraint]
    rw [he]
    unfold selectedLensValue radialIncrement LensClosure.increment
    simp only [Complex.ofReal_one, one_mul]
    have hrot :
        (radialLength (by omega) θ r j : ℂ) * unit (radialPhase (by omega) θ r j) +
            unit (radialPhase (by omega) θ r j) *
              (((s j * Lens.width (radialLength (by omega) θ r j)
                (heightParameter ν ξ j) : ℝ) : ℂ) +
                (heightParameter ν ξ j : ℂ) * I) =
          unit (radialPhase (by omega) θ r j) *
            ((radialLength (by omega) θ r j : ℂ) +
              (((s j * Lens.width (radialLength (by omega) θ r j)
                (heightParameter ν ξ j) : ℝ) : ℂ) +
                (heightParameter ν ξ j : ℂ) * I)) := by ring
    rw [hrot, norm_mul, norm_unit, one_mul]
    simp only [unit, ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    rw [hp]
    norm_num
  · have he : radialConfiguration (by omega) θ s ν r ξ a
          (CommonClosureEnergy.halfIndex j) -
        radialConfiguration (by omega) θ s ν r ξ a
          (halfTurn (by omega)
            (successor (by omega) (CommonClosureEnergy.halfIndex j))) =
        (radialLength (by omega) θ r j : ℂ) *
            unit (radialPhase (by omega) θ r j) -
          radialIncrement (by omega) θ s ν r ξ j := by
      rw [← weighted_diameter_sum (by omega) θ r j, ← hd]
      simp only [radialConfiguration, vertices, radiusFull_halfTurn,
        diameterVector_halfTurn (by omega) θ hθ, hc, difference]
      ring
    simp only [selectedConstraint, selectedFirst, selectedSecond, hn,
      show (-1 : ℝ) ≠ 1 by norm_num, if_false, edgeConstraint]
    rw [he]
    unfold selectedLensValue radialIncrement LensClosure.increment
    simp only [Complex.ofReal_neg, Complex.ofReal_one]
    have hrot :
        (radialLength (by omega) θ r j : ℂ) * unit (radialPhase (by omega) θ r j) -
            unit (radialPhase (by omega) θ r j) *
              (((s j * Lens.width (radialLength (by omega) θ r j)
                (heightParameter ν ξ j) : ℝ) : ℂ) +
                (heightParameter ν ξ j : ℂ) * I) =
          unit (radialPhase (by omega) θ r j) *
            ((radialLength (by omega) θ r j : ℂ) -
              (((s j * Lens.width (radialLength (by omega) θ r j)
                (heightParameter ν ξ j) : ℝ) : ℂ) +
                (heightParameter ν ξ j : ℂ) * I)) := by ring
    rw [hrot, norm_mul, norm_unit, one_mul]
    simp only [unit, ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    rw [hn]
    congr 2
    ring

/-- Varying one matching radius along the genuine implicit closure graph has
zero first response on every selected endpoint crossing. -/
theorem selected_radial_response_zero {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (a : ℂ)
    (g : (Fin m → ℝ) → ℂ) (i j : Fin m)
    (hchart : IsFeasibleRadialChart (by omega) θ s ν r a g)
    (hθ : HalfPeriodic (by omega) (fun k => (θ k : ℂ)))
    (hs : ∀ k, s k = 1 ∨ s k = -1)
    (hpos : ∀ k, 0 < (pair (halfAngle (by omega) θ k)
      (r k) (r (nextIndex (by omega) k))).re)
    (ht : ∀ k, ν k ^ 2 < 4) :
    edgeDifferential
        (outwardPath (by omega) θ s ν r a g i 0)
        (directVelocity (by omega) θ i + centerVelocity (by omega) θ s ν r g i)
        (selectedFirst (by omega) s j) (selectedSecond (by omega) s j) = 0 := by
  have hv (k : Fin (2 * m)) := outwardPath_hasDerivAt (show 0 < m by omega)
    θ s ν r a g i hchart hpos ht k
  have hc := selectedConstraint_hasDerivAt (show 0 < m by omega) s j hv
  have hnear : Tendsto (radiusPath r i) (nhds 0) (nhds r) := by
    have hp := (radiusPath_contDiff r i).contDiffAt (x := (0 : ℝ))
    simpa only [radiusPath_zero] using hp.continuousAt.tendsto
  have hz := hnear.eventually hchart.2.2.2.1
  have hg := closureSpeed_hasDerivAt r g i hchart.2.2.1
  have hh := heightParameter_hasDerivAt
    (ν := fun _ : ℝ => ν) (ξ := fun t => g (radiusPath r i t))
    (ν' := fun _ => 0) (fun k => hasDerivAt_const 0 (ν k)) hg j
  have hheight : ∀ᶠ t in nhds (0 : ℝ),
      heightParameter ν (g (radiusPath r i t)) j ^ 2 < 4 := by
    have h0 : heightParameter ν (g (radiusPath r i 0)) j ^ 2 < 4 := by
      simpa only [radiusPath_zero, hchart.2.1, heightParameter, map_zero, add_zero]
        using ht j
    exact (hh.continuousAt.pow 2).tendsto.eventually (eventually_lt_nhds h0)
  have heq : (fun t => selectedConstraint (by omega) s
      (outwardPath (by omega) θ s ν r a g i t) j) =ᶠ[nhds (0 : ℝ)]
      (fun _ : ℝ => 4) := by
    filter_upwards [hz, hheight] with t hzt htt
    rw [show selectedConstraint (by omega) s
        (outwardPath (by omega) θ s ν r a g i t) j =
      selectedLensValue (s j)
        (radialLength (by omega) θ (radiusPath r i t) j) (s j)
        (heightParameter ν (g (radiusPath r i t)) j) by
      exact selectedConstraint_radialConfiguration hm θ s ν (radiusPath r i t) a
        (g (radiusPath r i t)) j hθ hzt (hs j)]
    exact selectedLensValue_endpoint (hs j) htt.le
  have hzero : HasDerivAt (fun _ : ℝ => (4 : ℝ)) 0 0 := hasDerivAt_const 0 (4 : ℝ)
  exact hc.unique (hzero.congr_of_eventuallyEq heq)

end
end StructuralNote.MatchingActivityKKTRadialResponse

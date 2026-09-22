import StructuralNote.MatchingActivityActiveConstraintLensDerivative
import StructuralNote.MatchingActivityCrossingEndpointActual

/-! The active crossing constraints have a diagonal, nonzero response to the
one-site lens-control paths. -/

namespace StructuralNote.MatchingActivityActiveConstraintCrossingResponse

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonTangentialParameters BoxLensLift
open MatchingActivityRadialClosure MatchingActivityRadialGeometry
open MatchingActivityRadialIntegration MatchingActivityRadialConstraints
open MatchingActivityCrossingVariationGraph MatchingActivityCrossingVariationDerivative
open MatchingActivityActiveConstraintDifferentials
open MatchingActivityActiveConstraintLensDerivative
open LensIncrementDerivatives LensClosurePathDerivatives
open scoped BigOperators Topology ContDiff

noncomputable section

theorem selectedConstraint_crossingPath {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (a : ℂ)
    (i j : Fin m) (ξ : ℝ → ℂ) (t : ℝ)
    (hθ : HalfPeriodic (by omega) (fun k => (θ k : ℂ)))
    (hz : closureFamily (parameters (by omega) θ (sigmaPath s i t) ν r) (ξ t) = 0)
    (hs : ∀ k, s k = 1 ∨ s k = -1) :
    selectedConstraint (by omega) s
        (crossingPath (by omega) θ s ν r a ξ i t) j =
      selectedLensValue (s j) (radialLength (by omega) θ r j)
        (sigmaPath s i t j) (heightParameter ν (ξ t) j) := by
  have hd : difference (by omega)
      (radialCenter (by omega) θ (sigmaPath s i t) ν r (ξ t))
        (CommonClosureEnergy.halfIndex j) =
      radialIncrement (by omega) θ (sigmaPath s i t) ν r (ξ t) j := by
    rw [radialCenter_difference (by omega) θ (sigmaPath s i t) ν r (ξ t) hz]
    exact repeatHalf_halfIndex (by omega) _ j
  have hc := radialCenter_halfPeriodic (by omega) θ (sigmaPath s i t) ν r (ξ t) hz
  change ∀ k, radialCenter (by omega) θ (sigmaPath s i t) ν r (ξ t)
      (halfTurn (by omega) k) =
    radialCenter (by omega) θ (sigmaPath s i t) ν r (ξ t) k at hc
  rcases hs j with hp | hn
  · have he : crossingPath (by omega) θ s ν r a ξ i t
          (successor (by omega) (CommonClosureEnergy.halfIndex j)) -
        crossingPath (by omega) θ s ν r a ξ i t
          (halfTurn (by omega) (CommonClosureEnergy.halfIndex j)) =
        (radialLength (by omega) θ r j : ℂ) * unit (radialPhase (by omega) θ r j) +
          radialIncrement (by omega) θ (sigmaPath s i t) ν r (ξ t) j := by
      rw [← weighted_diameter_sum (by omega) θ r j, ← hd]
      simp only [crossingPath, radialConfiguration, vertices, radiusFull_halfTurn,
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
              (((sigmaPath s i t j * Lens.width (radialLength (by omega) θ r j)
                (heightParameter ν (ξ t) j) : ℝ) : ℂ) +
                (heightParameter ν (ξ t) j : ℂ) * I) =
          unit (radialPhase (by omega) θ r j) *
            ((radialLength (by omega) θ r j : ℂ) +
              (((sigmaPath s i t j * Lens.width (radialLength (by omega) θ r j)
                (heightParameter ν (ξ t) j) : ℝ) : ℂ) +
                (heightParameter ν (ξ t) j : ℂ) * I)) := by ring
    rw [hrot, norm_mul, norm_unit, one_mul]
    simp only [unit, ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  · have he : crossingPath (by omega) θ s ν r a ξ i t
          (CommonClosureEnergy.halfIndex j) -
        crossingPath (by omega) θ s ν r a ξ i t
          (halfTurn (by omega)
            (successor (by omega) (CommonClosureEnergy.halfIndex j))) =
        (radialLength (by omega) θ r j : ℂ) * unit (radialPhase (by omega) θ r j) -
          radialIncrement (by omega) θ (sigmaPath s i t) ν r (ξ t) j := by
      rw [← weighted_diameter_sum (by omega) θ r j, ← hd]
      simp only [crossingPath, radialConfiguration, vertices, radiusFull_halfTurn,
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
              (((sigmaPath s i t j * Lens.width (radialLength (by omega) θ r j)
                (heightParameter ν (ξ t) j) : ℝ) : ℂ) +
                (heightParameter ν (ξ t) j : ℂ) * I) =
          unit (radialPhase (by omega) θ r j) *
            ((radialLength (by omega) θ r j : ℂ) -
              (((sigmaPath s i t j * Lens.width (radialLength (by omega) θ r j)
                (heightParameter ν (ξ t) j) : ℝ) : ℂ) +
                (heightParameter ν (ξ t) j : ℂ) * I)) := by ring
    rw [hrot, norm_mul, norm_unit, one_mul]
    simp only [unit, ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    congr 2
    ring

theorem selected_crossing_response {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (a : ℂ)
    (i j : Fin m) (ξ : ℝ → ℂ)
    (hθ : HalfPeriodic (by omega) (fun k => (θ k : ℂ)))
    (hs : ∀ k, s k = 1 ∨ s k = -1)
    (hsmall : ∀ k, |radialPhase (by omega) θ r k - midpoint m k| + |ν k| ≤ 1 / 4)
    (_hwidth : ∀ k, 0 < Lens.width (radialLength (by omega) θ r k) (ν k))
    (hξ0 : ξ 0 = 0) (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hz : ∀ᶠ t in nhds (0 : ℝ),
      closureFamily (parameters (by omega) θ (sigmaPath s i t) ν r) (ξ t) = 0) :
    edgeDifferential
        (crossingPath (by omega) θ s ν r a ξ i 0)
        (centerVelocity (by omega) θ s ν r ξ i)
        (selectedFirst (by omega) s j) (selectedSecond (by omega) s j) =
      if j = i then
        2 * s j * Lens.height (ν j) *
          Lens.width (radialLength (by omega) θ r j) (ν j)
      else 0 := by
  have hv (k : Fin (2 * m)) := crossingPath_hasDerivAt hm θ s ν r a i ξ
    hsmall hξ0 hξ hz k
  have hc := selectedConstraint_hasDerivAt (show 0 < m by omega) s j hv
  have hh := heightParameter_hasDerivAt
    (ν := fun _ : ℝ => ν) (ξ := ξ) (ν' := fun _ => 0)
    (fun k => hasDerivAt_const 0 (ν k)) (crossingRootSpeed_hasDerivAt hξ) j
  have hsigma := sigmaPath_hasDerivAt s i j
  have hνsmall : (ν j) ^ 2 < 4 := by
    have hb : |ν j| ≤ 1 / 4 := by
      linarith [hsmall j, abs_nonneg (radialPhase (by omega) θ r j - midpoint m j)]
    nlinarith [(abs_le.mp hb).1, (abs_le.mp hb).2]
  have hlens := selectedLensValue_hasDerivAt
    (L := radialLength (by omega) θ r j) hsigma hh (hs j)
    (by simp [sigmaPath_zero]) (by
      simpa only [hξ0, heightParameter, map_zero, add_zero] using hνsmall)
  have heq : (λ t => selectedConstraint (by omega) s
      (crossingPath (by omega) θ s ν r a ξ i t) j) =ᶠ[nhds (0 : ℝ)]
      (λ t => selectedLensValue (s j) (radialLength (by omega) θ r j)
        (sigmaPath s i t j) (heightParameter ν (ξ t) j)) := by
    filter_upwards [hz] with t ht
    exact selectedConstraint_crossingPath hm θ s ν r a i j ξ t hθ ht hs
  have hlens' := hlens.congr_of_eventuallyEq heq
  have hu := hc.unique hlens'
  simp only [hξ0, heightParameter, map_zero, add_zero] at hu
  rw [hu]
  unfold sigmaVelocity
  split_ifs <;> ring

theorem selected_crossing_response_diagonal_ne_zero {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (i : Fin m)
    (hs : s i = 1 ∨ s i = -1)
    (hsmall : (ν i) ^ 2 < 4)
    (hwidth : 0 < Lens.width (radialLength (by omega) θ r i) (ν i)) :
    2 * s i * Lens.height (ν i) *
      Lens.width (radialLength (by omega) θ r i) (ν i) ≠ 0 := by
  exact selectedLensValue_derivative_ne_zero hs hsmall hwidth

/-- Changing a lens-control coordinate leaves every matching squared length
fixed, including after the implicit closure correction. -/
theorem matching_crossing_response_zero {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (a : ℂ)
    (i j : Fin m) (ξ : ℝ → ℂ)
    (hθ : HalfPeriodic (by omega) (fun k => (θ k : ℂ)))
    (hsmall : ∀ k, |radialPhase (by omega) θ r k - midpoint m k| + |ν k| ≤ 1 / 4)
    (hξ0 : ξ 0 = 0) (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hz : ∀ᶠ t in nhds (0 : ℝ),
      closureFamily (parameters (by omega) θ (sigmaPath s i t) ν r) (ξ t) = 0) :
    edgeDifferential
        (crossingPath (by omega) θ s ν r a ξ i 0)
        (centerVelocity (by omega) θ s ν r ξ i)
        (matchingFirst j) (matchingSecond (by omega) j) = 0 := by
  have hv (k : Fin (2 * m)) := crossingPath_hasDerivAt hm θ s ν r a i ξ
    hsmall hξ0 hξ hz k
  have hc := matchingConstraint_hasDerivAt (show 0 < m by omega) j hv
  have heq : (λ t => matchingConstraint (by omega)
      (crossingPath (by omega) θ s ν r a ξ i t) j) =ᶠ[nhds (0 : ℝ)]
      (λ _ : ℝ => (2 * |r j|) ^ 2) := by
    filter_upwards [hz] with t ht
    unfold matchingConstraint edgeConstraint matchingFirst matchingSecond crossingPath
    rw [norm_sub_rev, matching_distance (show 0 < m by omega) θ (sigmaPath s i t)
      ν r (ξ t) a hθ ht, radiusFull_halfIndex]
  have hzero : HasDerivAt (λ _ : ℝ => (2 * |r j|) ^ 2) 0 0 :=
    hasDerivAt_const 0 _
  have hzero' := hzero.congr_of_eventuallyEq heq
  exact hc.unique hzero'

end
end StructuralNote.MatchingActivityActiveConstraintCrossingResponse

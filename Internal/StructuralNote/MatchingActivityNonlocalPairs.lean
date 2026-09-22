import StructuralNote.MatchingActivityNonlocalSlack
import StructuralNote.StrongPointwiseSmallness

/-! Actual distant pairs are strict before any matching radius is saturated. -/

namespace StructuralNote.MatchingActivityNonlocalPairs

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonFiberGeometry CommonFiberNonlocalFrames CommonFiberNonlocalAngles CommonFiberNonlocalProjection
open MatchingActivityNonlocalSlack StrongPointwiseCoordinates StrongPointwiseSmallness
open ActualCrossingGeometry NormalizedPolarRepresentation ExtremalPolarCenter SignedPressureRemainder
open SinglePressureEstimate StrongBudgetConsequences StrongObjectiveEstimate
noncomputable section

theorem normalizedPoint_decomposition (m : ℕ) (β : ℂ) (u : ℕ → ℂ) (j : Fin (2 * m)) :
    normalizedPoint m β u j = (PolarRepresentation.radius m ‖β‖ u j : ℂ) *
      diameterVector (normalizedAngle m u) j + actualCenter m β u j := by
  simp only [normalizedPoint, diameterVector, character, Nat.mul_one, actualCenter,
    SignedPressureAngular.root]
  change GapRigidity.circle _ * ((_ : ℂ) * _ + _) = (_ : ℂ) * (_ * GapRigidity.circle _) + _
  ring

theorem actualCenter_halfPeriodic {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) : HalfPeriodic hm (actualCenter m β u) := by
  have hc := PolarCenterNormalization.correctedCenter_halfPeriodic hm (ExtremalPolarCenter.angles m u)
    (ExtremalPolarCenter.physicalCenter m β u) (ExtremalPolarCenter.angles_halfPeriodic hm u hu)
    (ExtremalPolarCenter.physicalCenter_halfPeriodic hm β u hu)
  change HalfPeriodic hm (polarCenter m β u) at hc
  intro j
  simp only [actualCenter, normalizedAngle_halfPeriodic hm u hu, hc j]

theorem model_forward_strict {m k : ℕ} (hm : 8 ≤ m) (hk : 2 ≤ k) (hkm : k ≤ m)
    {z : Points (2 * m)} {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z)
    (hbounds : PointwiseBounds (m := m) (by omega) β u)
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2)
    (hsmallB : 4 * budgetConstant / (2 * m : ℝ) ≤ 1 / 1000000)
    (hsmallC : StrongPointwiseSteps.physicalStepConstant / (2 * m : ℝ) ≤ 1 / 1000)
    (hsmallR : StrongPointwiseRadial.radialErrorConstant / (2 * m : ℝ) ≤ 10 - Real.pi ^ 2)
    (hsmallb : 2 * budgetConstant / (2 * m : ℝ) ≤ 1 / 10) (j : Fin (2 * m)) :
    ‖normalizedPoint m β u (cyclicAdvance j (m + k)) - normalizedPoint m β u j‖ < 2 := by
  obtain ⟨hθ, hstep, hrad⟩ := model_nonlocal_smallness hm h hz hbounds hbudget hsmallB hsmallC hsmallR
  let θ := normalizedAngle m u
  let c := actualCenter m β u
  let l := cyclicAdvance j k
  have hstep' (i : Fin (2 * m)) : ‖difference (by omega) (fun i => -c i) i‖ ≤ 1 / (1000 * (2 * m : ℝ)) := by
    simpa only [difference, neg_sub_neg, norm_sub_rev] using hstep i
  have hrad' (i : Fin (2 * m)) : |radial (meanFrame (by omega) θ i)
      (difference (by omega) (fun i => -c i) i)| ≤ 10 / (2 * m : ℝ) ^ 2 := by
    have he : difference (by omega) (fun i => -c i) i = -difference (by omega) c i := by unfold difference; ring
    simpa only [he, radial, mul_neg, Complex.neg_re, abs_neg] using hrad i
  have hs := chain_pair_squared_slack (by omega : 16 ≤ 2 * m) hk (by omega) θ (fun i => -c i)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hθ)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hstep')
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hrad') j.val
  have hs' : ‖diameterVector θ j + diameterVector θ l + (c j - c l)‖ ^ 2 ≤
      4 - (k : ℝ) ^ 2 / (2 * m : ℝ) ^ 2 := by
    simpa only [periodize_fin, periodize, Nat.mod_eq_of_lt j.isLt, neg_sub_neg,
      Nat.cast_mul, Nat.cast_ofNat, l, cyclicAdvance] using hs
  let e := -(radialDeficit m β u j : ℂ) * diameterVector θ j -
    (radialDeficit m β u l : ℂ) * diameterVector θ l
  have he : ‖e‖ ≤ 1 / (10 * (2 * m : ℝ) ^ 2) := by
    have hb := hbounds.2.2.1
    have hn0 : (0 : ℝ) < 2 * m := by positivity
    have herr := div_le_div_of_nonneg_right hsmallb (sq_nonneg (2 * m : ℝ))
    calc
      _ ≤ ‖-(radialDeficit m β u j : ℂ) * diameterVector θ j‖ +
          ‖(radialDeficit m β u l : ℂ) * diameterVector θ l‖ := norm_sub_le _ _
      _ = radialDeficit m β u j + radialDeficit m β u l := by
        rw [norm_mul, norm_mul, norm_neg, diameterVector_norm, diameterVector_norm,
          mul_one, mul_one, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (hb j).1, abs_of_nonneg (hb l).1]
      _ ≤ budgetConstant / (2 * m : ℝ) ^ 3 + budgetConstant / (2 * m : ℝ) ^ 3 :=
        add_le_add (hb j).2 (hb l).2
      _ = (2 * budgetConstant / (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by ring
      _ ≤ (1 / 10) / (2 * m : ℝ) ^ 2 := herr
      _ = _ := by ring
  have hn1 : (1 : ℝ) ≤ 2 * m := by
    have hmR : (8 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hstrict := small_perturbation_strict hn1
    (by exact_mod_cast hk : (2 : ℝ) ≤ k) hs' he
  have hturn : cyclicAdvance j (m + k) = halfTurn (show 0 < m by omega) l := by
    apply Fin.ext
    simp only [cyclicAdvance, halfTurn, l, Nat.mod_add_mod]
    congr 1
    omega
  have hθhalf : HalfPeriodic (m := m) (by omega) (fun j => (θ j : ℂ)) := by
    intro i
    exact congrArg (Complex.ofReal) (normalizedAngle_halfPeriodic (by omega) u h.periodic i)
  rw [hturn, normalizedPoint_decomposition, normalizedPoint_decomposition,
    radius_halfTurn (by omega) ‖β‖ u h.periodic,
    diameterVector_halfTurn (by omega) θ hθhalf,
    actualCenter_halfPeriodic (by omega) β u h.periodic]
  have hid : (PolarRepresentation.radius m ‖β‖ u l : ℂ) * -diameterVector θ l + c l -
      ((PolarRepresentation.radius m ‖β‖ u j : ℂ) * diameterVector θ j + c j) =
      -(diameterVector θ j + diameterVector θ l + (c j - c l) + e) := by
    dsimp [e, radialDeficit]
    push_cast
    ring
  change ‖(PolarRepresentation.radius m ‖β‖ u l : ℂ) * -diameterVector θ l + c l -
    ((PolarRepresentation.radius m ‖β‖ u j : ℂ) * diameterVector θ j + c j)‖ < 2
  rw [hid, norm_neg]
  exact hstrict

end
end StructuralNote.MatchingActivityNonlocalPairs

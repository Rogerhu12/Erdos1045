import StructuralNote.ExplicitThresholdFunctions
import StructuralNote.MatchingActivityActualWordPressure
import StructuralNote.MatchingActivityCrossingKernelRate
import StructuralNote.SolNearMaximumSigns

/-! Explicit order bounds for small geometric coefficients and strict pressure signs. -/

namespace StructuralNote.ExplicitPressureThreshold

open Erdos1045 Erdos1045.EventualExact Erdos1045.ExplicitThreshold
open StrongPointwiseSteps StrongPointwiseRadial SinglePressureEstimate
open MatchingActivityRadialDiameterError MatchingActivityRadialModelCenterError
open MatchingActivityCrossingKernelRate FourierMultiplier FiniteBox
open FixedDualClassificationFinite SolScalarGap SolDiagonalKernelGrowth
open Complex Configuration CommonLocalization StrongPointwiseCoordinates
open NormalizedPolarRepresentation ExtremalPolarCenter SignedPressureRemainder
open ActualCrossingGeometry MatchingActivitySaturation CommonClosureEnergy
open StrongObjectiveEstimate MatchingActivityActualChartSelection
open MatchingActivityCrossingExclusivity MatchingActivityRadialActual
noncomputable section

def smallnessThreshold : ℕ :=
  max 16 (max (inverseThreshold (4 * budgetConstant) (1 / 1000000))
    (max (inverseThreshold physicalStepConstant (1 / 1000))
      (max (inverseThreshold radialErrorConstant (10 - Real.pi ^ 2))
        (max (inverseThreshold (2 * budgetConstant) (1 / 10))
          (inverseThreshold diameterStepConstant (1 / 2))))))

theorem coefficients_small {n : ℕ} (hn : smallnessThreshold ≤ n) :
    16 ≤ n ∧ 4 * budgetConstant / (n : ℝ) ≤ 1 / 1000000 ∧
    physicalStepConstant / (n : ℝ) ≤ 1 / 1000 ∧
    radialErrorConstant / (n : ℝ) ≤ 10 - Real.pi ^ 2 ∧
    2 * budgetConstant / (n : ℝ) ≤ 1 / 10 ∧
    diameterStepConstant / (n : ℝ) ≤ 1 / 2 := by
  simp only [smallnessThreshold, max_le_iff] at hn
  have hpi : 0 < 10 - Real.pi ^ 2 := by
    nlinarith only [Real.pi_lt_d2, Real.pi_pos]
  exact ⟨hn.1, (inverse_small (by norm_num) hn.2.1).le,
    (inverse_small (by norm_num) hn.2.2.1).le,
    (inverse_small hpi hn.2.2.2.1).le,
    (inverse_small (by norm_num) hn.2.2.2.2.1).le,
    (inverse_small (by norm_num) hn.2.2.2.2.2).le⟩

theorem log_quarter_lower {n : ℕ} (hn : 0 < n) :
    Real.log (n : ℝ) - Real.log 4 ≤ Real.log (((n / 4 : ℕ) : ℝ) + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnat : n < 4 * (n / 4 + 1) := by omega
  have hcast : (n : ℝ) < 4 * ((n / 4 : ℕ) + 1) := by exact_mod_cast hnat
  have hdiv : (n : ℝ) / 4 ≤ ((n / 4 : ℕ) : ℝ) + 1 := by linarith only [hcast]
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) / 4) hdiv
  rwa [Real.log_div (ne_of_gt hnR) (by norm_num : (4 : ℝ) ≠ 0)] at hh

def signThreshold (C M : ℝ) : ℕ :=
  max 4 (growthThreshold (16 * (|M| + |C| / 2) + 1 + Real.log 4))

theorem scaled_potential_large {m : ℕ} {C M : ℝ}
    (hn : signThreshold C M ≤ 2 * m) (q : Fin (2 * m) → ℝ)
    (hG : G (by have := (le_max_left 4 _).trans hn; omega) q ≤ C / (2 * m : ℝ) ^ 2)
    (i : Fin (2 * m)) : M < (2 * m : ℝ) * |operator (2 * m) q i| := by
  have hn4 : 4 ≤ 2 * m := (le_max_left _ _).trans hn
  have hlog := growth_log_gt ((le_max_right _ _).trans hn)
  have hlower := log_quarter_lower (n := 2 * m) (by omega)
  have hG' : G (by omega) q ≤ |C| / (2 * m : ℝ) ^ 2 :=
    hG.trans (div_le_div_of_nonneg_right (le_abs_self C) (sq_nonneg _))
  have hpot := scaled_potential_log_lower (by omega : 2 ≤ m) q (abs_nonneg C) hG' i
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hlog hlower
  linarith only [hlog, hlower, hpot, le_abs_self M]

def marginConstant : ℝ :=
  8 * (31 * Real.pi / 64) + budgetConstant / 16 + (1 + Real.log 4) / 128

def marginThreshold : ℕ :=
  max 16 (linearGrowthThreshold marginConstant ((9 / 2) * centerErrorConstant) 128)

theorem pressure_margin {n : ℕ} (hn : marginThreshold ≤ n) :
    8 * (31 * Real.pi / 64) +
        (9 / 2 : ℝ) * centerErrorConstant * Real.sqrt (1 + Real.log (n : ℝ)) <
      ((Real.log (((n / 4 : ℕ) : ℝ) + 1) - 1) / 16 - budgetConstant / 2) / 8 := by
  have hn16 : 16 ≤ n := (le_max_left _ _).trans hn
  have hg := log_dominates_sqrt (by norm_num : (0 : ℝ) < 128)
    ((le_max_right _ _).trans hn)
  have hl := log_quarter_lower (n := n) (by omega)
  dsimp [marginConstant] at hg
  linarith only [hg, hl]

theorem near_maximum_signs {m : ℕ} {C : ℝ}
    (hn : signThreshold C (|C| + 1) ≤ 2 * m)
    (hm : 0 < m) (s : SignPattern hm)
    (hdef : deficit hm s ≤ C / (2 * m : ℝ) ^ 2) (i : Fin (2 * m)) :
    potential s i ≠ 0 ∧ patternSign s i * potential s i = |potential s i| := by
  have hG : G hm (vertex (amplitude (2 * m)) s) ≤ C / (2 * m : ℝ) ^ 2 :=
    (vertex_gap_le_deficit hm s).trans hdef
  have hpot := scaled_potential_large hn (vertex (amplitude (2 * m)) s) hG i
  change |C| + 1 < (2 * m : ℝ) * |potential s i| at hpot
  have hnR : (0 : ℝ) < (2 * m : ℕ) := by positivity
  have hnR' : (0 : ℝ) < 2 * (m : ℝ) := by positivity
  have hnonzero : potential s i ≠ 0 := by
    intro hz
    rw [hz, abs_zero, mul_zero] at hpot
    linarith only [hpot, abs_nonneg C]
  refine ⟨hnonzero, ?_⟩
  have hnonneg : 0 ≤ patternSign s i * potential s i := by
    by_contra hneg
    have hneg' : patternSign s i * potential s i < 0 := lt_of_not_ge hneg
    have hcost := single_wrong_sign_cost hm s i hneg'
    have hscaled : (2 * m : ℝ) * deficit hm s ≤ C / (2 * m : ℝ) := by
      calc
        _ ≤ (2 * m : ℝ) * (C / (2 * m : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hdef hnR'.le
        _ = _ := by field_simp
    have hA := amplitude_ge_one (n := 2 * m) (by omega)
    have hC := le_abs_self C
    have hAn := mul_le_mul_of_nonneg_right hA
      (mul_nonneg hnR.le (abs_nonneg (potential s i)))
    have hscaled' := (le_div_iff₀ hnR').mp hscaled
    have hcostn := mul_le_mul_of_nonneg_left hcost hnR.le
    ring_nf at hpot hAn hscaled' hcostn
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hAn hcostn
    ring_nf at hAn hcostn
    nlinarith only [hpot, hAn, hscaled', hcostn, hC, abs_nonneg (potential s i)]
  have hs := sign_mul_abs (patternSign_is_sign s i) (x := potential s i)
  rwa [abs_of_nonneg hnonneg] at hs

def activeWordThreshold : ℕ := max smallnessThreshold marginThreshold

/-- The actual active crossing word has the strict pressure sign at an explicit order. -/
theorem model_activeHalfSign_pressure_pos {m : ℕ} (hm : 8 ≤ m)
    (hn : activeWordThreshold ≤ 2 * m)
    {z : Points (2 * m)} {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ}
    {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z π α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hbounds : PointwiseBounds (m := m) (by omega) β u)
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤
        budgetConstant / (2 * m : ℝ) ^ 2)
    (hgap : G (m := m) (by omega) (polarConstraint (by omega) β u) ≤
      budgetConstant / (2 * m : ℝ) ^ 2)
    (hpressure : ‖operator (2 * m) (polarConstraint (by omega) β u)‖ ≤ 31 * Real.pi / 64)
    (hsat : ∀ j : Fin m, modelRadii m β u j = 1)
    (i : Fin m)
    (hactive :
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2) ∨
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2)) :
    0 < activeHalfSign (by omega) (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) i *
        operator (2 * m) (polarConstraint (by omega) β u) (halfIndex i) := by
  have hs := coefficients_small ((le_max_left _ _).trans hn)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
  have hθ := (StrongPointwiseSmallness.model_nonlocal_smallness hm h hz.1 hbounds
    hbudget hs.2.1 hs.2.2.1 hs.2.2.2.1).1
  exact MatchingActivityActualWordPressure.model_activeHalfSign_pressure_pos hm h hz
    hbounds hθ hbudget hgap hpressure hs.2.1 hs.2.2.1 hs.2.2.2.1
    hs.2.2.2.2.1 hs.2.2.2.2.2 hsat
    (pressure_margin ((le_max_right _ _).trans hn)) i hactive

end
end StructuralNote.ExplicitPressureThreshold

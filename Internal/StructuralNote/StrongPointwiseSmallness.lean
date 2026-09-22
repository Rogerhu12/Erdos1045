import StructuralNote.StrongPointwiseRadial
import Mathlib.Analysis.Real.Pi.Bounds

/-! Small parameters for distant-pair exclusion follow from the actual strong budget. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.StrongPointwiseSmallness

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open SchurSpectrum DiscreteEnergy FiniteFourierLift
open ExtremalPolarCenter NormalizedPolarRepresentation SignedPressureRemainder StrongObjectiveEstimate
open SinglePressureEstimate StrongBudgetConsequences StrongPointwiseCoordinates StrongPointwiseSteps
open StrongPointwiseRadial ActualCrossingGeometry CommonFiberNonlocalFrames CommonFiberNonlocalProjection

theorem angle_pointwise_small {n : ℕ} (hn : 2 ≤ n) (θ : Fin n → ℝ)
    (hmean : ∑ j, θ j = 0) (hE : realEnergy (by omega) θ ≤ budgetConstant / (n : ℝ) ^ 2)
    (hsmall : 4 * budgetConstant / (n : ℝ) ≤ 1 / 1000000) (j : Fin n) :
    |θ j| ≤ 1 / (1000 * (n : ℝ)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hp := mean_zero_poincare hn (fun j => (θ j : ℂ)) (by rw [← ofReal_sum, hmean, ofReal_zero])
  simp only [normSq_ofReal, ← pow_two] at hp
  change ((n : ℝ) - 1) / 2 * (∑ j, θ j ^ 2) ≤ realEnergy (by omega) θ at hp
  have hsingle := Finset.single_le_sum (s := Finset.univ) (f := fun j => θ j ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have hm := mul_le_mul_of_nonneg_left hsingle (show 0 ≤ ((n : ℝ) - 1) / 2 by linarith)
  have hweight : (n : ℝ) / 4 * θ j ^ 2 ≤ ((n : ℝ) - 1) / 2 * θ j ^ 2 := by
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hbudget : (n : ℝ) / 4 * θ j ^ 2 ≤ budgetConstant / (n : ℝ) ^ 2 := hweight.trans (hm.trans (hp.trans hE))
  have hsq : θ j ^ 2 ≤ 4 * budgetConstant / (n : ℝ) ^ 3 := by
    apply (le_of_mul_le_mul_left ?_ (show (0 : ℝ) < n / 4 by positivity))
    calc
      _ ≤ budgetConstant / (n : ℝ) ^ 2 := hbudget
      _ = _ := by field_simp
  have hsmall' := div_le_div_of_nonneg_right hsmall (sq_nonneg (n : ℝ))
  have hlast : 4 * budgetConstant / (n : ℝ) ^ 3 ≤ (1 / (1000 * (n : ℝ))) ^ 2 := by
    calc
      _ = (4 * budgetConstant / (n : ℝ)) / (n : ℝ) ^ 2 := by ring
      _ ≤ (1 / 1000000) / (n : ℝ) ^ 2 := hsmall'
      _ = _ := by ring
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 (by simpa only [sq_abs] using hsq.trans hlast)

theorem eventual_coefficients_small : ∀ᶠ n : ℕ in atTop,
    16 ≤ n ∧ 4 * budgetConstant / (n : ℝ) ≤ 1 / 1000000 ∧
    physicalStepConstant / (n : ℝ) ≤ 1 / 1000 ∧
    radialErrorConstant / (n : ℝ) ≤ 10 - Real.pi ^ 2 ∧
    2 * budgetConstant / (n : ℝ) ≤ 1 / 10 := by
  have hpi : 0 < 10 - Real.pi ^ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  filter_upwards [eventually_ge_atTop 16,
    (tendsto_const_div_atTop_nhds_zero_nat (4 * budgetConstant)).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 1000000),
    (tendsto_const_div_atTop_nhds_zero_nat physicalStepConstant).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 1000),
    (tendsto_const_div_atTop_nhds_zero_nat radialErrorConstant).eventually_le_const hpi,
    (tendsto_const_div_atTop_nhds_zero_nat (2 * budgetConstant)).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 10)]
      with n hn hb hc hr hb'
  exact ⟨hn, hb, hc, hr, hb'⟩

theorem model_nonlocal_smallness {m : ℕ} (hm : 8 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z)
    (hbounds : PointwiseBounds (m := m) (by omega) β u)
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2)
    (hsmallB : 4 * budgetConstant / (2 * m : ℝ) ≤ 1 / 1000000)
    (hsmallC : physicalStepConstant / (2 * m : ℝ) ≤ 1 / 1000)
    (hsmallR : radialErrorConstant / (2 * m : ℝ) ≤ 10 - Real.pi ^ 2) :
    (∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ))) ∧
    (∀ j, ‖difference (by omega) (actualCenter m β u) j‖ ≤ 1 / (1000 * (2 * m : ℝ))) ∧
    (∀ j, |radial (meanFrame (by omega) (normalizedAngle m u) j)
      (difference (by omega) (actualCenter m β u) j)| ≤ 10 / (2 * m : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have hτ : 0 ≤ radialMass m β u := by
    unfold radialMass
    exact mul_nonneg hn0.le (Finset.sum_nonneg fun j _ => (hbounds.2.2.1 j).1)
  have hD : 0 ≤ residualEnergy (by omega) (polarCenter m β u) := pairEnergy_nonneg (by omega) _
  have hEb : realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 := by
    linarith only [hbudget, hτ, hD]
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using angle_pointwise_small (show 2 ≤ 2 * m by omega)
      (normalizedAngle m u) (normalizedAngle_mean_zero (by omega) u)
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hEb)
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsmallB) j
  · intro j
    have hh := div_le_div_of_nonneg_right hsmallC hn0.le
    have he : physicalStepConstant / (2 * m : ℝ) ^ 2 ≤ 1 / (1000 * (2 * m : ℝ)) := by
      calc
        _ = (physicalStepConstant / (2 * m : ℝ)) / (2 * m : ℝ) := by ring
        _ ≤ (1 / 1000) / (2 * m : ℝ) := hh
        _ = _ := by ring
    exact (hbounds.2.2.2.2.2.2 j).trans he
  · intro j
    have hp := model_radial_bound (show 0 < m by omega) h hz hbounds j
    have hh := div_le_div_of_nonneg_right hsmallR (sq_nonneg (2 * m : ℝ))
    have he : radialErrorConstant / (2 * m : ℝ) ^ 3 ≤ (10 - Real.pi ^ 2) / (2 * m : ℝ) ^ 2 := by
      calc
        _ = (radialErrorConstant / (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by ring
        _ ≤ _ := hh
    calc
      _ ≤ Real.pi ^ 2 / (2 * m : ℝ) ^ 2 + radialErrorConstant / (2 * m : ℝ) ^ 3 := hp
      _ ≤ Real.pi ^ 2 / (2 * m : ℝ) ^ 2 + (10 - Real.pi ^ 2) / (2 * m : ℝ) ^ 2 := add_le_add le_rfl he
      _ = _ := by ring

end StructuralNote.StrongPointwiseSmallness

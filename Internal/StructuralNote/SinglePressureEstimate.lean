import StructuralNote.ActualPressureAbsorption
import StructuralNote.ReusedEvenLift

/-! The single pressure estimate for genuine diameter maximizers. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.SinglePressureEstimate

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open PolarAngleControl NormalizedPolarRepresentation ExtremalPolarCenter
open SchurSpectrum SchurLift SchurLiftBounds FiniteFourierLift FourierMultiplier DiscreteEnergy
open ActualObjectiveLoss ActualAngularLoss CanonicalNonlinearError StrongObjectiveEstimate
open ActualPressureAbsorption SignedPressureRemainder

def comparisonConstant : ℝ := objectiveConstant + pressureConstant

def budgetConstant : ℝ := 256 * (comparisonConstant + 1000000)

theorem actualMass_eq_radialMass (m : ℕ) (β : ℂ) (u : ℕ → ℂ) :
    ActualRadialPrice.actualMass m ‖β‖ u = radialMass m β u := by
  simp only [ActualRadialPrice.actualMass, RadialObjectivePrice.mass, radialMass, radialDeficit,
    RadialDeficitControl.deficit, Nat.cast_mul, Nat.cast_ofNat]

theorem root_log_discriminant {n : ℕ} (hn : 3 ≤ n) :
    Real.log (discriminant (SignedPressureAngular.root n)) = (n : ℝ) * Real.log n := by
  have he : SignedPressureAngular.root n = regular n := by
    funext j
    exact (ClosedRegularGeometry.regular_eq_root_power n j).symm
  rw [he, ClosedRegularGeometry.regular_discriminant n hn, Real.log_pow]

theorem diameter_sequence_single_pressure {M : ℕ → ℕ} (hM2 : ∀ k, 2 ≤ M k)
    (hM : Tendsto M atTop atTop) (z : ∀ k, Points (2 * M k))
    (hz : ∀ k, ExtremalNormalization.DiameterExtremal (z k)) :
    ∃ (σ : ∀ k, Equiv.Perm (Fin (2 * M k))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ), Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ k in atTop,
        NormalizedRelativeEdgeModel (z k) (σ k) (α k) (β k) (u k) (η k) ∧
        CenterBounds (m := M k) (by have := hM2 k; omega) (β k) (u k) ∧
        η k ≤ 1 / 1024 ∧
        meanSquare (polarConstraint (m := M k) (by have := hM2 k; omega) (β k) (u k)) ≤ 65 * Real.pi ^ 2 ∧
        ‖operator (2 * M k) (polarConstraint (by have := hM2 k; omega) (β k) (u k))‖ ≤ 31 * Real.pi / 64 ∧
        Real.log (discriminant (z k)) - ((2 * M k : ℕ) : ℝ) * Real.log (2 * M k : ℕ) ≤
          FiniteBox.B (m := M k) (by have := hM2 k; omega) - radialMass (M k) (β k) (u k) / 4 -
            residualEnergy (by have := hM2 k; omega) (polarCenter (M k) (β k) (u k)) / 256 -
            realEnergy (by have := hM2 k; omega) (normalizedAngle (M k) (u k)) / 8 +
            comparisonConstant / ((2 * M k : ℕ) : ℝ) ^ 2 ∧
        radialMass (M k) (β k) (u k) +
          residualEnergy (by have := hM2 k; omega) (polarCenter (M k) (β k) (u k)) +
          realEnergy (by have := hM2 k; omega) (normalizedAngle (M k) (u k)) ≤
            budgetConstant / ((2 * M k : ℕ) : ℝ) ^ 2 := by
  obtain ⟨σ, α, β, u, η, hη, _, hgood⟩ := ActualPressureGap.diameter_sequence_pressure_gap hM2 hM z hz
  refine ⟨σ, α, β, u, η, hη, ?_⟩
  have hN : Tendsto (fun k => 2 * M k) atTop atTop := tendsto_atTop_mono (fun _ => by omega) hM
  have hcoef := coefficient_tendsto hN (coordinateBudget_tendsto hN hη) (65 * Real.pi ^ 2) (320 * Real.pi ^ 2)
  filter_upwards [hgood, eventual_model_objective_loss hM hη (by norm_num : (0 : ℝ) < 1 / 8),
    (sizeBudget_tendsto hN).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 16),
    hcoef.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 128),
    eventual_model_pressure_absorbed hM, hN.eventually_ge_atTop 256]
    with k hk hobj hs hcoef hpressure hn256
  have hm2 := hM2 k
  have hE := model_energy_le (by omega) hk.1 hk.2.2.1 hk.2.2.2.1
  have hp := model_polar_bounds hm2 hk.1 hE (hs.trans (by norm_num))
  have hβ := (ExtremalScaleBound.model_matching_deficit_bound hm2 hk.1 (by linarith [hk.2.2.1]) (hz k) hE).1
  have hcoords := model_coordinate_bounds hm2 hk.1 hp hβ hs
  have hmass := ActualSignedAngular.model_constraint_mass hm2 hk.1 hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2.1
  have hδ : 0 ≤ coordinateBudget (2 * M k) (η k) := by
    unfold coordinateBudget
    have := hk.1.error_nonneg
    positivity
  have herr := nonlinear_error_le (show 3 ≤ 2 * M k by omega) (polarCenter (M k) (β k) (u k))
    (polarConstraint (by omega) (β k) (u k)) hk.2.1.mean_zero hδ hmass hk.2.1.energy hcoords.2.2.1
  have hpot := potential_residual_bound hm2 (polarCenter (M k) (β k) (u k)) hk.2.1.half_periodic hk.2.1.mean_zero
  have hactual := hobj (z k) (σ k) (α k) (β k) (u k) (by omega) hk.1 (hz k) hE
  have hmul := mul_le_mul_of_nonneg_right hcoef (pairEnergy_nonneg (show 0 < 2 * M k by omega)
    (polarCenter (M k) (β k) (u k) - canonicalLift (polarConstraint (by omega) (β k) (u k))))
  have hpres := hpressure (z k) (σ k) (α k) (β k) (u k) (η k) (by omega)
    hk.1 hk.2.2.1 (hz k) hk.2.2.2.1 hk.2.1 hk.2.2.2.2.1 hk.2.2.2.2.2
  rw [constantTerm_eq] at herr
  change _ ≤ objectiveConstant / ((2 * M k : ℕ) : ℝ) ^ 2 + _ at herr
  have hstrong : Real.log (discriminant (z k)) - ((2 * M k : ℕ) : ℝ) * Real.log (2 * M k : ℕ) ≤
      FiniteBox.B (m := M k) (by omega) - radialMass (M k) (β k) (u k) / 4 -
        residualEnergy (by omega) (polarCenter (M k) (β k) (u k)) / 256 -
        realEnergy (by omega) (normalizedAngle (M k) (u k)) / 8 +
        comparisonConstant / ((2 * M k : ℕ) : ℝ) ^ 2 := by
    rw [actualMass_eq_radialMass, root_log_discriminant (by omega)] at hactual
    simp only [Nat.cast_mul, Nat.cast_ofNat] at herr hactual hmul ⊢
    dsimp only [residualEnergy, polarConstraint, quartic, comparisonConstant] at herr hpot hpres ⊢
    dsimp only [polarConstraint] at hmul
    rw [add_div]
    linarith only [herr, hactual, hpot, hmul, hpres]
  refine ⟨hk.1, hk.2.1, hk.2.2.1, hmass, hk.2.2.2.2.2, hstrong, ?_⟩
  have hlo := WholeBoxLowerBound.diameterExtremal_log_lower hn256 (z k) (hz k)
  have hτ : 0 ≤ radialMass (M k) (β k) (u k) := by
    unfold radialMass
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun j _ => sub_nonneg.mpr
      (PolarRepresentation.model_radius_le_one (by omega) hk.1 (hz k).1 j)
  have hD : 0 ≤ residualEnergy (by omega) (polarCenter (M k) (β k) (u k)) :=
    pairEnergy_nonneg (by omega) _
  have hθ : 0 ≤ realEnergy (by omega) (normalizedAngle (M k) (u k)) := pairEnergy_nonneg (by omega) _
  have hcst : budgetConstant / ((2 * M k : ℕ) : ℝ) ^ 2 =
      256 * (comparisonConstant / ((2 * M k : ℕ) : ℝ) ^ 2 + 1000000 / ((2 * M k : ℕ) : ℝ) ^ 2) := by
    unfold budgetConstant
    ring
  rw [hcst]
  linarith only [hstrong, hlo, hτ, hD, hθ]

/-- All bounds refer to the same coordinates of the actual configuration. -/
def HasStrongCoordinates (m : ℕ) (z : Points (2 * m)) : Prop :=
  ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
    NormalizedRelativeEdgeModel z σ α β u η ∧ CenterBounds hm β u ∧ η ≤ 1 / 1024 ∧
    meanSquare (polarConstraint hm β u) ≤ 65 * Real.pi ^ 2 ∧
    ‖operator (2 * m) (polarConstraint hm β u)‖ ≤ 31 * Real.pi / 64 ∧
    Real.log (discriminant z) - ((2 * m : ℕ) : ℝ) * Real.log (2 * m : ℕ) ≤
      FiniteBox.B hm - radialMass m β u / 4 - residualEnergy (by omega) (polarCenter m β u) / 256 -
        realEnergy (by omega) (normalizedAngle m u) / 8 + comparisonConstant / ((2 * m : ℕ) : ℝ) ^ 2 ∧
    radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / ((2 * m : ℕ) : ℝ) ^ 2

/-- Proposition 6.4's strong energy budget, uniformly for all sufficiently large
even-order global maximizers. No analytic estimate is an input hypothesis. -/
theorem eventual_diameter_single_pressure :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z → HasStrongCoordinates m z := by
  by_contra h
  push Not at h
  choose M hMk z hz hbad using fun k : ℕ => h (k + 2)
  have hM2 (k : ℕ) : 2 ≤ M k := by have := hMk k; omega
  have hM : Tendsto M atTop atTop :=
    tendsto_atTop_mono (fun k => by have := hMk k; omega : ∀ k, k ≤ M k) tendsto_id
  obtain ⟨σ, α, β, u, η, _, hg⟩ := diameter_sequence_single_pressure hM2 hM z hz
  obtain ⟨k, hk⟩ := hg.exists
  exact hbad k ⟨by have := hM2 k; omega, σ k, α k, β k, u k, η k, hk⟩

end StructuralNote.SinglePressureEstimate

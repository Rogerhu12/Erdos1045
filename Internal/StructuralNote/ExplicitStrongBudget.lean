import StructuralNote.ExplicitObjectiveThreshold
import StructuralNote.MatchingActivityCrossingPressure

/-! The strong pressure budget at a specified finite order. -/

namespace StructuralNote.ExplicitStrongBudget

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization
open PolarAngleControl NormalizedPolarRepresentation ExtremalPolarCenter
open SchurSpectrum SchurLift SchurLiftBounds FiniteFourierLift FourierMultiplier DiscreteEnergy
open ActualObjectiveLoss ActualAngularLoss CanonicalNonlinearError StrongObjectiveEstimate
open ActualPressureAbsorption SignedPressureRemainder SinglePressureEstimate
open Erdos1045.ExplicitThreshold ExplicitLocalBudgets
open SolScalarGap
noncomputable section

def orderThreshold : ℕ :=
  max 256 (max ExplicitObjectiveThreshold.orderThreshold
    (max (canonicalThreshold (65 * Real.pi ^ 2) (320 * Real.pi ^ 2)) absorptionThreshold))

def edgeTolerance : ℝ := min ExplicitObjectiveThreshold.edgeTolerance (1 / 1024)

theorem edgeTolerance_pos : 0 < edgeTolerance :=
  lt_min ExplicitObjectiveThreshold.edgeTolerance_pos (by norm_num)

theorem model_scalar_gap_budget {m : ℕ} (hm : 8 ≤ m)
    (hn : orderThreshold ≤ 2 * m) {η : ℝ} (hη : η ≤ edgeTolerance)
    {z : Points (2 * m)} {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hJ : objective (regular (2 * m)) - objective (z ∘ σ) ≤ 33 * Real.pi ^ 2 / 256)
    (hc : CenterBounds (m := m) (by omega) β u)
    (herr : meanSquare (polarConstraint (by omega) β u - ExtremalSchurGap.evenConstraint m u) ≤
      Real.pi ^ 2 / 2048)
    (hG : ‖operator (2 * m) (polarConstraint (by omega) β u)‖ ≤ 31 * Real.pi / 64) :
    (Real.log (discriminant z) - ((2 * m : ℕ) : ℝ) * Real.log (2 * m : ℕ) ≤
      FiniteBox.B (m := m) (by omega) - G (m := m) (by omega) (polarConstraint (by omega) β u) -
        radialMass m β u / 4 -
        residualEnergy (by omega) (polarCenter m β u) / 256 -
        realEnergy (by omega) (normalizedAngle m u) / 8 +
        comparisonConstant / ((2 * m : ℕ) : ℝ) ^ 2) ∧
    G (m := m) (by omega) (polarConstraint (by omega) β u) +
      radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / ((2 * m : ℕ) : ℝ) ^ 2 := by
  have hn256 : 256 ≤ 2 * m := (le_max_left _ _).trans hn
  have hno := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnc := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hna := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hηo := hη.trans (min_le_left _ _)
  have hη1024 := hη.trans (min_le_right _ _)
  have hs := ExplicitObjectiveThreshold.parameters_small hno hmodel.error_nonneg hηo
  have hs16 := hs.2.2.2.1.trans (by norm_num : (1 / 10000 : ℝ) ≤ 1 / 16)
  have hE := model_energy_le (by omega) hmodel hη1024 hJ
  have hp := model_polar_bounds (show 2 ≤ m by omega) hmodel hE (hs16.trans (by norm_num))
  have hβ := (ExtremalScaleBound.model_matching_deficit_bound (show 2 ≤ m by omega)
    hmodel hs.2.1 hz hE).1
  have hcoords := model_coordinate_bounds (show 2 ≤ m by omega) hmodel hp hβ hs16
  have hmass := ActualSignedAngular.model_constraint_mass (show 2 ≤ m by omega)
    hmodel hη1024 hJ herr
  have hδ : 0 ≤ coordinateBudget (2 * m) η := by
    unfold coordinateBudget
    have := hmodel.error_nonneg
    positivity
  have hcoef := canonical_small (by positivity : 0 ≤ 320 * Real.pi ^ 2) hδ hs.2.2.1 hnc
  have he := nonlinear_error_le (show 3 ≤ 2 * m by omega) (polarCenter m β u)
    (polarConstraint (by omega) β u) hc.mean_zero hδ hmass hc.energy hcoords.2.2.1
  have hpot := potential_residual_bound (show 2 ≤ m by omega) (polarCenter m β u)
    hc.half_periodic hc.mean_zero
  have hactual := ExplicitObjectiveThreshold.model_objective_loss (show 2 ≤ m by omega)
    hno hηo hmodel hz hE
  have hmul := mul_le_mul_of_nonneg_right hcoef (pairEnergy_nonneg (show 0 < 2 * m by omega)
    (polarCenter m β u - canonicalLift (polarConstraint (by omega) β u)))
  have ha := absorption_small hna
  simp only [Nat.cast_mul, Nat.cast_ofNat] at ha
  have hpres := MatchingActivityCrossingPressure.model_pressure_absorbed_with_gap hm hmodel hη1024 hz hJ hc herr hG
    ha.2.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.2.2.2
  rw [constantTerm_eq] at he
  change _ ≤ objectiveConstant / ((2 * m : ℕ) : ℝ) ^ 2 + _ at he
  have hstrong : Real.log (discriminant z) - ((2 * m : ℕ) : ℝ) * Real.log (2 * m : ℕ) ≤
      FiniteBox.B (m := m) (by omega) - G (m := m) (by omega) (polarConstraint (by omega) β u) -
        radialMass m β u / 4 -
        residualEnergy (by omega) (polarCenter m β u) / 256 -
        realEnergy (by omega) (normalizedAngle m u) / 8 +
        comparisonConstant / ((2 * m : ℕ) : ℝ) ^ 2 := by
    rw [actualMass_eq_radialMass, root_log_discriminant (by omega)] at hactual
    simp only [Nat.cast_mul, Nat.cast_ofNat] at he hactual hmul ⊢
    dsimp only [residualEnergy, polarConstraint, quartic, comparisonConstant] at he hpot hpres ⊢
    dsimp only [polarConstraint] at hmul
    rw [add_div]
    linarith only [he, hactual, hpot, hmul, hpres]
  refine ⟨hstrong, ?_⟩
  have hlo := WholeBoxLowerBound.diameterExtremal_log_lower hn256 z hz
  have hgap := gap_nonneg (show 0 < m by omega) (polarConstraint (m := m) (by omega) β u)
  have hτ : 0 ≤ radialMass m β u := by
    unfold radialMass
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun j _ =>
      sub_nonneg.mpr (PolarRepresentation.model_radius_le_one (by omega) hmodel hz.1 j)
  have hD : 0 ≤ residualEnergy (by omega) (polarCenter m β u) := pairEnergy_nonneg (by omega) _
  have hθ : 0 ≤ realEnergy (by omega) (normalizedAngle m u) := pairEnergy_nonneg (by omega) _
  have hcst : budgetConstant / ((2 * m : ℕ) : ℝ) ^ 2 =
      256 * (comparisonConstant / ((2 * m : ℕ) : ℝ) ^ 2 + 1000000 / ((2 * m : ℕ) : ℝ) ^ 2) := by
    unfold budgetConstant
    ring
  rw [hcst]
  linarith only [hstrong, hlo, hgap, hτ, hD, hθ]

theorem model_strong_budget {m : ℕ} (hm : 8 ≤ m)
    (hn : orderThreshold ≤ 2 * m) {η : ℝ} (hη : η ≤ edgeTolerance)
    {z : Points (2 * m)} {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hJ : objective (regular (2 * m)) - objective (z ∘ σ) ≤ 33 * Real.pi ^ 2 / 256)
    (hc : CenterBounds (m := m) (by omega) β u)
    (herr : meanSquare (polarConstraint (by omega) β u - ExtremalSchurGap.evenConstraint m u) ≤
      Real.pi ^ 2 / 2048)
    (hG : ‖operator (2 * m) (polarConstraint (by omega) β u)‖ ≤ 31 * Real.pi / 64) :
    (Real.log (discriminant z) - ((2 * m : ℕ) : ℝ) * Real.log (2 * m : ℕ) ≤
      FiniteBox.B (m := m) (by omega) - radialMass m β u / 4 -
        residualEnergy (by omega) (polarCenter m β u) / 256 -
        realEnergy (by omega) (normalizedAngle m u) / 8 +
        comparisonConstant / ((2 * m : ℕ) : ℝ) ^ 2) ∧
    radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / ((2 * m : ℕ) : ℝ) ^ 2 := by
  obtain ⟨hobj, hbudget⟩ := model_scalar_gap_budget hm hn hη hmodel hz hJ hc herr hG
  have hgap := gap_nonneg (show 0 < m by omega) (polarConstraint (m := m) (by omega) β u)
  constructor <;> linarith only [hobj, hbudget, hgap]

end
end StructuralNote.ExplicitStrongBudget

import StructuralNote.ExplicitLocalBudgets

/-! The pressure coordinates and strict operator gap at a specified finite order. -/

namespace StructuralNote.ExplicitPressureCoordinates

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization
open Erdos1045.ExplicitThreshold ExplicitLocalBudgets ExtremalEnergyBound
open PolarAngleControl NormalizedPolarRepresentation ExtremalPolarCenter
open FiniteFourierLift FourierMultiplier ActualPressureGap
open HullGeometry SchurLiftBounds SchurSpectrum PressureCoercivity
open scoped BigOperators
noncomputable section

theorem diameter_budget_small {n : ℕ} (hn : 16 ≤ n) :
    diameterBudget n ≤ 33 * Real.pi ^ 2 / 256 := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hnR]
  have hangle := (halfAngle_bounds (by omega : 4 ≤ n)).1
  have hangle8 : halfAngle n ≤ 1 / 8 := by
    unfold halfAngle
    apply (div_le_iff₀ (show 0 < 2 * (n : ℝ) by positivity)).mpr
    linarith only [Real.pi_lt_four, hnR]
  have hsq := pow_le_pow_left₀ hangle.le hangle8 2
  have hcos := Real.one_sub_sq_div_two_le_cos (x := halfAngle n)
  have hcos0 : 0 < 8 * Real.cos (halfAngle n) := by linarith only [hsq, hcos]
  unfold diameterBudget
  apply (div_le_iff₀ hcos0).mpr
  have hb : (32 / 33 : ℝ) ≤ Real.cos (halfAngle n) := by linarith only [hsq, hcos]
  have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg Real.pi)
  nlinarith only [hh]

def constraintThreshold (ε : ℝ) : ℕ :=
  max (decayThreshold (4352 * 384 * Real.pi ^ 6) (ε / 2))
    (decayThreshold (64 * Real.pi ^ 2 * (256 * Real.pi ^ 2) ^ 2) (ε / 2))

theorem constraint_error_small {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hn : constraintThreshold ε ≤ n) : constraintErrorBudget n < ε := by
  have h₁ := (le_max_left _ _).trans hn
  have h₂ := (le_max_right _ _).trans hn
  have hn2 := (decayThreshold_two_le _ _).trans h₁
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have ha := log_div_power_small (by positivity : 0 ≤ 4352 * 384 * Real.pi ^ 6)
    (by positivity : 0 < ε / 2) (by norm_num : 1 ≤ 1) h₁
  have hb := monomial_small (n := n) (j := 0)
    (by positivity : 0 ≤ 64 * Real.pi ^ 2 * (256 * Real.pi ^ 2) ^ 2)
    (by positivity : 0 < ε / 2) (by norm_num) (by norm_num : (1 / 4 : ℝ) ≤ 4) h₂
  rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_ofNat] at hb
  simp only [pow_zero, mul_one] at hb
  have he : constraintErrorBudget n =
      (4352 * 384 * Real.pi ^ 6) * Real.log n / (n : ℝ) +
      (64 * Real.pi ^ 2 * (256 * Real.pi ^ 2) ^ 2) / (n : ℝ) ^ 4 := by
    unfold constraintErrorBudget sizeBudget
    field_simp
  rw [he]
  simp only [pow_one] at ha
  have hb' : (64 * Real.pi ^ 2 * (256 * Real.pi ^ 2) ^ 2) / (n : ℝ) ^ 4 < ε / 2 := by
    simpa only [div_eq_mul_inv] using hb
  linarith only [ha, hb']

def orderThreshold : ℕ :=
  max 2048 (max (sizeThreshold (1 / 16)) (constraintThreshold (Real.pi ^ 2 / 2048)))

theorem model_pressure_coordinates {m : ℕ} (hm : 2 ≤ m)
    (hn : orderThreshold ≤ 2 * m) {η : ℝ} (hη : η ≤ 1 / 1024)
    {z : Points (2 * m)} {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hboundary : boundaryLength (z ∘ σ) ≤ hullPerimeter z) :
    CenterBounds (m := m) (by omega) β u ∧
    objective (regular (2 * m)) - objective (z ∘ σ) ≤ 33 * Real.pi ^ 2 / 256 ∧
    meanSquare (polarConstraint (by omega) β u - ExtremalSchurGap.evenConstraint m u) ≤
      Real.pi ^ 2 / 2048 ∧
    ‖operator (2 * m) (polarConstraint (by omega) β u)‖ ≤ 31 * Real.pi / 64 := by
  have hn2048 : 2048 ≤ 2 * m := (le_max_left _ _).trans hn
  have hs := (size_small (by norm_num : (0 : ℝ) < 1 / 16)
    ((le_max_left _ _).trans ((le_max_right _ _).trans hn))).le
  have he := (constraint_error_small (by positivity : 0 < Real.pi ^ 2 / 2048)
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn))).le
  have hb := model_energy_bound hmodel (by omega) (hη.trans (by norm_num)) hz hboundary
  have hE := hb.2.1
  have hp := model_polar_bounds hm hmodel hE (hs.trans (by norm_num))
  have hscale := ExtremalScaleBound.model_matching_deficit_bound hm hmodel
    (hη.trans (by norm_num)) hz hE
  have hc : CenterBounds (m := m) (by omega) β u := by
    apply model_center_bounds (by omega) β u hmodel.periodic hmodel.mean_zero hE hp hscale.1 _ hs
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hscale.2.1
  have herr := hc.constraint_error.trans he
  have hJ : objective (regular (2 * m)) - objective (z ∘ σ) ≤ 33 * Real.pi ^ 2 / 256 := by
    rw [model_deficit_eq hmodel (by omega) (hη.trans (by norm_num))]
    exact hb.1.trans (diameter_budget_small (by omega))
  have hfinite := model_objectiveDeficit_eq (by omega : 4 ≤ 2 * m) hmodel (hη.trans (by norm_num))
  have hsPair : ∀ i, ‖periodize (by omega) (fun j : Fin (2 * m) => u j) (i + 1) -
      periodize (by omega) (fun j : Fin (2 * m) => u j) i‖ ≤
        η * ‖LocalPhase.regularRoot (2 * m) - 1‖ := by
    simpa only [ActualPressureGap.periodize_restrict _ _ hmodel.periodic] using hmodel.relative_edges
  refine ⟨hc, hJ, herr, ?_⟩
  apply operator_pressure_gap_of_perturbation hn2048 (fun j : Fin (2 * m) => u j)
    (model_first_zero (by omega) hmodel) hmodel.error_nonneg hη hsPair (hfinite.trans_le hJ)
  simpa only [evenNormal_restrict _ _ hmodel.periodic] using herr

end
end StructuralNote.ExplicitPressureCoordinates

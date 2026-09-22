import StructuralNote.EdgeEnergyComparison
import EventualExact.LocalTaylorRemainder
import EventualExact.LocalGradientLimit
import EventualExact.AntipodalEnergy

/-! The actual perimeter-normalized objective controls the energy and the
physical force error. These are finite local estimates: localization itself
is not an input disguised as an analytic or coercivity conclusion. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.PressureCoercivity

open Erdos1045 Erdos1045.EventualExact
open Complex SchurSpectrum EdgeCoordinates EdgeNormalForm EdgeEnergyComparison
open Filter

/-- The difference of the actual logarithmic distance/perimeter objectives. -/
def objectiveDeficit {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ) : ℝ :=
  LocalObjective.objective n (LocalObjective.regularVertices n) -
    LocalObjective.objective n (LocalObjective.perturbedVertices n (periodize hn u))

def energy {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ) : ℝ :=
  pairEnergy hn u + (n : ℝ) * LocalDFT.energyB n (periodize hn u)

theorem energy_nonneg {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ) : 0 ≤ energy hn u :=
  ExtremalEnergyBound.totalEnergy_nonneg n (periodize hn u)

theorem pairEnergy_le_energy {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ) :
    pairEnergy hn u ≤ energy hn u := by
  have hB := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    (LocalMaximum.energyB_nonneg n (periodize hn u))
  unfold energy
  linarith

theorem similarity_zero {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient hn u 0 = 0) :
    (∑ j ∈ Finset.range n, periodize hn u j *
      (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0 := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold centerCoefficient LocalDFT.coefficient at hfirst
  simpa only [zero_add, mul_one] using (div_eq_zero_iff.mp hfirst).resolve_right hn0

theorem deficit_eq_positiveQuadratic {n : ℕ} (hn : 0 < n) (u : Fin n → ℂ) :
    deficit hn u = LocalDFT.positiveQuadratic n (periodize hn u) := by
  rw [LocalTaylorRemainder.positiveQuadratic_eq]
  unfold deficit pairPotential LocalTaylorRemainder.pairTerm
  ring

theorem objectiveDeficit_eq_neg_gain {n : ℕ} (hn : 4 ≤ n) (u : Fin n → ℂ)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hstep : ∀ j, ‖periodize (by omega) u (j + 1) - periodize (by omega) u j‖ ≤
      η * ‖LocalPhase.regularRoot n - 1‖) :
    objectiveDeficit (by omega) u = -LocalMaximum.gain n (periodize (by omega) u) := by
  have h := LocalObjective.objective_difference_eq_gain ClosedFourier.geometricSine hn
    (periodize (by omega) u) (periodize_periodic _ _) hη hsmall hstep
  unfold objectiveDeficit
  linarith

theorem objectiveDeficit_eq_configuration {n : ℕ} (hn : 4 ≤ n) (u : Fin n → ℂ)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hstep : ∀ j, ‖periodize (by omega) u (j + 1) - periodize (by omega) u j‖ ≤
      η * ‖LocalPhase.regularRoot n - 1‖) :
    objectiveDeficit (by omega) u = Configuration.objective (Configuration.regular n) -
      Configuration.objective (fun j => Configuration.regular n j + u j) := by
  have hp := LocalConfiguration.objective_eq (show 2 ≤ n by omega)
    (LocalObjective.perturbedVertices n (periodize (by omega) u))
    (LocalConfiguration.periodic_of_perturbed (by omega) _ (periodize_periodic _ _))
    (LocalConfiguration.small_perturbation_injective ClosedFourier.geometricSine hn _
      (periodize_periodic _ _) hη hsmall hstep)
  have hregperiod : Function.Periodic (LocalObjective.regularVertices n) n := by
    intro j
    simp [LocalObjective.regularVertices, pow_add, LocalDFT.regularRoot_pow (by omega : 0 < n)]
  have hr := LocalConfiguration.objective_eq (show 2 ≤ n by omega)
    (LocalObjective.regularVertices n) hregperiod (by
      simpa only [LocalObjective.regularVertices, LocalRigidity.root_power_eq_regular] using
        LocalConfiguration.regular_injective hn ClosedFourier.geometricSine)
  unfold objectiveDeficit
  rw [hr, hp]
  simp only [LocalObjective.perturbedVertices, LocalObjective.regularVertices,
    LocalRigidity.root_power_eq_regular, periodize_fin]

/-- The Taylor error concerns actual distances and actual edge lengths. -/
theorem objective_taylor_bound {n : ℕ} (hn : 4 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hstep : ∀ j, ‖periodize (by omega) u (j + 1) - periodize (by omega) u j‖ ≤
      η * ‖LocalPhase.regularRoot n - 1‖) :
    |objectiveDeficit (by omega) u - deficit (by omega) u| ≤
      4 * η * energy (by omega) u := by
  have h := LocalTaylorRemainder.gain_remainder_bound hn (periodize (by omega) u)
    (periodize_periodic _ _) (similarity_zero (by omega) u hfirst) hη hsmall hstep
  rw [objectiveDeficit_eq_neg_gain hn u hη hsmall hstep, deficit_eq_positiveQuadratic]
  rw [show -LocalMaximum.gain n (periodize (by omega) u) -
      LocalDFT.positiveQuadratic n (periodize (by omega) u) =
      -(LocalMaximum.gain n (periodize (by omega) u) +
        LocalDFT.positiveQuadratic n (periodize (by omega) u)) by ring, abs_neg]
  exact h

/-- The manuscript's fixed neighborhood and constant in (5.1). -/
theorem objective_coercive {n : ℕ} (hn : 4 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 64)
    (hstep : ∀ j, ‖periodize (by omega) u (j + 1) - periodize (by omega) u j‖ ≤
      η * ‖LocalPhase.regularRoot n - 1‖) :
    energy (by omega) u / 16 ≤ objectiveDeficit (by omega) u := by
  have hr := (abs_le.mp (objective_taylor_bound hn u hfirst hη (by linarith) hstep)).1
  have hc := deficit_coercive (show 3 ≤ n by omega) u hfirst
  change energy (by omega) u / 8 ≤ deficit (by omega) u at hc
  have hm := mul_le_mul_of_nonneg_right hsmall (energy_nonneg (by omega) u)
  nlinarith

theorem energy_le_objective_budget {n : ℕ} (hn : 4 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0)
    {η B : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 64)
    (hstep : ∀ j, ‖periodize (by omega) u (j + 1) - periodize (by omega) u j‖ ≤
      η * ‖LocalPhase.regularRoot n - 1‖)
    (hbudget : objectiveDeficit (by omega) u ≤ B) : energy (by omega) u ≤ 16 * B := by
  have h := objective_coercive hn u hfirst hη hsmall hstep
  linarith

theorem quadratic_le_objective_budget {n : ℕ} (hn : 4 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0)
    {η B : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 64)
    (hstep : ∀ j, ‖periodize (by omega) u (j + 1) - periodize (by omega) u j‖ ≤
      η * ‖LocalPhase.regularRoot n - 1‖)
    (hbudget : objectiveDeficit (by omega) u ≤ B) :
    deficit (by omega) u ≤ (1 + 64 * η) * B := by
  have hr := (abs_le.mp (objective_taylor_bound hn u hfirst hη (by linarith) hstep)).1
  have he := energy_le_objective_budget hn u hfirst hη hsmall hstep hbudget
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 4 * η by positivity)
  nlinarith

/-- Normal energy alone is controlled with the stronger coefficient required
by the pressure argument. This follows from the proved full-frequency weights. -/
theorem normal_mass_coercive {n : ℕ} (hn : 3 ≤ n) (u : Fin n → ℂ)
    (hfirst : centerCoefficient (by omega) u 0 = 0) :
    (((n : ℝ) - 1) / n) / 3 * SchurLiftBounds.meanSquare (normal (by omega) u) ≤
      deficit (by omega) u := by
  rw [deficit_eq_mass hn u hfirst]
  have hv := value_with_firstMass_le hn (normal (by omega) u)
  have hfirst0 : 0 ≤ firstMass (normal (by omega) u) := by
    unfold firstMass
    exact mul_nonneg (by norm_num) (normSq_nonneg _)
  have hs0 : 0 ≤ ((n : ℝ) - 1) / n := by
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hm := mul_nonneg hs0 hfirst0
  have hfree := value_nonneg (freeTangent (by omega) u)
  nlinarith

/-- The actual odd Fourier multiplier, on the actual normal edge sequence.
No exact limiting evaluation of the dual norm is needed for a strict gap. -/
theorem operator_sq_le_deficit_of_mass_le {m : ℕ} (hm : 2048 ≤ 2 * m)
    (u : Fin (2 * m) → ℂ) (hfirst : centerCoefficient (by omega) u 0 = 0)
    (q : Fin (2 * m) → ℝ)
    (hq : SchurLiftBounds.meanSquare q ≤ SchurLiftBounds.meanSquare (normal (by omega) u)) :
    ‖FourierMultiplier.operator (2 * m) q‖ ^ 2 ≤
      3 / 2 * deficit (by omega) u := by
  have hnR : (2048 : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast hm
  have hs : (15 / 16 : ℝ) ≤ (((2 * m : ℕ) : ℝ) - 1) / (2 * m : ℕ) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 * m : ℕ))).2
    linarith
  have hmass := normal_mass_coercive (show 3 ≤ 2 * m by omega) u hfirst
  have hM := SchurLiftBounds.meanSquare_nonneg (normal (show 0 < 2 * m by omega) u)
  have hmultiply := mul_le_mul_of_nonneg_right hs hM
  have hop := SchurOperatorBounds.operator_sup_sq_le (show 0 < 2 * m by omega) q
  have hw := mul_le_mul_of_nonneg_right (SchurWeights.weight_square_sum_le_fifteen_thirtytwo hm)
    (SchurLiftBounds.meanSquare_nonneg q)
  have hbound := hop.trans hw
  nlinarith

theorem operator_normal_sq_le_deficit {m : ℕ} (hm : 2048 ≤ 2 * m)
    (u : Fin (2 * m) → ℂ) (hfirst : centerCoefficient (by omega) u 0 = 0) :
    ‖FourierMultiplier.operator (2 * m) (normal (by omega) u)‖ ^ 2 ≤
      3 / 2 * deficit (by omega) u :=
  operator_sq_le_deficit_of_mass_le hm u hfirst _ le_rfl

/-- The true normal edge variable of the antipodal even center column. -/
def evenNormal {m : ℕ} (hm : 0 < m) (u : Fin (2 * m) → ℂ) : Fin (2 * m) → ℝ := fun j =>
  -(2 * m : ℝ) * (LocalDFT.pairRatio (2 * m)
    (AntipodalDecomposition.evenSequence m (periodize (by omega) u)) j 1).im

theorem evenNormal_mass_le {m : ℕ} (hm : 0 < m) (u : Fin (2 * m) → ℂ) :
    SchurLiftBounds.meanSquare (evenNormal hm u) ≤
      SchurLiftBounds.meanSquare (normal (by omega) u) := by
  have he := AntipodalDecomposition.evenSequence_constraint_energy hm (periodize (by omega) u)
  have hb := AntipodalDecomposition.even_energyB_le hm (periodize (by omega) u) (periodize_periodic _ _)
  have hn := normal_mean_square (show 0 < 2 * m by omega) u
  change SchurLiftBounds.meanSquare (normal (by omega) u) =
    ((2 * m : ℕ) : ℝ) * LocalDFT.energyB (2 * m) (periodize (by omega) u) at hn
  change SchurLiftBounds.meanSquare (evenNormal hm u) =
    (2 * m : ℝ) * LocalDFT.energyB (2 * m)
      (AntipodalDecomposition.evenSequence m (periodize (by omega) u)) at he
  rw [he, hn]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

theorem operator_evenNormal_sq_le_deficit {m : ℕ} (hm : 2048 ≤ 2 * m)
    (u : Fin (2 * m) → ℂ) (hfirst : centerCoefficient (by omega) u 0 = 0) :
    ‖FourierMultiplier.operator (2 * m) (evenNormal (by omega) u)‖ ^ 2 ≤
      3 / 2 * deficit (by omega) u :=
  operator_sq_le_deficit_of_mass_le hm u hfirst _ (evenNormal_mass_le (by omega) u)

theorem operator_normal_sq_le_objective_budget {m : ℕ} (hm : 2048 ≤ 2 * m)
    (u : Fin (2 * m) → ℂ) (hfirst : centerCoefficient (by omega) u 0 = 0)
    {η B : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 64)
    (hstep : ∀ j, ‖periodize (by omega) u (j + 1) - periodize (by omega) u j‖ ≤
      η * ‖LocalPhase.regularRoot (2 * m) - 1‖)
    (hbudget : objectiveDeficit (by omega) u ≤ B) :
    ‖FourierMultiplier.operator (2 * m) (normal (by omega) u)‖ ^ 2 ≤
      3 / 2 * (1 + 64 * η) * B := by
  have h := operator_normal_sq_le_deficit hm u hfirst
  have hb := quadratic_le_objective_budget (show 4 ≤ 2 * m by omega) u hfirst
    hη hsmall hstep hbudget
  nlinarith

/-- An explicit strict pressure gap, with room for the later de-rotation error. -/
theorem operator_normal_pressure_gap {m : ℕ} (hm : 2048 ≤ 2 * m)
    (u : Fin (2 * m) → ℂ) (hfirst : centerCoefficient (by omega) u 0 = 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 1024)
    (hstep : ∀ j, ‖periodize (by omega) u (j + 1) - periodize (by omega) u j‖ ≤
      η * ‖LocalPhase.regularRoot (2 * m) - 1‖)
    (hbudget : objectiveDeficit (by omega) u ≤ 33 * Real.pi ^ 2 / 256) :
    ‖FourierMultiplier.operator (2 * m) (normal (by omega) u)‖ ≤ 15 * Real.pi / 32 := by
  have h := operator_normal_sq_le_objective_budget hm u hfirst hη (by linarith) hstep hbudget
  have he := mul_le_mul_of_nonneg_right hsmall (sq_nonneg Real.pi)
  have hn := norm_nonneg (FourierMultiplier.operator (2 * m) (normal (by omega) u))
  nlinarith [Real.pi_pos]

theorem operator_evenNormal_pressure_gap {m : ℕ} (hm : 2048 ≤ 2 * m)
    (u : Fin (2 * m) → ℂ) (hfirst : centerCoefficient (by omega) u 0 = 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 1024)
    (hstep : ∀ j, ‖periodize (by omega) u (j + 1) - periodize (by omega) u j‖ ≤
      η * ‖LocalPhase.regularRoot (2 * m) - 1‖)
    (hbudget : objectiveDeficit (by omega) u ≤ 33 * Real.pi ^ 2 / 256) :
    ‖FourierMultiplier.operator (2 * m) (evenNormal (by omega) u)‖ ≤ 15 * Real.pi / 32 := by
  have h := operator_evenNormal_sq_le_deficit hm u hfirst
  have hb := quadratic_le_objective_budget (show 4 ≤ 2 * m by omega) u hfirst
    hη (by linarith) hstep hbudget
  have he := mul_le_mul_of_nonneg_right hsmall (sq_nonneg Real.pi)
  have hn := norm_nonneg (FourierMultiplier.operator (2 * m) (evenNormal (by omega) u))
  nlinarith [Real.pi_pos]

/-- Stability of the strict gap under a quantified change of center coordinates. -/
theorem operator_pressure_gap_of_perturbation {m : ℕ} (hm : 2048 ≤ 2 * m)
    (u : Fin (2 * m) → ℂ) (hfirst : centerCoefficient (by omega) u 0 = 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 1024)
    (hstep : ∀ j, ‖periodize (by omega) u (j + 1) - periodize (by omega) u j‖ ≤
      η * ‖LocalPhase.regularRoot (2 * m) - 1‖)
    (hbudget : objectiveDeficit (by omega) u ≤ 33 * Real.pi ^ 2 / 256)
    (q : Fin (2 * m) → ℝ)
    (herror : SchurLiftBounds.meanSquare (q - evenNormal (by omega) u) ≤ Real.pi ^ 2 / 2048) :
    ‖FourierMultiplier.operator (2 * m) q‖ ≤ 31 * Real.pi / 64 := by
  have he := SchurOperatorBounds.operator_sup_sq_le (show 0 < 2 * m by omega)
    (q - evenNormal (by omega) u)
  have hw := mul_le_mul_of_nonneg_right (SchurWeights.weight_square_sum_le_fifteen_thirtytwo hm)
    (SchurLiftBounds.meanSquare_nonneg (q - evenNormal (by omega) u))
  have hh := he.trans hw
  have herr : ‖FourierMultiplier.operator (2 * m) (q - evenNormal (by omega) u)‖ ≤
      Real.pi / 64 := by
    have hn := norm_nonneg (FourierMultiplier.operator (2 * m) (q - evenNormal (by omega) u))
    nlinarith [Real.pi_pos]
  have hbase := operator_evenNormal_pressure_gap hm u hfirst hη hsmall hstep hbudget
  have htri := norm_add_le (FourierMultiplier.operator (2 * m) (q - evenNormal (by omega) u))
    (FourierMultiplier.operator (2 * m) (evenNormal (by omega) u))
  rw [map_sub, sub_add_cancel] at htri
  rw [map_sub] at herr
  linarith

theorem objectiveDeficit_eq_zero_iff {n : ℕ} (hn : 4 ≤ n) (u : Fin n → ℂ)
    (hmean : ∑ j, u j = 0) (hfirst : centerCoefficient (by omega) u 0 = 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 64)
    (hstep : ∀ j, ‖periodize (by omega) u (j + 1) - periodize (by omega) u j‖ ≤
      η * ‖LocalPhase.regularRoot n - 1‖) :
    objectiveDeficit (by omega) u = 0 ↔ u = 0 := by
  constructor
  · intro hz
    have he := objective_coercive hn u hfirst hη hsmall hstep
    have hA := pairEnergy_le_energy (show 0 < n by omega) u
    have hA0 := pairEnergy_nonneg (show 0 < n by omega) u
    apply pairEnergy_zero_forces_zero (show 0 < n by omega) u hmean
    linarith
  · rintro rfl
    have hz : LocalObjective.perturbedVertices n (periodize (by omega) (0 : Fin n → ℂ)) =
        LocalObjective.regularVertices n := by
      funext j
      simp [LocalObjective.perturbedVertices, periodize]
    simp only [objectiveDeficit, hz, sub_self]

/-- The physical gradient is controlled by an actual objective budget, without
assuming an energy budget or a force estimate. The integer K is a free cutoff. -/
theorem gradientError_le_objective_budget {n K : ℕ} (hn : 4 ≤ n) (hK : 0 < K)
    (u : Fin n → ℂ) (hfirst : centerCoefficient (by omega) u 0 = 0)
    {η B : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 64)
    (hstep : ∀ j, ‖periodize (by omega) u (j + 1) - periodize (by omega) u j‖ ≤
      η * ‖LocalPhase.regularRoot n - 1‖)
    (hbudget : objectiveDeficit (by omega) u ≤ B) :
    LocalGradient.gradientError n (periodize (by omega) u) ≤
      2 * (2 * η * (harmonic K : ℝ) + Real.sqrt (32 * B) * Real.sqrt (1 / (K : ℝ))) := by
  have hpair (i : Fin n) (h : ℕ) (hh : h ∈ Finset.Ico 1 n) :
      ‖LocalDFT.pairRatio n (periodize (by omega) u) i h‖ ≤ 2 * η := by
    apply LocalMaximum.pair_ratio_bound ClosedFourier.geometricSine hn _
      (periodize_periodic _ _) hη hstep
    rcases Finset.mem_Ico.mp hh with ⟨hlo, hhi⟩
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr hhi⟩
  have hforce := LocalGradient.gradientError_bound (show 0 < n by omega) hK
    (periodize (by omega) u) (periodize_periodic _ _) (by positivity : 0 ≤ 2 * η)
    (by linarith : 2 * η ≤ 1 / 2) hpair
  have hA := (pairEnergy_le_energy (show 0 < n by omega) u).trans
    (energy_le_objective_budget hn u hfirst hη hsmall hstep hbudget)
  have hs := Real.sqrt_le_sqrt (show 2 * pairEnergy (by omega) u ≤ 32 * B by linarith)
  have hm := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (1 / (K : ℝ)))
  change LocalGradient.gradientError n (periodize (by omega) u) ≤
    2 * (2 * η * (harmonic K : ℝ) + Real.sqrt (2 * pairEnergy (by omega) u) *
      Real.sqrt (1 / (K : ℝ))) at hforce
  linarith

/-- The asymptotic Taylor equality follows from localization and a true
objective budget; bounded quadratic energy is a conclusion. -/
theorem taylor_remainder_tendsto_of_objective_budget {N : ℕ → ℕ}
    (hN : ∀ j, 4 ≤ N j) (u : ∀ j, Fin (N j) → ℂ) {η : ℕ → ℝ} {B : ℝ}
    (hη : Tendsto η atTop (𝓝 0))
    (hgood : ∀ᶠ j in atTop, centerCoefficient (by have := hN j; omega) (u j) 0 = 0 ∧
      0 ≤ η j ∧
      (∀ i, ‖periodize (by have := hN j; omega) (u j) (i + 1) -
        periodize (by have := hN j; omega) (u j) i‖ ≤ η j * ‖LocalPhase.regularRoot (N j) - 1‖) ∧
      objectiveDeficit (by have := hN j; omega) (u j) ≤ B) :
    Tendsto (fun j => objectiveDeficit (by have := hN j; omega) (u j) -
      deficit (by have := hN j; omega) (u j)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hbound : ∀ᶠ j in atTop,
      |objectiveDeficit (by have := hN j; omega) (u j) -
        deficit (by have := hN j; omega) (u j)| ≤ 64 * B * η j := by
    filter_upwards [hgood, hη.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 64))]
      with j hj hsmall
    have he := energy_le_objective_budget (hN j) (u j) hj.1 hj.2.1 hsmall.le hj.2.2.1 hj.2.2.2
    have ht := objective_taylor_bound (hN j) (u j) hj.1 hj.2.1 (by linarith) hj.2.2.1
    have hm := mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hj.2.1)
    nlinarith
  have hlim : Tendsto (fun j => 64 * B * η j) atTop (𝓝 0) := by
    simpa only [mul_zero] using hη.const_mul (64 * B)
  exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hbound hlim

/-- In particular, the actual force is (n-1)w+o(n), uniformly in the vertex.
No force convergence or quadratic energy bound is assumed here. -/
theorem gradientError_tendsto_of_objective_budget {N : ℕ → ℕ}
    (hN : ∀ j, 4 ≤ N j) (u : ∀ j, Fin (N j) → ℂ) {η : ℕ → ℝ} {B : ℝ}
    (hη : Tendsto η atTop (𝓝 0))
    (hgood : ∀ᶠ j in atTop, centerCoefficient (by have := hN j; omega) (u j) 0 = 0 ∧
      0 ≤ η j ∧
      (∀ i, ‖periodize (by have := hN j; omega) (u j) (i + 1) -
        periodize (by have := hN j; omega) (u j) i‖ ≤ η j * ‖LocalPhase.regularRoot (N j) - 1‖) ∧
      objectiveDeficit (by have := hN j; omega) (u j) ≤ B) :
    Tendsto (fun j => LocalGradient.gradientError (N j)
      (periodize (by have := hN j; omega) (u j))) atTop (𝓝 0) := by
  apply LocalGradient.gradientError_tendsto_of_edges (C := 16 * B) hη
  filter_upwards [hgood, hη.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 64))]
    with j hj hsmall
  refine ⟨hN j, periodize_periodic _ _, hj.2.1, hj.2.2.1, ?_⟩
  exact (pairEnergy_le_energy (by have := hN j; omega) (u j)).trans
    (energy_le_objective_budget (hN j) (u j) hj.1 hj.2.1 hsmall.le hj.2.2.1 hj.2.2.2)

theorem eventually_operator_pressure_gap {M : ℕ → ℕ}
    (hMpos : ∀ j, 0 < M j) (hM : Tendsto (fun j => 2 * M j) atTop atTop)
    (u : ∀ j, Fin (2 * M j) → ℂ) (q : ∀ j, Fin (2 * M j) → ℝ)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hgood : ∀ᶠ j in atTop, centerCoefficient (by have := hMpos j; omega) (u j) 0 = 0 ∧
      0 ≤ η j ∧
      (∀ i, ‖periodize (by have := hMpos j; omega) (u j) (i + 1) -
        periodize (by have := hMpos j; omega) (u j) i‖ ≤ η j * ‖LocalPhase.regularRoot (2 * M j) - 1‖) ∧
      objectiveDeficit (by have := hMpos j; omega) (u j) ≤ 33 * Real.pi ^ 2 / 256)
    (herror : Tendsto (fun j => SchurLiftBounds.meanSquare (q j - evenNormal (hMpos j) (u j)))
      atTop (𝓝 0)) :
    ∀ᶠ j in atTop, ‖FourierMultiplier.operator (2 * M j) (q j)‖ ≤ 31 * Real.pi / 64 := by
  filter_upwards [hgood, hM.eventually (eventually_ge_atTop 2048),
    hη.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 1024)),
    herror.eventually (gt_mem_nhds (show 0 < Real.pi ^ 2 / 2048 by positivity))]
    with j hj hn hs he
  exact operator_pressure_gap_of_perturbation hn (u j) hj.1 hj.2.1 hs.le hj.2.2.1 hj.2.2.2 (q j) he.le

end StructuralNote.PressureCoercivity

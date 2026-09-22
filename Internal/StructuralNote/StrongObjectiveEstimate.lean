import StructuralNote.CanonicalNonlinearError

/-! The actual objective estimate of Lemma 6.3, with its canonical residual and all analytic inputs discharged. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.StrongObjectiveEstimate

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open PolarAngleControl NormalizedPolarRepresentation ExtremalPolarCenter
open SchurSpectrum SchurLift SchurLiftBounds FiniteFourierLift FourierMultiplier DiscreteEnergy
open ActualObjectiveLoss ActualAngularLoss CanonicalNonlinearError

def residualEnergy {n : ℕ} (hn : 0 < n) (c : Points n) : ℝ :=
  pairEnergy hn (c - canonicalLift (constraint hn c))

theorem actual_constraint_antiperiodic {m : ℕ} (hm : 0 < m) (c : Points (2 * m))
    (hc : HalfPeriodic hm c) : FiniteBox.Antiperiodic hm (constraint (by omega) c) := by
  intro j
  have hd : difference (by omega) c (halfTurn hm j) = difference (by omega) c j := by
    unfold difference
    rw [← halfTurn_successor, hc, hc]
  unfold constraint
  rw [frame_halfTurn, hd]
  simp only [map_neg, neg_mul, Complex.neg_re, mul_neg]

theorem potential_residual_bound {m : ℕ} (hm : 2 ≤ m) (c : Points (2 * m))
    (hc : HalfPeriodic (by omega) c) (hmean : ∑ j, c j = 0) :
    pairPotential (by omega) c ≤ normalizedBoxEnergy (operator (2 * m)) (constraint (by omega) c) -
      residualEnergy (by omega) c / 64 := by
  let q := constraint (show 0 < 2 * m by omega) c
  let v := c - canonicalLift q
  have hq := actual_constraint_antiperiodic (by omega) c hc
  have hv : HalfPeriodic (by omega) v := by
    intro j
    simp only [v, Pi.sub_apply, hc j, canonicalLift_halfTurn hm q hq]
  have hvm : ∑ j, v j = 0 := by
    simp only [v, Pi.sub_apply, Finset.sum_sub_distrib, hmean,
      canonicalLift_mean_zero (show 0 < 2 * m by omega), sub_self]
  have hvq : constraint (by omega) v = 0 := by
    rw [show v = c - canonicalLift q from rfl, constraint_sub (by omega),
      constraint_canonicalLift (by omega)]
    exact sub_self q
  have he := geometric_orthogonal_decomposition hm q hq v hv hvq
  have hh := kernel_coercivity hm v hv hvm hvq
  have hsum : canonicalLift q + v = c := by dsimp [v]; abel
  rw [hsum] at he
  change pairPotential (by omega) c ≤ normalizedBoxEnergy (operator (2 * m)) q - pairEnergy (by omega) v / 64
  linarith only [he, hh]

def objectiveConstant : ℝ :=
  8320 * Real.pi ^ 4 * (65 * Real.pi ^ 2) ^ 2 +
    4096 * (320 * Real.pi ^ 2) * Real.pi ^ 2 * (65 * Real.pi ^ 2)

/-- In the very same coordinates that satisfy the strict actual pressure gap,
the full radial, angular, and free-center losses have fixed positive coefficients. -/
theorem diameter_sequence_strong_objective {M : ℕ → ℕ} (hM2 : ∀ k, 2 ≤ M k)
    (hM : Tendsto M atTop atTop) (z : ∀ k, Points (2 * M k))
    (hz : ∀ k, ExtremalNormalization.DiameterExtremal (z k)) :
    ∃ (σ : ∀ k, Equiv.Perm (Fin (2 * M k))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ), Tendsto η atTop (𝓝 0) ∧
      (∀ᶠ k in atTop, NormalizedRelativeEdgeModel (z k) (σ k) (α k) (β k) (u k) (η k) ∧
        CenterBounds (m := M k) (by have := hM2 k; omega) (β k) (u k) ∧
        ‖operator (2 * M k) (polarConstraint (by have := hM2 k; omega) (β k) (u k))‖ ≤ 31 * Real.pi / 64) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        Real.log (discriminant (z k)) - Real.log (discriminant (SignedPressureAngular.root (2 * M k))) ≤
          normalizedBoxEnergy (operator (2 * M k)) (polarConstraint (by have := hM2 k; omega) (β k) (u k)) -
          residualEnergy (by have := hM2 k; omega) (polarCenter (M k) (β k) (u k)) / 128 -
          realEnergy (by have := hM2 k; omega) (normalizedAngle (M k) (u k)) / 4 -
          (1 - ε) * ActualRadialPrice.actualMass (M k) ‖β k‖ (u k) +
          objectiveConstant / ((2 * M k : ℕ) : ℝ) ^ 2 := by
  obtain ⟨σ, α, β, u, η, hη, _, hgood⟩ := ActualPressureGap.diameter_sequence_pressure_gap hM2 hM z hz
  refine ⟨σ, α, β, u, η, hη, hgood.mono (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.2⟩), ?_⟩
  intro ε hε
  have hN : Tendsto (fun k => 2 * M k) atTop atTop := tendsto_atTop_mono (fun _ => by omega) hM
  have hcoef := coefficient_tendsto hN (coordinateBudget_tendsto hN hη) (65 * Real.pi ^ 2) (320 * Real.pi ^ 2)
  filter_upwards [hgood, eventual_model_objective_loss hM hη hε,
    (sizeBudget_tendsto hN).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 16),
    hcoef.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 128)] with k hk hobj hs hcoef
  have hm2 := hM2 k
  have hE := SignedPressureRemainder.model_energy_le (by omega) hk.1 hk.2.2.1 hk.2.2.2.1
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
  rw [constantTerm_eq] at herr
  change _ ≤ objectiveConstant / ((2 * M k : ℕ) : ℝ) ^ 2 + _ at herr
  change pairPotential (by omega) (polarCenter (M k) (β k) (u k)) ≤
    normalizedBoxEnergy (operator (2 * M k)) (polarConstraint (by omega) (β k) (u k)) -
      pairEnergy (by omega) (polarCenter (M k) (β k) (u k) - canonicalLift (polarConstraint (by omega) (β k) (u k))) / 64 at hpot
  unfold residualEnergy
  dsimp only [polarConstraint] at herr hactual hpot hmul ⊢
  dsimp only [quartic] at herr
  nlinarith only [herr, hactual, hpot, hmul]

end StructuralNote.StrongObjectiveEstimate

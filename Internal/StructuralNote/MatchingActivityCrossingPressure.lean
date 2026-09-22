import StructuralNote.MatchingActivitySaturation
import StructuralNote.SolDiagonalKernelGrowth

/-! The scalar-gap and pointwise-pressure part of the crossing-activity argument.
The gap is retained in the signed crossing estimate instead of being discarded
when the finite-box support inequality is applied. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.MatchingActivityCrossingPressure

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open FourierMultiplier FiniteFourierLift ExtremalPolarCenter NormalizedPolarRepresentation
open SignedCrossingPressure SignedPressureRemainder ActualCrossingGeometry ActualSignedAngular
open ActualSignedPressure
open PolarAngleControl PolarRepresentation SolScalarGap
open SchurSpectrum SchurLift SchurLiftBounds DiscreteEnergy StrongObjectiveEstimate
open ActualObjectiveLoss ActualAngularLoss CanonicalNonlinearError ActualPressureAbsorption
open PressureAngularAbsorption SinglePressureEstimate SolDiagonalKernelGrowth
open StrongBudgetConsequences StrongPointwiseNormal StrongPointwiseCoordinates
open StrongPointwiseSmallness MatchingActivityRadialActual MatchingActivitySaturation

/-- The signed crossing estimate with the scalar gap left visible. -/
theorem model_finite_pressure_with_gap {m : ℕ} (hm : 0 < m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z)
    (hb : ∀ j, radialDeficit m β u j + radialDeficit m β u (finRotate (2 * m) j) ≤ 1 / 2)
    (hφ : ∀ j, |Real.pi / (2 * m) +
      (normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j) / 2| ≤ 1 / 2)
    {K : ℝ} (hK : ‖operator (2 * m) (polarConstraint hm β u)‖ ≤ K) :
    G hm (polarConstraint hm β u) +
        normalizedBoxEnergy (operator (2 * m)) (polarConstraint hm β u) ≤
      FiniteBox.B hm +
        K / ((2 * m) * Real.sin (Real.pi / (2 * m))) * radialMass m β u +
        actualAngularSum hm β u + actualRemainder hm β u := by
  have hb0 (j : Fin (2 * m)) : 0 ≤ radialDeficit m β u j :=
    sub_nonneg.mpr (model_radius_le_one hm h hz j)
  have hcross := actual_rotated_crossing hm h hz
  have hg (j : Fin (2 * m)) : |operator (2 * m) (polarConstraint hm β u) j| ≤ K := by
    have hh := norm_le_pi_norm (operator (2 * m) (polarConstraint hm β u)) j
    rw [Real.norm_eq_abs] at hh
    exact hh.trans hK
  have hp := finite_signed_pressure (show 2 ≤ 2 * m by omega) (finRotate (2 * m))
    (fun j => normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j)
    (radialDeficit m β u) (operator (2 * m) (polarConstraint hm β u))
    (fun j => rotatedCenter m β u j j)
    (fun j => rotatedCenter m β u j (successor (by omega) j)) hb0 hb
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hφ)
    (fun j => by
      simpa only [finRotate_eq_successor (show 2 ≤ 2 * m by omega), Nat.cast_mul,
        Nat.cast_ofNat] using (hcross j).1)
    (fun j => by
      simpa only [finRotate_eq_successor (show 2 ≤ 2 * m by omega), Nat.cast_mul,
        Nat.cast_ofNat] using (hcross j).2) hg
  have hn (j : Fin (2 * m)) : normalComponent (2 * m) (Real.pi / ((2 * m : ℕ) : ℝ))
      (rotatedCenter m β u j j) (rotatedCenter m β u j (successor (by omega) j)) =
      polarConstraint hm β u j := by
    rw [rotatedCenter, rotatedCenter, normalComponent_eq_normal (by omega)]
    exact congrFun (ActualPressureGap.polarConstraint_eq_normal hm β u).symm j
  simp_rw [hn] at hp
  have ha : actualAngularSum hm β u =
      (Real.pi / (2 * m)) / (2 * Real.sin (Real.pi / (2 * m))) *
        (∑ j, |operator (2 * m) (polarConstraint hm β u) j| *
          (normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j)) +
      (1 / (4 * Real.sin (Real.pi / (2 * m)))) *
        (∑ j, operator (2 * m) (polarConstraint hm β u) j *
          (rotatedCenter m β u j (successor (by omega) j) + rotatedCenter m β u j j).im *
          (normalizedAngle m u (successor (by omega) j) - normalizedAngle m u j)) := by
    simp only [actualAngularSum, actual_tangentialSum hm β u]
  rw [ha]
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hp ⊢
  have hident :
      G hm (polarConstraint hm β u) +
          normalizedBoxEnergy (operator (2 * m)) (polarConstraint hm β u) =
        FiniteBox.B hm +
          ((∑ j, polarConstraint hm β u j *
              operator (2 * m) (polarConstraint hm β u) j) -
            FiniteBox.amplitude (2 * m) *
              ∑ j, |operator (2 * m) (polarConstraint hm β u) j|) / (2 * m) := by
    unfold G V potentialAverage normalizedBoxEnergy boxEnergy finitePairing
    simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    ring
  rw [hident]
  unfold actualRemainder radialMass
  linarith only [hp]

/-- Remainder absorption preserves the scalar gap with the same constants as
the established single-pressure estimate. -/
theorem model_pressure_absorbed_with_gap {m : ℕ} (hm : 8 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hη : η ≤ 1 / 1024)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hJ : objective (regular (2 * m)) - objective (z ∘ σ) ≤ 33 * Real.pi ^ 2 / 256)
    (hc : CenterBounds (m := m) (by omega) β u)
    (herr : meanSquare (polarConstraint (by omega) β u -
      ExtremalSchurGap.evenConstraint m u) ≤ Real.pi ^ 2 / 2048)
    (hK : ‖operator (2 * m) (polarConstraint (by omega) β u)‖ ≤ 31 * Real.pi / 64)
    (hS : sizeBudget (2 * m) ≤ 1 / 256)
    (hN : 512 * Real.pi ^ 2 / (2 * m) ≤ 1 / 2)
    (hE : 4 * (31 * Real.pi / 64) * Real.pi ^ 2 / (2 * m) ≤ 1 / 16)
    (hR : radialErrorCoefficient (2 * m) (31 * Real.pi / 64) ≤ 1 / 8)
    (hD : residualCoefficient (2 * m) ≤ 1 / 256) :
    G (m := m) (by omega) (polarConstraint (m := m) (by omega) β u) +
        normalizedBoxEnergy (operator (2 * m)) (polarConstraint (by omega) β u) ≤
      FiniteBox.B (by omega : 0 < m) + 5 * radialMass m β u / 8 +
        residualEnergy (by omega) (polarCenter m β u) / 256 +
        realEnergy (by omega) (normalizedAngle m u) / 8 +
        pressureConstant / (2 * m : ℝ) ^ 2 := by
  have hsmall := model_small_crossing_parameters hm h hη hz hJ hS hN
  have hp := model_finite_pressure_with_gap (show 0 < m by omega) h hz.1
    hsmall.1 hsmall.2 hK
  have ha := model_angular_sum_le (show 2 ≤ m by omega) h hη hJ hc herr hK
  have hmass := model_constraint_mass (show 2 ≤ m by omega) h hη hJ herr
  have hy := angular_budget_absorption (show 3 ≤ 2 * m by omega)
    (polarCenter m β u) (polarConstraint (by omega) β u) (normalizedAngle m u)
    hc.mean_zero hmass hc.energy
  have hr := model_remainder_le hm h hη hz hJ hc (hS.trans (by norm_num)) hK
  have hτ : 0 ≤ radialMass m β u := by
    unfold radialMass
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun j _ => sub_nonneg.mpr
      (PolarRepresentation.model_radius_le_one (by omega) h hz.1 j)
  have hrad := radial_price_le_half (show 16 ≤ 2 * m by omega)
    (le_refl (31 * Real.pi / 64)) hτ
  have hmulD := mul_le_mul_of_nonneg_right hD
    (pairEnergy_nonneg (show 0 < 2 * m by omega)
      (polarCenter m β u - SchurLift.canonicalLift (polarConstraint (by omega) β u)))
  have hmulE := mul_le_mul_of_nonneg_right hE
    (pairEnergy_nonneg (show 0 < 2 * m by omega) (fun j => (normalizedAngle m u j : ℂ)))
  have hmulR := mul_le_mul_of_nonneg_right hR hτ
  simp only [actualAngularBudget, Nat.cast_mul, Nat.cast_ofNat] at ha hy hrad hmulD hmulE
  unfold residualEnergy
  simp only [radialErrorCoefficient, Nat.cast_mul, Nat.cast_ofNat] at hmulR
  have hcst : angularConstant / (2 * m : ℝ) ^ 2 +
      9 * (31 * Real.pi / 64) * Real.pi ^ 4 / (4 * (2 * m : ℝ) ^ 2) =
      pressureConstant / (2 * m : ℝ) ^ 2 := by
    unfold pressureConstant
    ring
  change 4 * (31 * Real.pi / 64) * Real.pi ^ 2 / (2 * m) *
    realEnergy (by omega) (normalizedAngle m u) ≤
      1 / 16 * realEnergy (by omega) (normalizedAngle m u) at hmulE
  dsimp only [polarConstraint] at hp ha hy hr hmulD ⊢
  linarith only [hp, ha, hy, hr, hrad, hmulD, hmulE, hmulR, hcst]

theorem eventual_model_pressure_absorbed_with_gap {M : ℕ → ℕ}
    (hM : Tendsto M atTop atTop) :
    ∀ᶠ k in atTop, ∀ (z : Points (2 * M k)) (σ : Equiv.Perm (Fin (2 * M k)))
      (α β : ℂ) (u : ℕ → ℂ) (η : ℝ) (hm : 0 < M k),
      NormalizedRelativeEdgeModel z σ α β u η → η ≤ 1 / 1024 →
      ExtremalNormalization.DiameterExtremal z →
      objective (regular (2 * M k)) - objective (z ∘ σ) ≤ 33 * Real.pi ^ 2 / 256 →
      CenterBounds hm β u →
      meanSquare (polarConstraint hm β u - ExtremalSchurGap.evenConstraint (M k) u) ≤
        Real.pi ^ 2 / 2048 →
      ‖operator (2 * M k) (polarConstraint hm β u)‖ ≤ 31 * Real.pi / 64 →
      G hm (polarConstraint hm β u) +
          normalizedBoxEnergy (operator (2 * M k)) (polarConstraint hm β u) ≤
        FiniteBox.B hm + 5 * radialMass (M k) β u / 8 +
          residualEnergy (by omega) (polarCenter (M k) β u) / 256 +
          realEnergy (by omega) (normalizedAngle (M k) u) / 8 +
          pressureConstant / (2 * M k : ℝ) ^ 2 := by
  have hN : Tendsto (fun k => 2 * M k) atTop atTop :=
    tendsto_atTop_mono (fun _ => by omega) hM
  have hb := ((tendsto_const_div_atTop_nhds_zero_nat (512 * Real.pi ^ 2)).comp hN).eventually_le_const
    (by norm_num : (0 : ℝ) < 1 / 2)
  have he := ((tendsto_const_div_atTop_nhds_zero_nat
    (4 * (31 * Real.pi / 64) * Real.pi ^ 2)).comp hN).eventually_le_const
      (by norm_num : (0 : ℝ) < 1 / 16)
  filter_upwards [hM.eventually_ge_atTop 8,
    (sizeBudget_tendsto hN).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 256), hb, he,
    (radialErrorCoefficient_tendsto hN (31 * Real.pi / 64)).eventually_le_const
      (by norm_num : (0 : ℝ) < 1 / 8),
    (residualCoefficient_tendsto hN).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 256)]
    with k hm8 hs hb he hr hd
  intro z σ α β u η hm h hη hz hJ hc herr hK
  exact model_pressure_absorbed_with_gap hm8 h hη hz hJ hc herr hK hs
    (by simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using hb)
    (by simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using he) hr hd

/-- Proposition 6.4 with its scalar-gap term restored, for a sequence of actual
diameter maximizers. All estimates use one common coordinate choice. -/
theorem diameter_sequence_scalar_gap {M : ℕ → ℕ} (hM2 : ∀ k, 2 ≤ M k)
    (hM : Tendsto M atTop atTop) (z : ∀ k, Points (2 * M k))
    (hz : ∀ k, ExtremalNormalization.DiameterExtremal (z k)) :
    ∃ (σ : ∀ k, Equiv.Perm (Fin (2 * M k))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ), Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ k in atTop,
        NormalizedRelativeEdgeModel (z k) (σ k) (α k) (β k) (u k) (η k) ∧
        CenterBounds (m := M k) (by have := hM2 k; omega) (β k) (u k) ∧
        η k ≤ 1 / 1024 ∧
        meanSquare (polarConstraint (m := M k) (by have := hM2 k; omega) (β k) (u k)) ≤
          65 * Real.pi ^ 2 ∧
        ‖operator (2 * M k)
          (polarConstraint (m := M k) (by have := hM2 k; omega) (β k) (u k))‖ ≤ 31 * Real.pi / 64 ∧
        G (m := M k) (by have := hM2 k; omega)
            (polarConstraint (m := M k) (by have := hM2 k; omega) (β k) (u k)) +
          radialMass (M k) (β k) (u k) +
          residualEnergy (by have := hM2 k; omega) (polarCenter (M k) (β k) (u k)) +
          realEnergy (by have := hM2 k; omega) (normalizedAngle (M k) (u k)) ≤
            budgetConstant / ((2 * M k : ℕ) : ℝ) ^ 2 := by
  obtain ⟨σ, α, β, u, η, hη, _, hgood⟩ :=
    ActualPressureGap.diameter_sequence_pressure_gap hM2 hM z hz
  refine ⟨σ, α, β, u, η, hη, ?_⟩
  have hN : Tendsto (fun k => 2 * M k) atTop atTop :=
    tendsto_atTop_mono (fun _ => by omega) hM
  have hcoef := coefficient_tendsto hN (coordinateBudget_tendsto hN hη)
    (65 * Real.pi ^ 2) (320 * Real.pi ^ 2)
  filter_upwards [hgood,
    eventual_model_objective_loss hM hη (by norm_num : (0 : ℝ) < 1 / 8),
    (sizeBudget_tendsto hN).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 16),
    hcoef.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 128),
    eventual_model_pressure_absorbed_with_gap hM, hN.eventually_ge_atTop 256]
    with k hk hobj hs hcoef hpressure hn256
  have hm2 := hM2 k
  have hE := model_energy_le (by omega) hk.1 hk.2.2.1 hk.2.2.2.1
  have hp := model_polar_bounds hm2 hk.1 hE (hs.trans (by norm_num))
  have hβ := (ExtremalScaleBound.model_matching_deficit_bound hm2 hk.1
    (by linarith [hk.2.2.1]) (hz k) hE).1
  have hcoords := model_coordinate_bounds hm2 hk.1 hp hβ hs
  have hmass := model_constraint_mass hm2 hk.1 hk.2.2.1 hk.2.2.2.1 hk.2.2.2.2.1
  have hδ : 0 ≤ coordinateBudget (2 * M k) (η k) := by
    unfold coordinateBudget
    have := hk.1.error_nonneg
    positivity
  have herr := nonlinear_error_le (show 3 ≤ 2 * M k by omega)
    (polarCenter (M k) (β k) (u k))
    (polarConstraint (by omega) (β k) (u k)) hk.2.1.mean_zero hδ hmass hk.2.1.energy
    hcoords.2.2.1
  have hpot := potential_residual_bound hm2 (polarCenter (M k) (β k) (u k))
    hk.2.1.half_periodic hk.2.1.mean_zero
  have hactual := hobj (z k) (σ k) (α k) (β k) (u k) (by omega)
    hk.1 (hz k) hE
  have hmul := mul_le_mul_of_nonneg_right hcoef
    (pairEnergy_nonneg (show 0 < 2 * M k by omega)
      (polarCenter (M k) (β k) (u k) -
        canonicalLift (polarConstraint (by omega) (β k) (u k))))
  have hpres := hpressure (z k) (σ k) (α k) (β k) (u k) (η k) (by omega)
    hk.1 hk.2.2.1 (hz k) hk.2.2.2.1 hk.2.1 hk.2.2.2.2.1 hk.2.2.2.2.2
  rw [constantTerm_eq] at herr
  change _ ≤ objectiveConstant / ((2 * M k : ℕ) : ℝ) ^ 2 + _ at herr
  have hstrong :
      Real.log (discriminant (z k)) - ((2 * M k : ℕ) : ℝ) * Real.log (2 * M k : ℕ) ≤
        FiniteBox.B (m := M k) (by omega) -
          G (m := M k) (by omega) (polarConstraint (m := M k) (by omega) (β k) (u k)) -
          radialMass (M k) (β k) (u k) / 4 -
          residualEnergy (by omega) (polarCenter (M k) (β k) (u k)) / 256 -
          realEnergy (by omega) (normalizedAngle (M k) (u k)) / 8 +
          comparisonConstant / ((2 * M k : ℕ) : ℝ) ^ 2 := by
    rw [SinglePressureEstimate.actualMass_eq_radialMass,
      SinglePressureEstimate.root_log_discriminant (by omega)] at hactual
    simp only [Nat.cast_mul, Nat.cast_ofNat] at herr hactual hmul ⊢
    dsimp only [residualEnergy, polarConstraint, quartic, comparisonConstant] at herr hpot hpres ⊢
    dsimp only [polarConstraint] at hmul
    rw [add_div]
    linarith only [herr, hactual, hpot, hmul, hpres]
  have hlo := WholeBoxLowerBound.diameterExtremal_log_lower hn256 (z k) (hz k)
  have hG0 : 0 ≤ G (m := M k) (by omega)
      (polarConstraint (m := M k) (by omega) (β k) (u k)) :=
    gap_nonneg (by omega) _
  have hτ : 0 ≤ radialMass (M k) (β k) (u k) := by
    unfold radialMass
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun j _ => sub_nonneg.mpr
      (PolarRepresentation.model_radius_le_one (by omega) hk.1 (hz k).1 j)
  have hD : 0 ≤ residualEnergy (by omega) (polarCenter (M k) (β k) (u k)) :=
    pairEnergy_nonneg (by omega) _
  have hθ : 0 ≤ realEnergy (by omega) (normalizedAngle (M k) (u k)) :=
    pairEnergy_nonneg (by omega) _
  have hcst : budgetConstant / ((2 * M k : ℕ) : ℝ) ^ 2 =
      256 * (comparisonConstant / ((2 * M k : ℕ) : ℝ) ^ 2 +
        1000000 / ((2 * M k : ℕ) : ℝ) ^ 2) := by
    unfold budgetConstant
    ring
  refine ⟨hk.1, hk.2.1, hk.2.2.1, hmass, hk.2.2.2.2.2, ?_⟩
  rw [hcst]
  linarith only [hstrong, hlo, hG0, hτ, hD, hθ]

def HasScalarGapCoordinates (m : ℕ) (z : Points (2 * m)) : Prop :=
  ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
    NormalizedRelativeEdgeModel z σ α β u η ∧ CenterBounds hm β u ∧
    η ≤ 1 / 1024 ∧ meanSquare (polarConstraint hm β u) ≤ 65 * Real.pi ^ 2 ∧
    ‖operator (2 * m) (polarConstraint hm β u)‖ ≤ 31 * Real.pi / 64 ∧
    G hm (polarConstraint hm β u) + radialMass m β u +
      residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2

/-- The scalar gap is an unconditional conclusion for every sufficiently large
actual even-order maximizer. -/
theorem eventual_diameter_scalar_gap :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z → HasScalarGapCoordinates m z := by
  by_contra h
  push Not at h
  choose M hMk z hz hbad using fun k : ℕ => h (k + 2)
  have hM2 (k : ℕ) : 2 ≤ M k := by
    have := hMk k
    omega
  have hM : Tendsto M atTop atTop :=
    tendsto_atTop_mono (fun k => by have := hMk k; omega : ∀ k, k ≤ M k) tendsto_id
  obtain ⟨σ, α, β, u, η, _, hg⟩ := diameter_sequence_scalar_gap hM2 hM z hz
  obtain ⟨k, hk⟩ := hg.exists
  apply hbad k
  refine ⟨(by have := hM2 k; omega), σ k, α k, β k, u k, η k, ?_⟩
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hk

/-- On one common set of actual coordinates, every matching constraint is
saturated and every pressure coordinate has a uniform scaled margin. This is
the pressure input for the later KKT edge-stress argument. -/
theorem eventual_diameter_matching_pressure_margin (L : ℝ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ)
        (u : ℕ → ℂ) (η : ℝ),
        NormalizedRelativeEdgeModel z σ α β u η ∧ CenterBounds hm β u ∧
        meanSquare (polarConstraint hm β u) ≤ 65 * Real.pi ^ 2 ∧
        ‖operator (2 * m) (polarConstraint hm β u)‖ ≤ 31 * Real.pi / 64 ∧
        G hm (polarConstraint hm β u) + radialMass m β u +
          residualEnergy (by omega) (polarCenter m β u) +
          realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 ∧
        PointwiseBounds hm β u ∧
        (∀ i : Fin m, modelRadii m β u i = 1) ∧
        ∀ j : Fin (2 * m),
          L < (2 * m : ℝ) * |operator (2 * m) (polarConstraint hm β u) j| ∧
          operator (2 * m) (polarConstraint hm β u) j ≠ 0 := by
  obtain ⟨m₀, h₀⟩ := eventual_diameter_scalar_gap
  obtain ⟨m₁, h₁⟩ := eventually_atTop.1 strong_scale_small
  have hnormalScale : ∀ᶠ m : ℕ in atTop, normalConstant / (2 * m : ℝ) ≤ 1 := by
    have hN : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
      tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
    have hh := ((tendsto_const_div_atTop_nhds_zero_nat normalConstant).comp hN).eventually_le_const
      (by norm_num : (0 : ℝ) < 1)
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using hh
  obtain ⟨m₂, h₂⟩ := eventually_atTop.1 hnormalScale
  obtain ⟨m₃, h₃⟩ := eventually_atTop.1 eventual_coefficients_small
  obtain ⟨m₄, h₄⟩ := eventually_atTop.1 eventual_radial_derivative_scales
  obtain ⟨m₅, h₅⟩ := eventually_atTop.1
    (scaled_potential_eventually budgetConstant (max L 0))
  let mstar := max (max (max m₀ m₁) (max m₂ m₃)) (max m₄ (max m₅ 8))
  refine ⟨mstar, ?_⟩
  intro m hm z hz
  have hm₀ : m₀ ≤ m := by dsimp [mstar] at hm; omega
  have hm₁ : m₁ ≤ m := by dsimp [mstar] at hm; omega
  have hm₂ : m₂ ≤ m := by dsimp [mstar] at hm; omega
  have hm₃ : m₃ ≤ 2 * m := by dsimp [mstar] at hm; omega
  have hm₄ : m₄ ≤ 2 * m := by dsimp [mstar] at hm; omega
  have hm₅ : m₅ ≤ m := by dsimp [mstar] at hm; omega
  have hm8 : 8 ≤ m := by dsimp [mstar] at hm; omega
  obtain ⟨hmp, σ, α, β, u, η, hmodel, hc, _, hq, hpressure, hcombined⟩ :=
    h₀ m hm₀ z hz
  have hG0 : 0 ≤ G hmp (polarConstraint hmp β u) := gap_nonneg hmp _
  have hτ : 0 ≤ radialMass m β u := by
    unfold radialMass
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun j _ => sub_nonneg.mpr
      (PolarRepresentation.model_radius_le_one hmp hmodel hz.1 j)
  have hD : 0 ≤ residualEnergy (by omega) (polarCenter m β u) :=
    pairEnergy_nonneg (by omega) _
  have hE : 0 ≤ realEnergy (by omega) (normalizedAngle m u) :=
    pairEnergy_nonneg (by omega) _
  have hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 := by
    linarith only [hcombined, hG0]
  have hGupper : G hmp (polarConstraint hmp β u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 := by
    linarith only [hcombined, hτ, hD, hE]
  have hscale := h₁ m hm₁
  have hnormal := model_normal_bound hm8 hmodel hz.1 hc hq hbudget
    hscale.1 hscale.2.1 hscale.2.2
  have hbounds := model_pointwise_coordinates (by omega) hmodel hz.1 hc hq hbudget
    (h₂ m hm₂) hnormal
  have hs := h₃ (2 * m) hm₃
  have hd := h₄ (2 * m) hm₄
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs hd
  have hsat := model_matching_saturated hm8 hmodel hz hpressure hbudget hbounds
    hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2 hd.2.1 hd.2.2 hd.1
  have hmargin := h₅ m hm₅ hmp (polarConstraint hmp β u) hGupper
  refine ⟨hmp, σ, α, β, u, η, hmodel, hc, hq, hpressure, hcombined, hbounds,
    hsat, ?_⟩
  intro j
  have hj := hmargin j
  refine ⟨(lt_of_le_of_lt (le_max_left L 0) hj), ?_⟩
  intro hzj
  rw [hzj, abs_zero, mul_zero] at hj
  exact (not_lt_of_ge (le_max_right L 0)) hj

end StructuralNote.MatchingActivityCrossingPressure

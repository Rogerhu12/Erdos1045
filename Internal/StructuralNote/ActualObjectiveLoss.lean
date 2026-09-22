import StructuralNote.ActualAngularLoss

/-! A genuine objective inequality retaining only explicit quartic and center energy errors. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.ActualObjectiveLoss

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open PolarAngleControl NormalizedPolarRepresentation ExtremalPolarCenter
open GeometricRelativeRemainder SignedPressureAngular AngularFirstEnergy ActualAngularFirst
open AngularObjectiveCurvature SchurSpectrum DiscreteEnergy ActualAngularLoss
open NormalizedRadialPrice ActualRadialPrice

theorem fourthEnergy_nonneg {n : ℕ} (hn : 0 < n) (c : Points n) :
    0 ≤ AntipodalLog.fourthEnergy n (periodize hn c) := by
  rw [fourthEnergy_eq_chord_sum]
  positivity

theorem quadratic_eq_pairPotential {n : ℕ} (hn : 0 < n) (c : Points n) :
    quadratic (root n) c = pairPotential hn c := by
  rw [AntipodalLog.pairPotential_eq_real_sum,
    cyclic_pair_sum hn c (fun z => (z ^ 2).re) (by simp)]
  rfl

theorem quartic_objective_upper {m : ℕ} (hm : 0 < m) (c : Points (2 * m))
    (hc : HalfPeriodic hm c) (hs : ∀ p, ‖quotient c (root (2 * m)) p‖ ≤ 1 / 2) :
    Real.log (discriminant (configuration (root (2 * m)) c)) ≤
      Real.log (discriminant (root (2 * m))) + pairPotential (by omega) c +
        AntipodalLog.fourthEnergy (2 * m) (periodize (by omega) c) := by
  let e := Equiv.ofBijective (FourierMultiplier.halfTurn hm) (SchurLift.halfTurn_involutive hm).bijective
  have hpair := AntipodalLog.sum_quartic_bound (Equiv.prodCongr e e) (quotient c (root (2 * m)))
    (quotient_antipodal e (root (2 * m)) c (root_halfTurn hm) hc) hs
  have hgain := gain_eq_sum (root (2 * m)) c (root_injective (by omega))
    (fun p => (hs p).trans_lt (by norm_num))
  have hpot := quadratic_eq_pairPotential (show 0 < 2 * m by omega) c
  rw [← fourthEnergy_eq_chord_sum (show 0 < 2 * m by omega) c] at hpair
  unfold quadratic at hpot
  unfold gain at hgain
  have hh := (abs_le.mp hpair).2
  linarith only [hh, hpot, hgain]

theorem angular_error_young {n : ℕ} (hn : 0 < n) (c : Points n) (θ : Fin n → ℝ) :
    8 * Real.sqrt (AntipodalLog.fourthEnergy n (periodize hn c) + ‖c‖ ^ 2 * pairEnergy hn c) *
        Real.sqrt (realEnergy hn θ) ≤
      64 * (AntipodalLog.fourthEnergy n (periodize hn c) + ‖c‖ ^ 2 * pairEnergy hn c) +
        realEnergy hn θ / 4 := by
  have hH : 0 ≤ AntipodalLog.fourthEnergy n (periodize hn c) + ‖c‖ ^ 2 * pairEnergy hn c :=
    add_nonneg (fourthEnergy_nonneg hn c) (mul_nonneg (sq_nonneg _) (pairEnergy_nonneg hn c))
  have hE : 0 ≤ realEnergy hn θ := pairEnergy_nonneg hn _
  have hh := sq_nonneg (8 * Real.sqrt (AntipodalLog.fourthEnergy n (periodize hn c) +
    ‖c‖ ^ 2 * pairEnergy hn c) - Real.sqrt (realEnergy hn θ) / 2)
  nlinarith only [hh, Real.sq_sqrt hH, Real.sq_sqrt hE]

theorem eventual_model_objective_loss {M : ℕ → ℕ} (hM : Tendsto M atTop atTop)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ (z : Points (2 * M k)) (σ : Equiv.Perm (Fin (2 * M k)))
      (α β : ℂ) (u : ℕ → ℂ) (hm : 0 < M k),
      NormalizedRelativeEdgeModel z σ α β u (η k) → ExtremalNormalization.DiameterExtremal z →
      ExtremalEnergyBound.totalEnergy (2 * M k) u ≤ 32 * Real.pi ^ 2 →
      Real.log (discriminant z) - Real.log (discriminant (root (2 * M k))) ≤
        pairPotential (by omega) (polarCenter (M k) β u) +
        65 * AntipodalLog.fourthEnergy (2 * M k) (periodize (by omega) (polarCenter (M k) β u)) +
        64 * ‖polarCenter (M k) β u‖ ^ 2 * pairEnergy (by omega) (polarCenter (M k) β u) -
        realEnergy (by omega) (normalizedAngle (M k) u) / 4 -
        (1 - ε) * actualMass (M k) ‖β‖ u := by
  have hN : Tendsto (fun k => 2 * M k) atTop atTop := tendsto_atTop_mono (fun _ => by omega) hM
  filter_upwards [eventual_model_normalized_price hM hη hε, eventual_model_angular_loss hM hη,
    hM.eventually_ge_atTop 2, hη.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4),
    (sizeBudget_tendsto hN).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 16),
    (coordinateBudget_tendsto hN hη).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)] with k hr ha hm2 he hs hsmall
  intro z σ α β u hm hmodel hz hE
  have hp := model_polar_bounds hm2 hmodel hE (hs.trans (by norm_num))
  have hβ := (ExtremalScaleBound.model_matching_deficit_bound hm2 hmodel he hz hE).1
  have hcoords := model_coordinate_bounds hm2 hmodel hp hβ hs
  have hc := PolarCenterNormalization.correctedCenter_halfPeriodic hm (angles (M k) u)
    (ExtremalPolarCenter.physicalCenter (M k) β u) (angles_halfPeriodic hm u hmodel.periodic)
    (physicalCenter_halfPeriodic hm β u hmodel.periodic)
  have hzero := quartic_objective_upper hm (polarCenter (M k) β u) hc
    (fun p => (hcoords.2.2.1 p).trans hsmall)
  have hrad := hr z σ α β u hmodel hz hE
  have hang := ha z σ α β u hm hmodel hz hE
  have hy := angular_error_young (show 0 < 2 * M k by omega) (polarCenter (M k) β u) (normalizedAngle (M k) u)
  have h0 : angularLogDiscriminant (normalizedAngle (M k) u)
      (configuration (root (2 * M k)) (polarCenter (M k) β u)) 0 =
      Real.log (discriminant (configuration (root (2 * M k)) (polarCenter (M k) β u))) := by
    simp only [angularLogDiscriminant, angularOrbit, zero_mul, ofReal_zero, exp_zero, one_mul]
  rw [h0] at hang
  nlinarith only [hzero, hrad, hang, hy]

end StructuralNote.ActualObjectiveLoss

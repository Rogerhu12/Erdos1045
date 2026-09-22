import StructuralNote.ExplicitLocalBudgets

/-! Finite-order radial and angular objective losses with explicit tolerances. -/

namespace StructuralNote.ExplicitObjectiveThreshold

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization
open Erdos1045.ExplicitThreshold ExplicitGradientThreshold ExplicitLocalBudgets
open PolarAngleControl PolarRepresentation PolarCenterEnergy PolarCenterNormalization
open NormalizedPolarRepresentation ExtremalPolarCenter ActualAngularLoss
open GeometricRelativeRemainder SignedPressureAngular AngularObjectiveCurvature
open AngularPathGeometry AngularFirstEnergy ActualAngularFirst SchurSpectrum DiscreteEnergy
open ActualRadialGradient ActualRadialPrice RadialObjectivePrice NormalizedRadialPrice
open RadialInterpolationQuotients ActualObjectiveLoss
noncomputable section

def edgeTolerance : ℝ :=
  min (pathTolerance (1 / 24)) (min 1 (1 / 1000 : ℝ) / 100)

def orderThreshold : ℕ :=
  max 4 (max (pathThreshold (1 / 24)) (max (coordinateThreshold (1 / 1000))
    (max (sizeThreshold (1 / 10000)) (inverseThreshold 1 (1 / 100)))))

theorem edgeTolerance_pos : 0 < edgeTolerance := by
  unfold edgeTolerance
  exact lt_min (pathTolerance_pos (by norm_num)) (by norm_num)

theorem parameters_small {n : ℕ} {η : ℝ} (hn : orderThreshold ≤ n)
    (hη0 : 0 ≤ η) (hη : η ≤ edgeTolerance) :
    4 ≤ n ∧ η ≤ 1 / 4 ∧ coordinateBudget n η ≤ 1 / 1000 ∧
    sizeBudget n ≤ 1 / 10000 ∧ 1 / (n : ℝ) ≤ 1 / 100 := by
  simp only [orderThreshold, max_le_iff] at hn
  have hηc := hη.trans (min_le_right _ _)
  have hηquarter : η ≤ 1 / 4 := by
    norm_num at hηc
    linarith only [hηc]
  exact ⟨hn.1, hηquarter,
    coordinate_small (by norm_num) hη0 hηc hn.2.2.1,
    (size_small (by norm_num) hn.2.2.2.1).le,
    (inverse_small (by norm_num) hn.2.2.2.2).le⟩

theorem model_normalized_price {m : ℕ} (hm : 2 ≤ m)
    (hn : orderThreshold ≤ 2 * m) {η : ℝ} (hη : η ≤ edgeTolerance)
    {z : Points (2 * m)} {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hE : ExtremalEnergyBound.totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2) :
    Real.log (discriminant z) ≤ angularLogDiscriminant (normalizedAngle m u)
      (configuration (root (2 * m)) (polarCenter m β u)) 1 - (7 / 8) * actualMass m ‖β‖ u := by
  have hs := parameters_small hn hmodel.error_nonneg hη
  have hp := model_polar_bounds hm hmodel hE (hs.2.2.2.1.trans (by norm_num))
  have hpath : pathThreshold (1 / 24) ≤ 2 * m :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hηpath := hη.trans (min_le_left _ _)
  have hpair := pair_small (pairTolerance_pos (C := pathEnergy) (by norm_num : (0 : ℝ) < 1 / 24))
    hmodel.error_nonneg hηpath hpath
  have hpairhalf : pairBudget (2 * m) η ≤ 1 / 2 :=
    hpair.le.trans (min_le_left _ _)
  have hgrad (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      gradientDeviation (actualPath m ‖β‖ u t) ≤ 1 / 24 :=
    (model_path_gradient hm (by norm_num) hpath hηpath hmodel hz hE hp ht).le
  have hh := model_radial_price hm hmodel hs.2.1 hz hE hp hpairhalf hgrad
  have hroot : Real.sqrt (sizeBudget (2 * m)) ≤ 1 / 100 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · norm_num
      exact hs.2.2.2.1
  have hcoeff : (7 / 8 : ℝ) ≤
      1 - 1 / ((2 * m : ℕ) : ℝ) - 1 / 24 - 2 * Real.sqrt (sizeBudget (2 * m)) := by
    linarith only [hs.2.2.2.2, hroot]
  have hmass : 0 ≤ actualMass m ‖β‖ u := by
    unfold actualMass mass
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Finset.sum_nonneg fun j _ =>
      sub_nonneg.mpr (model_radius_le_one (by omega) hmodel hz.1 j)
  have hmul := mul_le_mul_of_nonneg_right hcoeff hmass
  rw [model_discriminant_one hmodel, discriminant_zero_normalized] at hh
  linarith only [hh, hmul]

theorem model_angular_loss {m : ℕ} (hm : 2 ≤ m)
    (hn : orderThreshold ≤ 2 * m) {η : ℝ} (hη : η ≤ edgeTolerance)
    {z : Points (2 * m)} {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hE : ExtremalEnergyBound.totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2) :
    angularLogDiscriminant (normalizedAngle m u)
      (configuration (root (2 * m)) (polarCenter m β u)) 1 ≤
    angularLogDiscriminant (normalizedAngle m u)
      (configuration (root (2 * m)) (polarCenter m β u)) 0 +
      8 * Real.sqrt (AntipodalLog.fourthEnergy (2 * m) (periodize (by omega) (polarCenter m β u)) +
        ‖polarCenter m β u‖ ^ 2 * pairEnergy (by omega) (polarCenter m β u)) *
          Real.sqrt (realEnergy (by omega) (normalizedAngle m u)) -
      realEnergy (by omega) (normalizedAngle m u) / 2 := by
  have hs := parameters_small hn hmodel.error_nonneg hη
  have hs16 := hs.2.2.2.1.trans (by norm_num : (1 / 10000 : ℝ) ≤ 1 / 16)
  have hp := model_polar_bounds hm hmodel hE (hs16.trans (by norm_num))
  have hb := ExtremalScaleBound.model_matching_deficit_bound hm hmodel hs.2.1 hz hE
  have hcoords := model_coordinate_bounds hm hmodel hp hb.1 hs16
  have hc := correctedCenter_halfPeriodic (show 0 < m by omega) (angles m u)
    (ExtremalPolarCenter.physicalCenter m β u)
    (angles_halfPeriodic (by omega) u hmodel.periodic)
    (physicalCenter_halfPeriodic (by omega) β u hmodel.periodic)
  apply angular_loss_of_coordinate_bounds (by omega) (polarCenter m β u) (normalizedAngle m u)
    hc (normalizedAngle_halfPeriodic (by omega) u hmodel.periodic) _
    (hs.2.2.1.trans (by norm_num : (1 / 1000 : ℝ) ≤ 1 / 512))
    hcoords.1 hcoords.2.1 hcoords.2.2.1 hcoords.2.2.2
  unfold coordinateBudget
  have := hmodel.error_nonneg
  positivity

theorem model_objective_loss {m : ℕ} (hm : 2 ≤ m)
    (hn : orderThreshold ≤ 2 * m) {η : ℝ} (hη : η ≤ edgeTolerance)
    {z : Points (2 * m)} {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hE : ExtremalEnergyBound.totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2) :
    Real.log (discriminant z) - Real.log (discriminant (root (2 * m))) ≤
      pairPotential (by omega) (polarCenter m β u) +
      65 * AntipodalLog.fourthEnergy (2 * m) (periodize (by omega) (polarCenter m β u)) +
      64 * ‖polarCenter m β u‖ ^ 2 * pairEnergy (by omega) (polarCenter m β u) -
      realEnergy (by omega) (normalizedAngle m u) / 4 - (7 / 8) * actualMass m ‖β‖ u := by
  have hs := parameters_small hn hmodel.error_nonneg hη
  have hs16 := hs.2.2.2.1.trans (by norm_num : (1 / 10000 : ℝ) ≤ 1 / 16)
  have hp := model_polar_bounds hm hmodel hE (hs16.trans (by norm_num))
  have hβ := (ExtremalScaleBound.model_matching_deficit_bound hm hmodel hs.2.1 hz hE).1
  have hcoords := model_coordinate_bounds hm hmodel hp hβ hs16
  have hc := correctedCenter_halfPeriodic (show 0 < m by omega) (angles m u)
    (ExtremalPolarCenter.physicalCenter m β u)
    (angles_halfPeriodic (by omega) u hmodel.periodic)
    (physicalCenter_halfPeriodic (by omega) β u hmodel.periodic)
  have hzero := quartic_objective_upper (show 0 < m by omega) (polarCenter m β u) hc
    (fun p => (hcoords.2.2.1 p).trans (hs.2.2.1.trans (by norm_num)))
  have hrad := model_normalized_price hm hn hη hmodel hz hE
  have hang := model_angular_loss hm hn hη hmodel hz hE
  have hy := angular_error_young (show 0 < 2 * m by omega) (polarCenter m β u) (normalizedAngle m u)
  have h0 : angularLogDiscriminant (normalizedAngle m u)
      (configuration (root (2 * m)) (polarCenter m β u)) 0 =
      Real.log (discriminant (configuration (root (2 * m)) (polarCenter m β u))) := by
    simp only [angularLogDiscriminant, angularOrbit, zero_mul, ofReal_zero, exp_zero, one_mul]
  rw [h0] at hang
  nlinarith only [hzero, hrad, hang, hy]

end
end StructuralNote.ExplicitObjectiveThreshold

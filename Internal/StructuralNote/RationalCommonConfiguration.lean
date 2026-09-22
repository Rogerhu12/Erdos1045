import StructuralNote.RationalBranchRecovery

/-! The precise rotation and translation from the base-edge rational gauge to
the mean-zero common-fiber gauge. No feasibility or maximizing hypothesis is
needed for this identity of actual configurations. -/

namespace StructuralNote.RationalCommonConfiguration

open Erdos1045.EventualExact LensClosure FiniteFourierLift FourierMultiplier SchurSpectrum
open CommonTangentialParameters RationalBranchRecovery
open scoped BigOperators
noncomputable section

def angleMean {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) : ℝ :=
  (∑ j : Fin m, RationalAngleBranch.angle hm X j) / m

def theta {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) (j : Fin (2 * m)) : ℝ :=
  RationalAngleBranch.angle hm X j - angleMean hm X

def centerMean {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (X : RationalConfiguration.Variables m → ℝ) : ℂ :=
  (∑ j : Fin m, RationalConfiguration.centerPrefix hm σ X j) / m

def normalizedCenter {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (j : Fin (2 * m)) : ℂ :=
  unit (-angleMean hm X) * (RationalConfiguration.centerPrefix hm σ X (j.val % m) - centerMean hm σ X)

def recoveredVector {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) : Fin (2 * m) → ℂ :=
  freeVector hm (RationalAngleBranch.tangential hm σ X)

def recoveredCorrection {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) : ℂ :=
  correction (RationalAngleBranch.tangential hm σ X)

theorem theta_eq_repeat {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) :
    (fun j => (theta hm X j : ℂ)) = BoxLensLift.repeatHalf hm
      (fun j => ((RationalAngleBranch.angle hm X j - angleMean hm X : ℝ) : ℂ)) := by
  funext j
  simp only [theta, BoxLensLift.repeatHalf, RationalAngleBranch.angle, Nat.mod_mod]

theorem theta_halfPeriodic {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) :
    HalfPeriodic hm (fun j => (theta hm X j : ℂ)) := by
  rw [theta_eq_repeat]
  exact BoxLensLift.repeatHalf_halfTurn hm _

theorem theta_mean_zero {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) :
    (∑ j, (theta hm X j : ℂ)) = 0 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hr : (∑ j : Fin m, (RationalAngleBranch.angle hm X j - angleMean hm X)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold angleMean
    field_simp
    ring
  have hc : (∑ j : Fin m, ((RationalAngleBranch.angle hm X j - angleMean hm X : ℝ) : ℂ)) = 0 := by
    exact_mod_cast hr
  have he := congrArg (fun f : Fin (2 * m) → ℂ => ∑ j, f j) (theta_eq_repeat hm X)
  change (∑ j, (theta hm X j : ℂ)) = (∑ j, BoxLensLift.repeatHalf hm
    (fun j => ((RationalAngleBranch.angle hm X j - angleMean hm X : ℝ) : ℂ)) j) at he
  rw [he, BoxLensLift.repeatHalf_sum, hc, mul_zero]

theorem normalizedCenter_halfPeriodic {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) : HalfPeriodic hm (normalizedCenter hm σ X) :=
  BoxLensLift.repeatHalf_halfTurn hm
    (fun j => unit (-angleMean hm X) * (RationalConfiguration.centerPrefix hm σ X j - centerMean hm σ X))

theorem normalizedCenter_mean_zero {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) : (∑ j, normalizedCenter hm σ X j) = 0 := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  change (∑ j, BoxLensLift.repeatHalf hm
    (fun k => unit (-angleMean hm X) * (RationalConfiguration.centerPrefix hm σ X k - centerMean hm σ X)) j) = 0
  rw [BoxLensLift.repeatHalf_sum, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold centerMean
  field_simp
  ring

theorem successor_half_val {m : ℕ} (hm : 0 < m) (j : Fin m) :
    (successor (by omega) (CommonClosureEnergy.halfIndex j)).val = j.val + 1 := by
  dsimp [successor, CommonClosureEnergy.halfIndex]
  exact Nat.mod_eq_of_lt (by omega)

theorem normalized_phase {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) (j : Fin m) :
    CommonClosureEnergy.phase hm (theta hm X) j = RationalAngleBranch.phase hm X j - angleMean hm X := by
  unfold CommonClosureEnergy.phase CommonClosureEnergy.angleAverage
  simp only [theta]
  rw [successor_half_val hm j]
  simp only [CommonClosureEnergy.halfIndex]
  unfold RationalAngleBranch.phase
  ring

theorem normalized_halfAngle {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) (j : Fin m) :
    CommonClosureEnergy.halfAngle hm (theta hm X) j = RationalAngleBranch.halfAngle hm X j := by
  unfold CommonClosureEnergy.halfAngle CommonClosureEnergy.angleDifference
  simp only [theta]
  rw [successor_half_val hm j]
  simp only [CommonClosureEnergy.halfIndex]
  unfold RationalAngleBranch.halfAngle
  ring

theorem rotated_increment (a β L s t : ℝ) :
    increment (β - a) L s t = unit (-a) * increment β L s t := by
  rw [increment, increment, ← mul_assoc, ← CommonFiberGeometry.unit_add]
  congr 2
  ring

theorem recovered_height {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) :
    heightParameter (coordinates (by omega) (recoveredVector (by omega) σ X))
      (recoveredCorrection (by omega) σ X) = RationalAngleBranch.tangential (by omega) σ X :=
  heightParameter_freeVector hm _

theorem fiberIncrement_eq_rotated {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (hX : RationalAngleBranch.SmallWindow X)
    (hσ : ∀ j, σ j ^ 2 = 1) (j : Fin m) :
    CommonFiberGeometry.fiberIncrement (by omega) (theta (by omega) X) (recoveredVector (by omega) σ X) σ
      (recoveredCorrection (by omega) σ X) j =
      unit (-angleMean (by omega) X) * RationalConfiguration.increment (by omega) σ X j := by
  rw [CommonFiberGeometry.fiberIncrement, recovered_height hm σ X, normalized_phase, normalized_halfAngle,
    rotated_increment, RationalAngleBranch.smallWindow_increment_eq_lens hm σ X hX j (hσ j)]

theorem recovered_closure_zero {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (hX : RationalAngleBranch.SmallWindow X)
    (hσ : ∀ j, σ j ^ 2 = 1) (hH : RationalConfiguration.closure (by omega) σ X = 0) :
    closure (CommonClosureEnergy.phase (by omega) (theta (by omega) X))
      (fun j => 2 * Real.cos (CommonClosureEnergy.halfAngle (by omega) (theta (by omega) X) j))
      σ (coordinates (by omega) (recoveredVector (by omega) σ X))
      (recoveredCorrection (by omega) σ X) = 0 := by
  change (∑ j, CommonFiberGeometry.fiberIncrement (by omega) (theta (by omega) X)
    (recoveredVector (by omega) σ X) σ (recoveredCorrection (by omega) σ X) j) = 0
  simp_rw [fiberIncrement_eq_rotated hm σ X hX hσ]
  rw [← Finset.mul_sum]
  change unit (-angleMean (by omega) X) * RationalConfiguration.closure (by omega) σ X = 0
  rw [hH, mul_zero]

theorem normalizedCenter_half_difference {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (hH : RationalConfiguration.closure hm σ X = 0) (j : Fin m) :
    difference (by omega) (normalizedCenter hm σ X) (CommonClosureEnergy.halfIndex j) =
      unit (-angleMean hm X) * RationalConfiguration.increment hm σ X j := by
  unfold difference normalizedCenter
  rw [successor_half_val hm j, RationalConfiguration.prefix_mod_of_closed hm σ X hH (by omega)]
  simp only [CommonClosureEnergy.halfIndex, Nat.mod_eq_of_lt j.isLt]
  rw [RationalConfiguration.prefix_succ]
  ring

theorem normalizedCenter_eq_fiberCenter {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (hX : RationalAngleBranch.SmallWindow X)
    (hσ : ∀ j, σ j ^ 2 = 1) (hH : RationalConfiguration.closure (by omega) σ X = 0) :
    normalizedCenter (by omega) σ X = CommonFiberGeometry.center (by omega) (theta (by omega) X)
      (recoveredVector (by omega) σ X) σ (recoveredCorrection (by omega) σ X) := by
  apply integral_unique (by omega) _ _ (normalizedCenter_mean_zero (by omega) σ X)
  apply eq_of_half_restriction (by omega)
    (difference_halfPeriodic (by omega) _ (normalizedCenter_halfPeriodic (by omega) σ X))
    (BoxLensLift.repeatHalf_halfTurn (by omega) _)
  intro j
  change difference (by omega) (normalizedCenter (by omega) σ X) (CommonClosureEnergy.halfIndex j) =
    BoxLensLift.repeatHalf (by omega) (CommonFiberGeometry.fiberIncrement (by omega) (theta (by omega) X)
      (recoveredVector (by omega) σ X) σ (recoveredCorrection (by omega) σ X)) (CommonClosureEnergy.halfIndex j)
  rw [normalizedCenter_half_difference (by omega) σ X hH j]
  simp only [BoxLensLift.repeatHalf, CommonClosureEnergy.halfIndex, Nat.mod_eq_of_lt j.isLt]
  rw [fiberIncrement_eq_rotated hm σ X hX hσ]

theorem normalized_diameter {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) (j : Fin (2 * m)) :
    CommonFiberGeometry.diameterVector (theta hm X) j =
      unit (-angleMean hm X) * RationalConfiguration.diameter hm X j := by
  rw [CommonFiberGeometry.diameterVector_eq_unit, RationalAngleBranch.diameter_eq_unit,
    ← CommonFiberGeometry.unit_add]
  congr 1
  unfold theta
  push_cast
  ring

theorem configuration_eq_rigid_motion {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (hX : RationalAngleBranch.SmallWindow X)
    (hσ : ∀ j, σ j ^ 2 = 1) (hH : RationalConfiguration.closure (by omega) σ X = 0) (j : Fin (2 * m)) :
    CommonFiberGeometry.configuration (by omega) (theta (by omega) X) (recoveredVector (by omega) σ X)
      σ (recoveredCorrection (by omega) σ X) j = unit (-angleMean (by omega) X) *
        (RationalConfiguration.configuration (by omega) σ X j - centerMean (by omega) σ X) := by
  rw [CommonFiberGeometry.configuration, ← normalizedCenter_eq_fiberCenter hm σ X hX hσ hH,
    normalized_diameter]
  unfold normalizedCenter RationalConfiguration.configuration RationalConfiguration.point
  ring

end
end StructuralNote.RationalCommonConfiguration

import StructuralNote.CommonRationalChart

/-! Exact recovery of the common-fiber gauge, closed tangential vector and
closure correction from the explicit rational inverse chart. -/

namespace StructuralNote.CommonRationalRecovery

open Erdos1045.EventualExact LensClosure FiniteFourierLift SchurSpectrum
open CommonClosureEnergy CommonTangentialParameters CommonFiberGeometry CommonRationalChart
open scoped BigOperators
noncomputable section

theorem half_sum_zero {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (hmean : ∑ j, (θ j : ℂ) = 0) :
    (∑ j : Fin m, θ (CommonClosureEnergy.halfIndex j)) = 0 := by
  have hh := congrArg (fun f : Fin (2 * m) → ℂ => ∑ j, f j) (half_repeat hm θ hθ)
  change (∑ j, (θ j : ℂ)) = ∑ j, BoxLensLift.repeatHalf hm
    (fun k => (θ (CommonClosureEnergy.halfIndex k) : ℂ)) j at hh
  rw [hmean, BoxLensLift.repeatHalf_sum] at hh
  have hz : (∑ j : Fin m, (θ (CommonClosureEnergy.halfIndex j) : ℂ)) = 0 := by
    exact (mul_eq_zero.mp hh.symm).resolve_left (by norm_num)
  exact_mod_cast hz

theorem angleMean_parameters {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (hmean : ∑ j, (θ j : ℂ) = 0)
    (ha : ∀ j, |relativeAngle hm θ j| < Real.pi) :
    RationalCommonConfiguration.angleMean hm (parameters hm θ v σ ξ) = -initialAngle hm θ := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold RationalCommonConfiguration.angleMean
  have he (j : Fin m) : RationalAngleBranch.angle hm (parameters hm θ v σ ξ) j =
      θ (CommonClosureEnergy.halfIndex j) - initialAngle hm θ :=
    angle_parameters hm θ v σ ξ hθ ha (CommonClosureEnergy.halfIndex j)
  simp_rw [he]
  rw [Finset.sum_sub_distrib, half_sum_zero hm θ hθ hmean, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem theta_parameters {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (hmean : ∑ j, (θ j : ℂ) = 0)
    (ha : ∀ j, |relativeAngle hm θ j| < Real.pi) :
    RationalCommonConfiguration.theta hm (parameters hm θ v σ ξ) = θ := by
  funext j
  rw [RationalCommonConfiguration.theta, angle_parameters hm θ v σ ξ hθ ha,
    angleMean_parameters hm θ v σ ξ hθ hmean ha]
  ring

theorem tangential_crossingUnit {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (j : Fin m) :
    RationalAngleBranch.tangential hm σ X j = σ j * 2 *
      (unit (-RationalAngleBranch.phase hm X j) * RationalConfiguration.crossingUnit X j).im := by
  rw [RationalConfiguration.crossingUnit, RationalAngleBranch.rotation_eq_unit_arctan,
    ← unit_add, ← unit_add]
  have he : -RationalAngleBranch.phase hm X j +
      (midpoint m j + 2 * Real.arctan (RationalConfiguration.crossingParameter X j)) =
      RationalAngleBranch.crossingOffset hm X j := by
    unfold RationalAngleBranch.phase RationalAngleBranch.crossingOffset
    ring
  rw [he, unit_im]
  unfold RationalAngleBranch.tangential
  ring

theorem tangential_parameters {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (hmean : ∑ j, (θ j : ℂ) = 0)
    (ha : ∀ j, |relativeAngle hm θ j| < Real.pi) (hs : ∀ j, σ j ^ 2 = 1)
    (ht : ∀ j, (heightParameter (coordinates hm v) ξ j) ^ 2 ≤ 4)
    (hR : ∀ j, 0 < 1 + (crossingRelative hm θ v σ ξ j).re) :
    RationalAngleBranch.tangential hm σ (parameters hm θ v σ ξ) = heightParameter (coordinates hm v) ξ := by
  have hphase (j : Fin m) : RationalAngleBranch.phase hm (parameters hm θ v σ ξ) j =
      midpoint m j + relativeAverage hm θ j := by
    have he := RationalCommonConfiguration.normalized_phase hm (parameters hm θ v σ ξ) j
    rw [theta_parameters hm θ v σ ξ hθ hmean ha, angleMean_parameters hm θ v σ ξ hθ hmean ha] at he
    unfold phase relativeAverage at *
    linarith
  funext j
  rw [tangential_crossingUnit, parameters,
    RationalParameterRecovery.crossingUnit_parameters _ _
      (fun j => crossingRelative_norm hm θ v σ ξ j (hs j) (ht j)) hR]
  change σ j * 2 * (unit (-RationalAngleBranch.phase hm (parameters hm θ v σ ξ) j) *
    (unit (midpoint m j) * crossingRelative hm θ v σ ξ j)).im = _
  rw [hphase, crossingRelative, ← mul_assoc, ← mul_assoc, ← unit_add, ← unit_add]
  have he : -(midpoint m j + relativeAverage hm θ j) + midpoint m j + relativeAverage hm θ j = 0 := by ring
  rw [he]
  simp only [unit, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, lensUnit]
  calc
    _ = σ j ^ 2 * heightParameter (coordinates hm v) ξ j := by ring
    _ = _ := by rw [hs j, one_mul]

theorem correction_parameters {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (hv : ParameterSpace (by omega) v)
    (ht : RationalAngleBranch.tangential (by omega) σ (parameters (by omega) θ v σ ξ) =
      heightParameter (coordinates (by omega) v) ξ) :
    RationalCommonConfiguration.recoveredCorrection (by omega) σ (parameters (by omega) θ v σ ξ) = ξ := by
  rw [RationalCommonConfiguration.recoveredCorrection, ht]
  exact RationalBranchRecovery.correction_heightParameter hm _ (coordinates_closed (by omega) v hv.1 hv.2.2) ξ

theorem vector_parameters {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (hv : ParameterSpace (by omega) v)
    (ht : RationalAngleBranch.tangential (by omega) σ (parameters (by omega) θ v σ ξ) =
      heightParameter (coordinates (by omega) v) ξ) :
    RationalCommonConfiguration.recoveredVector (by omega) σ (parameters (by omega) θ v σ ξ) = v := by
  have he := RationalBranchRecovery.decomposition_unique hm
    (RationalAngleBranch.tangential (by omega) σ (parameters (by omega) θ v σ ξ))
    (coordinates (by omega) v) ξ (coordinates_closed (by omega) v hv.1 hv.2.2) ht.symm
  unfold RationalCommonConfiguration.recoveredVector RationalBranchRecovery.freeVector
  rw [← he.2]
  exact reconstruct_coordinates (by omega) v hv

end
end StructuralNote.CommonRationalRecovery

import StructuralNote.ExplicitComparisonGeometry
import StructuralNote.ExplicitFixedSchurCoefficients
import StructuralNote.FixedSchurAngularDerivativeEnergy
import StructuralNote.FixedSchurCircularCurvature
import StructuralNote.FixedSchurChosenDerivativeSymmetry
/-! Explicit angular and symmetry estimates for the fixed-Schur Hessian. -/
namespace StructuralNote.ExplicitFixedSchurHessianGeometry
open Complex Filter Erdos1045.EventualExact SchurSpectrum
open CommonDomainClosure CommonFiberGeometry CommonFiberHessianGeometryEnergy
open GeometricRelativeRemainder SignedPressureAngular FixedSchurChartQuotients
open scoped BigOperators Topology
open Complex Filter Erdos1045 Erdos1045.EventualExact SchurSpectrum
open CommonDomainClosure CommonDomainRadius CommonFiberGeometry CommonFiberCanonicalPaths
open FixedSchurChosenPath FixedSchurConfigurationDerivatives FixedSchurChosenRemainderSecond
open GeometricRelativeRemainder SignedPressureAngular LogDiscriminantSecondDerivative
open HessianAngularReference HessianDenominator CommonFiberHessianGeometryEnergy
open FixedSchurChartQuotients AngularObjectiveCurvature
open Complex Filter Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum SchurLiftBounds
open CommonDomainClosure CommonFiberCanonicalPaths CommonFiberCanonical
open CommonFiberCanonicalDirections FixedSchurChart FixedSchurChosenPath
open FixedSchurChosenLinearization FixedSchurChosenFirstBounds
open FixedSchurAngularDerivativeEnergy FixedSchurCircularCurvature
noncomputable section

theorem log_ratio_small {n : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ n) :
    (CommonDomainRadius.logOrder n : ℝ) / n < 1 / 144 := by
  have h := ExplicitFixedSchurCoefficients.logOrder_div_small hN
  rw [mul_div_assoc] at h
  linarith only [h]

theorem logOrder_le_sqrt {n : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ n) :
    (CommonDomainRadius.logOrder n : ℝ) ≤ Real.sqrt n := by
  have hb := ExplicitHessianThreshold.logOrder_bound hN
  have hs := Erdos1045.ExplicitThreshold.sqrt_monomial_lt (j := 1) (c := 2)
    hN (by norm_num) (by norm_num)
  have hn := Real.sqrt_pos.mpr (ExplicitHessianThreshold.order_pos hN)
  simp only [pow_one] at hs
  have hh := (div_lt_one hn).mp (hs.trans (by norm_num))
  exact hb.trans hh.le

theorem hessian_coefficient_small {n : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ n) :
    304000000000 / Real.sqrt n < (1 / 64 : ℝ) := by
  have hs := Erdos1045.ExplicitThreshold.sqrt_monomial_lt (j := 0) (c := 304000000000)
    hN (by norm_num) (by norm_num)
  simp only [pow_zero, mul_one] at hs
  exact hs.trans (by norm_num)

theorem angular_derivative_energy {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) : ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
      (θ η : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → (∑ j, (η j : ℂ) = 0) →
      pairEnergy (by omega) (fun j => I * diameterVector θ j * (η j : ℂ)) ≤
        18 * pairEnergy (by omega) (fun j => (η j : ℂ)) ∧
      pairEnergy (by omega) (fun j => -diameterVector θ j * (η j : ℂ) ^ 2) ≤
        500 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 *
          pairEnergy (by omega) (fun j => (η j : ℂ)) ^ 2 := by
  have hquot := ExplicitComparisonGeometry.quotient_properties hN
  clear hN
  intro hm s θ η v hdom hmean
  have hq := diameter_quotient_le θ (hquot hm s θ v hdom).2.2.1
  constructor
  · have he : (fun j => I * diameterVector θ j * (η j : ℂ)) =
        fun j => I * (diameterVector θ j * (η j : ℂ)) := by funext j; ring
    rw [he, RadialInterpolationEnergy.pairEnergy_scale, norm_I, one_pow, one_mul]
    exact angular_velocity_energy (by omega) θ η hmean hq
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using angular_acceleration_energy (by omega) θ η hmean hq

theorem circular_curvature {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) : ∀ (hm : 2 ≤ m) (_s : FiniteBox.SignPattern (m := m) (by omega))
      (θ η : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      |second (diameterVector θ) (fun j => I * diameterVector θ j * (η j : ℂ))
        (angularAcceleration θ η) + 2 * pairEnergy (by omega) (fun j => (η j : ℂ))| ≤
          220 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) *
            pairEnergy (by omega) (fun j => (η j : ℂ)) := by
  have hq := ExplicitComparisonGeometry.quotient_properties hN
  have hs := log_ratio_small hN
  have hsmall : (logOrder (2 * m) : ℝ) / (2 * m : ℝ) < 1 / 22 := by
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
    exact hs.trans (by norm_num)
  clear hs
  clear hN
  intro hm s θ η v hdom
  have hδ : 11 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ≤ 1 / 2 := by
    rw [mul_div_assoc]
    linarith
  have hr (i j : Fin (2 * m)) (hij : i ≠ j) :
      ‖(diameterVector θ i - diameterVector θ j) / (root (2 * m) i - root (2 * m) j) - 1‖ ≤
        11 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
    have hroot : root (2 * m) i - root (2 * m) j ≠ 0 :=
      sub_ne_zero.mpr ((root_injective (show 4 ≤ 2 * m by omega)).ne hij)
    have he : (diameterVector θ i - diameterVector θ j) / (root (2 * m) i - root (2 * m) j) - 1 =
        quotient (diameterVector θ - root (2 * m)) (root (2 * m)) (i, j) := by
      simp only [quotient, Pi.sub_apply]
      field_simp [hroot]
      ring
    rw [he]
    exact domain_angularError_ratio (by omega) θ v hdom i j
  have hb := circular_second_error (show 4 ≤ 2 * m by omega) (diameterVector θ) η
    (diameterVector_norm θ) (hq hm s θ v hdom).1 hδ hr
  exact hb.trans_eq (by ring)

theorem chosen_derivatives_antiperiodic {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) : ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      FiniteBox.Antiperiodic (by omega) (chosenFirstDerivative (by omega) s θ η v h) ∧
      FiniteBox.Antiperiodic (by omega) (chosenSecondDerivative (by omega) s θ η v h) := by
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties hN
  clear hN
  intro hm s θ η v h hdom hdir
  have hn := affine_domain_near_zero (show 0 < m by omega) (θ, v) (η, h) hdom hdir
  have hq : ∀ᶠ t in 𝓝 (0 : ℝ),
      FiniteBox.Antiperiodic (by omega) (chosenQPath (by omega) s θ η v h t) := by
    filter_upwards [hn] with t ht
    exact (hprops hm s _ _ ht).antiperiodic
  have he (j : Fin (2 * m)) :
      (fun t : ℝ => chosenQPath (by omega) s θ η v h t (halfTurn (by omega) j)) =ᶠ[𝓝 0]
        (fun t => -chosenQPath (by omega) s θ η v h t j) := by
    filter_upwards [hq] with t ht
    exact ht j
  constructor
  · intro j
    simpa only [chosenFirstDerivative, chosenQFirstPath, deriv.fun_neg'] using (he j).deriv_eq
  · intro j
    change deriv (deriv (fun t : ℝ =>
      chosenQPath (by omega) s θ η v h t (halfTurn (by omega) j))) 0 =
        -deriv (deriv (fun t : ℝ => chosenQPath (by omega) s θ η v h t j)) 0
    simpa only [deriv.fun_neg'] using (he j).deriv.deriv_eq

end
end StructuralNote.ExplicitFixedSchurHessianGeometry

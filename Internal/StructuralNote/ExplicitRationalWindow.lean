import StructuralNote.ExplicitComparisonGeometry
import StructuralNote.FixedSchurRationalWindowDomain
import StructuralNote.FixedSchurRationalWindowAngleChart
/-! Explicit entry of the rational selection window into the fixed-Schur domain. -/
namespace StructuralNote.ExplicitRationalWindow
open Erdos1045 Erdos1045.EventualExact Complex Filter
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open RationalCommonConfiguration RationalAngleBranch
open CommonTangentialParameters FixedSchurLinear FixedSchurProjectionDomain
open EdgeCoordinates EdgeEnergyComparison AngularObjectiveCurvature
open CommonDomainClosure CommonDomainRadius FixedSchurChart
open FixedSchurChartCenterBounds
open scoped BigOperators Topology
open CommonDomainClosure CommonDomainRadius
open FixedSchurRationalWindowEnergy FixedSchurLiftStability
open AngularObjectiveCurvature LensClosure
open RationalCommonConfiguration RationalAngleBranch RationalChart
open CommonDomainRadius CommonFiberGeometry
open FixedSchurRationalWindowEnergy FixedSchurRationalWindowDomain
open PolarCenterNormalization LensClosure LensIncrementDerivatives
open FixedSchurRationalWindowDomain FixedSchurRationalWindowAngleChart
noncomputable section

theorem window_error_small {n : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ n) :
    2306880 * Real.log n / (n : ℝ) ^ 2 < 1 / 2 := by
  have hh := ExplicitHessianThreshold.log_monomial_div_small (j := 1) (c := 2306880)
    hN (by norm_num) (by norm_num)
  have hn := ExplicitHessianThreshold.order_pos hN
  have hn1 : (1 : ℝ) ≤ n := by
    have hx := ExplicitHessianThreshold.two_fifty_six_le_order hN
    exact_mod_cast (show 1 ≤ n by omega)
  have hl : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hnum : 2306880 * Real.log n / (n : ℝ) ^ 2 ≤
      2306880 * Erdos1045.ExplicitThreshold.logBudget n / n := by
    calc
      _ ≤ 2306880 * Real.log n / n := by
        apply div_le_div_of_nonneg_left (by positivity) hn
        nlinarith only [hn1]
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hn.le
        unfold Erdos1045.ExplicitThreshold.logBudget
        linarith
  simp only [pow_one] at hh
  exact hnum.trans_lt (hh.trans (by norm_num))

theorem fixedReferenceCenter_data {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m)),
        HalfPeriodic (by omega) (fixedReferenceCenter (by omega) s) ∧
          (∑ j, fixedReferenceCenter (by omega) s j) = 0 ∧
          pairEnergy (by omega) (fixedReferenceCenter (by omega) s) ≤ 1602 := by
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties hN
  have hcenter := ExplicitComparisonGeometry.center_bounds hN
  clear hN
  intro hm s
  have hdom := zero_inDomain (by omega : 0 < m)
  have hp := hprops hm s 0 0 hdom
  refine ⟨?_, ?_, (hcenter hm s 0 0 hdom).2⟩
  · unfold fixedReferenceCenter
    exact center_halfPeriodic hm _ 0 hp.antiperiodic (by intro j; rfl)
  · simpa only [fixedReferenceCenter] using hp.mean_zero

theorem selectedWindow_inDomain {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        InDomain (by omega) (theta (by omega) X)
          (projection hm
            (normalizedCenter (by omega) (rationalSign s) X)) := by
  have href := fixedReferenceCenter_data hN
  have herr := window_error_small hN
  simp only [Nat.cast_mul, Nat.cast_ofNat] at herr
  clear hN
  intro hm s X hwindow
  have hrefData := href hm s
  let Ex := pairEnergy (by omega : 0 < 2 * m)
    (fun j => (extendedAngleParameter (by omega : 0 < m) X j : ℂ))
  let AR := pairEnergy (by omega : 0 < 2 * m)
    (rationalCenter (by omega : 0 < m) (rationalSign s) X -
      fixedReferenceCenter (by omega) s)
  let Aref := pairEnergy (by omega : 0 < 2 * m)
    (fixedReferenceCenter (by omega : 0 < m) s)
  have hEx0 : 0 ≤ Ex := pairEnergy_nonneg _ _
  have hAR0 : 0 ≤ AR := pairEnergy_nonneg _ _
  have hAref0 : 0 ≤ Aref := pairEnergy_nonneg _ _
  have htheta := theta_energy_le_four (by omega : 0 < m) X
  have halpha := angleMean_sq_le (by omega : 0 < m) X
  have hproject := projected_normalizedCenter_energy_le hm s X hrefData.1 hrefData.2.1
  have hrotation :
      30 * angleMean (by omega : 0 < m) X ^ 2 * Aref ≤
        (2306880 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2) * Ex := by
    have h1 := mul_le_mul_of_nonneg_left halpha (by norm_num : (0 : ℝ) ≤ 30)
    have h2 := mul_le_mul_of_nonneg_right h1 hAref0
    have hbound := hrefData.2.2
    have hlog0 : 0 ≤ Real.log (2 * m : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 2 * m by omega)
    have hcoef0 : 0 ≤ 30 * (48 * Real.log (2 * m : ℝ) /
        (2 * m : ℝ) ^ 2 * Ex) := by positivity
    calc
      _ ≤ 30 * (48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * Ex) * Aref := by
        simpa only [Ex] using h2
      _ ≤ 30 * (48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * Ex) * 1602 :=
        mul_le_mul_of_nonneg_left hbound hcoef0
      _ = _ := by ring
  have herrle :
      2306880 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 ≤ 1 / 2 := herr.le
  have hrotation' : 30 * angleMean (by omega : 0 < m) X ^ 2 * Aref ≤
      (1 / 2 : ℝ) * Ex :=
    hrotation.trans (mul_le_mul_of_nonneg_right herrle hEx0)
  have htotal :
      pairEnergy (by omega) (fun j => (theta (by omega) X j : ℂ)) +
          pairEnergy (by omega)
            (projection hm
              (normalizedCenter (by omega) (rationalSign s) X)) ≤
        (15 / 2 : ℝ) * (Ex + AR) := by
    change pairEnergy _ _ ≤ 4 * Ex at htheta
    change pairEnergy _ _ ≤ (15 / 2 : ℝ) * AR +
      30 * angleMean (by omega : 0 < m) X ^ 2 * Aref at hproject
    nlinarith only [htheta, hproject, hrotation', hEx0, hAR0]
  have hQ : Ex + AR <
      (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
    simpa only [selectedWindowEnergy, Ex, AR] using hwindow
  have hQ0 : 0 ≤ Ex + AR := add_nonneg hEx0 hAR0
  have hstrict :
      pairEnergy (by omega) (fun j => (theta (by omega) X j : ℂ)) +
          pairEnergy (by omega)
            (projection hm
              (normalizedCenter (by omega) (rationalSign s) X)) <
        energyRadius (2 * m) := by
    have h75lt8 : (15 / 2 : ℝ) * (Ex + AR) < 8 * (Ex + AR) ∨ Ex + AR = 0 := by
      rcases hQ0.eq_or_lt with hzero | hpos
      · exact Or.inr hzero.symm
      · left
        nlinarith
    have h8 : 8 * (Ex + AR) < energyRadius (2 * m) := by
      have hmul := mul_lt_mul_of_pos_left hQ (show (0 : ℝ) < 8 by norm_num)
      have heq :
          8 * ((logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2)) =
            energyRadius (2 * m) := by
        unfold energyRadius
        field_simp
        norm_num [Nat.cast_mul]
        ring
      exact hmul.trans_eq heq
    rcases h75lt8 with hlt | hzero
    · exact htotal.trans_lt (hlt.trans h8)
    · rw [hzero, mul_zero] at htotal
      rw [hzero, mul_zero] at h8
      exact htotal.trans_lt h8
  exact ⟨theta_halfPeriodic (by omega) X, theta_mean_zero (by omega) X,
    projection_parameterSpace hm
      (normalizedCenter_halfPeriodic (by omega) (rationalSign s) X)
      (normalizedCenter_mean_zero (by omega) (rationalSign s) X),
    hstrict⟩

theorem angle_error_small {n : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ n) :
    6 * (CommonDomainRadius.logOrder n : ℝ) ^ 2 * Real.log n / (n : ℝ) ^ 2 < 1 := by
  have hh := ExplicitHessianThreshold.log_monomial_div_small (j := 3) (c := 24)
    hN (by norm_num) (by norm_num)
  have hb := ExplicitHessianThreshold.logOrder_bound hN
  have hH := Erdos1045.ExplicitThreshold.logBudget_ge_one hN
  have hn := ExplicitHessianThreshold.order_pos hN
  have hn1 : (1 : ℝ) ≤ n := by
    have hx := ExplicitHessianThreshold.two_fifty_six_le_order hN
    exact_mod_cast (show 1 ≤ n by omega)
  clear hN
  have hl : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlog : Real.log n ≤ Erdos1045.ExplicitThreshold.logBudget n := by
    unfold Erdos1045.ExplicitThreshold.logBudget
    linarith
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (CommonDomainRadius.logOrder n)) hb 2
  have hp := mul_le_mul hs hlog hl (sq_nonneg _)
  have hnum : 6 * (CommonDomainRadius.logOrder n : ℝ) ^ 2 * Real.log n ≤
      24 * Erdos1045.ExplicitThreshold.logBudget n ^ 3 := by
    nlinarith only [hp]
  have hbound : 6 * (CommonDomainRadius.logOrder n : ℝ) ^ 2 * Real.log n / (n : ℝ) ^ 2 ≤
      24 * Erdos1045.ExplicitThreshold.logBudget n ^ 3 / n := by
    calc
      _ ≤ 24 * Erdos1045.ExplicitThreshold.logBudget n ^ 3 / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by positivity) hn
        nlinarith only [hn1]
  exact hbound.trans_lt (hh.trans (by norm_num))

theorem selectedWindow_angleParameter_small {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        ∀ j : Fin m,
          |RationalConfiguration.angleParameter X j| < 1 / (2 * m : ℝ) := by
  have hsmall := angle_error_small hN
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hsmall
  clear hN
  intro hm s X hwindow j
  let Ex := pairEnergy (by omega : 0 < 2 * m)
    (fun k => (extendedAngleParameter (by omega : 0 < m) X k : ℂ))
  let AR := pairEnergy (by omega : 0 < 2 * m)
    (rationalCenter (by omega : 0 < m) (rationalSign s) X -
      fixedReferenceCenter (by omega) s)
  let L : ℝ := logOrder (2 * m)
  have hAR0 : 0 ≤ AR := pairEnergy_nonneg _ _
  have hEx : Ex < L ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
    change Ex + AR < L ^ 2 / (8 * (2 * m : ℝ) ^ 2) at hwindow
    linarith
  have hlog : 0 < Real.log (2 * m : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < 2 * m by omega))
  have hfactor : 0 < 48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 := by
    positivity
  have hx := angleParameter_sq_le_energy (by omega : 0 < m) X j
  change RationalConfiguration.angleParameter X j ^ 2 ≤
    48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * Ex at hx
  have hx' : RationalConfiguration.angleParameter X j ^ 2 <
      (6 * L ^ 2 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2) *
        (1 / (2 * m : ℝ)) ^ 2 := by
    calc
      _ ≤ 48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * Ex := hx
      _ < 48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 *
          (L ^ 2 / (8 * (2 * m : ℝ) ^ 2)) :=
        mul_lt_mul_of_pos_left hEx hfactor
      _ = _ := by ring
  have hone : 6 * L ^ 2 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 < 1 := by
    simpa only [L, Function.comp_apply, Nat.cast_mul, Nat.cast_ofNat] using hsmall
  have hx'' : RationalConfiguration.angleParameter X j ^ 2 <
      (1 / (2 * m : ℝ)) ^ 2 := by
    have hr : 0 < (1 / (2 * m : ℝ)) ^ 2 := by
      apply sq_pos_of_pos
      positivity
    exact hx'.trans (by simpa only [one_mul] using mul_lt_mul_of_pos_right hone hr)
  exact (sq_lt_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hx'')

/-- The forward scalar angle coordinate has the exact directional derivative
used by the chart chain rule. -/

theorem selectedWindow_angle_chart {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        (∀ j : Fin m,
          |RationalConfiguration.angleParameter X j| < 1 / (2 * m : ℝ) ∧
          1 < 2 / (1 + RationalConfiguration.angleParameter X j ^ 2) ∧
          2 / (1 + RationalConfiguration.angleParameter X j ^ 2) ≤ 2 ∧
          Real.tan ((2 * Real.arctan
            (RationalConfiguration.angleParameter X j)) / 2) =
              RationalConfiguration.angleParameter X j) ∧
        (∀ j : Fin m, 1 < ‖RationalConfiguration.diameter (by omega) X j +
          RationalConfiguration.diameter (by omega) X (j.val + 1)‖) := by
  have hsmall := selectedWindow_angleParameter_small hN
  clear hN
  intro hm s X hwindow
  have hx := hsmall (by omega) s X hwindow
  constructor
  · intro j
    have hx1 : |RationalConfiguration.angleParameter X j| < 1 :=
      (hx j).trans (by
        have hmR : (8 : ℝ) ≤ m := by exact_mod_cast hm
        apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * m)).2
        linarith)
    exact ⟨hx j, (angle_derivative_bounds hx1).1,
      (angle_derivative_bounds hx1).2, angle_inverse_exact _⟩
  · exact diameter_sum_norm_gt_one hm X hx

end
end StructuralNote.ExplicitRationalWindow

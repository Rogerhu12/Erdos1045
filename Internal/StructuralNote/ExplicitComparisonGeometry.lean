import StructuralNote.ExplicitComparisonScalars
import StructuralNote.ExplicitHessianThresholdFixedSchur
import StructuralNote.FixedSchurChartQuotients
import StructuralNote.FixedSchurChartCenterBounds
import StructuralNote.FixedSchurNormalInnerBound
import StructuralNote.FixedSchurInnerSizes

/-! Pointwise geometric estimates for the fixed-Schur comparison. -/
namespace StructuralNote.ExplicitComparisonGeometry
open scoped BigOperators Topology
open Complex Erdos1045 Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum SchurLiftBounds FiniteBox
open CommonClosureEnergy CommonDomainClosure CommonDomainRadius CommonTangentialParameters
open CommonFiberBounds CommonFiberNonlocalSizes CommonFiberSmallCoefficients
open CommonFiberNormalProjectionScaled CommonFiberGeometry SignedPressureAngular
open GeometricRelativeRemainder HessianAngularReference
open EdgeCoordinates FixedSchurData FixedSchurChart FixedSchurChartRadial
open FixedSchurChartRotated FixedSchurDomainBounds FixedSchurDomainSmallness
open FixedSchurNormalExpansion FixedSchurNormalInnerBound FixedSchurInnerAngles FixedSchurRotatedAlgebra
open FixedSchurChartQuotients FixedSchurChartCenterBounds FixedSchurInnerSizes
open CommonFiberHessianGeometryChord CommonFiberHessianGeometryEnergy CommonFiberRelativeRemainderGeometry
open FixedSchurLinear
noncomputable section
theorem quotient_properties {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      Function.Injective (diameterVector θ) ∧
      (∀ p, ‖quotient (FixedSchurLinear.center (coordinate (by omega) s θ v) v)
          (root (2 * m)) p‖ ≤ 1 / 4) ∧
      (∀ p, ‖quotient (diameterVector θ - root (2 * m)) (root (2 * m)) p‖ ≤ 1 / 4) ∧
      (∀ p, ‖quotient (FixedSchurLinear.center (coordinate (by omega) s θ v) v)
          (diameterVector θ) p‖ ≤ 1 / 2) := by
  have hp := ExplicitHessianThresholdFixedSchur.coordinate_properties hN
  have hsmall : (logOrder (2 * m) : ℝ) / (2 * m : ℝ) < 1 / 144 := by
    have hL := ExplicitHessianThreshold.logOrder_bound hN
    have hh := ExplicitHessianThreshold.log_monomial_div_small (j := 1) (c := 2) hN
      (by norm_num) (by norm_num)
    simp only [pow_one, Nat.cast_mul, Nat.cast_ofNat] at hL hh
    have hle := div_le_div_of_nonneg_right hL (by positivity : (0 : ℝ) ≤ 2 * m)
    linarith only [hle, hh]
  clear hN
  intro hm s θ v hdom
  have hratio : 36 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ≤ 1 / 4 := by
    rw [mul_div_assoc]
    linarith
  have hangle : 11 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ≤ 1 / 4 := by
    rw [mul_div_assoc]
    linarith
  have ha (p : Fin (2 * m) × Fin (2 * m)) :
      ‖quotient (angularError θ) (root (2 * m)) p‖ ≤ 1 / 4 :=
    (domain_angularError_ratio (by omega) θ v hdom p.1 p.2).trans hangle
  have hc (p : Fin (2 * m) × Fin (2 * m)) :
      ‖quotient (FixedSchurLinear.center (coordinate (by omega) s θ v) v)
          (root (2 * m)) p‖ ≤ 1 / 4 :=
    (domain_center_quotient hm θ v hdom _ (hp hm s θ v hdom).norm_le p).trans hratio
  refine ⟨domain_diameter_injective hm θ v hdom (by linarith), hc, ha, ?_⟩
  intro p
  have h := quotient_true_le θ (FixedSchurLinear.center (coordinate (by omega) s θ v) v)
    (HessianAngularReference.root_injective (by omega))
    (fun i j => (ha (i, j)).trans (by norm_num)) p
  linarith [hc p]


theorem center_bounds {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      ‖center (coordinate (by omega) s θ v) v‖ ≤ 121 / (2 * m : ℝ) ∧
        pairEnergy (by omega) (center (coordinate (by omega) s θ v) v) ≤ 1602 := by
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties hN
  have hcoeff := ExplicitComparisonScalars.small_coefficients hN
  have hradius := ExplicitHessianThreshold.energyRadius_le_inverse hN
  clear hN
  intro hm s θ v hdom
  have hp := hprops hm s θ v hdom
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hvsmall (j : Fin (2 * m)) : ‖v j‖ ≤ 1 / (1000 * (2 * m : ℝ)) := by
    apply (domain_free_center_bound (by omega) θ v hdom j).trans
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcoeff.2.2.1
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro j
    have hq := canonicalLift_bound (show 3 ≤ 2 * m by omega)
      (coordinate (by omega) s θ v) hp.norm_le j
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hq
    calc
      _ ≤ ‖canonicalLift (coordinate (by omega) s θ v) j‖ + ‖v j‖ := norm_add_le _ _
      _ ≤ 120 / (2 * m : ℝ) + 1 / (1000 * (2 * m : ℝ)) := add_le_add hq (hvsmall j)
      _ ≤ 121 / (2 * m : ℝ) := by
        field_simp
        nlinarith
  · have hA := canonicalLift_pairEnergy_le hm (coordinate (by omega) s θ v) hp.antiperiodic
    have hms := meanSquare_le_twentyFive (by omega) (coordinate (by omega) s θ v) hp.norm_le
    have hv : pairEnergy (by omega) v ≤ 1 := by
      have hv' := ((domain_energy_bounds (by omega) θ v hdom).2).trans hradius
      apply hv'.trans
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((2 * m : ℕ) : ℝ))).2
      norm_num
      exact_mod_cast (show 1 ≤ 2 * m by omega)
    have hadd := QuadraticStability.pairEnergy_add_le (show 0 < 2 * m by omega)
      (canonicalLift (coordinate (by omega) s θ v)) v
    change pairEnergy (by omega) (canonicalLift (coordinate (by omega) s θ v) + v) ≤ 1602
    linarith


private theorem tangential_abs_le {b q p P : ℝ}
    (hb : |b| ≤ 1) (hq : |q| ≤ 5) (hp : |p| ≤ P) (_hP : 0 ≤ P) :
    |tangential b q p| ≤ P + 5 := by
  unfold tangential
  calc
        |p * Real.cos b - q * Real.sin b| =
        |p * Real.cos b + -(q * Real.sin b)| := by congr 1
    _ ≤ |p * Real.cos b| + |-(q * Real.sin b)| := abs_add_le _ _
    _ = |p| * |Real.cos b| + |q| * |Real.sin b| := by
      rw [abs_mul, abs_neg, abs_mul]
    _ ≤ |p| + 5 * |b| := by
      have hc := Real.abs_cos_le_one b
      have hs := Real.abs_sin_le_abs (x := b)
      have hpc : |p| * |Real.cos b| ≤ |p| * 1 :=
        mul_le_mul_of_nonneg_left hc (abs_nonneg p)
      have hqs : |q| * |Real.sin b| ≤ 5 * |b| := by
        calc
          |q| * |Real.sin b| ≤ 5 * |Real.sin b| :=
            mul_le_mul_of_nonneg_right hq (abs_nonneg _)
          _ ≤ 5 * |b| := mul_le_mul_of_nonneg_left hs (by norm_num)
      calc
        |p| * |Real.cos b| + |q| * |Real.sin b| ≤
            |p| * 1 + 5 * |b| := add_le_add hpc hqs
        _ = |p| + 5 * |b| := by ring
    _ ≤ P + 5 := by
      have hb5 : 5 * |b| ≤ 5 := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 5))
      linarith [hp]

theorem normal_inner_local_bounds (B : ℝ) (hB : 0 ≤ B) {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
        (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
        InDomain (by omega) θ v →
        pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
          B ^ 2 / (2 * m : ℝ) ^ 2 →
        (∀ j, |angularErrorCoefficient (by omega) θ j| ≤
            angularSupConstant B / (2 * m : ℝ) ^ 2) ∧
        (∀ j, |rotatedP (by omega) v (coordinate (by omega) s θ v) j| ≤
            normalPConstant B) ∧
        (∀ j, |rotatedS (by omega) θ v (coordinate (by omega) s θ v) j| ≤
            normalSConstant B) ∧
        (∀ j, (1 / 2 : ℝ) ≤ Real.cos (angleAverage (by omega) θ j)) := by
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties hN
  have hsmall := ExplicitComparisonScalars.inner_angle_sup hN
  clear hN
  intro hm s θ v hdom henergy
  have hp := hprops hm s θ v hdom
  have hs := hsmall hm θ v hdom
  have hP : 0 ≤ normalPConstant B := normalPConstant_nonneg hB
  have hS : 0 ≤ normalSConstant B := normalSConstant_nonneg hB
  have hA : 0 ≤ angularSupConstant B := angularSupConstant_nonneg hB
  have hcoeff : ∀ j : Fin (2 * m),
      |angularErrorCoefficient (by omega) θ j| ≤
        angularSupConstant B / (2 * m : ℝ) ^ 2 := by
    intro j
    let n : ℝ := ((2 * m : ℕ) : ℝ)
    have hn : 0 < n := by dsimp [n]; positivity
    have hη := angleDifference_abs_le_of_joint_energy (by omega) θ v hB hdom henergy j
    have hη' : |angleDifference (by omega) θ j| ≤ 10 * B / n ^ 2 := by
      simpa only [n, Nat.cast_mul, Nat.cast_ofNat] using hη
    have hb : |angleAverage (by omega) θ j| ≤ 1 / (1000 * n) := by
      simpa only [n, Nat.cast_mul, Nat.cast_ofNat] using hs.1 j
    have hn4 : (4 : ℝ) ≤ n := by
      dsimp [n]
      exact_mod_cast (show 4 ≤ 2 * m by omega)
    have hηhalf : |angleDifference (by omega) θ j / 2| ≤ 1 := by
      have hh : |angleDifference (by omega) θ j| ≤ 1 / (1000 * n) := by
        simpa only [n, Nat.cast_mul, Nat.cast_ofNat] using hs.2 j
      calc
        |angleDifference (by omega) θ j / 2| =
            |angleDifference (by omega) θ j| / 2 := by
              rw [abs_div]
              norm_num
        _ ≤ (1 / (1000 * n)) / 2 := by gcongr
        _ ≤ 1 := by
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2)).2
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * n)).2
          have hn1 : (1 : ℝ) ≤ n := by linarith [hn4]
          nlinarith
    have haeta : |Real.pi / n + angleDifference (by omega) θ j / 2| ≤
        (4 + 5 * B) / n := by
      have hpi : Real.pi / n ≤ 4 / n :=
        div_le_div_of_nonneg_right Real.pi_lt_four.le hn.le
      have heta : |angleDifference (by omega) θ j / 2| ≤ 5 * B / n := by
        calc
          |angleDifference (by omega) θ j / 2| =
              |angleDifference (by omega) θ j| / 2 := by
              rw [abs_div]
              norm_num
          _ ≤ (10 * B / n ^ 2) / 2 := by gcongr
          _ = 5 * B / n ^ 2 := by ring
          _ ≤ 5 * B / n := by
            have hnum : 0 ≤ 5 * B / n := by positivity
            have hn1 : 1 ≤ n := by linarith [hn4]
            rw [show 5 * B / n ^ 2 = (5 * B / n) / n by field_simp]
            exact div_le_self hnum hn1
      have hpi0 : 0 ≤ Real.pi / n := by positivity
      have hpiabs : |Real.pi / n| ≤ 4 / n := by
        simpa only [abs_of_nonneg hpi0] using hpi
      have hadd : 4 / n + 5 * B / n = (4 + 5 * B) / n := by ring
      exact (abs_add_le _ _).trans ((add_le_add hpiabs heta).trans_eq hadd)
    have hscalar0 := scalar_angular_error_bound
      (Real.pi / ((2 * m : ℕ) : ℝ))
      (angleDifference (by omega) θ j) (angleAverage (by omega) θ j)
      hηhalf (by
        have hn1 : (1 : ℝ) ≤ n := by linarith [hn4]
        have hden : 0 < 1000 * n := by positivity
        have hsmall : 1 / (1000 * n) ≤ 1 := by
          apply (div_le_iff₀ hden).2
          nlinarith
        exact hb.trans hsmall)
    have hscalar :
        |(2 - 2 * Real.cos (Real.pi / n + angleDifference (by omega) θ j / 2)) /
            Real.cos (angleAverage (by omega) θ j) -
          (2 - 2 * Real.cos (Real.pi / n)) -
          Real.sin (Real.pi / n) * angleDifference (by omega) θ j| ≤
          angleDifference (by omega) θ j ^ 2 / 2 +
            (Real.pi / n + angleDifference (by omega) θ j / 2) ^ 2 *
              angleAverage (by omega) θ j ^ 2 := by
      simpa only [n] using hscalar0
    have hnum :
        |(2 - chordLength (by omega) θ j) /
            Real.cos (angleAverage (by omega) θ j) -
          (2 - 2 * Real.cos (Real.pi / n)) -
          Real.sin (Real.pi / n) * angleDifference (by omega) θ j| ≤
          (50 * B ^ 2 + (4 + 5 * B) ^ 2 / 1000000) / n ^ 4 := by
      have hηsq : (angleDifference (by omega) θ j) ^ 2 ≤
          (10 * B / n ^ 2) ^ 2 := by
        have hh : |angleDifference (by omega) θ j| ^ 2 ≤
            (10 * B / n ^ 2) ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hη'
        simpa only [sq_abs] using hh
      have hbsq : (angleAverage (by omega) θ j) ^ 2 ≤
          (1 / (1000 * n)) ^ 2 := by
        have hh : |angleAverage (by omega) θ j| ^ 2 ≤
            (1 / (1000 * n)) ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb
        simpa only [sq_abs] using hh
      have hAsq : (Real.pi / n + angleDifference (by omega) θ j / 2) ^ 2 ≤
          ((4 + 5 * B) / n) ^ 2 := by
        have hh : |Real.pi / n + angleDifference (by omega) θ j / 2| ^ 2 ≤
            ((4 + 5 * B) / n) ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr haeta
        simpa only [sq_abs] using hh
      have hfirst : (angleDifference (by omega) θ j) ^ 2 / 2 ≤
          50 * B ^ 2 / n ^ 4 := by
        calc
          _ ≤ (10 * B / n ^ 2) ^ 2 / 2 := by gcongr
          _ = 50 * B ^ 2 / n ^ 4 := by ring
      have hsecond :
          (Real.pi / n + angleDifference (by omega) θ j / 2) ^ 2 *
              (angleAverage (by omega) θ j) ^ 2 ≤
            (4 + 5 * B) ^ 2 / (1000000 * n ^ 4) := by
        calc
          _ ≤ ((4 + 5 * B) / n) ^ 2 *
              (1 / (1000 * n)) ^ 2 :=
            mul_le_mul hAsq hbsq (sq_nonneg _) (by positivity)
          _ = (4 + 5 * B) ^ 2 / (1000000 * n ^ 4) := by ring
      have hraw :
          |(2 - chordLength (by omega) θ j) /
              Real.cos (angleAverage (by omega) θ j) -
            (2 - 2 * Real.cos (Real.pi / n)) -
            Real.sin (Real.pi / n) * angleDifference (by omega) θ j| ≤
          angleDifference (by omega) θ j ^ 2 / 2 +
            (Real.pi / n + angleDifference (by omega) θ j / 2) ^ 2 *
              angleAverage (by omega) θ j ^ 2 := by
        convert hscalar using 1;
          simp only [FixedSchurChartRotated.chordLength, n,
            Nat.cast_mul, Nat.cast_ofNat]
      have hsum := add_le_add hfirst hsecond
      exact hraw.trans (by
        convert hsum using 1; ring)
    have hnum' :
        |(2 - chordLength (by omega) θ j) /
            Real.cos (angleAverage (by omega) θ j) -
          (2 - 2 * Real.cos (Real.pi / ((2 * m : ℕ) : ℝ))) -
          Real.sin (Real.pi / ((2 * m : ℕ) : ℝ)) * angleDifference (by omega) θ j| ≤
          (50 * B ^ 2 + (4 + 5 * B) ^ 2 / 1000000) /
            ((2 * m : ℕ) : ℝ) ^ 4 := by
      simpa only [n, Nat.cast_mul, Nat.cast_ofNat] using hnum
    have hK :
        50 * B ^ 2 + (4 + 5 * B) ^ 2 / 1000000 ≤
          4000 * (1 + B) ^ 2 := by
      nlinarith [sq_nonneg B, sq_nonneg (1 + B)]
    have hε : 0 < epsilon (2 * m) := epsilon_pos (by omega)
    have hinv : (epsilon (2 * m))⁻¹ ≤ ((2 * m : ℕ) : ℝ) ^ 2 / 4 := by
      have hh := (scale_bounds (show 2 ≤ 2 * m by omega)).2
      rw [epsilon_inv (show 2 ≤ 2 * m by omega)]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
    have hcoef0 : |angularErrorCoefficient (by omega) θ j| ≤
        (50 * B ^ 2 + (4 + 5 * B) ^ 2 / 1000000) /
          (4 * ((2 * m : ℕ) : ℝ) ^ 2) := by
      unfold angularErrorCoefficient
      rw [abs_div, abs_of_pos hε]
      have hden : 0 ≤ (epsilon (2 * m))⁻¹ := le_of_lt (inv_pos.mpr hε)
      calc
        _ ≤ ((50 * B ^ 2 + (4 + 5 * B) ^ 2 / 1000000) /
            ((2 * m : ℕ) : ℝ) ^ 4) /
            epsilon (2 * m) := div_le_div_of_nonneg_right hnum' hε.le
        _ = (epsilon (2 * m))⁻¹ *
            ((50 * B ^ 2 + (4 + 5 * B) ^ 2 / 1000000) /
              ((2 * m : ℕ) : ℝ) ^ 4) := by
          rw [inv_eq_one_div]
          ring
        _ ≤ (((2 * m : ℕ) : ℝ) ^ 2 / 4) *
            ((50 * B ^ 2 + (4 + 5 * B) ^ 2 / 1000000) /
              ((2 * m : ℕ) : ℝ) ^ 4) := by
          gcongr
        _ = (50 * B ^ 2 + (4 + 5 * B) ^ 2 / 1000000) /
              (4 * ((2 * m : ℕ) : ℝ) ^ 2) := by
          field_simp
    have htarget :
        (50 * B ^ 2 + (4 + 5 * B) ^ 2 / 1000000) /
            (4 * ((2 * m : ℕ) : ℝ) ^ 2) ≤
          angularSupConstant B / ((2 * m : ℕ) : ℝ) ^ 2 := by
      have hid :
          (50 * B ^ 2 + (4 + 5 * B) ^ 2 / 1000000) /
              (4 * ((2 * m : ℕ) : ℝ) ^ 2) =
            (50 * B ^ 2 + (4 + 5 * B) ^ 2 / 1000000) / 4 /
              ((2 * m : ℕ) : ℝ) ^ 2 := by
        ring
      rw [hid]
      apply (div_le_div_iff_of_pos_right (sq_pos_of_pos (by positivity))).2
      unfold angularSupConstant
      nlinarith [hK]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcoef0.trans htarget
  have hpbound : ∀ j : Fin (2 * m),
      |rotatedP (by omega) v (coordinate (by omega) s θ v) j| ≤
        normalPConstant B := by
    intro j
    have hJnorm := FixedSchurHarmonicBounds.J_norm_le (by omega)
      (coordinate (by omega) s θ v)
    have hJpoint : |J (coordinate (by omega) s θ v) j| ≤
        ‖J (coordinate (by omega) s θ v)‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (J (coordinate (by omega) s θ v)) j)
    have hJ : |J (coordinate (by omega) s θ v) j| ≤ 10 := by
      exact hJpoint.trans (hJnorm.trans (by nlinarith [hp.norm_le]))
    have ht := tangent_abs_le_of_joint_energy (by omega) θ v hB hdom henergy j
    unfold rotatedP
    rw [Pi.add_apply]
    exact (abs_add_le _ _).trans (by
      unfold normalPConstant
      linarith)
  have hsbound : ∀ j : Fin (2 * m),
      |rotatedS (by omega) θ v (coordinate (by omega) s θ v) j| ≤
        normalSConstant B := by
    intro j
    have hq : |coordinate (by omega) s θ v j| ≤ 5 := by
      simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (coordinate (by omega) s θ v) j).trans hp.norm_le
    have hPj := hpbound j
    have hb := hs.1 j
    unfold rotatedS
    have hb1 : |angleAverage (by omega) θ j| ≤ 1 := by
      have hn1 : (1 : ℝ) ≤ (2 * m : ℝ) := by
        exact_mod_cast (show 1 ≤ 2 * m by omega)
      have hden : 0 < 1000 * (2 * m : ℝ) := by positivity
      have hmul := (le_div_iff₀ hden).mp hb
      nlinarith
    have hstarget : normalPConstant B + 5 ≤ normalSConstant B := by
      unfold normalPConstant normalSConstant
      linarith
    exact (tangential_abs_le hb1 hq hPj hP).trans hstarget
  have hcos : ∀ j : Fin (2 * m),
      (1 / 2 : ℝ) ≤ Real.cos (angleAverage (by omega) θ j) := by
    intro j
    have hb := hs.1 j
    have hh := Real.one_sub_sq_div_two_le_cos
      (x := angleAverage (by omega) θ j)
    have hsq : (angleAverage (by omega) θ j) ^ 2 ≤ 1 := by
      have hh' : |angleAverage (by omega) θ j| ≤ 1 := by
        have hn1 : (1 : ℝ) ≤ (2 * m : ℝ) := by
          exact_mod_cast (show 1 ≤ 2 * m by omega)
        have hden : 0 < 1000 * (2 * m : ℝ) := by positivity
        have hmul := (le_div_iff₀ hden).mp hb
        nlinarith
      nlinarith [sq_abs (angleAverage (by omega) θ j), abs_le.mp hh']
    nlinarith
  exact ⟨hcoeff, hpbound, hsbound, hcos⟩



end
end StructuralNote.ExplicitComparisonGeometry

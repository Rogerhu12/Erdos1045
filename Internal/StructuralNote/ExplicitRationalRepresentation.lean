import StructuralNote.ExplicitRationalWindow
import StructuralNote.ExplicitCanonicalEntrySelected
import StructuralNote.FixedSchurRationalWindowRepresentation
/-! The rational selection window gives the literal selected fixed-Schur chart. -/
namespace StructuralNote.ExplicitRationalRepresentation
open Erdos1045 Erdos1045.EventualExact Complex Filter
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open RationalCommonConfiguration RationalAngleBranch RationalChart
open CommonTangentialParameters CommonFiberBounds CommonFiberGeometry
open CommonDomainClosure CommonDomainRadius CommonFiberNormalProjectionScaled
open EdgeCoordinates FixedSchurData FixedSchurLinear FixedSchurProjectionDomain
open FixedSchurChart FixedSchurEdgeGeometry FixedSchurLogBoundedRepresentation
open FixedSchurDomainSmallness
open FixedSchurRationalWindowEnergy FixedSchurRationalWindowDomain
open LensClosure
open scoped BigOperators Topology
open FixedSchurRationalWindowRepresentation
noncomputable section

def orderThreshold : ℕ := max ExplicitHessianThreshold.orderThreshold
  (ExplicitCanonicalEntrySelected.representationThreshold MatchingActivityActualChart.actualConstraintConstant)

theorem actualConstraint_lower : representationConstraintConstant ≤
    MatchingActivityActualChart.actualConstraintConstant := by
  have ha : 0 ≤ StrongBudgetConsequences.angleConstant := by
    unfold StrongBudgetConsequences.angleConstant
    positivity
  have hc : 0 ≤ StrongBudgetConsequences.centerConstant := by
    unfold StrongBudgetConsequences.centerConstant
    positivity
  have hp := mul_nonneg ha hc
  unfold representationConstraintConstant MatchingActivityActualChart.actualConstraintConstant
    StrongPointwiseSteps.physicalStepConstant StrongPointwiseSteps.centerStepConstant
  linarith only [ha, hp, Real.pi_gt_three]

private theorem normal_abs_le_scale_difference {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → ℂ) (j : Fin n) :
    |EdgeCoordinates.normal (by omega) v j| ≤
      scale n * ‖difference (by omega) v j‖ := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsin : 0 < Real.sin (Real.pi / n) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · apply (div_lt_iff₀ hnR).2
      have hnR2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [Real.pi_pos]
  have hnormal : |EdgeCoordinates.normal (by omega) v j| ≤
      ‖(n : ℂ) * edgeRatio (by omega) v j‖ := by
    calc
      |EdgeCoordinates.normal (by omega) v j| ≤
          ‖(EdgeCoordinates.tangent (by omega) v j : ℂ) -
            I * (EdgeCoordinates.normal (by omega) v j : ℂ)‖ := by
        have h := Complex.abs_im_le_norm
          ((EdgeCoordinates.tangent (by omega) v j : ℂ) -
            I * (EdgeCoordinates.normal (by omega) v j : ℂ))
        simpa only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
          zero_add, zero_sub, abs_neg] using h
      _ = ‖(n : ℂ) * edgeRatio (by omega) v j‖ := by
        rw [EdgeCoordinates.scaled_edgeRatio (by omega) v j]
  have href :
      ‖difference (by omega) (fun k => character n 1 k) j‖ =
        2 * Real.sin (Real.pi / n) := by
    rw [SchurLift.reference_difference (by omega) j]
    simp only [norm_mul, norm_real, Real.norm_eq_abs, Complex.norm_I,
      FixedSchurData.norm_frame]
    rw [abs_of_pos hsin]
    norm_num
  calc
    |EdgeCoordinates.normal (by omega) v j| ≤
        ‖(n : ℂ) * edgeRatio (by omega) v j‖ := hnormal
    _ = (n : ℝ) * ‖edgeRatio (by omega) v j‖ := by
      simp only [norm_mul, Complex.norm_natCast]
    _ = (n : ℝ) *
        (‖difference (by omega) v j‖ / (2 * Real.sin (Real.pi / n))) := by
      rw [edgeRatio_eq_difference, norm_div, href]
    _ = scale n * ‖difference (by omega) v j‖ := by
      unfold scale
      field_simp

theorem reference_constraint_norm {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m)),
        ‖constraint (by omega) (fixedReferenceCenter (by omega) s)‖ ≤ 5 := by
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties hN
  clear hN
  intro hm s
  have hp := hprops hm s (0 : Fin (2 * m) → ℝ) (0 : Fin (2 * m) → ℂ)
    (zero_inDomain (by omega : 0 < m))
  have heq : constraint (by omega) (fixedReferenceCenter (by omega) s) =
      coordinate (by omega) s 0 0 := by
    unfold fixedReferenceCenter
    apply center_constraint hm
    funext j
    simp [constraint, difference]
  rw [heq]
  exact hp.norm_le

/-- The rational single window bounds the actual normalized center's normal
coordinate by a fixed multiple of the logarithmic scale. -/

theorem normalizedCenter_constraint_bound {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        ‖constraint (by omega)
          (normalizedCenter (by omega) (rationalSign s) X)‖ ≤
            representationConstraintConstant * (logOrder (2 * m) : ℝ) := by
  have href := ExplicitRationalWindow.fixedReferenceCenter_data hN
  have hrefNorm := reference_constraint_norm hN
  have hs := ExplicitRationalWindow.window_error_small hN
  have hn := ExplicitHessianThreshold.order_pos hN
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs hn
  have hm1 : (1 : ℝ) ≤ 2 * m := by
    have hh := ExplicitHessianThreshold.two_fifty_six_le_order hN
    exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hl : 0 ≤ Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 := by
    exact div_nonneg (Real.log_nonneg hm1) (sq_nonneg _)
  have herr : 384480 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 < 3 / 4 := by
    rw [mul_div_assoc] at hs ⊢
    linarith only [hs, hl]
  clear hs hn hm1 hl
  clear hN
  intro hm s X hwindow
  let C := normalizedCenter (by omega : 0 < m) (rationalSign s) X
  let R := fixedReferenceCenter (by omega : 0 < m) s
  let D := C - R
  let Ex := pairEnergy (by omega : 0 < 2 * m)
    (fun j => (extendedAngleParameter (by omega : 0 < m) X j : ℂ))
  let AR := pairEnergy (by omega : 0 < 2 * m)
    (rationalCenter (by omega : 0 < m) (rationalSign s) X - R)
  let Aref := pairEnergy (by omega : 0 < 2 * m) R
  let L : ℝ := logOrder (2 * m)
  have hEx0 : 0 ≤ Ex := pairEnergy_nonneg _ _
  have hAR0 : 0 ≤ AR := pairEnergy_nonneg _ _
  have hAref0 : 0 ≤ Aref := pairEnergy_nonneg _ _
  have hL0 : 0 ≤ L := by positivity
  have halpha := angleMean_sq_le (by omega : 0 < m) X
  have hcenter := normalizedCenter_reference_energy_le (by omega : 0 < m) s X
  have hrot : 5 * angleMean (by omega : 0 < m) X ^ 2 * Aref ≤
      (384480 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2) * Ex := by
    have h1 := mul_le_mul_of_nonneg_left halpha (by norm_num : (0 : ℝ) ≤ 5)
    have h2 := mul_le_mul_of_nonneg_right h1 hAref0
    have hbound := (href hm s).2.2
    have hlog0 : 0 ≤ Real.log (2 * m : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 2 * m by omega)
    have hcoef0 : 0 ≤ 5 *
        (48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * Ex) := by
      positivity
    calc
      _ ≤ 5 * (48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * Ex) * Aref := by
        simpa only [Ex, Aref] using h2
      _ ≤ 5 * (48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * Ex) * 1602 :=
        mul_le_mul_of_nonneg_left hbound hcoef0
      _ = _ := by ring
  have hrot' : 5 * angleMean (by omega : 0 < m) X ^ 2 * Aref ≤
      (3 / 4 : ℝ) * Ex :=
    hrot.trans (mul_le_mul_of_nonneg_right herr.le hEx0)
  have hDenergy : pairEnergy (by omega) D ≤ 2 * (Ex + AR) := by
    change pairEnergy _
      (normalizedCenter (by omega) (rationalSign s) X -
        fixedReferenceCenter (by omega) s) ≤ _
    change pairEnergy _ _ ≤ (5 / 4 : ℝ) * AR +
      5 * angleMean (by omega : 0 < m) X ^ 2 * Aref at hcenter
    nlinarith only [hcenter, hrot', hEx0, hAR0]
  have hQ : Ex + AR < L ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
    simpa only [selectedWindowEnergy, Ex, AR, R, L] using hwindow
  have hDscaled : pairEnergy (by omega) D ≤ (L / 2) ^ 2 / (2 * m : ℝ) ^ 2 := by
    calc
      _ ≤ 2 * (Ex + AR) := hDenergy
      _ ≤ 2 * (L ^ 2 / (8 * (2 * m : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hQ.le (by norm_num)
      _ = _ := by ring
  have hDscaled' : pairEnergy (by omega) D ≤
      (L / 2) ^ 2 / ((2 * m : ℕ) : ℝ) ^ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hDscaled
  have hnormalD : ‖constraint (by omega) D‖ ≤ (5 / 4 : ℝ) * L := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hL0)).2
    intro j
    rw [← normal_eq_constraint hm D]
    simp only [Real.norm_eq_abs]
    have hn := normal_abs_le_scale_difference (show 2 ≤ 2 * m by omega) D j
    have hd := difference_of_scaled_energy (show 0 < 2 * m by omega) D
      (L := L / 2) (div_nonneg hL0 (by norm_num)) hDscaled' j
    have hd' : ‖difference (by omega) D j‖ ≤
        10 * (L / 2) / (2 * m : ℝ) ^ 2 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hd
    have hs := (scale_bounds (show 2 ≤ 2 * m by omega)).2
    have hs' : scale (2 * m) ≤ (2 * m : ℝ) ^ 2 / 4 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs
    calc
      _ ≤ scale (2 * m) * ‖difference (by omega) D j‖ := hn
      _ ≤ ((2 * m : ℝ) ^ 2 / 4) *
          (10 * (L / 2) / (2 * m : ℝ) ^ 2) :=
        mul_le_mul hs' hd' (norm_nonneg _) (by positivity)
      _ = (5 / 4 : ℝ) * L := by field_simp; ring
  have hconstraint : constraint (by omega) C =
      constraint (by omega) D + constraint (by omega) R := by
    rw [← constraint_add (show 2 ≤ 2 * m by omega)]
    congr 1
    dsimp [D]
    abel
  rw [hconstraint]
  calc
    _ ≤ ‖constraint (by omega) D‖ + ‖constraint (by omega) R‖ := norm_add_le _ _
    _ ≤ (5 / 4 : ℝ) * L + 5 := add_le_add hnormalD (hrefNorm hm s)
    _ ≤ representationConstraintConstant * L := by
      have hL1 : 1 ≤ L := by
        dsimp [L]
        exact FixedSchurDomainSmallness.logOrder_one_le (show 2 ≤ 2 * m by omega)
      norm_num [representationConstraintConstant]
      linarith

/-- The normalized fixed-Schur vertices are exactly a rotation and translation
of the actual rational configuration.  This identity is global in the rational
variables and needs no small-window assumption. -/

theorem selectedWindow_representation {m : ℕ} (hN : orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        RationalConfiguration.closure (by omega) (rationalSign s) X = 0 →
        let C := normalizedCenter (by omega) (rationalSign s) X
        let v := projection hm C
        constraint (by omega) C = coordinate (by omega) s (theta (by omega) X) v ∧
          C = center (coordinate (by omega) s (theta (by omega) X) v) v ∧
          vertex (theta (by omega) X) C =
            FixedSchurChart.configuration (by omega) s (theta (by omega) X) v ∧
          (vertex (theta (by omega) X) C = fun j =>
            unit (-angleMean (by omega) X) *
              (RationalConfiguration.configuration (by omega) (rationalSign s) X j -
                centerMean (by omega) (rationalSign s) X)) ∧
          ‖constraint (by omega) C - baseWord (FiniteBox.patternSign s)‖ ≤
            radius (2 * m) := by
  have hbase := (le_max_left _ _).trans hN
  have hrepN := (le_max_right _ _).trans hN
  have hdomain := ExplicitRationalWindow.selectedWindow_inDomain hbase
  have hnormal := normalizedCenter_constraint_bound hbase
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties hbase
  clear hbase
  clear hN
  intro hm s X hwindow hclosure
  dsimp only
  let C := normalizedCenter (by omega : 0 < m) (rationalSign s) X
  let v := projection hm C
  have hC := normalizedCenter_halfPeriodic (by omega : 0 < m) (rationalSign s) X
  have hmean := normalizedCenter_mean_zero (by omega : 0 < m) (rationalSign s) X
  have hdom := hdomain hm s X hwindow
  have hqnorm := hnormal hm s X hwindow
  have hcross := normalizedCenter_selectedCrossing hm s X hclosure
  have hnorm : ‖constraint (by omega) C‖ ≤
      MatchingActivityActualChart.actualConstraintConstant * (logOrder (2 * m) : ℝ) :=
    hqnorm.trans (mul_le_mul_of_nonneg_right actualConstraint_lower (Nat.cast_nonneg _))
  have hrep := ExplicitCanonicalEntrySelected.selected_chart_representation hm hrepN s
    (theta (by omega) X) C hdom.1 hdom.2.1 hC hmean hdom hnorm hcross
  have hrigid := vertex_normalizedCenter_eq_rigid (by omega : 0 < m)
    (rationalSign s) X
  have hp := hprops hm s (theta (by omega) X) v hdom
  refine ⟨hrep.1, hrep.2.1, hrep.2.2, hrigid, ?_⟩
  rw [hrep.1]
  exact hp.close

end
end StructuralNote.ExplicitRationalRepresentation

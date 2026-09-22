import StructuralNote.ExplicitComparisonScalars
import StructuralNote.ExplicitHessianThresholdFixedSchur
import StructuralNote.FixedSchurNormalExpansion

/-! The positive rotated branch at an explicit order. -/
namespace StructuralNote.ExplicitComparisonRotated
open scoped BigOperators Topology
open Complex Set Erdos1045 Erdos1045.EventualExact
open FiniteBox FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonClosureEnergy CommonDomainClosure CommonDomainRadius CommonFiberBounds
open CommonFiberNonlocalFrames CommonFiberNonlocalProjection CommonTangentialParameters
open EdgeCoordinates FixedSchurData FixedSchurDomainSmallness FixedSchurChart
open FixedSchurChartRadial FixedSchurEquations FixedSchurLinear FixedSchurChartRotated
open FixedSchurRotatedAlgebra FixedSchurExistence FixedSchurRadialAlgebra FixedSchurNormalExpansion
noncomputable section

theorem radial_coefficient {n : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ n) :
    Real.pi ^ 2 + FixedSchurRadialLimits.error n ≤ 10 := by
  have hL := ExplicitHessianThreshold.logOrder_bound hN
  have hLdiv := div_le_div_of_nonneg_right hL (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hs := ExplicitHessianThresholdFixedSchur.domain_log_scale hN
  have hh := ExplicitHessianThreshold.log_monomial_div_small (j := 1) (c := 66368) hN
    (by norm_num) (by norm_num)
  simp only [pow_one] at hh
  have hprod := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ 416 * ((logOrder n : ℝ) / n))
  have he : FixedSchurRadialLimits.error n ≤
      66368 * Erdos1045.ExplicitThreshold.logBudget n / n := by
    calc
      _ = 32768 * ((logOrder n : ℝ) / n) +
          416 * ((logOrder n : ℝ) / n) * ((logOrder n : ℝ) * (1 + Real.log n) / n) := by
        unfold FixedSchurRadialLimits.error FixedSchurDomainSmallness.radius
        ring
      _ ≤ 33184 * ((logOrder n : ℝ) / n) := by linarith only [hprod]
      _ ≤ 33184 * (2 * Erdos1045.ExplicitThreshold.logBudget n / n) :=
        mul_le_mul_of_nonneg_left hLdiv (by norm_num)
      _ = _ := by ring
  nlinarith only [he, hh, Real.pi_lt_d2, Real.pi_pos]

theorem coordinate_radial {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → ∀ j,
      |radial (meanFrame (by omega) θ j)
        (difference (by omega) (center (coordinate (by omega) s θ v) v) j)| ≤
          10 / (2 * m : ℝ) ^ 2 := by
  have hprop := ExplicitHessianThresholdFixedSchur.coordinate_properties hN
  have hcoef : Real.pi ^ 2 + FixedSchurRadialLimits.error (2 * m) ≤ 10 := radial_coefficient hN
  clear hN
  intro hm s θ v hdom j
  have hp := hprop hm s θ v hdom
  exact (domain_radial_bound hm θ v _ _ hdom (FiniteBox.patternSign_is_sign s)
    hp.close hp.norm_le j).trans
      (div_le_div_of_nonneg_right hcoef (sq_nonneg _))


private theorem chordLength_ge_one_of_abs_le_one {n : ℕ} (hn : 0 < n)
    (θ : Fin n → ℝ) (j : Fin n)
    (ha : |Real.pi / (n : ℝ) + angleDifference hn θ j / 2| ≤ 1) :
    1 ≤ chordLength hn θ j := by
  unfold chordLength
  have ha2 : (Real.pi / (n : ℝ) + angleDifference hn θ j / 2) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr ha
  have hc := Real.one_sub_sq_div_two_le_cos
    (x := Real.pi / (n : ℝ) + angleDifference hn θ j / 2)
  nlinarith

private theorem cos_angleAverage_pos_of_abs_le_one {n : ℕ} (hn : 0 < n)
    (θ : Fin n → ℝ) (j : Fin n)
    (hb : |angleAverage hn θ j| ≤ 1) :
    0 < Real.cos (angleAverage hn θ j) := by
  apply Real.cos_pos_of_mem_Ioo
  have hb' := abs_le.mp hb
  constructor <;> nlinarith [Real.pi_gt_three]

theorem angle_smallness {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      (∀ j : Fin (2 * m),
        |angleAverage (by omega) θ j| ≤ 1) ∧
      (∀ j : Fin (2 * m),
        |Real.pi / (2 * m : ℝ) +
          angleDifference (by omega) θ j / 2| ≤ 1) := by
  have hs := ExplicitComparisonScalars.small_coefficients hN
  clear hN
  intro hm θ v hdom
  have hscale : (10 * (logOrder (2 * m) : ℝ) + 1049) /
      (2 * m : ℝ) ^ 2 ≤ 1 / (1000 * (2 * m : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs.2.2.2
  have havg0 := domain_angleAverage_bound_all (by omega) θ v hdom
  have hdiff0 := domain_angle_difference (by omega) θ v hdom
  have havg : ∀ j : Fin (2 * m), |angleAverage (by omega) θ j| ≤ 1 := by
    intro j
    have hNpos : (0 : ℝ) < 2 * m := by positivity
    have hlog : 0 ≤ (logOrder (2 * m) : ℝ) := by positivity
    have hsqlog : 0 ≤ Real.sqrt (Real.log (2 * m : ℝ)) := Real.sqrt_nonneg _
    have hbase := havg0 j
    have hsqrt : Real.sqrt (Real.log (2 * m : ℝ)) ≤
        1 + Real.log (2 * m : ℝ) := by
      have hlog' : 0 ≤ Real.log (2 * m : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * m by omega))
      apply (Real.sqrt_le_iff).2
      constructor
      · linarith
      · nlinarith [sq_nonneg (Real.log (2 * m : ℝ))]
    have hsavg : 4 * (logOrder (2 * m) : ℝ) *
        Real.sqrt (Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 ≤
        1 / (1000 * (2 * m : ℝ)) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs.2.2.1
    have hsmall : |angleAverage (by omega) θ j| ≤
        1 / (1000 * (2 * m : ℝ)) := hbase.trans hsavg
    have hsmall_le_one : 1 / (1000 * (2 * m : ℝ)) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * (2 * m : ℝ))).2
      have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
    exact hsmall.trans hsmall_le_one
  refine ⟨havg, ?_⟩
  intro j
  have hdiff := hdiff0 j
  have hdiff' : |angleDifference (by omega) θ j| ≤
      1 / (1000 * (2 * m : ℝ)) := by
    have hraw := hscale
    have hL : (10 * (logOrder (2 * m) : ℝ)) ≤
        10 * (logOrder (2 * m) : ℝ) + 1049 := by linarith
    have hnonneg : 0 ≤ (2 * m : ℝ) ^ 2 := sq_nonneg _
    have hbound : 10 * (logOrder (2 * m) : ℝ) /
        (2 * m : ℝ) ^ 2 ≤
        (10 * (logOrder (2 * m) : ℝ) + 1049) /
          (2 * m : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right hL hnonneg
    exact hdiff.trans (hbound.trans hscale)
  have hpi : |Real.pi / (2 * m : ℝ)| = Real.pi / (2 * m : ℝ) :=
    abs_of_pos (by positivity)
  have hsum := abs_add_le (Real.pi / (2 * m : ℝ))
    (angleDifference (by omega) θ j / 2)
  rw [hpi, abs_div] at hsum
  norm_num at hsum
  have hpi' : Real.pi / (2 * m : ℝ) ≤ 4 / (2 * m : ℝ) := by
    exact div_le_div_of_nonneg_right Real.pi_lt_four.le (by positivity)
  have hsmall := hdiff'
  have hfour : 4 / (2 * m : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 * m : ℝ))).2
    have hn16 : (16 : ℝ) ≤ 2 * m := by exact_mod_cast hs.1
    nlinarith
  have hsmall_le_one : 1 / (1000 * (2 * m : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * (2 * m : ℝ))).2
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  nlinarith [hsum, hpi', hfour, hsmall, hsmall_le_one]


theorem coordinate_rotated {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → ∀ j : Fin (2 * m),
      0 < Real.cos (angleAverage (by omega) θ j) ∧
      1 ≤ chordLength (by omega) θ j ∧
      ((chordLength (by omega) θ j *
          Real.cos (angleAverage (by omega) θ j) +
          patternSign s j * epsilon (2 * m) * coordinate (by omega) s θ v j) ^ 2 +
        (chordLength (by omega) θ j *
          Real.sin (angleAverage (by omega) θ j) +
          patternSign s j * epsilon (2 * m) *
            (J (coordinate (by omega) s θ v) + tangent (by omega) v) j) ^ 2 = 4) ∧
      0 < chordLength (by omega) θ j + patternSign s j * epsilon (2 * m) *
        FixedSchurRotatedAlgebra.radial (angleAverage (by omega) θ j)
          (coordinate (by omega) s θ v j)
          ((J (coordinate (by omega) s θ v) + tangent (by omega) v) j) ∧
      FixedSchurRotatedAlgebra.radial (angleAverage (by omega) θ j)
          (coordinate (by omega) s θ v j)
          ((J (coordinate (by omega) s θ v) + tangent (by omega) v) j) =
        patternSign s j / epsilon (2 * m) *
          (Real.sqrt (4 -
            (epsilon (2 * m) *
              FixedSchurRotatedAlgebra.tangential (angleAverage (by omega) θ j)
                (coordinate (by omega) s θ v j)
                ((J (coordinate (by omega) s θ v) + tangent (by omega) v) j)) ^ 2) -
            chordLength (by omega) θ j) ∧
      coordinate (by omega) s θ v j =
        patternSign s j / epsilon (2 * m) *
            ((2 - chordLength (by omega) θ j) /
              Real.cos (angleAverage (by omega) θ j)) -
          ((J (coordinate (by omega) s θ v) + tangent (by omega) v) j) *
            Real.tan (angleAverage (by omega) θ j) -
          patternSign s j * epsilon (2 * m) *
            (FixedSchurRotatedAlgebra.tangential (angleAverage (by omega) θ j)
              (coordinate (by omega) s θ v j)
              ((J (coordinate (by omega) s θ v) + tangent (by omega) v) j)) ^ 2 /
              (Real.cos (angleAverage (by omega) θ j) *
                (2 + Real.sqrt (4 -
                  (epsilon (2 * m) *
                    FixedSchurRotatedAlgebra.tangential (angleAverage (by omega) θ j)
                      (coordinate (by omega) s θ v j)
                      ((J (coordinate (by omega) s θ v) + tangent (by omega) v) j)) ^ 2))) := by
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties hN
  have hinput := ExplicitHessianThresholdFixedSchur.ball_positive_input hN
  have hrad := coordinate_radial hN
  have hangle := angle_smallness hN
  have hm8 : 8 ≤ m := by have := ExplicitHessianThreshold.two_fifty_six_le_order hN; omega
  clear hN
  intro hm s θ v hdom j
  have hp := hprops hm s θ v hdom
  have hσ := patternSign_is_sign s
  have harg_all := hinput (by omega) θ v (patternSign s) hdom hσ _ hp.close
  have harg := harg_all j
  have hsq := (solution_positive_branch (by omega) θ v (patternSign s)
    (coordinate (by omega) s θ v) hσ hp.fixed harg_all j).2
  have hX := X_eq_chordLength_mul_cos (by omega) θ hdom.1 j
  have hY := Y_eq_chordLength_mul_sin (by omega) θ hdom.1 j
  rw [hX, hY] at hsq
  have hangle' := hangle hm θ v hdom
  have hcos : 0 < Real.cos (angleAverage (by omega) θ j) :=
    cos_angleAverage_pos_of_abs_le_one (by omega) θ j (hangle'.1 j)
  have hangle_j : |Real.pi / ((2 * m : ℕ) : ℝ) +
      angleDifference (by omega) θ j / 2| ≤ 1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hangle'.2 j
  have hL : 1 ≤ chordLength (by omega) θ j :=
    chordLength_ge_one_of_abs_le_one (n := 2 * m) (by omega) θ j hangle_j
  have hrad := hrad hm s θ v hdom j
  rw [center_difference (by omega) (coordinate (by omega) s θ v) v
    hdom.2.2.1.2.2, radial_edgeIncrement] at hrad
  have hrad' :
      |epsilon (2 * m) * FixedSchurRotatedAlgebra.radial
          (angleAverage (by omega) θ j) (coordinate (by omega) s θ v j)
          ((J (coordinate (by omega) s θ v) + tangent (by omega) v) j)| ≤
        10 / (2 * m : ℝ) ^ 2 := by
    simpa only [FixedSchurRotatedAlgebra.radial, Pi.add_apply] using hrad
  have hσabs : |patternSign s j| = 1 := by
    rcases hσ j with h | h <;> simp [h]
  have hradσ :
      |patternSign s j * epsilon (2 * m) *
          FixedSchurRotatedAlgebra.radial (angleAverage (by omega) θ j)
            (coordinate (by omega) s θ v j)
            ((J (coordinate (by omega) s θ v) + tangent (by omega) v) j)| ≤
        10 / (2 * m : ℝ) ^ 2 := by
    simpa only [abs_mul, hσabs, one_mul, abs_of_pos
      (epsilon_pos (show 2 ≤ 2 * m by omega))] using hrad'
  have hsmallrad : 10 / (2 * m : ℝ) ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos (by positivity : (0 : ℝ) < 2 * m))).2
    have hm8R : (8 : ℝ) ≤ m := by exact_mod_cast hm8
    nlinarith
  have hpos :
      0 < chordLength (by omega) θ j + patternSign s j * epsilon (2 * m) *
        FixedSchurRotatedAlgebra.radial (angleAverage (by omega) θ j)
          (coordinate (by omega) s θ v j)
          ((J (coordinate (by omega) s θ v) + tangent (by omega) v) j) := by
    have hlow := (abs_le.mp hradσ).1
    nlinarith
  have hroot := rotated_root (L := chordLength (by omega) θ j)
    (ε := epsilon (2 * m)) (σ := patternSign s j)
    (b := angleAverage (by omega) θ j) (q := coordinate (by omega) s θ v j)
    (p := (J (coordinate (by omega) s θ v) + tangent (by omega) v) j)
    (epsilon_pos (show 2 ≤ 2 * m by omega)) (hσ j) hsq hpos
  have hrot := rotated_square (chordLength (by omega) θ j)
    (epsilon (2 * m)) (patternSign s j) (angleAverage (by omega) θ j)
    (coordinate (by omega) s θ v j)
    ((J (coordinate (by omega) s θ v) + tangent (by omega) v) j) (hσ j)
  have hradicand : 0 ≤ 4 -
      (epsilon (2 * m) *
        FixedSchurRotatedAlgebra.tangential (angleAverage (by omega) θ j)
          (coordinate (by omega) s θ v j)
          ((J (coordinate (by omega) s θ v) + tangent (by omega) v) j)) ^ 2 := by
    nlinarith [hrot, hsq]
  let H : ℝ := Real.sqrt (4 -
    (epsilon (2 * m) *
      FixedSchurRotatedAlgebra.tangential (angleAverage (by omega) θ j)
        (coordinate (by omega) s θ v j)
        ((J (coordinate (by omega) s θ v) + tangent (by omega) v) j)) ^ 2)
  have hH : H ^ 2 +
      (epsilon (2 * m) *
        FixedSchurRotatedAlgebra.tangential (angleAverage (by omega) θ j)
          (coordinate (by omega) s θ v j)
          ((J (coordinate (by omega) s θ v) + tangent (by omega) v) j)) ^ 2 = 4 := by
    have hradicand' : 0 ≤ 4 -
        (epsilon (2 * m) *
          FixedSchurRotatedAlgebra.tangential (angleAverage (by omega) θ j)
            (coordinate (by omega) s θ v j)
            (J (coordinate (by omega) s θ v) j + tangent (by omega) v j)) ^ 2 := by
      simpa only [Pi.add_apply] using hradicand
    dsimp [H]
    rw [Real.sq_sqrt hradicand']
    ring
  have hnormal := normal_expansion
    (L := chordLength (by omega) θ j) (ε := epsilon (2 * m))
    (σ := patternSign s j) (b := angleAverage (by omega) θ j)
    (q := coordinate (by omega) s θ v j)
    (p := (J (coordinate (by omega) s θ v) + tangent (by omega) v) j)
    (H := H)
    (ne_of_gt (epsilon_pos (show 2 ≤ 2 * m by omega))) hcos.ne' hH
    (by positivity) hroot
  refine ⟨hcos, hL, hsq, hpos, hroot, ?_⟩
  simpa only [H] using hnormal


theorem normalError_rotated_expansion {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → ∀ j : Fin (2 * m),
      normalError (by omega) θ (coordinate (by omega) s θ v)
          (FiniteBox.patternSign s) j =
        FiniteBox.patternSign s j * angularErrorCoefficient (by omega) θ j -
          rotatedP (by omega) v (coordinate (by omega) s θ v) j *
            Real.tan (angleAverage (by omega) θ j) -
          FiniteBox.patternSign s j * epsilon (2 * m) *
            (rotatedS (by omega) θ v (coordinate (by omega) s θ v) j) ^ 2 /
            (Real.cos (angleAverage (by omega) θ j) *
              (2 + rotatedH (by omega) θ v (coordinate (by omega) s θ v) j)) := by
  have hrot := coordinate_rotated hN
  clear hN
  intro hm s θ v hdom j
  have hr := hrot hm s θ v hdom j
  have hcoord := hr.2.2.2.2.2
  have hcoord' : coordinate (by omega) s θ v j =
      FiniteBox.patternSign s j / epsilon (2 * m) *
          ((2 - chordLength (by omega) θ j) /
            Real.cos (angleAverage (by omega) θ j)) -
        rotatedP (by omega) v (coordinate (by omega) s θ v) j *
          Real.tan (angleAverage (by omega) θ j) -
        FiniteBox.patternSign s j * epsilon (2 * m) *
          (rotatedS (by omega) θ v (coordinate (by omega) s θ v) j) ^ 2 /
          (Real.cos (angleAverage (by omega) θ j) *
            (2 + rotatedH (by omega) θ v (coordinate (by omega) s θ v) j)) := by
    simpa only [rotatedP, rotatedS, rotatedH] using hcoord
  have hden : 2 + rotatedH (by omega) θ v (coordinate (by omega) s θ v) j ≠ 0 := by
    have hh : 0 ≤ rotatedH (by omega) θ v (coordinate (by omega) s θ v) j :=
      Real.sqrt_nonneg _
    nlinarith
  simpa only [rotatedP, rotatedS, rotatedH] using
    (normalError_from_rotated_formula (by omega) (by omega) θ
      (coordinate (by omega) s θ v) (FiniteBox.patternSign s) j hr.1 hcoord' hden)



end
end StructuralNote.ExplicitComparisonRotated

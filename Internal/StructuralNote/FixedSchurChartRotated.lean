import StructuralNote.FixedSchurRotatedAlgebra
import StructuralNote.FixedSchurChartRadial
import StructuralNote.CommonFiberNonlocalSizes

/-! Exact polar coordinates for the actual fixed-Schur chord, followed by the
eventual positive rotated branch on the actual domain. -/

namespace StructuralNote.FixedSchurChartRotated

open scoped BigOperators Topology

open Complex Filter Set
open Erdos1045 Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.FiniteFourierLift
open Erdos1045.EventualExact.SchurLift
open Erdos1045.EventualExact.SchurSpectrum
open CommonClosureEnergy CommonDomainClosure CommonDomainRadius
open CommonFiberBounds CommonFiberNonlocalFrames CommonFiberNonlocalProjection
open CommonFiberNonlocalSizes CommonTangentialParameters
open EdgeCoordinates FixedSchurData FixedSchurDomainSmallness FixedSchurChart
open FixedSchurChartRadial FixedSchurEquations FixedSchurLinear
open FixedSchurRotatedAlgebra
open FixedSchurExistence
open FixedSchurRadialAlgebra

noncomputable section

def chordLength {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (j : Fin n) : ℝ :=
  2 * Real.cos (Real.pi / (n : ℝ) + angleDifference hn θ j / 2)

private theorem halfIndex_eq {m : ℕ} (j : Fin m) :
    BoxLensLift.halfIndex j = CommonClosureEnergy.halfIndex j := by
  apply Fin.ext
  rfl

private theorem angleDifference_halfTurn {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (j : Fin (2 * m)) :
    angleDifference (by omega) θ (halfTurn hm j) =
      angleDifference (by omega) θ j := by
  have hh (j : Fin (2 * m)) : θ (halfTurn hm j) = θ j :=
    Complex.ofReal_injective (hθ j)
  unfold angleDifference
  rw [← halfTurn_successor, hh, hh]

private theorem chordLength_halfIndex {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (j : Fin m) :
    chordLength (by omega) θ (CommonClosureEnergy.halfIndex j) =
      2 * Real.cos (halfAngle hm θ j) := by
  unfold chordLength halfAngle
  simp only [Nat.cast_mul, Nat.cast_ofNat]

private theorem chordLength_halfTurn {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (j : Fin (2 * m)) :
    chordLength (by omega) θ (halfTurn hm j) = chordLength (by omega) θ j := by
  unfold chordLength
  rw [angleDifference_halfTurn hm θ hθ]

theorem X_eq_chordLength_mul_cos {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (j : Fin (2 * m)) :
    X (by omega) θ j =
      chordLength (by omega) θ j * Real.cos (angleAverage (by omega) θ j) := by
  obtain ⟨k, hj | hj⟩ := half_decomposition hm j
  · rw [hj, halfIndex_eq k, X_halfIndex hm θ k, chordLength_halfIndex hm θ k]
  · rw [hj, X_halfTurn hm θ hθ, chordLength_halfTurn hm θ hθ,
      angleAverage_halfTurn hm θ hθ, halfIndex_eq k, X_halfIndex hm θ k,
      chordLength_halfIndex hm θ k]

theorem Y_eq_chordLength_mul_sin {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (j : Fin (2 * m)) :
    Y (by omega) θ j =
      chordLength (by omega) θ j * Real.sin (angleAverage (by omega) θ j) := by
  obtain ⟨k, hj | hj⟩ := half_decomposition hm j
  · rw [hj, halfIndex_eq k, Y_halfIndex hm θ k, chordLength_halfIndex hm θ k]
  · rw [hj, Y_halfTurn hm θ hθ, chordLength_halfTurn hm θ hθ,
      angleAverage_halfTurn hm θ hθ, halfIndex_eq k, Y_halfIndex hm θ k,
      chordLength_halfIndex hm θ k]

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

private theorem eventual_angle_smallness : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      (∀ j : Fin (2 * m),
        |angleAverage (by omega) θ j| ≤ 1) ∧
      (∀ j : Fin (2 * m),
        |Real.pi / (2 * m : ℝ) +
          angleDifference (by omega) θ j / 2| ≤ 1) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventual_small_coefficients
  filter_upwards [eventually_ge_atTop ((N + 15) / 2)] with m hmN
  intro hm θ v hdom
  have hnN : N ≤ 2 * m := by omega
  have hs := hN (2 * m) hnN
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

theorem eventual_coordinate_rotated : ∀ᶠ m : ℕ in atTop,
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
  filter_upwards [eventual_coordinate_properties, eventual_ball_positive_input,
    eventual_coordinate_radial, eventual_angle_smallness,
    eventually_ge_atTop 8] with m hprops hinput hrad hangle hm8
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

end
end StructuralNote.FixedSchurChartRotated

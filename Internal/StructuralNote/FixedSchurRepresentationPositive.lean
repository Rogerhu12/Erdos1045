import StructuralNote.FixedSchurRepresentation
import StructuralNote.FixedSchurChartRotated

/-! The positive branch in the representation theorem follows from the literal
common domain and the close-to-sign-word estimate.  No positive-branch
hypothesis is exposed at the final representation interface. -/

namespace StructuralNote.FixedSchurRepresentationPositive

open Filter
open Erdos1045 Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.FiniteFourierLift
open Erdos1045.EventualExact.SchurLift
open Erdos1045.EventualExact.SchurSpectrum
open CommonClosureEnergy CommonDomainClosure CommonDomainRadius CommonFiberBounds
open CommonFiberGeometry CommonFiberNonlocalSizes EdgeCoordinates
open FixedSchurData FixedSchurDomainBounds FixedSchurDomainSmallness
open FixedSchurLinear FixedSchurEdgeGeometry
open FixedSchurChart FixedSchurChartRotated FixedSchurExistence
open FixedSchurChartRadial
open FixedSchurProjectionDomain FixedSchurRepresentation
open scoped BigOperators Topology

noncomputable section

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

private theorem cos_ge_half_of_abs_le_one {n : ℕ} (hn : 0 < n)
    (θ : Fin n → ℝ) (j : Fin n)
    (ha : |angleAverage hn θ j| ≤ 1) :
    1 / 2 ≤ Real.cos (angleAverage hn θ j) := by
  have ha2 : (angleAverage hn θ j) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr ha
  have hc := Real.one_sub_sq_div_two_le_cos
    (x := angleAverage hn θ j)
  nlinarith

private theorem eventual_angle_bounds : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      (∀ j : Fin (2 * m),
        |angleAverage (by omega) θ j| ≤ 1) ∧
      (∀ j : Fin (2 * m),
        |Real.pi / (2 * m : ℝ) +
          angleDifference (by omega) θ j / 2| ≤ 1) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    CommonFiberNonlocalSizes.eventual_small_coefficients
  filter_upwards [eventually_ge_atTop ((N + 15) / 2)] with m hmN
  intro hm θ v hdom
  have hnN : N ≤ 2 * m := by omega
  have hs := hN (2 * m) hnN
  have havg0 := domain_angleAverage_bound_all (by omega) θ v hdom
  have hdiff0 := domain_angle_difference (by omega) θ v hdom
  have havg : ∀ j : Fin (2 * m), |angleAverage (by omega) θ j| ≤ 1 := by
    intro j
    have hsavg : 4 * (logOrder (2 * m) : ℝ) *
        Real.sqrt (Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 ≤
        1 / (1000 * (2 * m : ℝ)) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs.2.2.1
    have hsmall : |angleAverage (by omega) θ j| ≤
        1 / (1000 * (2 * m : ℝ)) := (havg0 j).trans hsavg
    have hsmall_le_one : 1 / (1000 * (2 * m : ℝ)) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * (2 * m : ℝ))).2
      have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
    exact hsmall.trans hsmall_le_one
  refine ⟨havg, ?_⟩
  intro j
  have hdiff' : |angleDifference (by omega) θ j| ≤
      1 / (1000 * (2 * m : ℝ)) := by
    have hscale :
        (10 * (logOrder (2 * m) : ℝ) + 1049) /
            (2 * m : ℝ) ^ 2 ≤ 1 / (1000 * (2 * m : ℝ)) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs.2.2.2
    have hL : 10 * (logOrder (2 * m) : ℝ) ≤
        10 * (logOrder (2 * m) : ℝ) + 1049 := by linarith
    have hbound : 10 * (logOrder (2 * m) : ℝ) /
        (2 * m : ℝ) ^ 2 ≤
        (10 * (logOrder (2 * m) : ℝ) + 1049) /
          (2 * m : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right hL (sq_nonneg _)
    exact (hdiff0 j).trans (hbound.trans hscale)
  have hpi : |Real.pi / (2 * m : ℝ)| = Real.pi / (2 * m : ℝ) :=
    abs_of_pos (by positivity)
  have hsum := abs_add_le (Real.pi / (2 * m : ℝ))
    (angleDifference (by omega) θ j / 2)
  rw [hpi, abs_div] at hsum
  norm_num at hsum
  have hpi' : Real.pi / (2 * m : ℝ) ≤ 4 / (2 * m : ℝ) :=
    div_le_div_of_nonneg_right Real.pi_lt_four.le (by positivity)
  have hfour : 4 / (2 * m : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 * m : ℝ))).2
    have hn16 : (16 : ℝ) ≤ 2 * m := by exact_mod_cast hs.1
    nlinarith
  have hsmall_le_one : 1 / (1000 * (2 * m : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * (2 * m : ℝ))).2
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  nlinarith [hsum, hpi', hfour, hdiff', hsmall_le_one]

theorem eventual_X_ge_half : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      ∀ j : Fin (2 * m), 1 / 2 ≤ X (by omega) θ j := by
  filter_upwards [eventual_angle_bounds] with m hangle
  intro hm θ v hdom j
  have ha := hangle hm θ v hdom
  have harg : |Real.pi / ((2 * m : ℕ) : ℝ) +
      angleDifference (by omega) θ j / 2| ≤ 1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using ha.2 j
  have hchord : 1 ≤ chordLength (by omega) θ j :=
    chordLength_ge_one_of_abs_le_one (by omega) θ j harg
  have hcos : 1 / 2 ≤ Real.cos (angleAverage (by omega) θ j) :=
    cos_ge_half_of_abs_le_one (by omega) θ j (ha.1 j)
  have hchord0 : (0 : ℝ) ≤ chordLength (by omega) θ j :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans hchord
  have hprod := mul_le_mul hchord hcos (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hchord0
  have hX := X_eq_chordLength_mul_cos (by omega) θ hdom.1 j
  rw [hX]
  simpa only [one_mul] using hprod

theorem eventual_constraint_epsilon_abs_le : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      ∀ q : Fin (2 * m) → ℝ,
        ‖q - baseWord (FiniteBox.patternSign s)‖ ≤ radius (2 * m) →
        ∀ j : Fin (2 * m),
          epsilon (2 * m) * |q j| ≤ 40 / (2 * m : ℝ) ^ 2 := by
  filter_upwards [eventual_domain_smallness] with m hsize
  intro hm s θ v hdom q hclose j
  have hs := FiniteBox.patternSign_is_sign s
  have hR := (hsize (by omega) θ v (FiniteBox.patternSign s)
    hdom hs).2.1
  have hnorm := close_norm_le_five hm (FiniteBox.patternSign s) q hs hR hclose
  have hqj : |q j| ≤ 5 := by
    have h := norm_le_pi_norm q j
    simpa only [Real.norm_eq_abs] using h.trans hnorm
  have hε := epsilon_le (show 2 ≤ 2 * m by omega)
  have hmul0 := mul_le_mul hε hqj (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 8 /
    ((2 * m : ℕ) : ℝ) ^ 2)
  have hmul : epsilon (2 * m) * |q j| ≤
      (8 / (2 * m : ℝ) ^ 2) * 5 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmul0
  calc
    epsilon (2 * m) * |q j| ≤ (8 / (2 * m : ℝ) ^ 2) * 5 := hmul
    _ = 40 / (2 * m : ℝ) ^ 2 := by ring

theorem eventually_representation_of_selected_crossing_positive :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
        (θ : Fin (2 * m) → ℝ) (C : Fin (2 * m) → ℂ),
        HalfPeriodic (by omega) C →
        (∑ j, C j) = 0 →
        InDomain (by omega) θ (projection hm C) →
        ‖constraint (by omega) C -
            baseWord (FiniteBox.patternSign s)‖ ≤ radius (2 * m) →
        (∀ j, ‖crossingVector hm θ C (FiniteBox.patternSign s) j‖ = 2) →
        constraint (by omega) C = coordinate (by omega) s θ (projection hm C) ∧
          C = center (coordinate (by omega) s θ (projection hm C))
            (projection hm C) ∧
          vertex θ C = FixedSchurChart.configuration (by omega) s θ
            (projection hm C) := by
  filter_upwards [eventual_coordinate_unique, eventual_ball_positive_input,
    eventual_X_ge_half, eventual_constraint_epsilon_abs_le,
    eventually_ge_atTop 5] with m huniq hinput hX heps hm5
  intro hm s θ C hC hCmean hdom hclose hcross
  have hθ := hdom.1
  have hθmean := hdom.2.1
  have hs := FiniteBox.patternSign_is_sign s
  have hsmall := hinput (by omega) θ (projection hm C)
    (FiniteBox.patternSign s) hdom hs _ hclose
  have hpos : ∀ j, 0 < X (by omega) θ j +
      FiniteBox.patternSign s j * epsilon (2 * m) *
        constraint (by omega) C j := by
    intro j
    have hXj := hX hm θ (projection hm C) hdom j
    have hepsj := heps hm s θ (projection hm C) hdom
      (constraint (by omega) C) hclose j
    have hσabs : |FiniteBox.patternSign s j| = 1 := by
      rcases hs j with h | h <;> simp [h]
    have herr :
        |FiniteBox.patternSign s j * epsilon (2 * m) *
            constraint (by omega) C j| ≤ 40 / (2 * m : ℝ) ^ 2 := by
      simpa only [abs_mul, hσabs,
        abs_of_pos (epsilon_pos (show 2 ≤ 2 * m by omega)), one_mul] using hepsj
    have hsmall : 40 / (2 * m : ℝ) ^ 2 < 1 / 2 := by
      apply (div_lt_iff₀ (sq_pos_of_pos (by positivity : (0 : ℝ) < 2 * m))).2
      have hm5R : (5 : ℝ) ≤ m := by exact_mod_cast hm5
      nlinarith
    have hlow := (abs_le.mp herr).1
    nlinarith
  exact representation_of_selected_crossing hm s θ C hθ hθmean hC hCmean hdom
    hclose hsmall hpos hcross
    (huniq (by omega) s θ (projection hm C) hdom)

end

end StructuralNote.FixedSchurRepresentationPositive

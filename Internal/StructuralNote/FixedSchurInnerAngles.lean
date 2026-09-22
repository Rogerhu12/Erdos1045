import StructuralNote.CommonFiberNormalMoments
import StructuralNote.CommonFiberNonlocalFrames
import StructuralNote.CommonFiberBounds
import StructuralNote.CommonFiberNormalProjectionScaled
import StructuralNote.CommonFiberNonlocalSizes
import StructuralNote.FixedSchurDomainBounds
import StructuralNote.MatchingActivityRadialProjection

/-! Inner angular and tangential estimates from the actual common domain and a
joint pair-energy budget.  The estimates are stated on the full even grid;
the half-grid forms used by the normal projection are included as well. -/

namespace StructuralNote.FixedSchurInnerAngles

open scoped BigOperators Topology

open Complex Filter
open Erdos1045 Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonClosureEnergy CommonDomainClosure CommonDomainRadius
open CommonTangentialParameters CommonFiberBounds CommonFiberNormalMoments
open CommonFiberNonlocalFrames CommonFiberNormalProjectionScaled
open CommonFiberNormalAverage CommonFiberSmallCoefficients
open EdgeCoordinates FixedSchurDomainBounds

noncomputable section

private theorem pairEnergy_angle_le {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) {B : ℝ} (_hB : 0 ≤ B)
    (henergy : pairEnergy (by omega) (fun j => (θ j : ℂ)) +
        pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2) :
    pairEnergy (by omega) (fun j => (θ j : ℂ)) ≤ B ^ 2 / (2 * m : ℝ) ^ 2 := by
  have hv := pairEnergy_nonneg (by omega) v
  linarith

private theorem pairEnergy_tangent_le {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) {B : ℝ} (_hB : 0 ≤ B)
    (henergy : pairEnergy (by omega) (fun j => (θ j : ℂ)) +
        pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2) :
    pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2 := by
  have hθ := pairEnergy_nonneg (by omega) (fun j => (θ j : ℂ))
  linarith

private theorem angleDifference_halfTurn {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (j : Fin (2 * m)) :
    angleDifference (by omega) θ (halfTurn hm j) =
      angleDifference (by omega) θ j := by
  have hh (k : Fin (2 * m)) : θ (halfTurn hm k) = θ k :=
    Complex.ofReal_injective (hθ k)
  unfold angleDifference
  rw [← halfTurn_successor, hh, hh]

private theorem angleAverage_sq_half_sum {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) :
    (∑ j : Fin (2 * m), angleAverage (by omega) θ j ^ 2) =
      2 * ∑ j : Fin m, angleAverage (by omega) θ (halfIndex j) ^ 2 := by
  apply MatchingActivityRadialProjection.real_half_sum hm
  intro j
  rw [angleAverage_halfTurn hm θ hθ]

private theorem angleDifference_sq_half_sum {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) :
    (∑ j : Fin (2 * m), angleDifference (by omega) θ j ^ 2) =
      2 * ∑ j : Fin m, angleDifference (by omega) θ (halfIndex j) ^ 2 := by
  apply MatchingActivityRadialProjection.real_half_sum hm
  intro j
  rw [angleDifference_halfTurn hm θ hθ]

theorem angleAverage_half_meanSquare_le_of_joint_energy {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hdom : InDomain hm θ v)
    (henergy : pairEnergy (by omega) (fun j => (θ j : ℂ)) +
        pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2) :
    average (fun j : Fin m => angleAverage (by omega) θ (halfIndex j) ^ 2) ≤
      8 * B ^ 2 / (2 * m : ℝ) ^ 4 := by
  have hbase := angle_average_square hm θ hdom.2.1
  have hθ := pairEnergy_angle_le hm θ v hB henergy
  calc
    _ ≤ 8 * pairEnergy (by omega) (fun j => (θ j : ℂ)) /
        (2 * m : ℝ) ^ 2 := hbase
    _ ≤ 8 * (B ^ 2 / (2 * m : ℝ) ^ 2) / (2 * m : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hθ (by norm_num)) (by positivity)
    _ = 8 * B ^ 2 / (2 * m : ℝ) ^ 4 := by ring

theorem angleDifference_half_meanSquare_le_of_joint_energy {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (_hdom : InDomain hm θ v)
    (henergy : pairEnergy (by omega) (fun j => (θ j : ℂ)) +
        pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2) :
    average (fun j : Fin m =>
      (angleDifference (by omega) θ (halfIndex j) / 2) ^ 2) ≤
      4 * Real.pi ^ 2 * B ^ 2 / (2 * m : ℝ) ^ 5 := by
  have hbase := angle_difference_square hm θ
  have hθ := pairEnergy_angle_le hm θ v hB henergy
  calc
    _ ≤ 4 * Real.pi ^ 2 * pairEnergy (by omega) (fun j => (θ j : ℂ)) /
        (2 * m : ℝ) ^ 3 := hbase
    _ ≤ 4 * Real.pi ^ 2 * (B ^ 2 / (2 * m : ℝ) ^ 2) /
        (2 * m : ℝ) ^ 3 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hθ (by positivity)) (by positivity)
    _ = 4 * Real.pi ^ 2 * B ^ 2 / (2 * m : ℝ) ^ 5 := by ring

theorem angleAverage_meanSquare_le_of_joint_energy {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hdom : InDomain hm θ v)
    (henergy : pairEnergy (by omega) (fun j => (θ j : ℂ)) +
        pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2) :
    SchurLiftBounds.meanSquare (fun j : Fin (2 * m) =>
      angleAverage (by omega) θ j) ≤ 8 * B ^ 2 / (2 * m : ℝ) ^ 4 := by
  have hs := angleAverage_half_meanSquare_le_of_joint_energy hm θ v hB hdom henergy
  have hsum := angleAverage_sq_half_sum hm θ hdom.1
  unfold SchurLiftBounds.meanSquare
  rw [hsum]
  unfold average at hs
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < 2 * m := by positivity
  calc
    (2 * ∑ j : Fin m, angleAverage (by omega) θ (halfIndex j) ^ 2) /
        ((2 * m : ℕ) : ℝ) =
        (∑ j : Fin m, angleAverage (by omega) θ (halfIndex j) ^ 2) / m := by
          field_simp
          norm_num [Nat.cast_mul]
          ring_nf
    _ ≤ 8 * B ^ 2 / (2 * m : ℝ) ^ 4 := hs

theorem angleDifference_meanSquare_le_of_joint_energy {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hdom : InDomain hm θ v)
    (henergy : pairEnergy (by omega) (fun j => (θ j : ℂ)) +
        pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2) :
    SchurLiftBounds.meanSquare (fun j : Fin (2 * m) =>
      angleDifference (by omega) θ j) ≤ 16 * Real.pi ^ 2 * B ^ 2 / (2 * m : ℝ) ^ 5 := by
  have hs := angleDifference_half_meanSquare_le_of_joint_energy hm θ v hB hdom henergy
  have hsum := angleDifference_sq_half_sum hm θ hdom.1
  unfold SchurLiftBounds.meanSquare
  rw [hsum]
  unfold average at hs
  have hhalf :
      (∑ j : Fin m, (angleDifference (by omega) θ (halfIndex j) / 2) ^ 2) =
        (∑ j : Fin m, angleDifference (by omega) θ (halfIndex j) ^ 2) / 4 := by
    simp only [div_pow]
    rw [← Finset.sum_div]
    norm_num
  rw [hhalf] at hs
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < 2 * m := by positivity
  calc
    (2 * ∑ j : Fin m, angleDifference (by omega) θ (halfIndex j) ^ 2) /
        ((2 * m : ℕ) : ℝ) =
        4 * (((∑ j : Fin m,
          angleDifference (by omega) θ (halfIndex j) ^ 2) / 4) / m) := by
      have he : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by
        norm_num [Nat.cast_mul]
      rw [he]
      field_simp
    _ ≤ 4 * (4 * Real.pi ^ 2 * B ^ 2 / (2 * m : ℝ) ^ 5) := by
      exact mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = 16 * Real.pi ^ 2 * B ^ 2 / (2 * m : ℝ) ^ 5 := by ring

theorem angleDifference_abs_le_of_joint_energy {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (_hdom : InDomain hm θ v)
    (henergy : pairEnergy (by omega) (fun j => (θ j : ℂ)) +
        pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2)
    (j : Fin (2 * m)) :
    |angleDifference (by omega) θ j| ≤ 10 * B / (2 * m : ℝ) ^ 2 := by
  have hθ := pairEnergy_angle_le hm θ v hB henergy
  have hθ' : pairEnergy (by omega) (fun j => (θ j : ℂ)) ≤
      B ^ 2 / (↑(2 * m) : ℝ) ^ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hθ
  have h := difference_of_scaled_energy (by omega) (fun k => (θ k : ℂ)) hB hθ' j
  simpa only [angleDifference, difference, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, Nat.cast_mul, Nat.cast_ofNat] using h

private theorem tangent_abs_le_scale_difference {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → ℂ) (j : Fin n) :
    |EdgeCoordinates.tangent (by omega) v j| ≤
      CommonFiberNormalProjectionScaled.scale n *
        ‖difference (by omega) v j‖ := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsin : 0 < Real.sin (Real.pi / n) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · apply (div_lt_iff₀ hnR).2
      have hnR2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [Real.pi_pos]
  have htan : |EdgeCoordinates.tangent (by omega) v j| ≤
      ‖(n : ℂ) * edgeRatio (by omega) v j‖ := by
    calc
      |EdgeCoordinates.tangent (by omega) v j| ≤
          ‖(EdgeCoordinates.tangent (by omega) v j : ℂ) -
            I * (EdgeCoordinates.normal (by omega) v j : ℂ)‖ := by
        have h := Complex.abs_re_le_norm
          ((EdgeCoordinates.tangent (by omega) v j : ℂ) -
            I * (EdgeCoordinates.normal (by omega) v j : ℂ))
        simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
          sub_zero] using h
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
    |EdgeCoordinates.tangent (by omega) v j| ≤
        ‖(n : ℂ) * edgeRatio (by omega) v j‖ := htan
    _ = (n : ℝ) * ‖edgeRatio (by omega) v j‖ := by
      simp only [norm_mul, Complex.norm_natCast]
    _ = (n : ℝ) *
        (‖difference (by omega) v j‖ /
          (2 * Real.sin (Real.pi / n))) := by
      rw [edgeRatio_eq_difference, norm_div, href]
    _ = CommonFiberNormalProjectionScaled.scale n *
        ‖difference (by omega) v j‖ := by
      unfold CommonFiberNormalProjectionScaled.scale
      field_simp

theorem tangent_abs_le_of_joint_energy {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (_hdom : InDomain hm θ v)
    (henergy : pairEnergy (by omega) (fun j => (θ j : ℂ)) +
        pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2)
    (j : Fin (2 * m)) :
    |EdgeCoordinates.tangent (by omega) v j| ≤ (5 / 2 : ℝ) * B := by
  have hv := pairEnergy_tangent_le hm θ v hB henergy
  have hv' : pairEnergy (by omega) v ≤ B ^ 2 / (↑(2 * m) : ℝ) ^ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hv
  have hd := difference_of_scaled_energy (by omega) v hB hv' j
  have hd' : ‖difference (by omega) v j‖ ≤
      10 * B / (2 * m : ℝ) ^ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hd
  have ht := tangent_abs_le_scale_difference (show 2 ≤ 2 * m by omega) v j
  have hs := scale_bounds (show 2 ≤ 2 * m by omega)
  have hs' : scale (2 * m) ≤ (2 * m : ℝ) ^ 2 / 4 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs.2
  have hmul :
      scale (2 * m) * ‖difference (by omega) v j‖ ≤
      ((2 * m : ℝ) ^ 2 / 4) * (10 * B / (2 * m : ℝ) ^ 2) := by
    exact mul_le_mul hs' hd' (norm_nonneg _) (by positivity)
  have hmain : |EdgeCoordinates.tangent (by omega) v j| ≤ (5 / 2 : ℝ) * B := by
    calc
      _ ≤ ((2 * m : ℝ) ^ 2 / 4) * (10 * B / (2 * m : ℝ) ^ 2) := ht.trans hmul
      _ = (5 / 2 : ℝ) * B := by field_simp; ring
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmain

theorem angleAverage_abs_le_of_joint_energy {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) {B : ℝ} (_hB : 0 ≤ B)
    (hdom : InDomain hm θ v)
    (_henergy : pairEnergy (by omega) (fun j => (θ j : ℂ)) +
        pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2)
    (j : Fin (2 * m)) :
    |angleAverage (by omega) θ j| ≤
      4 * (logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) /
        (2 * m : ℝ) ^ 2 := by
  have h₁ := domain_theta_bound hm θ v hdom j
  have h₂ := domain_theta_bound hm θ v hdom (successor (by omega) j)
  unfold angleAverage
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := abs_add_le (θ j) (θ (successor (by omega) j))
  linarith

theorem normalized_abs_sum_le_sqrt_meanSquare {n : ℕ} (hn : 0 < n)
    (q : Fin n → ℝ) :
    (∑ j, |q j|) / (n : ℝ) ≤
      Real.sqrt (SchurLiftBounds.meanSquare q) := by
  have h := CommonFiberNormalAverage.mixed_average q (fun _ : Fin n => (1 : ℝ))
  simp only [abs_one, mul_one, one_pow] at h
  rw [CommonFiberNormalAverage.average_const hn 1] at h
  simpa only [CommonFiberNormalAverage.average, SchurLiftBounds.meanSquare,
    Real.sqrt_one, mul_one] using h

private theorem tan_abs_le_two_mul_abs {x : ℝ}
    (hcos : (1 / 2 : ℝ) ≤ Real.cos x) :
    |Real.tan x| ≤ 2 * |x| := by
  have hcospos : 0 < Real.cos x := by linarith
  rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_pos hcospos]
  apply (div_le_iff₀ hcospos).2
  have hs : |Real.sin x| ≤ |x| := Real.abs_sin_le_abs
  have hm := mul_le_mul_of_nonneg_left hcos (abs_nonneg x)
  exact hs.trans (by nlinarith)

theorem normalized_tan_sum_le_of_meanSquare_le {n : ℕ} (hn : 0 < n)
    (b : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hmean : SchurLiftBounds.meanSquare b ≤ 8 * B ^ 2 / (n : ℝ) ^ 4)
    (hcos : ∀ j, (1 / 2 : ℝ) ≤ Real.cos (b j)) :
    (∑ j, |Real.tan (b j)|) / (n : ℝ) ≤ 6 * B / (n : ℝ) ^ 2 := by
  have habs :
      (∑ j, |b j|) / (n : ℝ) ≤ Real.sqrt (SchurLiftBounds.meanSquare b) :=
    normalized_abs_sum_le_sqrt_meanSquare hn b
  have hroot : Real.sqrt (SchurLiftBounds.meanSquare b) ≤
      3 * B / (n : ℝ) ^ 2 := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    calc
      SchurLiftBounds.meanSquare b ≤ 8 * B ^ 2 / (n : ℝ) ^ 4 := hmean
      _ ≤ (3 * B / (n : ℝ) ^ 2) ^ 2 := by
        rw [div_pow]
        have hden : ((n : ℝ) ^ 2) ^ 2 = (n : ℝ) ^ 4 := by ring
        rw [hden]
        apply div_le_div_of_nonneg_right
        · rw [mul_pow]
          nlinarith [sq_nonneg B]
        · positivity
  have htan (j : Fin n) : |Real.tan (b j)| ≤ 2 * |b j| :=
    tan_abs_le_two_mul_abs (hcos j)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => htan j)
  calc
    (∑ j, |Real.tan (b j)|) / (n : ℝ) ≤
        (∑ j, 2 * |b j|) / (n : ℝ) :=
      div_le_div_of_nonneg_right hsum (by positivity)
    _ = 2 * ((∑ j, |b j|) / (n : ℝ)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ 2 * Real.sqrt (SchurLiftBounds.meanSquare b) :=
      mul_le_mul_of_nonneg_left habs (by norm_num)
    _ ≤ 6 * B / (n : ℝ) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 2)
      calc
        _ ≤ 2 * (3 * B / (n : ℝ) ^ 2) := hh
        _ = 6 * B / (n : ℝ) ^ 2 := by ring

theorem normalized_tan_angleAverage_le_of_joint_energy {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hdom : InDomain hm θ v)
    (henergy : pairEnergy (by omega) (fun j => (θ j : ℂ)) +
        pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2)
    (hcos : ∀ j : Fin (2 * m), (1 / 2 : ℝ) ≤
      Real.cos (angleAverage (by omega) θ j)) :
    (∑ j, |Real.tan (angleAverage (by omega) θ j)|) / (2 * m : ℝ) ≤
      6 * B / (2 * m : ℝ) ^ 2 := by
  have hms : SchurLiftBounds.meanSquare (fun j : Fin (2 * m) =>
      angleAverage (by omega) θ j) ≤ 8 * B ^ 2 / (↑(2 * m) : ℝ) ^ 4 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (angleAverage_meanSquare_le_of_joint_energy hm θ v hB hdom henergy)
  have htan := normalized_tan_sum_le_of_meanSquare_le (show 0 < 2 * m by omega)
    (fun j => angleAverage (by omega) θ j) hB hms hcos
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using htan

theorem eventually_normalized_tan_angleAverage_le (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
        InDomain (by omega) θ v →
        pairEnergy (by omega) (fun j => (θ j : ℂ)) +
            pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2 →
        (∑ j, |Real.tan (angleAverage (by omega) θ j)|) /
            (2 * m : ℝ) ≤ 6 * B / (2 * m : ℝ) ^ 2 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    CommonFiberNonlocalSizes.eventual_small_coefficients
  filter_upwards [eventually_ge_atTop ((N + 1) / 2)] with m hmN
  intro hm θ v hdom henergy
  have hsmall := (hN (2 * m) (by omega)).2.2.1
  have hsmall' :
      4 * (logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) /
          (2 * m : ℝ) ^ 2 ≤ 1 / (1000 * (2 * m : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsmall
  have hav (j : Fin (2 * m)) :
      |angleAverage (by omega) θ j| ≤ 1 / (1000 * (2 * m : ℝ)) := by
    exact (angleAverage_abs_le_of_joint_energy (by omega) θ v hB hdom henergy j).trans hsmall'
  have hcos (j : Fin (2 * m)) : (1 / 2 : ℝ) ≤
      Real.cos (angleAverage (by omega) θ j) := by
    let x := angleAverage (by omega) θ j
    have hnR : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
    have hden : (1 : ℝ) ≤ 1000 * (2 * m : ℝ) := by nlinarith
    have hunit : |x| ≤ 1 := by
      have hx := hav j
      dsimp [x] at hx ⊢
      have hi : 1 / (1000 * (2 * m : ℝ)) ≤ (1 : ℝ) := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * (2 * m : ℝ))).2
        simpa only [one_mul] using hden
      exact hx.trans hi
    have hsq : x ^ 2 ≤ 1 := by
      have hh := pow_le_pow_left₀ (abs_nonneg x) hunit 2
      simpa only [sq_abs, one_pow] using hh
    have hc := Real.one_sub_sq_div_two_le_cos (x := x)
    dsimp [x] at hc hsq
    nlinarith
  exact normalized_tan_angleAverage_le_of_joint_energy (by omega) θ v hB hdom henergy hcos

end
end StructuralNote.FixedSchurInnerAngles

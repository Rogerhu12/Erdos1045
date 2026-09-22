import StructuralNote.ExplicitHessianThresholdFixedSchur
import StructuralNote.ExplicitComparisonRotated
import StructuralNote.ExplicitComparisonScalars
import StructuralNote.FixedSchurChartGeometry

/-! Explicit pointwise geometry of the fixed-Schur chart. -/

namespace StructuralNote.ExplicitHessianThresholdFixedSchurGeometry

open scoped BigOperators Topology
open Complex Real Set Metric
open Erdos1045 Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonDomainClosure CommonDomainRadius EdgeCoordinates FixedSchurData FixedSchurLinear
open CommonFiberGeometry CommonFiberNonlocalFeasibility CommonFiberInjectivity
open FixedSchurEdgeGeometry FixedSchurChart FixedSchurDomainBounds
open FixedSchurDomainSmallness FixedSchurDomainSource FixedSchurHarmonicBounds
open CommonFiberSmallCoefficients
open FixedSchurEquations
open FixedSchurChartSizes FixedSchurChartRadial FixedSchurChartAdjacent
open FixedSchurAdjacentAlgebra FixedSchurOffsetGeometry FixedSchurChartGeometry
open FixedDualClassificationFinite
open ExplicitHessianThreshold ExplicitHessianThresholdFixedSchur
open ExplicitHessianThresholdDownstream SignPatternSymmetry

noncomputable section

theorem step_numeric {n : ℕ} (hn : orderThreshold ≤ n) :
    144 * (CommonDomainRadius.logOrder n : ℝ) / (n : ℝ) ^ 2 ≤
      1 / (1000 * (n : ℝ)) := by
  have hn0 := order_pos hn
  have hb := logOrder_bound hn
  have h := log_monomial_div_small (j := 1) (c := 288000) hn
    (by norm_num) (by norm_num)
  simp only [pow_one] at h
  have hratio : 144000 * (CommonDomainRadius.logOrder n : ℝ) / n ≤ 1 := by
    have hh : 144000 * (CommonDomainRadius.logOrder n : ℝ) ≤
        288000 * Erdos1045.ExplicitThreshold.logBudget n := by
      calc
        _ ≤ 144000 * (2 * Erdos1045.ExplicitThreshold.logBudget n) :=
          mul_le_mul_of_nonneg_left hb (by norm_num)
        _ = _ := by ring
    have hh' : 144000 * (CommonDomainRadius.logOrder n : ℝ) / n ≤
        288000 * Erdos1045.ExplicitThreshold.logBudget n / n :=
      div_le_div_of_nonneg_right hh hn0.le
    linarith only [hh', h]
  calc
    144 * (CommonDomainRadius.logOrder n : ℝ) / (n : ℝ) ^ 2 =
        (1 / (1000 * (n : ℝ))) *
          (144000 * (CommonDomainRadius.logOrder n : ℝ) / n) := by
      field_simp
      ring
    _ ≤ (1 / (1000 * (n : ℝ))) * 1 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

theorem chart_small_steps {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) :
    (∀ j, |θ j| ≤ 1 / (1000 * (2 * m : ℝ))) ∧
      (∀ j, ‖difference (by omega) (center (coordinate (by omega) s θ v) v) j‖ ≤
        1 / (1000 * (2 * m : ℝ))) := by
  have hP := coordinate_properties hn hm s θ v hdom
  have hsmall := ExplicitComparisonScalars.small_coefficients hn
  have hθnum := hsmall.2.2.1
  have hnum := step_numeric hn
  constructor
  · intro j
    exact (domain_theta_bound (by omega) θ v hdom j).trans (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hθnum)
  · intro j
    exact (center_step_bound hm θ v hdom (coordinate (by omega) s θ v)
      hP.norm_le j).trans (by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hnum)

theorem configuration_injective {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) :
    Function.Injective (configuration (by omega) s θ v) := by
  obtain ⟨hθ, hstep⟩ := chart_small_steps hn hm s θ v hdom
  have hinj := small_center_step_injective (by omega : 4 ≤ 2 * m) θ
    (center (coordinate (by omega) s θ v) v)
    (fun j => by
      have h := hθ j
      have hrat : 1 / (1000 * (2 * m : ℝ)) ≤
          1 / (8 * (2 * m : ℝ)) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        have hmR : (0 : ℝ) < 2 * m := by positivity
        nlinarith only [hmR]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h.trans hrat)
    (fun j => by
      have h := hstep j
      have hrat : 1 / (1000 * (2 * m : ℝ)) ≤
          1 / (2 * (2 * m : ℝ)) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        have hmR : (0 : ℝ) < 2 * m := by positivity
        nlinarith only [hmR]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h.trans hrat)
  change Function.Injective
    (fun j => diameterVector θ j + center (coordinate (by omega) s θ v) v j)
  exact hinj

theorem radius_le_half {n : ℕ} (hn : orderThreshold ≤ n) :
    radius n ≤ 1 / 2 := by
  have hb := logOrder_bound hn
  have h := log_monomial_div_small (j := 1) (c := 8192) hn
    (by norm_num) (by norm_num)
  simp only [pow_one] at h
  unfold radius
  have hn0 := (order_pos hn).le
  have hh : 4096 * (CommonDomainRadius.logOrder n : ℝ) / n ≤
      8192 * Erdos1045.ExplicitThreshold.logBudget n / n := by
    apply div_le_div_of_nonneg_right _ hn0
    calc
      _ ≤ 4096 * (2 * Erdos1045.ExplicitThreshold.logBudget n) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = _ := by ring
  linarith only [hh, h]

theorem log_div_small {n : ℕ} (hn : orderThreshold ≤ n) :
    (CommonDomainRadius.logOrder n : ℝ) / n ≤ 1 / 416 := by
  have hb := logOrder_bound hn
  have h := log_monomial_div_small (j := 1) (c := 832) hn
    (by norm_num) (by norm_num)
  simp only [pow_one] at h
  have hn0 := (order_pos hn).le
  have hh : 416 * (CommonDomainRadius.logOrder n : ℝ) / n ≤
      832 * Erdos1045.ExplicitThreshold.logBudget n / n := by
    apply div_le_div_of_nonneg_right _ hn0
    calc
      _ ≤ 416 * (2 * Erdos1045.ExplicitThreshold.logBudget n) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = _ := by ring
  have hsmall : 416 * (CommonDomainRadius.logOrder n : ℝ) / n ≤ 1 := by
    linarith only [hh, h]
  calc
    (CommonDomainRadius.logOrder n : ℝ) / n =
        (1 / 416 : ℝ) * (416 * (CommonDomainRadius.logOrder n : ℝ) / n) := by ring
    _ ≤ (1 / 416 : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hsmall (by norm_num)
    _ = _ := by ring

private theorem scaled_source_error_le {N L R : ℝ}
    (hN : 0 < N) (hLnonneg : 0 ≤ L) (hR : 0 ≤ R)
    (hscale : L * (1 + R) / N ≤ 1) :
    40 * L / N ^ 3 + 25 * L ^ 2 / N ^ 4 +
        16 * L ^ 2 * R / N ^ 4 ≤ 81 / N ^ 2 := by
  have hscale' : L * (1 + R) ≤ N := by
    simpa only [one_mul] using (div_le_iff₀ hN).mp hscale
  have hL : L ≤ N := by
    nlinarith only [hscale', mul_nonneg hLnonneg hR]
  have hLR : L * R ≤ N := by
    nlinarith only [hscale', hLnonneg]
  have hLsq : L ^ 2 ≤ N ^ 2 := by
    have h := mul_le_mul hL hL hLnonneg hN.le
    nlinarith only [h]
  have hLsqR : L ^ 2 * R ≤ N ^ 2 := by
    calc
      L ^ 2 * R = L * (L * R) := by ring
      _ ≤ L * N := mul_le_mul_of_nonneg_left hLR hLnonneg
      _ ≤ N * N := mul_le_mul_of_nonneg_right hL hN.le
      _ = N ^ 2 := by ring
  have hN3 : 0 < N ^ 3 := by positivity
  have hN4 : 0 < N ^ 4 := by positivity
  have h₁ : 40 * L / N ^ 3 ≤ 40 / N ^ 2 := by
    apply (div_le_iff₀ hN3).2
    calc
      40 * L ≤ 40 * N := mul_le_mul_of_nonneg_left hL (by norm_num)
      _ = (40 / N ^ 2) * N ^ 3 := by field_simp
  have h₂ : 25 * L ^ 2 / N ^ 4 ≤ 25 / N ^ 2 := by
    apply (div_le_iff₀ hN4).2
    calc
      25 * L ^ 2 ≤ 25 * N ^ 2 := mul_le_mul_of_nonneg_left hLsq (by norm_num)
      _ = (25 / N ^ 2) * N ^ 4 := by field_simp
  have h₃ : 16 * L ^ 2 * R / N ^ 4 ≤ 16 / N ^ 2 := by
    apply (div_le_iff₀ hN4).2
    calc
      16 * L ^ 2 * R = 16 * (L ^ 2 * R) := by ring
      _ ≤ 16 * N ^ 2 := mul_le_mul_of_nonneg_left hLsqR (by norm_num)
      _ = (16 / N ^ 2) * N ^ 4 := by field_simp
  calc
    _ ≤ 40 / N ^ 2 + 25 / N ^ 2 + 16 / N ^ 2 :=
      add_le_add (add_le_add h₁ h₂) h₃
    _ = 81 / N ^ 2 := by ring

private theorem product_bound_of_scale {N L R : ℝ}
    (hN : 0 < N) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hscale : L * (1 + R) / N ≤ 1) (hsmall : L / N ≤ 1 / 416) :
    104 * L ^ 2 * (1 + R) / N ^ 2 ≤ 1 / 4 := by
  have hLnonneg : 0 ≤ L / N := div_nonneg hL hN.le
  calc
    104 * L ^ 2 * (1 + R) / N ^ 2 =
        104 * ((L / N) * (L * (1 + R) / N)) := by field_simp
    _ ≤ 104 * (L / N) := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hscale hLnonneg) (by norm_num))
    _ ≤ 1 / 4 := by nlinarith only [hsmall]

theorem X_ge_one {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain hm θ v) (j : Fin (2 * m)) :
    1 ≤ X (Nat.mul_pos (by norm_num) hm) θ j := by
  let N : ℝ := (2 * m : ℕ)
  let L : ℝ := (CommonDomainRadius.logOrder (2 * m) : ℝ)
  let R : ℝ := Real.log (2 * m : ℝ)
  have hpos2 : 0 < 2 * m := Nat.mul_pos (by norm_num) hm
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hpos2
  have hNnat : 256 ≤ 2 * m := two_fifty_six_le_order hn
  have hN16 : 16 ≤ N := by dsimp [N]; exact_mod_cast hNnat.trans' (by norm_num)
  have hL : 0 ≤ L := by positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    exact Real.log_nonneg (by exact_mod_cast hpos2)
  have hscale : L * (1 + R) / N ≤ 1 := by
    simpa only [N, L, R, Nat.cast_mul, Nat.cast_ofNat] using domain_log_scale hn
  have herr := scaled_source_error_le hN hL hR hscale
  have hN2 : 97 ≤ N ^ 2 := by nlinarith only [hN16, sq_nonneg (N - 16)]
  have hpi : (Real.pi / N) ^ 2 ≤ 16 / N ^ 2 := by
    have hpi4 : Real.pi ≤ 4 := Real.pi_lt_four.le
    have hpi2' := mul_self_le_mul_self (show 0 ≤ Real.pi by positivity) hpi4
    have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith only [hpi2']
    calc
      (Real.pi / N) ^ 2 = Real.pi ^ 2 / N ^ 2 := by ring
      _ ≤ 16 / N ^ 2 := div_le_div_of_nonneg_right hpi2 (sq_nonneg N)
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi / N)
  have hbase : 2 - 16 / N ^ 2 ≤ 2 * Real.cos (Real.pi / N) := by
    nlinarith only [hcos, hpi]
  have hX := domain_X_bound hm θ v hdom j
  have hX' : -(81 / N ^ 2) ≤ X (Nat.mul_pos (by norm_num) hm) θ j -
      2 * Real.cos (Real.pi / N) := by
    have hX0 : |X (Nat.mul_pos (by norm_num) hm) θ j - 2 * Real.cos (Real.pi / N)| ≤
        40 * L / N ^ 3 + 25 * L ^ 2 / N ^ 4 + 16 * L ^ 2 * R / N ^ 4 := by
      simpa only [N, L, R, Nat.cast_mul, Nat.cast_ofNat] using hX
    exact (neg_le_neg herr).trans (abs_le.mp hX0).1
  have h97 : 97 / N ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hN)).2
    nlinarith only [hN2]
  calc
    1 ≤ 2 - 97 / N ^ 2 := by linarith only [h97]
    _ = 2 - 16 / N ^ 2 - 81 / N ^ 2 := by ring
    _ ≤ 2 * Real.cos (Real.pi / N) - 81 / N ^ 2 := sub_le_sub_right hbase _
    _ ≤ X (Nat.mul_pos (by norm_num) hm) θ j := by linarith only [hX']

private theorem sqrt_log_le_one_add_log {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (Real.log (n : ℝ)) ≤ 1 + Real.log (n : ℝ) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  apply (Real.sqrt_le_iff).2
  constructor
  · linarith only [hlog]
  · nlinarith only [hlog, sq_nonneg (1 + Real.log (n : ℝ))]

theorem Y_product_le_quarter {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (q : Fin (2 * m) → ℝ)
    (hdom : InDomain hm θ v) (hq : ‖q‖ ≤ 5) (j : Fin (2 * m)) :
    |Y (Nat.mul_pos (by norm_num) hm) θ j *
      (J q + tangent (Nat.mul_pos (by norm_num) hm) v) j| ≤ 1 / 4 := by
  let N : ℝ := (2 * m : ℕ)
  let L : ℝ := (CommonDomainRadius.logOrder (2 * m) : ℝ)
  let R : ℝ := Real.log (2 * m : ℝ)
  have hpos2 : 0 < 2 * m := Nat.mul_pos (by norm_num) hm
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hpos2
  have hL : 0 ≤ L := by positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    exact Real.log_nonneg (by exact_mod_cast hpos2)
  have hscale : L * (1 + R) / N ≤ 1 := by
    simpa only [N, L, R, Nat.cast_mul, Nat.cast_ofNat] using domain_log_scale hn
  have hsmall : L / N ≤ 1 / 416 := by
    simpa only [N, L, Nat.cast_mul, Nat.cast_ofNat] using log_div_small hn
  have hY := domain_Y_bound hm θ v hdom j
  have hsqrt := sqrt_log_le_one_add_log (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos2))
  have hsqrt' : Real.sqrt R ≤ 1 + R := by
    simpa only [R, Nat.cast_mul, Nat.cast_ofNat] using hsqrt
  have hY' : |Y (Nat.mul_pos (by norm_num) hm) θ j| ≤
      8 * L * (1 + R) / N ^ 2 := by
    have hY0 : |Y (Nat.mul_pos (by norm_num) hm) θ j| ≤
        8 * L * Real.sqrt R / N ^ 2 := by
      simpa only [N, L, R, Nat.cast_mul, Nat.cast_ofNat] using hY
    calc
      _ ≤ 8 * L * Real.sqrt R / N ^ 2 := hY0
      _ = (8 * L / N ^ 2) * Real.sqrt R := by ring
      _ ≤ (8 * L / N ^ 2) * (1 + R) :=
        mul_le_mul_of_nonneg_left hsqrt' (by positivity)
      _ = 8 * L * (1 + R) / N ^ 2 := by ring
  have hp := tangent_total_bound hm θ v hdom q hq j
  have hmul : |Y (Nat.mul_pos (by norm_num) hm) θ j| *
      |(J q + tangent (Nat.mul_pos (by norm_num) hm) v) j| ≤
      (8 * L * (1 + R) / N ^ 2) * (13 * L) := by
    exact mul_le_mul hY' hp (abs_nonneg _) (by positivity)
  have hprod := product_bound_of_scale hN hL hR hscale hsmall
  calc
    |Y (Nat.mul_pos (by norm_num) hm) θ j *
        (J q + tangent (Nat.mul_pos (by norm_num) hm) v) j| =
        |Y (Nat.mul_pos (by norm_num) hm) θ j| *
          |(J q + tangent (Nat.mul_pos (by norm_num) hm) v) j| := by rw [abs_mul]
    _ ≤ (8 * L * (1 + R) / N ^ 2) * (13 * L) := hmul
    _ = 104 * L ^ 2 * (1 + R) / N ^ 2 := by ring
    _ ≤ 1 / 4 := hprod

theorem coordinate_q_half {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega)) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain (by omega) θ v)
    (j : Fin (2 * m)) :
    1 / 2 ≤ FiniteBox.patternSign s j * coordinate (by omega) s θ v j := by
  have hp := coordinate_properties hn hm s θ v hdom
  have hr := radius_le_half hn
  have hpoint : |coordinate (by omega) s θ v j -
      baseWord (FiniteBox.patternSign s) j| ≤ radius (2 * m) := by
    have hpi := norm_le_pi_norm
      (coordinate (by omega) s θ v - baseWord (FiniteBox.patternSign s)) j
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using hpi.trans hp.close
  have hpoint' : |coordinate (by omega) s θ v j -
      FiniteBox.amplitude (2 * m) * FiniteBox.patternSign s j| ≤ radius (2 * m) := by
    simpa only [baseWord] using hpoint
  have hA : 1 ≤ FiniteBox.amplitude (2 * m) :=
    amplitude_ge_one (show 2 ≤ 2 * m by omega)
  rcases FiniteBox.patternSign_is_sign s j with hs | hs
  · rw [hs] at hpoint' ⊢
    nlinarith only [(abs_le.mp hpoint').1, hr, hA]
  · rw [hs] at hpoint' ⊢
    nlinarith only [(abs_le.mp hpoint').1, (abs_le.mp hpoint').2, hr, hA]

theorem unselected_crossing_norm_lt_two {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) (j : Fin (2 * m)) :
    ‖crossingVector hm θ (center (coordinate (by omega) s θ v) v)
      (fun k => -FiniteBox.patternSign s k) j‖ < 2 := by
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hp := coordinate_properties hn hm s θ v hdom
  have hs := FiniteBox.patternSign_is_sign s j
  have harg := ball_positive_input hn hm0 θ v (FiniteBox.patternSign s) hdom
    (FiniteBox.patternSign_is_sign s) _ hp.close
  have hselected := (solution_positive_branch (by omega) θ v
    (FiniteBox.patternSign s) (coordinate (by omega) s θ v)
    (FiniteBox.patternSign_is_sign s) hp.fixed harg j).2
  have hselected' :
      (X (by omega) θ j + FiniteBox.patternSign s j * epsilon (2 * m) *
          coordinate (by omega) s θ v j) ^ 2 +
        (Y (by omega) θ j + FiniteBox.patternSign s j * epsilon (2 * m) *
          (J (coordinate (by omega) s θ v) + tangent (by omega) v) j) ^ 2 = 4 := by
    convert hselected using 1
  exact FixedSchurAdjacentAlgebra.unselected_crossing_norm_lt_two hm θ
    (coordinate (by omega) s θ v) v (FiniteBox.patternSign s)
    hdom.1 hp.antiperiodic hdom.2.2.1.1 hdom.2.2.1.2.2 j hs
    (X_ge_one hn (by omega) θ v hdom j)
    (coordinate_q_half hn hm s θ v hdom j)
    (Y_product_le_quarter hn (by omega) θ v (coordinate (by omega) s θ v)
      hdom hp.norm_le j)
    hselected'

theorem offset_classification {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) (r : ℕ) (hr : r < 2 * m)
    (j : Fin (2 * m)) :
    ‖configuration (by omega) s θ v (cyclicAdvance j r) -
        configuration (by omega) s θ v j‖ ≤ 2 ∧
      (‖configuration (by omega) s θ v (cyclicAdvance j r) -
        configuration (by omega) s θ v j‖ = 2 ↔
        FixedSchurOffsetGeometry.OffsetEdge (FiniteBox.patternSign s) j r) := by
  have hp := coordinate_properties hn hm s θ v hdom
  obtain ⟨hθ, hstep⟩ := chart_small_steps hn hm s θ v hdom
  have hrad := ExplicitComparisonRotated.coordinate_radial hn hm s θ v hdom
  have hC := center_halfPeriodic hm _ v hp.antiperiodic hdom.2.2.1.1
  have hm8 : 8 ≤ m := by
    have h256 := two_fifty_six_le_order hn
    omega
  apply FixedSchurOffsetGeometry.offset_classification hm
    (configuration (by omega) s θ v) (FiniteBox.patternSign s) hp.matching _ _ r hr j
  · intro k
    exact next_classification hm θ _ _ hdom.1 hC k
      (FiniteBox.patternSign_is_sign s k) (hp.selected k)
      (unselected_crossing_norm_lt_two hn hm s θ v hdom k)
  · intro r' hr' hprev hmatch hnext k
    exact nonlocal_strict hm8 hr' hprev hmatch hnext θ _ hdom.1 hC hθ hstep hrad k

theorem diameter_and_graph {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) :
    Configuration.DiameterAtMost 2 (configuration (by omega) s θ v) ∧
      (∀ i j, ‖configuration (by omega) s θ v i - configuration (by omega) s θ v j‖ = 2 ↔
        FixedSchurChartGeometry.WordEdge (FiniteBox.patternSign s) i j) := by
  have hh (i j : Fin (2 * m)) := offset_classification hn hm s θ v hdom
    (cyclicForwardDistance j i) (Nat.mod_lt (i.val + 2 * m - j.val) (by omega)) j
  simp only [cyclicAdvance_forwardDistance] at hh
  exact ⟨fun i j => (hh i j).1, fun i j => (hh i j).2⟩

theorem geometric_properties {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) :
    FixedSchurChartGeometry.GeometricProperties hm s θ v := by
  have hg := diameter_and_graph hn hm s θ v hdom
  exact ⟨coordinate_properties hn hm s θ v hdom,
    configuration_injective hn hm s θ v hdom, hg.1, hg.2⟩

/-- All fixed-Schur fiber fields other than strict concavity, packaged with a
pointwise strict-concavity certificate. -/
theorem fiberData_of_strictConcavity {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 3 ≤ m)
    (hstrict : ∀ s : FiniteBox.SignPattern (by omega : 0 < m),
      StrictConcaveOn ℝ (FixedSchurChartSmooth.domain (by omega))
        (FixedSchurObjectivePaths.objective (by omega) s)) :
    FixedSchurFiberData hm := by
  refine ⟨hstrict, ?_, ?_, ?_, ?_⟩
  · intro s x d hx hd
    exact objective_direction_contDiffAt_of_geometry hn (by omega) s x d hx hd
      (geometric_properties hn (by omega) s x.1 x.2 hx)
  · intro s θ v hdom
    exact geometric_properties hn (by omega) s θ v hdom
  · intro k s θ v hdom
    exact configuration_cyclic hn (by omega) k s θ v hdom
  · intro s θ v hdom
    exact configuration_reflect hn (by omega) s θ v hdom

end
end StructuralNote.ExplicitHessianThresholdFixedSchurGeometry

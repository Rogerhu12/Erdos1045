import StructuralNote.FixedSchurChartSizes
import StructuralNote.FixedSchurAdjacentAlgebra
import StructuralNote.FixedDualClassificationFinite

/-! The numerical hypotheses in the adjacent-edge algebra hold uniformly on the
actual fixed-Schur chart.  This file only closes the chosen/unselected adjacent
edge estimate; full feasibility is handled elsewhere. -/

namespace StructuralNote.FixedSchurChartAdjacent

open Complex Filter
open Erdos1045 Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.FiniteFourierLift
open Erdos1045.EventualExact.SchurLift
open Erdos1045.EventualExact.SchurSpectrum
open CommonDomainClosure CommonDomainRadius CommonFiberGeometry
open EdgeCoordinates FixedSchurData FixedSchurLinear
open FixedSchurChart FixedSchurChartSizes FixedSchurDomainBounds
open FixedSchurDomainSmallness FixedSchurDomainSource FixedSchurEquations
open FixedSchurExistence FixedSchurEdgeGeometry HessianErrorLimits
open FixedSchurAdjacentAlgebra FixedDualClassificationFinite
open scoped BigOperators Topology

noncomputable section

private theorem sqrt_log_le_one_add_log {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (Real.log (n : ℝ)) ≤ 1 + Real.log (n : ℝ) := by
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  apply (Real.sqrt_le_iff).2
  constructor
  · linarith [Real.sqrt_nonneg (Real.log (n : ℝ))]
  · nlinarith [sq_nonneg (Real.log (n : ℝ))]

private theorem scaled_source_error_le {N L R : ℝ}
    (hN : 0 < N) (hLnonneg : 0 ≤ L) (hR : 0 ≤ R)
    (hscale : L * (1 + R) / N ≤ 1) :
    40 * L / N ^ 3 + 25 * L ^ 2 / N ^ 4 +
        16 * L ^ 2 * R / N ^ 4 ≤ 81 / N ^ 2 := by
  have hscale' : L * (1 + R) ≤ N := by
    simpa only [one_mul] using (div_le_iff₀ hN).mp hscale
  have hL : L ≤ N := by
    nlinarith [mul_nonneg hLnonneg hR]
  have hLR : L * R ≤ N := by
    nlinarith [hscale', hLnonneg]
  have hLsq : L ^ 2 ≤ N ^ 2 := by
    have h := mul_le_mul hL hL hLnonneg hN.le
    nlinarith
  have hLsqR : L ^ 2 * R ≤ N ^ 2 := by
    calc
      L ^ 2 * R = L * (L * R) := by ring
      _ ≤ L * N := mul_le_mul_of_nonneg_left hLR hLnonneg
      _ ≤ N * N := mul_le_mul_of_nonneg_right hL hN.le
      _ = N ^ 2 := by ring
  have hN2 : 0 < N ^ 2 := sq_pos_of_pos hN
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
      16 * L ^ 2 * R ≤ 16 * N ^ 2 :=
        by nlinarith [hLsqR]
      _ = (16 / N ^ 2) * N ^ 4 := by field_simp
  calc
    40 * L / N ^ 3 + 25 * L ^ 2 / N ^ 4 +
        16 * L ^ 2 * R / N ^ 4 ≤ 40 / N ^ 2 + 25 / N ^ 2 + 16 / N ^ 2 :=
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
    _ ≤ 1 / 4 := by nlinarith

private theorem eventual_radius_le_half :
    ∀ᶠ m : ℕ in atTop, radius (2 * m) ≤ 1 / 2 := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hlim : Tendsto (fun m : ℕ => radius (2 * m)) atTop (𝓝 0) := by
    unfold radius
    convert (logOrder_div_tendsto.const_mul 4096).comp hnat using 1
    · funext m
      simp only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat]
      ring
    · norm_num
  exact (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
    (fun _ h => h.le)

private theorem eventual_log_div_small :
    ∀ᶠ m : ℕ in atTop,
      (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ≤ 1 / 416 := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hlim : Tendsto
      (fun m : ℕ => (logOrder (2 * m) : ℝ) / (2 * m : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv]
      using (logOrder_div_tendsto.comp hnat)
  exact (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 416))).mono
    (fun _ h => h.le)

private theorem eventual_X_ge_one :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
        InDomain hm θ v → ∀ j : Fin (2 * m),
          1 ≤ X (by omega) θ j := by
  filter_upwards [eventual_domain_log_scale, eventually_ge_atTop 8] with m hscale hm8
  intro hm θ v hdom j
  let N : ℝ := (2 * m : ℕ)
  let L : ℝ := (logOrder (2 * m) : ℝ)
  let R : ℝ := Real.log (2 * m : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (show 0 < 2 * m by omega)
  have hN16 : 16 ≤ N := by
    dsimp [N]
    exact_mod_cast (show 16 ≤ 2 * m by omega)
  have hL : 0 ≤ L := by positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * m by omega))
  have hscale' : L * (1 + R) / N ≤ 1 := by
    simpa only [N, L, R, Nat.cast_mul, Nat.cast_ofNat] using hscale
  have herr := scaled_source_error_le hN hL hR hscale'
  have hN2 : 97 ≤ N ^ 2 := by nlinarith [sq_nonneg (N - 16)]
  have hpi : (Real.pi / N) ^ 2 ≤ 16 / N ^ 2 := by
    have hpi4 : Real.pi ≤ 4 := Real.pi_lt_four.le
    have hpi2' := mul_self_le_mul_self (show 0 ≤ Real.pi by positivity) hpi4
    have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith
    have hN2pos : 0 < N ^ 2 := sq_pos_of_pos hN
    calc
      (Real.pi / N) ^ 2 = Real.pi ^ 2 / N ^ 2 := by ring
      _ ≤ 16 / N ^ 2 := div_le_div_of_nonneg_right hpi2 hN2pos.le
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi / N)
  have hbase : 2 - 16 / N ^ 2 ≤ 2 * Real.cos (Real.pi / N) := by
    nlinarith
  have hX := domain_X_bound hm θ v hdom j
  have hX' : -(81 / N ^ 2) ≤
      X (by omega) θ j - 2 * Real.cos (Real.pi / N) := by
    have hX0 : |X (by omega) θ j - 2 * Real.cos (Real.pi / N)| ≤
        40 * L / N ^ 3 + 25 * L ^ 2 / N ^ 4 +
          16 * L ^ 2 * R / N ^ 4 := by
      simpa only [N, L, R, Nat.cast_mul, Nat.cast_ofNat] using hX
    have habs := (abs_le.mp hX0).1
    have hlow : -(81 / N ^ 2) ≤
        -(40 * L / N ^ 3 + 25 * L ^ 2 / N ^ 4 +
          16 * L ^ 2 * R / N ^ 4) := neg_le_neg herr
    have hchain := le_trans hlow habs
    simpa only [N, L, R, Nat.cast_mul, Nat.cast_ofNat] using hchain
  have hN2pos : 0 < N ^ 2 := sq_pos_of_pos hN
  have h97 : 97 / N ^ 2 ≤ 1 := by
    apply (div_le_iff₀ hN2pos).2
    nlinarith
  have hbase' : 2 - 16 / N ^ 2 - 81 / N ^ 2 ≤
      2 * Real.cos (Real.pi / N) - 81 / N ^ 2 :=
    sub_le_sub_right hbase _
  have hxlower : 2 * Real.cos (Real.pi / N) - 81 / N ^ 2 ≤
      X (by omega) θ j := by
    linarith [hX']
  have hcombine0 := hbase'.trans hxlower
  have hcombine : 2 - 97 / N ^ 2 ≤ X (by omega) θ j := by
    calc
      2 - 97 / N ^ 2 = 2 - 16 / N ^ 2 - 81 / N ^ 2 := by ring
      _ ≤ X (by omega) θ j := hcombine0
  have hlower : 1 ≤ 2 - 97 / N ^ 2 := by linarith [h97]
  exact hlower.trans hcombine

private theorem eventual_Y_product_le_quarter :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
        (q : Fin (2 * m) → ℝ), InDomain hm θ v → ‖q‖ ≤ 5 →
        ∀ j : Fin (2 * m),
          |Y (by omega) θ j * (J q + tangent (by omega) v) j| ≤ 1 / 4 := by
  filter_upwards [eventual_domain_log_scale, eventual_log_div_small] with m hscale hsmall
  intro hm θ v q hdom hq j
  let N : ℝ := (2 * m : ℕ)
  let L : ℝ := (logOrder (2 * m) : ℝ)
  let R : ℝ := Real.log (2 * m : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (show 0 < 2 * m by omega)
  have hL : 0 ≤ L := by positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * m by omega))
  have hscale' : L * (1 + R) / N ≤ 1 := by
    simpa only [N, L, R, Nat.cast_mul, Nat.cast_ofNat] using hscale
  have hsmall' : L / N ≤ 1 / 416 := by
    simpa only [N, L, Nat.cast_mul, Nat.cast_ofNat] using hsmall
  have hY := domain_Y_bound hm θ v hdom j
  have hsqrt := sqrt_log_le_one_add_log (show 1 ≤ 2 * m by omega)
  have hsqrt' : Real.sqrt R ≤ 1 + R := by
    simpa only [R, Nat.cast_mul, Nat.cast_ofNat] using hsqrt
  have hY' : |Y (by omega) θ j| ≤ 8 * L * (1 + R) / N ^ 2 := by
    have hY0 : |Y (by omega) θ j| ≤
        8 * L * Real.sqrt R / N ^ 2 := by
      simpa only [N, L, R, Nat.cast_mul, Nat.cast_ofNat] using hY
    calc
      |Y (by omega) θ j| ≤ 8 * L * Real.sqrt R / N ^ 2 := hY0
      _ ≤ 8 * L * (1 + R) / N ^ 2 := by
        have hcoef : 0 ≤ 8 * L / N ^ 2 := by positivity
        calc
          8 * L * Real.sqrt R / N ^ 2 =
              (8 * L / N ^ 2) * Real.sqrt R := by ring
          _ ≤ (8 * L / N ^ 2) * (1 + R) :=
            mul_le_mul_of_nonneg_left hsqrt' hcoef
          _ = 8 * L * (1 + R) / N ^ 2 := by ring
  have hp := tangent_total_bound hm θ v hdom q hq j
  have hmul :
      |Y (by omega) θ j| * |(J q + tangent (by omega) v) j| ≤
        (8 * L * (1 + R) / N ^ 2) * (13 * L) := by
    exact mul_le_mul hY' hp (abs_nonneg _) (by positivity)
  have hprod := product_bound_of_scale hN hL hR hscale' hsmall'
  calc
    |Y (by omega) θ j * (J q + tangent (by omega) v) j| =
        |Y (by omega) θ j| * |(J q + tangent (by omega) v) j| := by
      rw [abs_mul]
    _ ≤ (8 * L * (1 + R) / N ^ 2) * (13 * L) := hmul
    _ = 104 * L ^ 2 * (1 + R) / N ^ 2 := by ring
    _ ≤ 1 / 4 := hprod

private theorem eventual_coordinate_q_half :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
        (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
        ∀ j : Fin (2 * m),
          1 / 2 ≤ FiniteBox.patternSign s j * coordinate (by omega) s θ v j := by
  filter_upwards [eventual_coordinate_properties, eventual_radius_le_half] with m hprops hr
  intro hm s θ v hdom j
  have hp := hprops hm s θ v hdom
  have hpoint :
      |coordinate (by omega) s θ v j -
          baseWord (FiniteBox.patternSign s) j| ≤ radius (2 * m) := by
    have hpi := norm_le_pi_norm
      (coordinate (by omega) s θ v - baseWord (FiniteBox.patternSign s)) j
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using hpi.trans hp.close
  have hpoint' :
      |coordinate (by omega) s θ v j -
          FiniteBox.amplitude (2 * m) * FiniteBox.patternSign s j| ≤ radius (2 * m) := by
    simpa only [baseWord] using hpoint
  have hA : 1 ≤ FiniteBox.amplitude (2 * m) :=
    amplitude_ge_one (show 2 ≤ 2 * m by omega)
  have hs := FiniteBox.patternSign_is_sign s j
  rcases hs with hs | hs
  · rw [hs] at hpoint' ⊢
    have hb := (abs_le.mp hpoint')
    nlinarith
  · rw [hs] at hpoint' ⊢
    have hb := (abs_le.mp hpoint')
    nlinarith

theorem eventual_unselected_crossing_norm_lt_two :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
        (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
        ∀ j : Fin (2 * m),
          ‖crossingVector hm θ
              (center (coordinate (by omega) s θ v) v)
              (fun k => -FiniteBox.patternSign s k) j‖ < 2 := by
  filter_upwards [eventual_coordinate_properties, eventual_X_ge_one,
    eventual_coordinate_q_half, eventual_Y_product_le_quarter,
    eventual_ball_positive_input] with m hprops hX hq hY hin
  intro hm s θ v hdom j
  have hp := hprops hm s θ v hdom
  have hs := FiniteBox.patternSign_is_sign s j
  have harg := hin (by omega) θ v (FiniteBox.patternSign s) hdom
    (FiniteBox.patternSign_is_sign s) _ hp.close
  have hselected := (solution_positive_branch (by omega) θ v
    (FiniteBox.patternSign s) (coordinate (by omega) s θ v)
    (FiniteBox.patternSign_is_sign s) hp.fixed harg j).2
  have hselected' :
      (X (by omega) θ j + FiniteBox.patternSign s j *
          epsilon (2 * m) * coordinate (by omega) s θ v j) ^ 2 +
        (Y (by omega) θ j + FiniteBox.patternSign s j * epsilon (2 * m) *
          (J (coordinate (by omega) s θ v) + tangent (by omega) v) j) ^ 2 = 4 := by
    convert hselected using 1
  exact unselected_crossing_norm_lt_two hm θ
    (coordinate (by omega) s θ v) v (FiniteBox.patternSign s)
    hdom.1 hp.antiperiodic hdom.2.2.1.1 hdom.2.2.1.2.2 j hs
    (hX (by omega) θ v hdom j)
    (hq hm s θ v hdom j)
    (hY (by omega) θ v (coordinate (by omega) s θ v) hdom hp.norm_le j)
    hselected'

end
end StructuralNote.FixedSchurChartAdjacent

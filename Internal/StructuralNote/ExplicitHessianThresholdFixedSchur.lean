import StructuralNote.ExplicitHessianThresholdDownstream
import StructuralNote.FixedSchurExistence
import StructuralNote.FixedSchurChart
import StructuralNote.FixedSchurCyclicEquivariance
import StructuralNote.FixedSchurReflectionEquivariance

/-! Explicit pointwise prerequisites for the fixed-Schur chart. -/

namespace StructuralNote.ExplicitHessianThresholdFixedSchur

open Erdos1045 Erdos1045.EventualExact Complex Real Filter Set Metric
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonClosureEnergy CommonDomainClosure CommonDomainRadius
open CommonFiberBounds CommonFiberSmallCoefficients CommonFiberNormalProjectionScaled
open CommonTangentialParameters EdgeCoordinates FixedSchurData FixedSchurDomainBounds
open FixedSchurDomainSmallness FixedSchurSourceArithmetic FixedSchurExistence
open FixedSchurDomainSource
open FixedSchurContraction FixedSchurEquations FixedSchurChart FixedSchurLinear
open FixedSchurEdgeGeometry
open FixedSchurStrictInterior FixedSchurChartSmooth FixedSchurChartRegularity
open FixedSchurConfigurationSmooth FixedSchurEquationSmooth FixedSchurImplicitBanach
open FixedSchurChartGeometry FixedSchurObjectiveSmooth FixedSchurObjectivePaths
open CommonFiberCanonicalPaths CommonFiberCanonicalDirections
open FixedSchurCyclicEquivariance FixedSchurReflectionEquivariance
open ExplicitHessianThreshold
open scoped BigOperators Topology ContDiff

noncomputable section

theorem radius_le_one {n : ℕ} (hn : orderThreshold ≤ n) :
    FixedSchurDomainSmallness.radius n ≤ 1 := by
  have hb := logOrder_bound hn
  have h := log_monomial_div_small (j := 1) (c := 8192) hn (by norm_num) (by norm_num)
  simp only [pow_one] at h
  unfold FixedSchurDomainSmallness.radius
  apply le_trans ?_ (show 8192 * Erdos1045.ExplicitThreshold.logBudget (n : ℝ) / n ≤ 1 by
    linarith only [h])
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  linarith only [hb]

theorem domain_log_scale {n : ℕ} (hn : orderThreshold ≤ n) :
    (CommonDomainRadius.logOrder n : ℝ) * (1 + Real.log (n : ℝ)) / (n : ℝ) ≤ 1 := by
  have hb := logOrder_bound hn
  have hB : 0 ≤ Erdos1045.ExplicitThreshold.logBudget (n : ℝ) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans
      (Erdos1045.ExplicitThreshold.logBudget_ge_one hn)
  have hmul := mul_le_mul_of_nonneg_right hb hB
  have h := log_monomial_div_small (j := 2) (c := 2) hn (by norm_num) (by norm_num)
  apply le_trans ?_ (show 2 * Erdos1045.ExplicitThreshold.logBudget (n : ℝ) ^ 2 / n ≤ 1 by
    linarith only [h])
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    (CommonDomainRadius.logOrder n : ℝ) * (1 + Real.log (n : ℝ)) =
        (CommonDomainRadius.logOrder n : ℝ) *
          Erdos1045.ExplicitThreshold.logBudget (n : ℝ) := by
            rfl
    _ ≤ 2 * Erdos1045.ExplicitThreshold.logBudget (n : ℝ) *
          Erdos1045.ExplicitThreshold.logBudget (n : ℝ) := hmul
    _ = 2 * Erdos1045.ExplicitThreshold.logBudget (n : ℝ) ^ 2 := by ring

theorem quadratic_scale_small {n : ℕ} (hn : orderThreshold ≤ n) :
    128 * (CommonDomainRadius.logOrder n : ℝ) * (1 + Real.log (n : ℝ)) / (n : ℝ) ^ 2 ≤ 1 / 4 := by
  have hb := logOrder_bound hn
  have hB : 0 ≤ Erdos1045.ExplicitThreshold.logBudget (n : ℝ) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans
      (Erdos1045.ExplicitThreshold.logBudget_ge_one hn)
  have hmul := mul_le_mul_of_nonneg_right hb hB
  have hmon := log_monomial_div_small (j := 2) (c := 256) hn (by norm_num) (by norm_num)
  have hnPos : 0 < n := by exact_mod_cast order_pos hn
  have hnNat : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hnPos)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hn1
  have hnum : 0 ≤ 256 * Erdos1045.ExplicitThreshold.logBudget (n : ℝ) ^ 2 := by positivity
  have hden : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn1]
  calc
    128 * (CommonDomainRadius.logOrder n : ℝ) * (1 + Real.log (n : ℝ)) / (n : ℝ) ^ 2 ≤
        256 * Erdos1045.ExplicitThreshold.logBudget (n : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have hh := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 128)
      calc
        128 * (CommonDomainRadius.logOrder n : ℝ) * (1 + Real.log (n : ℝ)) =
            128 * ((CommonDomainRadius.logOrder n : ℝ) *
              Erdos1045.ExplicitThreshold.logBudget (n : ℝ)) := by
                unfold Erdos1045.ExplicitThreshold.logBudget
                ring
        _ ≤ 128 * (2 * Erdos1045.ExplicitThreshold.logBudget (n : ℝ) *
              Erdos1045.ExplicitThreshold.logBudget (n : ℝ)) := hh
        _ = 256 * Erdos1045.ExplicitThreshold.logBudget (n : ℝ) ^ 2 := by ring
    _ ≤ 256 * Erdos1045.ExplicitThreshold.logBudget (n : ℝ) ^ 2 / (n : ℝ) :=
      div_le_div_of_nonneg_left hnum hn0 hden
    _ ≤ 1 / 4 := by linarith only [hmon]

theorem domain_pointwise_upper {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin (2 * m) → ℝ) (hdom : InDomain hm θ v)
    (hsign : ∀ j, σ j = 1 ∨ σ j = -1) (j : Fin (2 * m)) :
    |FixedSchurData.Y (by omega) θ j| + epsilon (2 * m) *
        (|EdgeCoordinates.tangent (by omega) v j| +
          2 * (‖baseWord σ‖ + FixedSchurDomainSmallness.radius (2 * m))) ≤
      128 * (CommonDomainRadius.logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) /
        (2 * m : ℝ) ^ 2 := by
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm)
  have htwo : 2 ≤ 2 * m := by
    simpa only [mul_one] using Nat.mul_le_mul_left 2 hm1
  have hpos2 : 0 < 2 * m := Nat.mul_pos (by norm_num) hm
  have hR := radius_le_one hn
  have hL : 1 ≤ (CommonDomainRadius.logOrder (2 * m) : ℝ) := logOrder_one_le htwo
  have hlog : 0 ≤ Real.log (2 * m : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hpos2
  have hsqrt : Real.sqrt (Real.log (2 * m : ℝ)) ≤ 1 + Real.log (2 * m : ℝ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · linarith only [hlog]
    · nlinarith only [hlog, sq_nonneg (1 + Real.log (2 * m : ℝ))]
  have hY := domain_Y_bound hm θ v hdom j
  have hT := domain_tangent_bound hm θ v hdom j
  have hε := epsilon_le htwo
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hε
  have hbase := baseWord_norm_le_four htwo hsign
  have hR0 := radius_nonneg hpos2
  have hinside : |EdgeCoordinates.tangent (by omega) v j| +
      2 * (‖baseWord σ‖ + FixedSchurDomainSmallness.radius (2 * m)) ≤
        (25 / 2 : ℝ) * (CommonDomainRadius.logOrder (2 * m) : ℝ) := by
    calc
      _ ≤ (5 / 2 : ℝ) * (CommonDomainRadius.logOrder (2 * m) : ℝ) + 2 * (4 + 1) := by
        exact add_le_add hT (mul_le_mul_of_nonneg_left (add_le_add hbase hR) (by norm_num))
      _ ≤ (25 / 2 : ℝ) * (CommonDomainRadius.logOrder (2 * m) : ℝ) := by
        nlinarith only [hL]
  have hprod : epsilon (2 * m) *
      (|EdgeCoordinates.tangent (by omega) v j| +
        2 * (‖baseWord σ‖ + FixedSchurDomainSmallness.radius (2 * m))) ≤
      100 * (CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by
    calc
      _ ≤ (8 / (2 * m : ℝ) ^ 2) *
          ((25 / 2 : ℝ) * (CommonDomainRadius.logOrder (2 * m) : ℝ)) := by
        exact mul_le_mul hε hinside (by positivity) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ 8 * (CommonDomainRadius.logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) /
          (2 * m : ℝ) ^ 2 + 100 * (CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 :=
      add_le_add hY hprod
    _ ≤ 8 * (CommonDomainRadius.logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) /
          (2 * m : ℝ) ^ 2 + 100 * (CommonDomainRadius.logOrder (2 * m) : ℝ) *
          (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by
      apply add_le_add
      · have hcoef : 0 ≤ 8 * (CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by positivity
        calc
          _ = (8 * (CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2) *
                Real.sqrt (Real.log (2 * m : ℝ)) := by ring
          _ ≤ (8 * (CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2) *
                (1 + Real.log (2 * m : ℝ)) := mul_le_mul_of_nonneg_left hsqrt hcoef
          _ = _ := by ring
      · apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (show (1 : ℝ) ≤ 1 + Real.log (2 * m : ℝ) by linarith)
          (show 0 ≤ 100 * (CommonDomainRadius.logOrder (2 * m) : ℝ) by positivity)
    _ = 108 * (CommonDomainRadius.logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) /
          (2 * m : ℝ) ^ 2 := by ring
    _ ≤ _ := by
      have hcoef : 0 ≤ (CommonDomainRadius.logOrder (2 * m) : ℝ) *
          (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by positivity
      calc
        108 * (CommonDomainRadius.logOrder (2 * m) : ℝ) *
              (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 =
            108 * ((CommonDomainRadius.logOrder (2 * m) : ℝ) *
              (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2) := by ring
        _ ≤ 128 * ((CommonDomainRadius.logOrder (2 * m) : ℝ) *
              (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (by norm_num) hcoef
        _ = _ := by ring

theorem domain_smallness {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ : Fin (2 * m) → ℝ)
    (hdom : InDomain hm θ v) (hsign : ∀ j, σ j = 1 ∨ σ j = -1) :
    0 ≤ FixedSchurDomainSmallness.radius (2 * m) ∧
      FixedSchurDomainSmallness.radius (2 * m) ≤ 1 ∧
      ∀ j, |FixedSchurData.Y (by omega) θ j| + epsilon (2 * m) *
        (|EdgeCoordinates.tangent (by omega) v j| +
          2 * (‖baseWord σ‖ + FixedSchurDomainSmallness.radius (2 * m))) ≤ 1 / 4 := by
  refine ⟨radius_nonneg (by omega), radius_le_one hn, ?_⟩
  intro j
  exact (domain_pointwise_upper hn hm θ v σ hdom hsign j).trans (by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using quadratic_scale_small hn)

theorem domain_smallness_bundle {m : ℕ} (hn : orderThreshold ≤ 2 * m) :
    (CommonDomainRadius.logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ≤ 1 ∧
    ∀ (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
      (σ : Fin (2 * m) → ℝ), InDomain hm θ v →
      (∀ j, σ j = 1 ∨ σ j = -1) →
      0 ≤ FixedSchurDomainSmallness.radius (2 * m) ∧
        FixedSchurDomainSmallness.radius (2 * m) ≤ 1 ∧
        ∀ j, |FixedSchurData.Y (by omega) θ j| + epsilon (2 * m) *
          (|EdgeCoordinates.tangent (by omega) v j| +
            2 * (‖baseWord σ‖ + FixedSchurDomainSmallness.radius (2 * m))) ≤ 1 / 4 := by
  exact ⟨(by simpa only [Nat.cast_mul, Nat.cast_ofNat] using domain_log_scale hn),
    fun hm θ v σ hdom hsign =>
    domain_smallness hn hm θ v σ hdom hsign⟩

theorem domain_root {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ : Fin (2 * m) → ℝ)
    (hdom : InDomain hm θ v) (hσ : ∀ j, σ j = 1 ∨ σ j = -1) :
    ∃! q : Fin (2 * m) → ℝ,
      ‖q - baseWord σ‖ ≤ radius (2 * m) ∧ equationMap hm θ v σ q = q := by
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm)
  have htwo : 2 ≤ 2 * m := by
    simpa only [mul_one] using Nat.mul_le_mul_left 2 hm1
  have hpos2 : 0 < 2 * m := Nat.mul_pos (by norm_num) hm
  have hsize := domain_smallness_bundle hn
  have hs := hsize.2 hm θ v σ hdom hσ
  have hf : baseWord σ ∈ closedBall (baseWord σ) (radius (2 * m)) := by simp [hs.1]
  have hsmall : ∀ j, |Y hpos2 θ j + σ j * epsilon (2 * m) *
      (tangent hpos2 v j + J (baseWord σ) j)| ≤ 1 := by
    intro j
    exact (ball_input_bound hpos2 (epsilon_pos htwo)
      _ _ _ _ hσ hs.2.2 hf j).trans (by norm_num)
  have hsource := domain_source_bound hm θ v σ hdom hσ hsmall
  have hnreal : (0 : ℝ) < 2 * m := by exact_mod_cast hpos2
  have hlog : 0 ≤ Real.log (2 * m : ℝ) := Real.log_nonneg (by exact_mod_cast hpos2)
  have hb := source_error_bound_under_unit_ratio
    (H := Real.sqrt (Real.log (2 * m : ℝ))) hnreal
    (logOrder_one_le htwo) (Real.sqrt_nonneg _)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.sq_sqrt hlog] using hsize.1)
  have hsource' : ‖equationMap hm θ v σ (baseWord σ) - baseWord σ‖ ≤ radius (2 * m) / 2 := by
    apply hsource.trans
    calc
      _ ≤ 2048 * (CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
        simpa only [Real.sq_sqrt hlog] using hb
      _ = radius (2 * m) / 2 := by
        simp only [radius, Nat.cast_mul, Nat.cast_ofNat]
        ring
  exact exists_unique_fixedPoint hpos2 (epsilon_pos htwo) hs.1
    _ _ _ _ _ hσ hs.2.2 hsource'

theorem ball_positive_input {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ : Fin (2 * m) → ℝ)
    (hdom : InDomain hm θ v) (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (q : Fin (2 * m) → ℝ) (hq : ‖q - baseWord σ‖ ≤ radius (2 * m)) (j : Fin (2 * m)) :
    |Y (Nat.mul_pos (by norm_num) hm) θ j + σ j * epsilon (2 * m) *
      (tangent (Nat.mul_pos (by norm_num) hm) v j + J q j)| < 2 := by
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm)
  have htwo : 2 ≤ 2 * m := by
    simpa only [mul_one] using Nat.mul_le_mul_left 2 hm1
  have hs := domain_smallness hn hm θ v σ hdom hσ
  have hqmem : q ∈ closedBall (baseWord σ) (radius (2 * m)) := by
    simpa only [mem_closedBall, dist_eq_norm] using hq
  exact (ball_input_bound (Nat.mul_pos (by norm_num) hm) (epsilon_pos htwo)
    _ _ _ _ hσ hs.2.2 hqmem j).trans_lt (by norm_num)

theorem signPattern_root {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain hm θ v) :
    ∃! q : Fin (2 * m) → ℝ,
      ‖q - baseWord (FiniteBox.patternSign s)‖ ≤ radius (2 * m) ∧
      equationMap hm θ v (FiniteBox.patternSign s) q = q :=
  domain_root hn hm θ v _ hdom (FiniteBox.patternSign_is_sign s)

theorem coordinate_spec {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain hm θ v) :
    ‖coordinate hm s θ v - baseWord (FiniteBox.patternSign s)‖ ≤ radius (2 * m) ∧
      equationMap hm θ v (FiniteBox.patternSign s) (coordinate hm s θ v) = coordinate hm s θ v := by
  exact coordinate_spec_of_exists hm s θ v (signPattern_root hn hm s θ v hdom).exists

theorem coordinate_unique {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain hm θ v) (q : Fin (2 * m) → ℝ)
    (hq : ‖q - baseWord (FiniteBox.patternSign s)‖ ≤ radius (2 * m))
    (hfix : equationMap hm θ v (FiniteBox.patternSign s) q = q) :
    q = coordinate hm s θ v := by
  have hu := signPattern_root hn hm s θ v hdom
  exact hu.unique ⟨hq, hfix⟩ (coordinate_spec_of_exists hm s θ v hu.exists)

theorem coordinate_properties {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega)) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain (by omega) θ v) :
    Properties hm θ v (FiniteBox.patternSign s) (coordinate (by omega) s θ v) := by
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have htwo : 2 ≤ 2 * m := by omega
  have hq := coordinate_spec hn hm0 s θ v hdom
  have hs := FiniteBox.patternSign_is_sign s
  have harg := ball_positive_input hn hm0 θ v _ hdom hs _ hq.1
  have hanti := solution_antiperiodic (by omega) θ v _ _ hdom.1 hdom.2.2.1.1
    (FiniteBox.patternSign_antiperiodic s) hq.2
  have hnorm : ‖coordinate (by omega) s θ v‖ ≤ 5 := by
    have hb := baseWord_norm_le_four htwo hs
    have hr := (domain_smallness hn (by omega) θ v _ hdom hs).2.1
    have ht := norm_sub_norm_le (coordinate (by omega) s θ v) (baseWord (FiniteBox.patternSign s))
    linarith only [hq.1, hb, hr, ht]
  refine ⟨hq.1, hq.2, hanti, hnorm,
    center_mean_zero hm _ v hdom.2.2.1.2.1,
    center_constraint hm _ v hdom.2.2.1.2.2,
    projection_center hm _ v hdom.2.2.1.2.2,
    center_pairPotential hm _ v hanti hdom.2.2.1.1 hdom.2.2.1.2.2, ?_, ?_, ?_⟩
  · intro j
    exact (solution_positive_branch (by omega) θ v _ _ hs hq.2 harg j).1
  · intro j
    exact vertex_antipodal_norm hm θ _ v hdom.1 hanti hdom.2.2.1.1 j
  · intro j
    exact solution_selected_edge hm θ v _ _ hdom.2.2.1.2.2 hs hq.2 harg j

theorem coordinate_cyclic {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 0 < m)
    (k : ℕ) (s : FiniteBox.SignPattern hm) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v) :
    coordinate hm (SignPatternSymmetry.rotatePattern k s)
        (FixedSchurCyclicEquivariance.cyclicReal k θ)
        (FixedSchurCyclicEquivariance.cyclicCenter k v) =
      FixedSchurCyclicEquivariance.cyclicReal k (coordinate hm s θ v) := by
  have hs := coordinate_spec hn hm s θ v hdom
  symm
  apply coordinate_unique hn hm (SignPatternSymmetry.rotatePattern k s)
    (FixedSchurCyclicEquivariance.cyclicReal k θ)
    (FixedSchurCyclicEquivariance.cyclicCenter k v)
    (inDomain_cyclic hm k θ v hdom)
    (FixedSchurCyclicEquivariance.cyclicReal k (coordinate hm s θ v))
  · rw [selectedWord_cyclic, baseWord_cyclic, norm_cyclicReal_sub]
    exact hs.1
  · rw [selectedWord_cyclic, equationMap_cyclic, hs.2]

theorem configuration_cyclic {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 2 ≤ m)
    (k : ℕ) (s : FiniteBox.SignPattern (by omega)) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain (by omega) θ v) :
    FixedSchurChart.configuration (by omega) (SignPatternSymmetry.rotatePattern k s)
        (FixedSchurCyclicEquivariance.cyclicReal k θ)
        (FixedSchurCyclicEquivariance.cyclicCenter k v) =
      FixedSchurCyclicEquivariance.cyclicCenter k
        (FixedSchurChart.configuration (by omega) s θ v) := by
  funext j
  unfold FixedSchurChart.configuration FixedSchurEdgeGeometry.vertex
  rw [coordinate_cyclic hn (by omega) k s θ v hdom]
  have hd := congrFun
    (diameterVector_cyclic (show 2 ≤ 2 * m by omega) k θ) j
  have hc := congrFun (center_cyclic hm k (coordinate (by omega) s θ v) v) j
  rw [hd, ← hc]
  simp only [cyclicCenter]
  ring

theorem coordinate_reflect {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega)) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain (by omega) θ v) :
    coordinate (by omega) (FixedSchurReflectionEquivariance.reflectPattern s)
        (FixedSchurReflectionEquivariance.reflectReal θ)
        (FixedSchurReflectionEquivariance.reflectCenter v) =
      FixedSchurReflectionEquivariance.reflectNormal
        (coordinate (by omega) s θ v) := by
  have hs := coordinate_spec hn (by omega) s θ v hdom
  symm
  apply coordinate_unique hn (by omega) (FixedSchurReflectionEquivariance.reflectPattern s)
    (FixedSchurReflectionEquivariance.reflectReal θ)
    (FixedSchurReflectionEquivariance.reflectCenter v)
    (inDomain_reflect hm θ v hdom)
    (FixedSchurReflectionEquivariance.reflectNormal (coordinate (by omega) s θ v))
  · rw [selectedWord_reflect, baseWord_reflect,
      norm_reflectNormal_sub (show 2 ≤ 2 * m by omega)]
    exact hs.1
  · rw [selectedWord_reflect, equationMap_reflect, hs.2]

theorem configuration_reflect {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega)) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain (by omega) θ v) :
    FixedSchurChart.configuration (by omega) (FixedSchurReflectionEquivariance.reflectPattern s)
        (FixedSchurReflectionEquivariance.reflectReal θ)
        (FixedSchurReflectionEquivariance.reflectCenter v) =
      FixedSchurReflectionEquivariance.reflectCenter
        (FixedSchurChart.configuration (by omega) s θ v) := by
  funext j
  unfold FixedSchurChart.configuration FixedSchurEdgeGeometry.vertex
  rw [coordinate_reflect hn hm s θ v hdom]
  have hd := congrFun
    (diameterVector_reflect (show 2 ≤ 2 * m by omega) θ) j
  have hc := congrFun (center_reflect hm (coordinate (by omega) s θ v) v) j
  rw [hd, ← hc]
  simp only [reflectCenter, map_add]

theorem root_error {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ q : Fin (2 * m) → ℝ)
    (hdom : InDomain hm θ v) (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hq : ‖q - baseWord σ‖ ≤ radius (2 * m))
    (hfix : equationMap hm θ v σ q = q) :
    ‖q - baseWord σ‖ ≤ 4020 * (CommonDomainRadius.logOrder (2 * m) : ℝ) /
      (2 * m : ℝ) := by
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm)
  have htwo : 2 ≤ 2 * m := by
    simpa only [mul_one] using Nat.mul_le_mul_left 2 hm1
  have hpos2 : 0 < 2 * m := Nat.mul_pos (by norm_num) hm
  have hsize := domain_smallness_bundle hn
  have hs := hsize.2 hm θ v σ hdom hσ
  have hf : baseWord σ ∈ closedBall (baseWord σ) (radius (2 * m)) := by simp [hs.1]
  have hsmall : ∀ j, |Y hpos2 θ j + σ j * epsilon (2 * m) *
      (tangent hpos2 v j + J (baseWord σ) j)| ≤ 1 := by
    intro j
    exact (ball_input_bound hpos2 (epsilon_pos htwo)
      _ _ _ _ hσ hs.2.2 hf j).trans (by norm_num)
  have hsource := domain_source_bound hm θ v σ hdom hσ hsmall
  have hnreal : (0 : ℝ) < 2 * m := by exact_mod_cast hpos2
  have hb := source_bound_2010 hnreal
    (show 0 ≤ (CommonDomainRadius.logOrder (2 * m) : ℝ) by positivity) hsize.1
  have herr := fixedPoint_error hpos2 (epsilon_pos htwo) hs.1
    _ _ _ _ _ hσ hs.2.2 hq hfix
  change ‖q - baseWord σ‖ ≤
    2 * ‖equationMap hm θ v σ (baseWord σ) - baseWord σ‖ at herr
  calc
    _ ≤ 2 * ‖equationMap hm θ v σ (baseWord σ) - baseWord σ‖ := herr
    _ ≤ 2 * (2010 * (CommonDomainRadius.logOrder (2 * m) : ℝ) /
        (2 * m : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (hsource.trans hb) (by norm_num)
    _ = _ := by ring

theorem coordinate_interior {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v) :
    ‖coordinate hm s θ v - baseWord (FiniteBox.patternSign s)‖ < radius (2 * m) := by
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm)
  have htwo : 2 ≤ 2 * m := by
    simpa only [mul_one] using Nat.mul_le_mul_left 2 hm1
  have hpos2 : 0 < 2 * m := Nat.mul_pos (by norm_num) hm
  have hp := coordinate_spec hn hm s θ v hdom
  have he := root_error hn hm θ v _ _ hdom (FiniteBox.patternSign_is_sign s) hp.1 hp.2
  have hnreal : (0 : ℝ) < 2 * m := by exact_mod_cast hpos2
  have hL := logOrder_one_le htwo
  apply he.trans_lt
  unfold radius
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  exact (div_lt_div_iff_of_pos_right hnreal).2 (by nlinarith only [hL])

private theorem radicand_pos_explicit {t : ℝ} (ht : |t| < 2) : 0 < 4 - t ^ 2 := by
  nlinarith only [(abs_lt.mp ht).1, (abs_lt.mp ht).2]

theorem local_model {m : ℕ} (hn : orderThreshold ≤ 2 * m) (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) (x : SchurParameters m) (hx : InDomain hm x.1 x.2) :
    ∃ g : SchurParameters m → SchurState m,
      g x = coordinate hm s x.1 x.2 ∧ ContDiffAt ℝ ∞ g x ∧
        (∀ᶠ y in 𝓝 x, equationMap hm y.1 y.2 (FiniteBox.patternSign s) (g y) = g y ∧
          ‖g y - baseWord (FiniteBox.patternSign s)‖ < radius (2 * m) ∧
          (InDomain hm y.1 y.2 → g y = coordinate hm s y.1 y.2)) := by
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hm)
  have htwo : 2 ≤ 2 * m := by
    simpa only [mul_one] using Nat.mul_le_mul_left 2 hm1
  have hpos2 : 0 < 2 * m := Nat.mul_pos (by norm_num) hm
  have hp := coordinate_spec hn hm s x.1 x.2 hx
  have hs := domain_smallness hn hm x.1 x.2 _ hx (FiniteBox.patternSign_is_sign s)
  have hi := coordinate_interior hn hm s x.1 x.2 hx
  have hF : ContDiffAt ℝ ∞ (equationFamily hm (FiniteBox.patternSign s))
      (x, coordinate hm s x.1 x.2) := by
    apply equationFamily_contDiffAt
    intro j
    have hj := ball_positive_input hn hm x.1 x.2 _ hx
      (FiniteBox.patternSign_is_sign s) _ hp.1 j
    change 0 < 4 - (Y hpos2 x.1 j + FiniteBox.patternSign s j * epsilon (2 * m) *
      (tangent hpos2 x.2 j + J (coordinate hm s x.1 x.2) j)) ^ 2
    exact radicand_pos_explicit hj
  have hLip : LipschitzOnWith (1 / 2)
      (fun z => equationFamily hm (FiniteBox.patternSign s) (x, z))
      (closedBall (baseWord (FiniteBox.patternSign s)) (radius (2 * m))) := by
    exact crossingMap_lipschitz hpos2 (epsilon_pos htwo) (X hpos2 x.1) (Y hpos2 x.1)
      (tangent hpos2 x.2) (FiniteBox.patternSign s) (baseWord (FiniteBox.patternSign s))
      (FiniteBox.patternSign_is_sign s) hs.2.2
  obtain ⟨g, hgx, hg, he⟩ := exists_smooth_fixedPoint
    (equationFamily hm (FiniteBox.patternSign s)) x (coordinate hm s x.1 x.2)
    (baseWord (FiniteBox.patternSign s)) hF hi hLip hp.2
  refine ⟨g, hgx, hg, ?_⟩
  filter_upwards [he] with y hy
  refine ⟨hy.1, hy.2, ?_⟩
  intro hyd
  exact coordinate_unique hn hm s y.1 y.2 hyd (g y) hy.2.le hy.1

theorem coordinate_contDiffWithinAt {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 0 < m) (s : FiniteBox.SignPattern hm) (x : SchurParameters m)
    (hx : x ∈ FixedSchurChartSmooth.domain hm) :
    ContDiffWithinAt ℝ ∞ (fun y : SchurParameters m => coordinate hm s y.1 y.2)
      (FixedSchurChartSmooth.domain hm) x := by
  obtain ⟨g, hgx, hg, he⟩ := local_model hn hm s x hx
  apply hg.contDiffWithinAt.congr_of_eventuallyEq _ hgx.symm
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with y hy hyd
  exact (hy.2.2 hyd).symm

theorem configuration_contDiffWithinAt {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 0 < m) (s : FiniteBox.SignPattern hm) (x : SchurParameters m)
    (hx : x ∈ FixedSchurChartSmooth.domain hm) :
    ContDiffWithinAt ℝ ∞
      (fun y : SchurParameters m => configuration hm s y.1 y.2)
      (FixedSchurChartSmooth.domain hm) x := by
  obtain ⟨g, hgx, hg, he⟩ := local_model hn hm s x hx
  have hparam : ContDiffAt ℝ ∞ (fun y => (y, g y)) x := contDiffAt_id.prodMk hg
  have hfamily : ContDiffAt ℝ ∞ (configurationFamily hm) (x, g x) :=
    (configurationFamily_contDiff hm).contDiffAt.of_le (by simp)
  have hc := hfamily.comp x hparam
  change ContDiffAt ℝ ∞ (fun y =>
    FixedSchurEdgeGeometry.vertex y.1 (FixedSchurLinear.center (g y) y.2)) x at hc
  apply hc.contDiffWithinAt.congr_of_eventuallyEq _ ?_
  · filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with y hy hyd
    simp only [configuration, hy.2.2 hyd]
  · simp only [configuration, hgx]

theorem objective_contDiffWithinAt_of_geometry {m : ℕ}
    (hn : orderThreshold ≤ 2 * m) (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega)) (x : SchurParameters m)
    (hx : InDomain (by omega) x.1 x.2)
    (hgeom : FixedSchurChartGeometry.GeometricProperties hm s x.1 x.2) :
    ContDiffWithinAt ℝ ∞ (FixedSchurObjectivePaths.objective (by omega) s)
      (FixedSchurChartSmooth.domain (by omega)) x := by
  have hconfig := configuration_contDiffWithinAt hn (by omega) s x hx
  have hF := F_contDiffAt_of_injective hgeom.injective
  have hcomp := hF.comp_contDiffWithinAt x hconfig
  change ContDiffWithinAt ℝ ∞
    (fun y : SchurParameters m =>
      FixedSchurObjective.F (FixedSchurChart.configuration (by omega) s y.1 y.2))
    (FixedSchurChartSmooth.domain (by omega)) x
  exact hcomp

theorem objective_direction_contDiffAt_of_geometry {m : ℕ}
    (hn : orderThreshold ≤ 2 * m) (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega)) (x d : SchurParameters m)
    (hx : x ∈ FixedSchurChartSmooth.domain (by omega)) (hd : Admissible (by omega) d)
    (hgeom : FixedSchurChartGeometry.GeometricProperties hm s x.1 x.2) :
    ContDiffAt ℝ ∞ (fun t => FixedSchurObjectivePaths.objective (by omega) s
      (affinePath x d t)) 0 := by
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) hm
  let S : Set ℝ := (affinePath x d) ⁻¹' FixedSchurChartSmooth.domain hm0
  have hdom : S ∈ 𝓝 (0 : ℝ) := affine_domain_near_zero hm0 x d hx hd
  have hx' : affinePath x d 0 ∈ FixedSchurChartSmooth.domain hm0 := by
    simpa only [affinePath, zero_smul, add_zero] using hx
  have hf := objective_contDiffWithinAt_of_geometry hn hm s
    (affinePath x d 0) hx' (by simpa only
      [affinePath, zero_smul, add_zero] using hgeom)
  have hp := (affinePath_contDiff x d).contDiffAt.contDiffWithinAt
    (s := S) (x := (0 : ℝ))
  exact (hf.comp 0 hp (fun _ h => h)).contDiffAt hdom

end
end StructuralNote.ExplicitHessianThresholdFixedSchur

import StructuralNote.FixedSchurBoundedRepresentation

/-! Identification of an actual center whose normal coordinate is bounded by
a fixed multiple of the logarithmic scale.  The proof first works in a ball
of radius `(K + 4) * logOrder n`; the fixed-point error then recovers the
standard close-to-word radius. -/

namespace StructuralNote.FixedSchurLogBoundedRepresentation

open Filter Set Metric
open Erdos1045 Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.FiniteFourierLift
open Erdos1045.EventualExact.SchurLift
open Erdos1045.EventualExact.SchurSpectrum
open CommonClosureEnergy CommonDomainClosure CommonDomainRadius CommonFiberBounds
open CommonFiberGeometry EdgeCoordinates HessianErrorLimits
open FixedSchurData FixedSchurDomainBounds FixedSchurDomainSmallness
open FixedSchurDomainSource FixedSchurChart FixedSchurChartRadial FixedSchurEdgeGeometry
open FixedSchurChartRotated FixedSchurExistence FixedSchurLinear
open FixedSchurProjectionDomain FixedSchurRepresentation
open FixedSchurRepresentationPositive FixedSchurStrictInterior
open FixedSchurContraction FixedSchurEquations
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

private theorem eventual_log_ball_input (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (show 0 < m by omega))
        (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
        InDomain (by omega) θ v →
        ∀ j : Fin (2 * m),
          |Y (by omega) θ j| +
            epsilon (2 * m) *
              (|EdgeCoordinates.tangent (by omega) v j| +
                2 * (‖baseWord (FiniteBox.patternSign s)‖ +
                  (K + 4) * (logOrder (2 * m) : ℝ))) ≤ 1 / 4 := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hlim : Tendsto
      (fun m : ℕ => 160 * (K + 1) *
        ((logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) /
          (2 * m : ℝ) ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat, Real.rpow_two,
      mul_zero] using
      ((logOrder_log_div_power_tendsto (p := 2) (by norm_num)).const_mul
        (160 * (K + 1))).comp hnat
  filter_upwards [hlim.eventually
      (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))] with m hbound
  intro hm s θ v hdom j
  let N : ℝ := (2 * m : ℕ)
  let L : ℝ := (logOrder (2 * m) : ℝ)
  let H : ℝ := Real.log (2 * m : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (show 0 < 2 * m by omega)
  have hL : 1 ≤ L := by
    dsimp [L]
    exact logOrder_one_le (show 2 ≤ 2 * m by omega)
  have hH : 0 ≤ H := by
    dsimp [H]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * m by omega))
  have hsqroot : Real.sqrt H ≤ 1 + H := by
    dsimp [H]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      sqrt_log_le_one_add_log (show 1 ≤ 2 * m by omega)
  have hY := domain_Y_bound (by omega) θ v hdom j
  have hY' : |Y (by omega) θ j| ≤
      8 * (K + 1) * L * (1 + H) / N ^ 2 := by
    have hY0 : |Y (by omega) θ j| ≤ 8 * L * Real.sqrt H / N ^ 2 := by
      simpa only [N, L, H, Nat.cast_mul, Nat.cast_ofNat] using hY
    calc
      |Y (by omega) θ j| ≤ 8 * L * Real.sqrt H / N ^ 2 := hY0
      _ ≤ 8 * L * (1 + H) / N ^ 2 := by
        have hc : 0 ≤ 8 * L / N ^ 2 := by positivity
        calc
          8 * L * Real.sqrt H / N ^ 2 =
              (8 * L / N ^ 2) * Real.sqrt H := by ring
          _ ≤ (8 * L / N ^ 2) * (1 + H) :=
            mul_le_mul_of_nonneg_left hsqroot hc
          _ = 8 * L * (1 + H) / N ^ 2 := by ring
      _ ≤ 8 * (K + 1) * L * (1 + H) / N ^ 2 := by
        have hfactor : 0 ≤ 8 * L * (1 + H) / N ^ 2 := by positivity
        have hK1 : 1 ≤ K + 1 := by linarith
        calc
          8 * L * (1 + H) / N ^ 2 =
              1 * (8 * L * (1 + H) / N ^ 2) := by ring
          _ ≤ (K + 1) * (8 * L * (1 + H) / N ^ 2) :=
            mul_le_mul_of_nonneg_right hK1 hfactor
          _ = 8 * (K + 1) * L * (1 + H) / N ^ 2 := by ring
  have hT := domain_tangent_bound (by omega) θ v hdom j
  have hbase := baseWord_norm_le_four (show 2 ≤ 2 * m by omega)
    (FiniteBox.patternSign_is_sign s)
  have hinside :
      |EdgeCoordinates.tangent (by omega) v j| +
          2 * (‖baseWord (FiniteBox.patternSign s)‖ + (K + 4) * L) ≤
        19 * (K + 1) * L := by
    calc
      _ ≤ (5 / 2 : ℝ) * L + 2 * (4 + (K + 4) * L) := by gcongr
      _ ≤ 19 * (K + 1) * L := by
        nlinarith [mul_nonneg hK (le_trans (by norm_num) hL)]
  have hε := epsilon_le (show 2 ≤ 2 * m by omega)
  have hprod :
      epsilon (2 * m) *
          (|EdgeCoordinates.tangent (by omega) v j| +
            2 * (‖baseWord (FiniteBox.patternSign s)‖ + (K + 4) * L)) ≤
        152 * (K + 1) * L * (1 + H) / N ^ 2 := by
    have hε' : epsilon (2 * m) ≤ 8 / N ^ 2 := by
      simpa only [N, Nat.cast_mul, Nat.cast_ofNat] using hε
    calc
      _ ≤ (8 / N ^ 2) * (19 * (K + 1) * L) :=
        mul_le_mul hε' hinside (by positivity) (by positivity)
      _ = 152 * (K + 1) * L / N ^ 2 := by ring
      _ ≤ 152 * (K + 1) * L * (1 + H) / N ^ 2 := by
        have hc : 0 ≤ 152 * (K + 1) * L / N ^ 2 := by positivity
        have hH1 : 1 ≤ 1 + H := by linarith
        calc
          152 * (K + 1) * L / N ^ 2 =
              (152 * (K + 1) * L / N ^ 2) * 1 := by ring
          _ ≤ (152 * (K + 1) * L / N ^ 2) * (1 + H) :=
            mul_le_mul_of_nonneg_left hH1 hc
          _ = 152 * (K + 1) * L * (1 + H) / N ^ 2 := by ring
  have htotal :
      |Y (by omega) θ j| +
          epsilon (2 * m) *
            (|EdgeCoordinates.tangent (by omega) v j| +
              2 * (‖baseWord (FiniteBox.patternSign s)‖ + (K + 4) * L)) ≤
        160 * (K + 1) * (L * (1 + H) / N ^ 2) := by
    calc
      _ ≤ 8 * (K + 1) * L * (1 + H) / N ^ 2 +
          152 * (K + 1) * L * (1 + H) / N ^ 2 := add_le_add hY' hprod
      _ = 160 * (K + 1) * (L * (1 + H) / N ^ 2) := by ring
  exact htotal.trans (by
    simpa only [N, L, H, Nat.cast_mul, Nat.cast_ofNat] using hbound.le)

private theorem fixed_of_selected_crossing {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega)) (θ : Fin (2 * m) → ℝ)
    (C : Fin (2 * m) → ℂ)
    (hC : HalfPeriodic (by omega) C) (hCmean : (∑ j, C j) = 0)
    (_hdom : InDomain (by omega) θ (projection hm C))
    (hsmall : ∀ j, |Y (by omega) θ j + FiniteBox.patternSign s j *
      epsilon (2 * m) *
        (tangent (by omega) (projection hm C) j +
          J (constraint (by omega) C) j)| ≤ 1 / 4)
    (hpos : ∀ j, 0 < X (by omega) θ j + FiniteBox.patternSign s j *
      epsilon (2 * m) * constraint (by omega) C j)
    (hcross : ∀ j, ‖crossingVector hm θ C (FiniteBox.patternSign s) j‖ = 2) :
    equationMap (by omega) θ (projection hm C) (FiniteBox.patternSign s)
        (constraint (by omega) C) = constraint (by omega) C := by
  have hv := projection_parameterSpace hm hC hCmean
  have hvq := hv.2.2
  have hcenter : center (constraint (by omega) C) (projection hm C) = C :=
    center_projection hm C
  have hsq (j : Fin (2 * m)) :
      (X (by omega) θ j + FiniteBox.patternSign s j * epsilon (2 * m) *
          constraint (by omega) C j) ^ 2 +
        (Y (by omega) θ j + FiniteBox.patternSign s j * epsilon (2 * m) *
          (J (constraint (by omega) C) + tangent (by omega) (projection hm C)) j) ^ 2 = 4 := by
    have hsel := selected_crossing_norm_sq (by omega) θ
      (constraint (by omega) C) (J (constraint (by omega) C) +
        tangent (by omega) (projection hm C)) (FiniteBox.patternSign s) j
    have hdiff : C (successor (by omega) j) - C j =
        edgeIncrement (constraint (by omega) C)
          (J (constraint (by omega) C) + tangent (by omega) (projection hm C)) j := by
      calc
        C (successor (by omega) j) - C j =
            center (constraint (by omega) C) (projection hm C) (successor (by omega) j) -
              center (constraint (by omega) C) (projection hm C) j := by rw [hcenter]
        _ = difference (by omega) (center (constraint (by omega) C) (projection hm C)) j := rfl
        _ = edgeIncrement (constraint (by omega) C)
            (J (constraint (by omega) C) + tangent (by omega) (projection hm C)) j :=
          congrFun (center_difference hm (constraint (by omega) C)
            (projection hm C) hvq) j
    have hvec : crossingVector hm θ C (FiniteBox.patternSign s) j =
        diameterVector θ j + diameterVector θ (successor (by omega) j) +
          (FiniteBox.patternSign s j : ℂ) *
            edgeIncrement (constraint (by omega) C)
              (J (constraint (by omega) C) + tangent (by omega) (projection hm C)) j := by
      unfold crossingVector
      rw [hdiff]
    rw [← hvec] at hsel
    rw [hcross j] at hsel
    nlinarith
  have hsmall' : ∀ j, |Y (by omega) θ j + FiniteBox.patternSign s j *
      epsilon (2 * m) *
        (tangent (by omega) (projection hm C) j +
          J (constraint (by omega) C) j)| < 2 := by
    intro j
    exact (hsmall j).trans_lt (by norm_num)
  exact positive_branch_solution (by omega) θ (projection hm C)
    (FiniteBox.patternSign s) (constraint (by omega) C)
    (FiniteBox.patternSign_is_sign s) hsmall' hpos hsq

/-- A logarithmic a priori normal-coordinate bound suffices to identify the
actual center with the selected fixed-Schur chart.  Saturated selected
crossings and common-domain membership remain explicit hypotheses. -/
theorem eventually_representation_of_selected_crossing_log_bounded
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (show 0 < m by omega))
        (θ : Fin (2 * m) → ℝ) (C : Fin (2 * m) → ℂ),
        HalfPeriodic (by omega) C →
        (∑ j, C j) = 0 →
        InDomain (by omega) θ (projection hm C) →
        ‖constraint (by omega) C‖ ≤ K * (logOrder (2 * m) : ℝ) →
        (∀ j, ‖crossingVector hm θ C (FiniteBox.patternSign s) j‖ = 2) →
        constraint (by omega) C = coordinate (by omega) s θ (projection hm C) ∧
          C = center (coordinate (by omega) s θ (projection hm C))
            (projection hm C) ∧
          vertex θ C = FixedSchurChart.configuration (by omega) s θ
            (projection hm C) := by
  filter_upwards [eventual_log_ball_input K hK, eventual_domain_log_scale,
    eventual_X_ge_half, eventually_representation_of_selected_crossing_positive]
    with m hlarge hscale hX hrepresentation
  intro hm s θ C hC hCmean hdom hqnorm hcross
  have hs := FiniteBox.patternSign_is_sign s
  have hL : 1 ≤ (logOrder (2 * m) : ℝ) :=
    logOrder_one_le (show 2 ≤ 2 * m by omega)
  have hbase := baseWord_norm_le_four (show 2 ≤ 2 * m by omega) hs
  have hR : 0 ≤ (K + 4) * (logOrder (2 * m) : ℝ) := by positivity
  have hball :
      ‖constraint (by omega) C - baseWord (FiniteBox.patternSign s)‖ ≤
        (K + 4) * (logOrder (2 * m) : ℝ) := by
    have htri := norm_sub_le (constraint (by omega) C)
      (baseWord (FiniteBox.patternSign s))
    calc
      _ ≤ ‖constraint (by omega) C‖ + ‖baseWord (FiniteBox.patternSign s)‖ := htri
      _ ≤ K * (logOrder (2 * m) : ℝ) + 4 := add_le_add hqnorm hbase
      _ ≤ (K + 4) * (logOrder (2 * m) : ℝ) := by
        nlinarith [mul_nonneg hK (le_trans (by norm_num) hL)]
  have hballmem : constraint (by omega) C ∈
      closedBall (baseWord (FiniteBox.patternSign s))
        ((K + 4) * (logOrder (2 * m) : ℝ)) := by
    simpa only [mem_closedBall, dist_eq_norm] using hball
  have hlarge' := hlarge hm s θ (projection hm C) hdom
  have hsmallq4 : ∀ j, |Y (by omega) θ j +
      FiniteBox.patternSign s j * epsilon (2 * m) *
        (tangent (by omega) (projection hm C) j +
          J (constraint (by omega) C) j)| ≤ 1 / 4 := by
    intro j
    exact ball_input_bound (by omega)
      (epsilon_pos (show 2 ≤ 2 * m by omega))
      (Y (by omega) θ) (tangent (by omega) (projection hm C))
      (FiniteBox.patternSign s) (baseWord (FiniteBox.patternSign s)) hs
      hlarge' hballmem j
  have hqtotal : ‖constraint (by omega) C‖ ≤
      ‖baseWord (FiniteBox.patternSign s)‖ +
        (K + 4) * (logOrder (2 * m) : ℝ) := by
    have heq : constraint (by omega) C =
        (constraint (by omega) C - baseWord (FiniteBox.patternSign s)) +
          baseWord (FiniteBox.patternSign s) := by abel
    rw [heq]
    calc
      _ ≤ ‖constraint (by omega) C - baseWord (FiniteBox.patternSign s)‖ +
          ‖baseWord (FiniteBox.patternSign s)‖ := norm_add_le _ _
      _ ≤ (K + 4) * (logOrder (2 * m) : ℝ) +
          ‖baseWord (FiniteBox.patternSign s)‖ := add_le_add hball le_rfl
      _ = ‖baseWord (FiniteBox.patternSign s)‖ +
          (K + 4) * (logOrder (2 * m) : ℝ) := by ring
  have hpos : ∀ j, 0 < X (by omega) θ j +
      FiniteBox.patternSign s j * epsilon (2 * m) * constraint (by omega) C j := by
    intro j
    have hXj := hX hm θ (projection hm C) hdom j
    have hqj : |constraint (by omega) C j| ≤
        ‖baseWord (FiniteBox.patternSign s)‖ +
          (K + 4) * (logOrder (2 * m) : ℝ) := by
      simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (constraint (by omega) C) j).trans hqtotal
    have hε := epsilon_pos (show 2 ≤ 2 * m by omega)
    have hsplit : epsilon (2 * m) *
        (|tangent (by omega) (projection hm C) j| +
          2 * (‖baseWord (FiniteBox.patternSign s)‖ +
            (K + 4) * (logOrder (2 * m) : ℝ))) =
        epsilon (2 * m) * |tangent (by omega) (projection hm C) j| +
          epsilon (2 * m) *
            (2 * (‖baseWord (FiniteBox.patternSign s)‖ +
              (K + 4) * (logOrder (2 * m) : ℝ))) := by ring
    have hinput := hlarge' j
    rw [hsplit] at hinput
    have hradial : epsilon (2 * m) *
        (2 * (‖baseWord (FiniteBox.patternSign s)‖ +
          (K + 4) * (logOrder (2 * m) : ℝ))) ≤ 1 / 4 := by
      nlinarith [abs_nonneg (Y (by omega) θ j),
        mul_nonneg hε.le (abs_nonneg (tangent (by omega) (projection hm C) j))]
    have hqmul := mul_le_mul_of_nonneg_left hqj hε.le
    have hepsq : epsilon (2 * m) * |constraint (by omega) C j| ≤ 1 / 8 := by
      nlinarith
    have hσabs : |FiniteBox.patternSign s j| = 1 := by
      rcases hs j with h | h <;> simp [h]
    have herr :
        |FiniteBox.patternSign s j * epsilon (2 * m) * constraint (by omega) C j| ≤
          1 / 8 := by
      simpa only [abs_mul, hσabs, abs_of_pos hε, one_mul] using hepsq
    have hlow := (abs_le.mp herr).1
    nlinarith
  have hfix := fixed_of_selected_crossing hm s θ C hC hCmean hdom
    hsmallq4 hpos hcross
  have hbase_mem : baseWord (FiniteBox.patternSign s) ∈
      closedBall (baseWord (FiniteBox.patternSign s))
        ((K + 4) * (logOrder (2 * m) : ℝ)) := by
    simpa only [mem_closedBall, dist_self] using hR
  have hsmallbase4 : ∀ j, |Y (by omega) θ j +
      FiniteBox.patternSign s j * epsilon (2 * m) *
        (tangent (by omega) (projection hm C) j +
          J (baseWord (FiniteBox.patternSign s)) j)| ≤ 1 / 4 := by
    intro j
    exact ball_input_bound (by omega)
      (epsilon_pos (show 2 ≤ 2 * m by omega))
      (Y (by omega) θ) (tangent (by omega) (projection hm C))
      (FiniteBox.patternSign s) (baseWord (FiniteBox.patternSign s)) hs
      hlarge' hbase_mem j
  have hsmallbase : ∀ j, |Y (by omega) θ j +
      FiniteBox.patternSign s j * epsilon (2 * m) *
        (tangent (by omega) (projection hm C) j +
          J (baseWord (FiniteBox.patternSign s)) j)| ≤ 1 := by
    intro j
    exact (hsmallbase4 j).trans (by norm_num)
  have hsource := domain_source_bound (by omega) θ (projection hm C)
    (FiniteBox.patternSign s) hdom hs hsmallbase
  have hN : (0 : ℝ) < 2 * m := by
    exact_mod_cast (show 0 < 2 * m by omega)
  have hL0 : 0 ≤ (logOrder (2 * m) : ℝ) := by positivity
  have hscale' :
      (logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) /
          (2 * m : ℝ) ≤ 1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hscale
  have hsource' :
      ‖equationMap (by omega) θ (projection hm C)
          (FiniteBox.patternSign s) (baseWord (FiniteBox.patternSign s)) -
          baseWord (FiniteBox.patternSign s)‖ ≤
        2010 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
    exact hsource.trans (source_bound_2010 hN hL0 hscale')
  have herr := fixedPoint_error (n := 2 * m)
    (R := (K + 4) * (logOrder (2 * m) : ℝ))
    (by omega) (epsilon_pos (show 2 ≤ 2 * m by omega)) hR
    (X (by omega) θ) (Y (by omega) θ)
    (tangent (by omega) (projection hm C)) (FiniteBox.patternSign s)
    (baseWord (FiniteBox.patternSign s)) hs hlarge' hball hfix
  have herr' :
      ‖constraint (by omega) C - baseWord (FiniteBox.patternSign s)‖ ≤
        4020 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
    change ‖constraint (by omega) C - baseWord (FiniteBox.patternSign s)‖ ≤
      2 * ‖equationMap (by omega) θ (projection hm C)
        (FiniteBox.patternSign s) (baseWord (FiniteBox.patternSign s)) -
        baseWord (FiniteBox.patternSign s)‖ at herr
    calc
      _ ≤ 2 * ‖equationMap (by omega) θ (projection hm C)
          (FiniteBox.patternSign s) (baseWord (FiniteBox.patternSign s)) -
          baseWord (FiniteBox.patternSign s)‖ := herr
      _ ≤ 2 * (2010 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hsource' (by norm_num)
      _ = 4020 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by ring
  have hclose :
      ‖constraint (by omega) C - baseWord (FiniteBox.patternSign s)‖ ≤ radius (2 * m) := by
    calc
      _ ≤ 4020 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := herr'
      _ ≤ 4096 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
        have hnonneg : 0 ≤ (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by positivity
        calc
          4020 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) =
              4020 * ((logOrder (2 * m) : ℝ) / (2 * m : ℝ)) := by ring
          _ ≤ 4096 * ((logOrder (2 * m) : ℝ) / (2 * m : ℝ)) :=
            mul_le_mul_of_nonneg_right (by norm_num) hnonneg
          _ = 4096 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by ring
      _ = radius (2 * m) := by
        simp only [radius, Nat.cast_mul, Nat.cast_ofNat]
  exact hrepresentation hm s θ C hC hCmean hdom hclose hcross

end
end StructuralNote.FixedSchurLogBoundedRepresentation

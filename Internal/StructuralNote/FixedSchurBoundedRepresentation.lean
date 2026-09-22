import StructuralNote.FixedSchurRepresentationPositive
import StructuralNote.FixedSchurStrictInterior

/-! Identification of a bounded actual center with the selected fixed-Schur
chart.  The close-to-sign-word estimate is derived from the fixed equation
inside a radius-nine contraction ball. -/

namespace StructuralNote.FixedSchurBoundedRepresentation

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

/-- The domain smallness estimate remains valid on the radius-nine ball
needed before the close-to-word estimate is known. -/
theorem eventual_radius_nine_input : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (show 0 < m by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      ∀ j : Fin (2 * m),
        |Y (by omega) θ j| +
          epsilon (2 * m) *
            (|EdgeCoordinates.tangent (by omega) v j| +
              2 * (‖baseWord (FiniteBox.patternSign s)‖ + 9)) ≤ 1 / 4 := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hlim : Tendsto
      (fun m : ℕ => 240 * ((logOrder (2 * m) : ℝ) *
        (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat, Real.rpow_two,
      mul_zero] using
      ((logOrder_log_div_power_tendsto (p := 2) (by norm_num)).const_mul 240).comp hnat
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
  have hY' : |Y (by omega) θ j| ≤ 8 * L * (1 + H) / N ^ 2 := by
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
  have hT := domain_tangent_bound (by omega) θ v hdom j
  have hbase := baseWord_norm_le_four (show 2 ≤ 2 * m by omega)
    (FiniteBox.patternSign_is_sign s)
  have hinside :
      |EdgeCoordinates.tangent (by omega) v j| +
          2 * (‖baseWord (FiniteBox.patternSign s)‖ + 9) ≤
        (57 / 2 : ℝ) * L := by
    calc
      _ ≤ (5 / 2 : ℝ) * L + 2 * (4 + 9) := by gcongr
      _ ≤ (57 / 2 : ℝ) * L := by nlinarith
  have hε := epsilon_le (show 2 ≤ 2 * m by omega)
  have hprod :
      epsilon (2 * m) *
          (|EdgeCoordinates.tangent (by omega) v j| +
            2 * (‖baseWord (FiniteBox.patternSign s)‖ + 9)) ≤
        228 * L / N ^ 2 := by
    have hε' : epsilon (2 * m) ≤ 8 / N ^ 2 := by
      simpa only [N, Nat.cast_mul, Nat.cast_ofNat] using hε
    calc
      _ ≤ (8 / N ^ 2) * ((57 / 2 : ℝ) * L) :=
        mul_le_mul hε' hinside (by positivity) (by positivity)
      _ = 228 * L / N ^ 2 := by ring
  have htotal :
      |Y (by omega) θ j| +
          epsilon (2 * m) *
            (|EdgeCoordinates.tangent (by omega) v j| +
              2 * (‖baseWord (FiniteBox.patternSign s)‖ + 9)) ≤
        240 * (L * (1 + H) / N ^ 2) := by
    calc
      _ ≤ 8 * L * (1 + H) / N ^ 2 + 228 * L / N ^ 2 :=
        add_le_add hY' hprod
      _ = (L / N ^ 2) * (8 * (1 + H) + 228) := by ring
      _ ≤ (L / N ^ 2) * (240 * (1 + H)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [hH]
      _ = 240 * (L * (1 + H) / N ^ 2) := by ring
  exact htotal.trans (by simpa only [N, L, H, Nat.cast_mul, Nat.cast_ofNat] using hbound.le)

/-- The selected crossing and the positive branch give a fixed equation before
the close-to-word radius is recovered. -/
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
          (J (constraint (by omega) C) +
            tangent (by omega) (projection hm C)) j) ^ 2 = 4 := by
    have hsel := selected_crossing_norm_sq (by omega) θ
      (constraint (by omega) C) (J (constraint (by omega) C) +
        tangent (by omega) (projection hm C)) (FiniteBox.patternSign s) j
    have hdiff : C (successor (by omega) j) - C j =
        edgeIncrement (constraint (by omega) C)
          (J (constraint (by omega) C) +
            tangent (by omega) (projection hm C)) j := by
      calc
        C (successor (by omega) j) - C j =
            center (constraint (by omega) C) (projection hm C)
              (successor (by omega) j) -
              center (constraint (by omega) C) (projection hm C) j := by
                rw [hcenter]
        _ = difference (by omega)
            (center (constraint (by omega) C) (projection hm C)) j := rfl
        _ = edgeIncrement (constraint (by omega) C)
            (J (constraint (by omega) C) +
              tangent (by omega) (projection hm C)) j :=
          congrFun (center_difference hm (constraint (by omega) C)
            (projection hm C) hvq) j
    have hvec : crossingVector hm θ C (FiniteBox.patternSign s) j =
        diameterVector θ j + diameterVector θ (successor (by omega) j) +
          (FiniteBox.patternSign s j : ℂ) *
            (edgeIncrement (constraint (by omega) C)
              (J (constraint (by omega) C) +
                tangent (by omega) (projection hm C)) j) := by
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

/-- The close-to-word hypothesis is unnecessary when the bounded
constraint is itself supplied. -/
theorem eventually_representation_of_selected_crossing_bounded :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (show 0 < m by omega))
        (θ : Fin (2 * m) → ℝ) (C : Fin (2 * m) → ℂ),
        HalfPeriodic (by omega) C →
        (∑ j, C j) = 0 →
        InDomain (by omega) θ (projection hm C) →
        ‖constraint (by omega) C‖ ≤ 5 →
        (∀ j, ‖crossingVector hm θ C (FiniteBox.patternSign s) j‖ = 2) →
        constraint (by omega) C = coordinate (by omega) s θ (projection hm C) ∧
          C = center (coordinate (by omega) s θ (projection hm C))
            (projection hm C) ∧
          vertex θ C = FixedSchurChart.configuration (by omega) s θ
            (projection hm C) := by
  filter_upwards [eventual_coordinate_unique, eventual_radius_nine_input,
    eventual_domain_log_scale, eventual_X_ge_half,
    eventually_ge_atTop 5] with m huniq hlarge hscale hX hm5
  intro hm s θ C hC hCmean hdom hqnorm hcross
  have hs := FiniteBox.patternSign_is_sign s
  have hbase := baseWord_norm_le_four (show 2 ≤ 2 * m by omega) hs
  have hqnorm' : ‖constraint (by omega) C‖ ≤ 5 := hqnorm
  have hball : ‖constraint (by omega) C -
      baseWord (FiniteBox.patternSign s)‖ ≤ 9 := by
    have htri := norm_sub_le (constraint (by omega) C)
      (baseWord (FiniteBox.patternSign s))
    linarith
  have hballmem : constraint (by omega) C ∈
      closedBall (baseWord (FiniteBox.patternSign s)) 9 := by
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
  have hsmallq : ∀ j, |Y (by omega) θ j +
      FiniteBox.patternSign s j * epsilon (2 * m) *
        (tangent (by omega) (projection hm C) j +
          J (constraint (by omega) C) j)| < 2 := by
    intro j
    exact (hsmallq4 j).trans_lt (by norm_num)
  have hpos : ∀ j, 0 < X (by omega) θ j +
      FiniteBox.patternSign s j * epsilon (2 * m) *
        constraint (by omega) C j := by
    intro j
    have hXj := hX hm θ (projection hm C) hdom j
    have hqj : |constraint (by omega) C j| ≤ 5 := by
      simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (constraint (by omega) C) j).trans hqnorm'
    have hε := epsilon_le (show 2 ≤ 2 * m by omega)
    have hmul0 := mul_le_mul hε hqj (abs_nonneg _) (by positivity :
      (0 : ℝ) ≤ 8 / ((2 * m : ℕ) : ℝ) ^ 2)
    have hepsq : epsilon (2 * m) * |constraint (by omega) C j| ≤
        40 / (2 * m : ℝ) ^ 2 := by
      have hmul : epsilon (2 * m) * |constraint (by omega) C j| ≤
          (8 / (2 * m : ℝ) ^ 2) * 5 := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmul0
      calc
        _ ≤ (8 / (2 * m : ℝ) ^ 2) * 5 := hmul
        _ = 40 / (2 * m : ℝ) ^ 2 := by ring
    have hσabs : |FiniteBox.patternSign s j| = 1 := by
      rcases hs j with h | h <;> simp [h]
    have herr :
        |FiniteBox.patternSign s j * epsilon (2 * m) *
            constraint (by omega) C j| ≤ 40 / (2 * m : ℝ) ^ 2 := by
      simpa only [abs_mul, hσabs,
        abs_of_pos (epsilon_pos (show 2 ≤ 2 * m by omega)), one_mul] using hepsq
    have hsmall : 40 / (2 * m : ℝ) ^ 2 < 1 / 2 := by
      apply (div_lt_iff₀ (sq_pos_of_pos (by positivity : (0 : ℝ) < 2 * m))).2
      have hm5R : (5 : ℝ) ≤ m := by exact_mod_cast hm5
      nlinarith
    have hlow := (abs_le.mp herr).1
    nlinarith
  have hfix := fixed_of_selected_crossing hm s θ C hC hCmean hdom
    hsmallq4 hpos hcross
  have hbase_mem : baseWord (FiniteBox.patternSign s) ∈
      closedBall (baseWord (FiniteBox.patternSign s)) 9 := by
    simp only [mem_closedBall, dist_self]
    norm_num
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
  have hL : 0 ≤ (logOrder (2 * m) : ℝ) := by positivity
  have hscale' :
    (logOrder (2 * m) : ℝ) *
          (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ≤ 1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      hscale
  have hsource' :
      ‖equationMap (by omega) θ (projection hm C)
          (FiniteBox.patternSign s) (baseWord (FiniteBox.patternSign s)) -
          baseWord (FiniteBox.patternSign s)‖ ≤
        2010 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
    have hb := source_bound_2010 hN hL hscale'
    exact hsource.trans hb
  have herr := fixedPoint_error (n := 2 * m) (R := 9)
    (by omega) (epsilon_pos (show 2 ≤ 2 * m by omega))
    (by norm_num : (0 : ℝ) ≤ 9)
    (X (by omega) θ) (Y (by omega) θ)
    (tangent (by omega) (projection hm C)) (FiniteBox.patternSign s)
    (baseWord (FiniteBox.patternSign s)) hs hlarge' hball hfix
  have herr' :
      ‖constraint (by omega) C -
          baseWord (FiniteBox.patternSign s)‖ ≤
        4020 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
    change ‖constraint (by omega) C -
        baseWord (FiniteBox.patternSign s)‖ ≤
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
      ‖constraint (by omega) C -
          baseWord (FiniteBox.patternSign s)‖ ≤ radius (2 * m) := by
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
  exact representation_of_selected_crossing hm s θ C hdom.1 hdom.2.1
    hC hCmean hdom hclose hsmallq hpos hcross
    (huniq (by omega) s θ (projection hm C) hdom)

end

end StructuralNote.FixedSchurBoundedRepresentation

import StructuralNote.ExplicitCanonicalEntry
import StructuralNote.ExplicitMatchingCoordinates
import StructuralNote.ExplicitHessianThreshold
import StructuralNote.ExplicitBalancedSelection

/-! Explicit entry of a saturated actual active word into the selected
fixed-Schur chart.  This file contains the finite replacement for the
log-bounded representation wrapper. -/

namespace StructuralNote.ExplicitCanonicalEntrySelected

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open Real Complex Set Metric
open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open Erdos1045.ExplicitThreshold
open Erdos1045.EventualExact.CommonLocalization
open Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.FiniteFourierLift
open Erdos1045.EventualExact.SchurLift
open Erdos1045.EventualExact.SchurSpectrum
open CommonClosureEnergy CommonDomainClosure CommonDomainRadius CommonFiberBounds
open CommonFiberGeometry CommonTangentialParameters EdgeCoordinates
open FixedSchurData FixedSchurDomainBounds FixedSchurDomainSmallness
open FixedSchurDomainSource FixedSchurSourceArithmetic FixedSchurEquations
open FixedSchurStrictInterior
open FixedSchurContraction FixedSchurExistence FixedSchurLinear
open FixedSchurProjectionDomain FixedSchurRepresentation FixedSchurChart
open FixedSchurEdgeGeometry FixedSchurEquationSmooth
open MatchingActivityRadialActual MatchingActivityRadialIntegration
open MatchingActivityNonlocalPairs MatchingActivityCrossingVariationSaturation
open MatchingActivityCrossingExclusivity
open MatchingActivityActualChart MatchingActivityActualChartSelection
open MatchingActivityActualChartEntry MatchingActivitySaturation
open MatchingActivityActualWordAlignment MatchingActivityActualWordBalanced
open StrongPointwiseCoordinates StrongPointwiseSmallness StrongBudgetConsequences
open StrongObjectiveEstimate StrongPointwiseSteps SinglePressureEstimate
open NormalizedPolarRepresentation ExtremalPolarCenter SignedPressureRemainder
open ActualCrossingGeometry DiscreteEnergy FixedDualClassificationFinite
open SolScalarGap MatchingActivityRadialGeometry FiniteWordClassification
open FixedSchurCanonicalWordSymmetry FixedSchurActualCanonicalEntry
open FixedSchurActualRigidEquivalence FixedSchurChartSmooth
open ExplicitCanonicalEntry ExplicitHessianThresholdDownstream
open ExplicitBalancedSelection
open scoped BigOperators

noncomputable section

def representationThreshold (K : ℝ) : ℕ :=
  max 1024 (max ExplicitThreshold.threshold
    (max (decayThreshold 8192 1)
      (max (decayThreshold 2 1)
        (decayThreshold (320 * (K + 1)) (1 / 4)))))

def analyticThreshold : ℕ :=
  max ExplicitMatchingCoordinates.crossingThreshold
    (max ExplicitCanonicalEntry.orderThreshold
      (representationThreshold actualConstraintConstant))

def actualThreshold (δ : ℝ) : ℕ :=
  max analyticThreshold
    (ExplicitBalancedSelection.orderThreshold (actualChartEnergyConstant + 1)
      budgetConstant δ)

theorem representation_1024 {n : ℕ}
    (hn : representationThreshold actualConstraintConstant ≤ n) : 1024 ≤ n :=
  (le_max_left _ _).trans hn

theorem representation_base {n : ℕ}
    (hn : representationThreshold actualConstraintConstant ≤ n) :
    ExplicitThreshold.threshold ≤ n :=
  (le_max_left _ _).trans ((le_max_right _ _).trans hn)

theorem representation_radius_decay {n : ℕ}
    (hn : representationThreshold actualConstraintConstant ≤ n) :
    decayThreshold 8192 1 ≤ n :=
  (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans hn))

theorem representation_scale_decay {n : ℕ}
    (hn : representationThreshold actualConstraintConstant ≤ n) :
    decayThreshold 2 1 ≤ n :=
  (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))

theorem representation_ball_decay {n : ℕ}
    (hn : representationThreshold actualConstraintConstant ≤ n) :
    decayThreshold (320 * (actualConstraintConstant + 1)) (1 / 4) ≤ n :=
  (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))

private theorem sqrt_log_le_one_add_log {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (Real.log (n : ℝ)) ≤ 1 + Real.log (n : ℝ) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  apply (Real.sqrt_le_iff).2
  exact ⟨by linarith [Real.sqrt_nonneg (Real.log (n : ℝ))],
    by nlinarith [sq_nonneg (Real.log (n : ℝ))]⟩

theorem log_scale_small {n : ℕ} (hn : representationThreshold actualConstraintConstant ≤ n) :
    (CommonDomainRadius.logOrder n : ℝ) * (1 + Real.log (n : ℝ)) / (n : ℝ) ≤ 1 := by
  have hbase := representation_base hn
  have hdecay := representation_scale_decay hn
  have hL := ExplicitHessianThreshold.logOrder_bound hbase
  have hH0 : 0 ≤ logBudget (n : ℝ) := by
    linarith only [logBudget_ge_one hbase]
  have hmul := mul_le_mul hL (le_refl (logBudget (n : ℝ))) hH0
    (mul_nonneg (by norm_num) hH0)
  have hsmall := monomial_small (n := n) (j := 2) (C := 2) (ε := (1 : ℝ))
    (α := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hdecay
  rw [Real.rpow_neg_one, ← div_eq_mul_inv] at hsmall
  change (CommonDomainRadius.logOrder n : ℝ) * logBudget (n : ℝ) / (n : ℝ) ≤ 1
  calc
    _ ≤ 2 * logBudget (n : ℝ) ^ 2 / (n : ℝ) := by
      exact div_le_div_of_nonneg_right (by simpa only [pow_two, mul_assoc] using hmul)
        (Nat.cast_nonneg n)
    _ ≤ 1 := hsmall.le

theorem radius_le_one {n : ℕ} (hn : representationThreshold actualConstraintConstant ≤ n) :
    radius n ≤ 1 := by
  have hbase := representation_base hn
  have hdecay := representation_radius_decay hn
  have hL := ExplicitHessianThreshold.logOrder_bound hbase
  have hH0 : 0 ≤ logBudget (n : ℝ) := by
    linarith only [logBudget_ge_one hbase]
  have hmul := mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 4096)
  have hsmall := monomial_small (n := n) (j := 1) (C := 8192) (ε := (1 : ℝ))
    (α := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hdecay
  rw [pow_one, Real.rpow_neg_one, ← div_eq_mul_inv] at hsmall
  unfold radius
  have hmul' : 4096 * (CommonDomainRadius.logOrder n : ℝ) ≤
      8192 * logBudget (n : ℝ) := by
    nlinarith only [hmul]
  exact (div_le_div_of_nonneg_right hmul' (Nat.cast_nonneg n)).trans hsmall.le

theorem log_ball_input {m : ℕ} (hm : 2 ≤ m)
    (hn : representationThreshold actualConstraintConstant ≤ 2 * m)
    (s : SignPattern (by omega : 0 < m)) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain (by omega) θ v)
    (j : Fin (2 * m)) :
    |Y (by omega) θ j| + epsilon (2 * m) *
      (|tangent (by omega) v j| +
        2 * (‖baseWord (patternSign s)‖ +
          (actualConstraintConstant + 4) * (CommonDomainRadius.logOrder (2 * m) : ℝ))) ≤ 1 / 4 := by
  have hdecay := representation_ball_decay hn
  have hbaseThreshold := representation_base hn
  clear hn
  let N : ℝ := (2 * m : ℕ)
  let L : ℝ := (CommonDomainRadius.logOrder (2 * m) : ℝ)
  let H : ℝ := Real.log (2 * m : ℝ)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast (show 0 < 2 * m by omega)
  have hL : 1 ≤ L := by
    dsimp [L]
    exact logOrder_one_le (show 2 ≤ 2 * m by omega)
  have hH : 0 ≤ H := by
    dsimp [H]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * m by omega))
  have hK : 0 ≤ actualConstraintConstant := actualConstraintConstant_nonneg
  have hsqroot : Real.sqrt H ≤ 1 + H := by
    dsimp [H]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      sqrt_log_le_one_add_log (show 1 ≤ 2 * m by omega)
  have hY := domain_Y_bound (by omega) θ v hdom j
  have hY' : |Y (by omega) θ j| ≤
      8 * (actualConstraintConstant + 1) * L * (1 + H) / N ^ 2 := by
    have hY0 : |Y (by omega) θ j| ≤ 8 * L * Real.sqrt H / N ^ 2 := by
      simpa only [N, L, H, Nat.cast_mul, Nat.cast_ofNat] using hY
    calc
      _ ≤ 8 * L * Real.sqrt H / N ^ 2 := hY0
      _ ≤ 8 * L * (1 + H) / N ^ 2 := by
        have hc : 0 ≤ 8 * L / N ^ 2 := by positivity
        calc
          _ = (8 * L / N ^ 2) * Real.sqrt H := by ring
          _ ≤ (8 * L / N ^ 2) * (1 + H) := mul_le_mul_of_nonneg_left hsqroot hc
          _ = _ := by ring
      _ ≤ 8 * (actualConstraintConstant + 1) * L * (1 + H) / N ^ 2 := by
        have hf : 0 ≤ 8 * L * (1 + H) / N ^ 2 := by positivity
        calc
          _ = 1 * (8 * L * (1 + H) / N ^ 2) := by ring
          _ ≤ (actualConstraintConstant + 1) *
              (8 * L * (1 + H) / N ^ 2) :=
            mul_le_mul_of_nonneg_right (by linarith) hf
          _ = _ := by ring
  have hT := domain_tangent_bound (by omega) θ v hdom j
  have hbase := baseWord_norm_le_four (show 2 ≤ 2 * m by omega)
    (patternSign_is_sign s)
  have hinside : |tangent (by omega) v j| +
      2 * (‖baseWord (patternSign s)‖ + (actualConstraintConstant + 4) * L) ≤
      19 * (actualConstraintConstant + 1) * L := by
    calc
      _ ≤ (5 / 2 : ℝ) * L + 2 * (4 + (actualConstraintConstant + 4) * L) := by gcongr
      _ ≤ 19 * (actualConstraintConstant + 1) * L := by
        nlinarith only [hK, hL,
          mul_nonneg hK (show 0 ≤ L by linarith only [hL])]
  have hε := epsilon_le (show 2 ≤ 2 * m by omega)
  have hprod : epsilon (2 * m) *
      (|tangent (by omega) v j| +
        2 * (‖baseWord (patternSign s)‖ + (actualConstraintConstant + 4) * L)) ≤
      152 * (actualConstraintConstant + 1) * L * (1 + H) / N ^ 2 := by
    have hε' : epsilon (2 * m) ≤ 8 / N ^ 2 := by
      simpa only [N, Nat.cast_mul, Nat.cast_ofNat] using hε
    calc
      _ ≤ (8 / N ^ 2) * (19 * (actualConstraintConstant + 1) * L) :=
        mul_le_mul hε' hinside (by positivity) (by positivity)
      _ = 152 * (actualConstraintConstant + 1) * L / N ^ 2 := by ring
      _ ≤ 152 * (actualConstraintConstant + 1) * L * (1 + H) / N ^ 2 := by
        have hc : 0 ≤ 152 * (actualConstraintConstant + 1) * L / N ^ 2 := by positivity
        calc
          _ = (152 * (actualConstraintConstant + 1) * L / N ^ 2) * 1 := by ring
          _ ≤ (152 * (actualConstraintConstant + 1) * L / N ^ 2) * (1 + H) :=
            mul_le_mul_of_nonneg_left (by linarith) hc
          _ = _ := by ring
  have htotal : |Y (by omega) θ j| + epsilon (2 * m) *
      (|tangent (by omega) v j| +
        2 * (‖baseWord (patternSign s)‖ + (actualConstraintConstant + 4) * L)) ≤
      160 * (actualConstraintConstant + 1) * (L * (1 + H) / N ^ 2) := by
    calc
      _ ≤ 8 * (actualConstraintConstant + 1) * L * (1 + H) / N ^ 2 +
          152 * (actualConstraintConstant + 1) * L * (1 + H) / N ^ 2 :=
        add_le_add hY' hprod
      _ = _ := by ring
  have hLub := ExplicitHessianThreshold.logOrder_bound hbaseThreshold
  have hHB : 1 + H = logBudget N := by
    simp only [H, N, logBudget, Nat.cast_mul, Nat.cast_ofNat]
  have hLub' : L ≤ 2 * logBudget N := by
    simpa only [L, N] using hLub
  have hH0 : 0 ≤ logBudget N := by
    rw [← hHB]
    linarith
  have hmul := mul_le_mul hLub' (le_refl (logBudget N)) hH0
    (mul_nonneg (by norm_num) hH0)
  have hsmall := monomial_small (n := 2 * m) (j := 2)
    (C := 320 * (actualConstraintConstant + 1)) (ε := (1 / 4 : ℝ)) (α := 2)
    (by positivity) (by norm_num) (by norm_num) (by norm_num) hdecay
  rw [Real.rpow_neg (Nat.cast_nonneg (2 * m))] at hsmall
  rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast] at hsmall
  have hsmall' : 320 * (actualConstraintConstant + 1) *
      logBudget (2 * m : ℝ) ^ 2 / (2 * m : ℝ) ^ 2 < 1 / 4 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv] using hsmall
  apply htotal.trans
  rw [hHB]
  have hcoef : 0 ≤ 160 * (actualConstraintConstant + 1) := by positivity
  have hmul' := mul_le_mul_of_nonneg_left hmul hcoef
  calc
    160 * (actualConstraintConstant + 1) *
        (L * logBudget N / N ^ 2) ≤
      320 * (actualConstraintConstant + 1) * logBudget N ^ 2 / N ^ 2 := by
        have hnum : 160 * (actualConstraintConstant + 1) *
            (L * logBudget N) ≤
            320 * (actualConstraintConstant + 1) * logBudget N ^ 2 := by
          calc
            _ ≤ 160 * (actualConstraintConstant + 1) *
                (2 * logBudget N * logBudget N) := hmul'
            _ = _ := by ring
        calc
          _ = (160 * (actualConstraintConstant + 1) *
              (L * logBudget N)) / N ^ 2 := by ring
          _ ≤ _ := div_le_div_of_nonneg_right hnum (sq_nonneg N)
    _ ≤ 1 / 4 := by simpa only [N, Nat.cast_mul, Nat.cast_ofNat] using hsmall'.le

private theorem scaled_source_error_le {N L R : ℝ}
    (hN : 0 < N) (hLnonneg : 0 ≤ L) (hR : 0 ≤ R)
    (hscale : L * (1 + R) / N ≤ 1) :
    40 * L / N ^ 3 + 25 * L ^ 2 / N ^ 4 +
        16 * L ^ 2 * R / N ^ 4 ≤ 81 / N ^ 2 := by
  have hscale' : L * (1 + R) ≤ N := by
    simpa only [one_mul] using (div_le_iff₀ hN).mp hscale
  have hL : L ≤ N := by nlinarith [mul_nonneg hLnonneg hR]
  have hLR : L * R ≤ N := by nlinarith [hscale', hLnonneg]
  have hLsq : L ^ 2 ≤ N ^ 2 := by
    have h := mul_le_mul hL hL hLnonneg hN.le
    nlinarith
  have hLsqR : L ^ 2 * R ≤ N ^ 2 := by
    calc
      _ = L * (L * R) := by ring
      _ ≤ L * N := mul_le_mul_of_nonneg_left hLR hLnonneg
      _ ≤ N * N := mul_le_mul_of_nonneg_right hL hN.le
      _ = N ^ 2 := by ring
  have hN3 : 0 < N ^ 3 := by positivity
  have hN4 : 0 < N ^ 4 := by positivity
  have h₁ : 40 * L / N ^ 3 ≤ 40 / N ^ 2 := by
    apply (div_le_iff₀ hN3).2
    calc
      _ ≤ 40 * N := mul_le_mul_of_nonneg_left hL (by norm_num)
      _ = (40 / N ^ 2) * N ^ 3 := by field_simp
  have h₂ : 25 * L ^ 2 / N ^ 4 ≤ 25 / N ^ 2 := by
    apply (div_le_iff₀ hN4).2
    calc
      _ ≤ 25 * N ^ 2 := mul_le_mul_of_nonneg_left hLsq (by norm_num)
      _ = (25 / N ^ 2) * N ^ 4 := by field_simp
  have h₃ : 16 * L ^ 2 * R / N ^ 4 ≤ 16 / N ^ 2 := by
    apply (div_le_iff₀ hN4).2
    calc
      _ ≤ 16 * N ^ 2 := by nlinarith [hLsqR]
      _ = (16 / N ^ 2) * N ^ 4 := by field_simp
  calc
    _ ≤ 40 / N ^ 2 + 25 / N ^ 2 + 16 / N ^ 2 := add_le_add (add_le_add h₁ h₂) h₃
    _ = 81 / N ^ 2 := by ring

theorem domain_X_ge_one {m : ℕ} (hm : 2 ≤ m)
    (hn : representationThreshold actualConstraintConstant ≤ 2 * m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v) (j : Fin (2 * m)) :
    1 ≤ X (by omega) θ j := by
  have hscaleNat := log_scale_small hn
  have hn1024 := representation_1024 hn
  clear hn
  let N : ℝ := (2 * m : ℕ)
  let L : ℝ := (CommonDomainRadius.logOrder (2 * m) : ℝ)
  let R : ℝ := Real.log (2 * m : ℝ)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast (show 0 < 2 * m by omega)
  have hN16 : 16 ≤ N := by
    dsimp [N]
    exact_mod_cast (show 16 ≤ 2 * m by
      omega)
  have hL : 0 ≤ L := by positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * m by omega))
  have hscale' : L * (1 + R) / N ≤ 1 := by
    simpa only [N, L, R, Nat.cast_mul, Nat.cast_ofNat] using hscaleNat
  have herr := scaled_source_error_le hN hL hR hscale'
  have hN2 : 97 ≤ N ^ 2 := by nlinarith [sq_nonneg (N - 16)]
  have hpi : (Real.pi / N) ^ 2 ≤ 16 / N ^ 2 := by
    have hpi2' := mul_self_le_mul_self (show 0 ≤ Real.pi by positivity) Real.pi_lt_four.le
    have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith
    calc
      _ = Real.pi ^ 2 / N ^ 2 := by ring
      _ ≤ 16 / N ^ 2 := div_le_div_of_nonneg_right hpi2 (sq_nonneg N)
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi / N)
  have hbase : 2 - 16 / N ^ 2 ≤ 2 * Real.cos (Real.pi / N) := by nlinarith
  have hX := domain_X_bound (by omega) θ v hdom j
  have hX' : -(81 / N ^ 2) ≤ X (by omega) θ j - 2 * Real.cos (Real.pi / N) := by
    have hX0 : |X (by omega) θ j - 2 * Real.cos (Real.pi / N)| ≤
        40 * L / N ^ 3 + 25 * L ^ 2 / N ^ 4 + 16 * L ^ 2 * R / N ^ 4 := by
      simpa only [N, L, R, Nat.cast_mul, Nat.cast_ofNat] using hX
    have habs := (abs_le.mp hX0).1
    have hlow : -(81 / N ^ 2) ≤
        -(40 * L / N ^ 3 + 25 * L ^ 2 / N ^ 4 + 16 * L ^ 2 * R / N ^ 4) :=
      neg_le_neg herr
    exact hlow.trans habs
  have h97 : 97 / N ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hN)).2
    simpa only [one_mul] using hN2
  have hxlower : 2 * Real.cos (Real.pi / N) - 81 / N ^ 2 ≤ X (by omega) θ j := by
    linarith [hX']
  have hcombine : 2 - 97 / N ^ 2 ≤ X (by omega) θ j := by
    calc
      _ = 2 - 16 / N ^ 2 - 81 / N ^ 2 := by ring
      _ ≤ 2 * Real.cos (Real.pi / N) - 81 / N ^ 2 := sub_le_sub_right hbase _
      _ ≤ _ := hxlower
  linarith

theorem coordinate_unique {m : ℕ} (hm : 2 ≤ m)
    (hn : representationThreshold actualConstraintConstant ≤ 2 * m)
    (s : SignPattern (by omega : 0 < m)) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain (by omega) θ v) :
    ∀ q : Fin (2 * m) → ℝ, ‖q - baseWord (patternSign s)‖ ≤ radius (2 * m) →
      equationMap (by omega) θ v (patternSign s) q = q →
      q = coordinate (by omega) s θ v := by
  have hn1024 := representation_1024 hn
  have hscaleNat := log_scale_small hn
  have hlargeAll := fun j => log_ball_input hm hn s θ v hdom j
  have hR1 := radius_le_one hn
  clear hn
  have hs := patternSign_is_sign s
  have hR0 := radius_nonneg (show 0 < 2 * m by omega)
  have hL : 1 ≤ (CommonDomainRadius.logOrder (2 * m) : ℝ) := logOrder_one_le (by omega)
  have hRlarge : radius (2 * m) ≤
      (actualConstraintConstant + 4) * (CommonDomainRadius.logOrder (2 * m) : ℝ) := by
    simp only [radius, Nat.cast_mul, Nat.cast_ofNat]
    have hnR : (1024 : ℝ) ≤ 2 * m := by exact_mod_cast hn1024
    have hfrac : 4096 / (2 * m : ℝ) ≤ 4 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m)).2
      nlinarith
    have hK := actualConstraintConstant_nonneg
    have hm := mul_le_mul_of_nonneg_right hfrac (by positivity : 0 ≤ (CommonDomainRadius.logOrder (2 * m) : ℝ))
    calc
      4096 * (CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ) =
          (4096 / (2 * m : ℝ)) * (CommonDomainRadius.logOrder (2 * m) : ℝ) := by ring
      _ ≤ 4 * (CommonDomainRadius.logOrder (2 * m) : ℝ) := hm
      _ ≤ (actualConstraintConstant + 4) * (CommonDomainRadius.logOrder (2 * m) : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hsmall : ∀ j, |Y (by omega) θ j| + epsilon (2 * m) *
      (|tangent (by omega) v j| + 2 * (‖baseWord (patternSign s)‖ + radius (2 * m))) ≤
      1 / 4 := by
    intro j
    have hε0 : 0 ≤ epsilon (2 * m) :=
      (epsilon_pos (show 2 ≤ 2 * m by omega)).le
    calc
      _ ≤ |Y (by omega) θ j| + epsilon (2 * m) *
          (|tangent (by omega) v j| + 2 * (‖baseWord (patternSign s)‖ +
            (actualConstraintConstant + 4) * (CommonDomainRadius.logOrder (2 * m) : ℝ))) := by
        gcongr
      _ ≤ 1 / 4 := hlargeAll j
  have hbaseMem : baseWord (patternSign s) ∈ closedBall (baseWord (patternSign s))
      (radius (2 * m)) := by simp [hR0]
  have hinput : ∀ j, |Y (by omega) θ j + patternSign s j * epsilon (2 * m) *
      (tangent (by omega) v j + J (baseWord (patternSign s)) j)| ≤ 1 := by
    intro j
    exact (ball_input_bound (by omega) (epsilon_pos (show 2 ≤ 2 * m by omega))
      _ _ _ _ hs hsmall hbaseMem j).trans (by norm_num)
  have hsource := domain_source_bound (by omega) θ v (patternSign s) hdom hs hinput
  have hN : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hsource' : ‖equationMap (by omega) θ v (patternSign s) (baseWord (patternSign s)) -
      baseWord (patternSign s)‖ ≤ 2010 * (CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ) :=
    hsource.trans (source_bound_2010 hN (by positivity)
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hscaleNat))
  have hsourceRadius : ‖equationMap (by omega) θ v (patternSign s)
      (baseWord (patternSign s)) - baseWord (patternSign s)‖ ≤ radius (2 * m) / 2 := by
    apply hsource'.trans
    have hnonneg : 0 ≤ (CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by positivity
    calc
      2010 * (CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ) =
          2010 * ((CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ)) := by ring
      _ ≤
          2048 * ((CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (by norm_num) hnonneg
      _ = radius (2 * m) / 2 := by
        simp only [radius, Nat.cast_mul, Nat.cast_ofNat]
        ring
  have hex := exists_unique_fixedPoint (by omega)
    (epsilon_pos (show 2 ≤ 2 * m by omega)) hR0
    (X (by omega) θ) (Y (by omega) θ) (tangent (by omega) v)
    (patternSign s) (baseWord (patternSign s)) hs hsmall hsourceRadius
  have hspec := coordinate_spec_of_exists (by omega) s θ v hex.exists
  intro q hq hfix
  exact hex.unique ⟨hq, hfix⟩ hspec

theorem selected_chart_representation {m : ℕ} (hm : 2 ≤ m)
    (hn : representationThreshold actualConstraintConstant ≤ 2 * m)
    (s : SignPattern (by omega : 0 < m)) (θ : Fin (2 * m) → ℝ)
    (C : Fin (2 * m) → ℂ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hθmean : (∑ j, (θ j : ℂ)) = 0)
    (hC : HalfPeriodic (by omega) C) (hCmean : (∑ j, C j) = 0)
    (hdom : InDomain (by omega) θ (projection hm C))
    (hqnorm : ‖constraint (by omega) C‖ ≤
      actualConstraintConstant * (CommonDomainRadius.logOrder (2 * m) : ℝ))
    (hcross : ∀ j, ‖crossingVector hm θ C (patternSign s) j‖ = 2) :
    constraint (by omega) C = coordinate (by omega) s θ (projection hm C) ∧
      C = center (coordinate (by omega) s θ (projection hm C)) (projection hm C) ∧
      vertex θ C = configuration (by omega) s θ (projection hm C) := by
  have hscaleNat := log_scale_small hn
  have hlarge := fun j => log_ball_input hm hn s θ (projection hm C) hdom j
  have hunique := coordinate_unique hm hn s θ (projection hm C) hdom
  have hXall := fun j => domain_X_ge_one hm hn θ (projection hm C) hdom j
  clear hn
  have hs := patternSign_is_sign s
  have hL : 1 ≤ (CommonDomainRadius.logOrder (2 * m) : ℝ) := logOrder_one_le (by omega)
  have hK := actualConstraintConstant_nonneg
  let R : ℝ := (actualConstraintConstant + 4) * (CommonDomainRadius.logOrder (2 * m) : ℝ)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hbase := baseWord_norm_le_four (show 2 ≤ 2 * m by omega) hs
  have hball : ‖constraint (by omega) C - baseWord (patternSign s)‖ ≤ R := by
    have htri := norm_sub_le (constraint (by omega) C) (baseWord (patternSign s))
    dsimp [R]
    calc
      _ ≤ ‖constraint (by omega) C‖ + ‖baseWord (patternSign s)‖ := htri
      _ ≤ actualConstraintConstant * (CommonDomainRadius.logOrder (2 * m) : ℝ) + 4 := add_le_add hqnorm hbase
      _ ≤ (actualConstraintConstant + 4) * (CommonDomainRadius.logOrder (2 * m) : ℝ) := by
        nlinarith [mul_nonneg hK (le_trans (by norm_num) hL)]
  have hballmem : constraint (by omega) C ∈ closedBall (baseWord (patternSign s)) R := by
    simpa only [mem_closedBall, dist_eq_norm] using hball
  have hsmallq4 : ∀ j, |Y (by omega) θ j + patternSign s j * epsilon (2 * m) *
      (tangent (by omega) (projection hm C) j + J (constraint (by omega) C) j)| ≤ 1 / 4 := by
    intro j
    exact ball_input_bound (by omega) (epsilon_pos (show 2 ≤ 2 * m by omega))
      _ _ _ _ hs hlarge hballmem j
  have hqtotal : ‖constraint (by omega) C‖ ≤ ‖baseWord (patternSign s)‖ + R := by
    have heq : constraint (by omega) C =
        (constraint (by omega) C - baseWord (patternSign s)) + baseWord (patternSign s) := by abel
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add hball le_rfl) |>.trans_eq (add_comm _ _)
  have hpos : ∀ j, 0 < X (by omega) θ j +
      patternSign s j * epsilon (2 * m) * constraint (by omega) C j := by
    intro j
    have hX := hXall j
    have hqj : |constraint (by omega) C j| ≤ ‖baseWord (patternSign s)‖ + R := by
      simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (constraint (by omega) C) j).trans hqtotal
    have hε := epsilon_pos (show 2 ≤ 2 * m by omega)
    have hsplit : epsilon (2 * m) *
        (|tangent (by omega) (projection hm C) j| + 2 * (‖baseWord (patternSign s)‖ + R)) =
      epsilon (2 * m) * |tangent (by omega) (projection hm C) j| +
        epsilon (2 * m) * (2 * (‖baseWord (patternSign s)‖ + R)) := by ring
    have hinput := hlarge j
    change |Y (by omega) θ j| + epsilon (2 * m) *
      (|tangent (by omega) (projection hm C) j| + 2 * (‖baseWord (patternSign s)‖ + R)) ≤ 1 / 4 at hinput
    rw [hsplit] at hinput
    have hradial : epsilon (2 * m) * (2 * (‖baseWord (patternSign s)‖ + R)) ≤ 1 / 4 := by
      nlinarith [abs_nonneg (Y (by omega) θ j),
        mul_nonneg hε.le (abs_nonneg (tangent (by omega) (projection hm C) j))]
    have hqmul := mul_le_mul_of_nonneg_left hqj hε.le
    have hepsq : epsilon (2 * m) * |constraint (by omega) C j| ≤ 1 / 8 := by nlinarith
    have hσabs : |patternSign s j| = 1 := by rcases hs j with h | h <;> simp [h]
    have herr : |patternSign s j * epsilon (2 * m) * constraint (by omega) C j| ≤ 1 / 8 := by
      simpa only [abs_mul, hσabs, abs_of_pos hε, one_mul] using hepsq
    linarith [(abs_le.mp herr).1]
  have hsmall : ∀ j, |Y (by omega) θ j + patternSign s j * epsilon (2 * m) *
      (tangent (by omega) (projection hm C) j + J (constraint (by omega) C) j)| < 2 :=
    fun j => (hsmallq4 j).trans_lt (by norm_num)
  have hfix : equationMap (by omega) θ (projection hm C) (patternSign s)
      (constraint (by omega) C) = constraint (by omega) C := by
    have hv := projection_parameterSpace hm hC hCmean
    have hcenter := center_projection hm C
    have hsq (j : Fin (2 * m)) :
        (X (by omega) θ j + patternSign s j * epsilon (2 * m) * constraint (by omega) C j) ^ 2 +
        (Y (by omega) θ j + patternSign s j * epsilon (2 * m) *
          (J (constraint (by omega) C) + tangent (by omega) (projection hm C)) j) ^ 2 = 4 := by
      have hsel := selected_crossing_norm_sq (by omega) θ (constraint (by omega) C)
        (J (constraint (by omega) C) + tangent (by omega) (projection hm C)) (patternSign s) j
      have hdiff : C (successor (by omega) j) - C j = edgeIncrement (constraint (by omega) C)
          (J (constraint (by omega) C) + tangent (by omega) (projection hm C)) j := by
        calc
          _ = center (constraint (by omega) C) (projection hm C) (successor (by omega) j) -
              center (constraint (by omega) C) (projection hm C) j := by rw [hcenter]
          _ = difference (by omega) (center (constraint (by omega) C) (projection hm C)) j := rfl
          _ = _ := congrFun (center_difference hm (constraint (by omega) C)
            (projection hm C) hv.2.2) j
      have hvec : crossingVector hm θ C (patternSign s) j =
          diameterVector θ j + diameterVector θ (successor (by omega) j) +
            (patternSign s j : ℂ) * edgeIncrement (constraint (by omega) C)
              (J (constraint (by omega) C) + tangent (by omega) (projection hm C)) j := by
        unfold crossingVector
        rw [hdiff]
      rw [← hvec, hcross j] at hsel
      nlinarith
    exact positive_branch_solution (by omega) θ (projection hm C) (patternSign s)
      (constraint (by omega) C) hs hsmall hpos hsq
  have hbaseMem : baseWord (patternSign s) ∈ closedBall (baseWord (patternSign s)) R := by
    simp [hR]
  have hsmallbase : ∀ j, |Y (by omega) θ j + patternSign s j * epsilon (2 * m) *
      (tangent (by omega) (projection hm C) j + J (baseWord (patternSign s)) j)| ≤ 1 := by
    intro j
    exact (ball_input_bound (by omega) (epsilon_pos (show 2 ≤ 2 * m by omega))
      _ _ _ _ hs hlarge hbaseMem j).trans (by norm_num)
  have hsource := domain_source_bound (by omega) θ (projection hm C)
    (patternSign s) hdom hs hsmallbase
  have hN : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hsource' : ‖equationMap (by omega) θ (projection hm C) (patternSign s)
      (baseWord (patternSign s)) - baseWord (patternSign s)‖ ≤
      2010 * (CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ) :=
    hsource.trans (source_bound_2010 hN (by positivity)
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hscaleNat))
  have herr := fixedPoint_error (n := 2 * m) (R := R) (by omega)
    (epsilon_pos (show 2 ≤ 2 * m by omega)) hR
    (X (by omega) θ) (Y (by omega) θ) (tangent (by omega) (projection hm C))
    (patternSign s) (baseWord (patternSign s)) hs hlarge hball hfix
  have hclose : ‖constraint (by omega) C - baseWord (patternSign s)‖ ≤ radius (2 * m) := by
    apply herr.trans
    change 2 * ‖equationMap (by omega) θ (projection hm C) (patternSign s)
      (baseWord (patternSign s)) - baseWord (patternSign s)‖ ≤ _
    calc
      _ ≤ 2 * (2010 * (CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ)) :=
        mul_le_mul_of_nonneg_left hsource' (by norm_num)
      _ ≤ 4096 * (CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
        have hnonneg : 0 ≤ (CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by positivity
        calc
          2 * (2010 * (CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ)) =
              4020 * ((CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ)) := by ring
          _ ≤ 4096 * ((CommonDomainRadius.logOrder (2 * m) : ℝ) / (2 * m : ℝ)) :=
            mul_le_mul_of_nonneg_right (by norm_num) hnonneg
          _ = _ := by ring
      _ = radius (2 * m) := by simp only [radius, Nat.cast_mul, Nat.cast_ofNat]
  exact representation_of_selected_crossing hm s θ C hθ hθmean hC hCmean hdom
    hclose hsmall hpos hcross hunique

/-- Pointwise actual selected-chart entry from the fields returned by
`diameter_crossings_active`, with balancedness supplied by the word classifier. -/
theorem model_canonical_entry_with_energy {m : ℕ} (hm3 : 3 ≤ m)
    (D : FixedSchurFiberData hm3) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    {δ : ℝ} (hδ : 0 < δ) (hfinite : FiniteImprovement m budgetConstant δ)
    (hn : actualThreshold δ ≤ 2 * m)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η)
    (hc : CenterBounds (by omega : 0 < m) β u)
    (hcombined : G (by omega : 0 < m) (polarConstraint (by omega) β u) +
      radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2)
    (hb : PointwiseBounds (by omega : 0 < m) β u)
    (hsat : ∀ i : Fin m, modelRadii m β u i = 1)
    (hactive : ∀ i : Fin m,
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2) ∨
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2))
    (hdef : deficit (by omega)
      (activePattern (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u)) ≤ budgetConstant / (2 * m : ℝ) ^ 2) :
    ∃ x : SchurParameters m,
      CanonicalRepresentative hm3 z x ∧
      pairEnergy (by omega) (fun j => (x.1 j : ℂ)) + pairEnergy (by omega) x.2 ≤
        actualChartEnergyConstant / (2 * m : ℝ) ^ 2 ∧
      DirectRigidRelabeling z (configuration (by omega) (canonicalPattern hm3) x.1 x.2) ∧
      FixedSchurStationaryUniqueness.Stationary (by omega) (canonicalPattern hm3) x := by
  have hanalytic : analyticThreshold ≤ 2 * m := (le_max_left _ _).trans hn
  have hselection : ExplicitBalancedSelection.orderThreshold
      (actualChartEnergyConstant + 1) budgetConstant δ ≤ 2 * m :=
    (le_max_right _ _).trans hn
  have hcrossN := (le_max_left _ _).trans hanalytic
  have hcanonN := (le_max_left _ _).trans ((le_max_right _ _).trans hanalytic)
  have hrepN := (le_max_right _ _).trans ((le_max_right _ _).trans hanalytic)
  have hsmallN := (le_max_left _ _).trans hcrossN
  have hm8 : 8 ≤ m := by
    have h16 : 16 ≤ 2 * m := (le_max_left _ _).trans
      ((le_max_left _ _).trans ((le_max_right _ _).trans hsmallN))
    omega
  obtain ⟨hbudget, _hgap⟩ :=
    ExplicitMatchingCoordinates.combined_budget_parts (by omega) hmodel hz.1 hcombined
  have hs := ExplicitPressureThreshold.coefficients_small
    ((le_max_left _ _).trans ((le_max_right _ _).trans hcrossN))
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
  have hθ := (model_nonlocal_smallness hm8 hmodel hz.1 hb hbudget
    hs.2.1 hs.2.2.1 hs.2.2.2.1).1
  have henergy := model_actual_projection_energy (show 2 ≤ m by omega)
    hmodel.periodic hc hb hθ hbudget
  let C := centerZero (actualCenter m β u)
  let s : SignPattern (by omega : 0 < m) :=
    activePattern (by omega) (normalizedAngle m u) (modelRadii m β u) (actualCenter m β u)
  have hθhalf : HalfPeriodic (by omega) (fun j => (normalizedAngle m u j : ℂ)) := by
    intro j
    exact congrArg Complex.ofReal
      (normalizedAngle_halfPeriodic (by omega) u hmodel.periodic j)
  have hθmean : (∑ j, (normalizedAngle m u j : ℂ)) = 0 := by
    rw [← Complex.ofReal_sum, normalizedAngle_mean_zero (by omega) u]
    norm_num
  have hCbase := actualCenter_halfPeriodic (by omega) β u hmodel.periodic
  have hChalf : HalfPeriodic (by omega) C := centerZero_halfPeriodic (by omega) _ hCbase
  have hCmean : (∑ j, C j) = 0 := centerZero_sum (by omega) _
  have hdom : InDomain (by omega) (normalizedAngle m u)
      (projection (by omega : 2 ≤ m) C) := by
    apply ExplicitCanonicalEntry.projection_inDomain hcanonN (by omega)
      (normalizedAngle m u) C hθhalf hθmean hChalf hCmean
    simpa only [C, Nat.cast_mul, Nat.cast_ofNat] using henergy
  have hcross : ∀ j, ‖crossingVector (by omega : 2 ≤ m) (normalizedAngle m u) C
      (patternSign s) j‖ = 2 := by
    exact selected_crossing_all (by omega) (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) hθhalf hCbase hsat hactive
  have hqnorm : ‖constraint (by omega) C‖ ≤
      actualConstraintConstant * (CommonDomainRadius.logOrder (2 * m) : ℝ) := by
    dsimp only [C]
    exact model_actual_constraint_log_bound (by omega) hb
  have hrep := selected_chart_representation (by omega) hrepN s (normalizedAngle m u) C
    hθhalf hθmean hChalf hCmean hdom hqnorm hcross
  have hconfig : (fun j => normalizedPoint m β u j - average (actualCenter m β u)) =
      configuration (by omega) s (normalizedAngle m u)
        (projection (by omega : 2 ≤ m) C) := by
    rw [normalizedPoint_meanGauge_eq_vertex (by omega) β u hmodel.periodic hsat]
    unfold FixedSchurChart.configuration
    exact congrArg (vertex (normalizedAngle m u)) hrep.2.1
  have hchartExt : ExtremalNormalization.DiameterExtremal
      (configuration (by omega) s (normalizedAngle m u)
        (projection (by omega : 2 ≤ m) C)) := by
    rw [← hconfig]
    exact diameterExtremal_sub_const (normalizedPoint m β u)
      (model_normalizedPoint_extremal hmodel hz) (average (actualCenter m β u))
  let B : ℝ := actualChartEnergyConstant + 1
  have hB : 0 ≤ B := by dsimp [B]; linarith [actualChartEnergyConstant_nonneg]
  have henergy' : pairEnergy (by omega) (fun j => (normalizedAngle m u j : ℂ)) +
      pairEnergy (by omega) (projection (by omega : 2 ≤ m) C) ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 := by
    apply henergy.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    dsimp [B]
    nlinarith only [actualChartEnergyConstant_nonneg,
      sq_nonneg actualChartEnergyConstant]
  have hbalanced : BalancedWord (by omega) s :=
    ExplicitBalancedSelection.extremal_chart_word_balanced hB hδ hselection (by omega)
      hfinite (fun t θ v hd => D.geometry t θ v hd) s (normalizedAngle m u)
      (projection (by omega : 2 ≤ m) C) hdom henergy'
      (by simpa only [s] using hdef) hchartExt
  obtain ⟨x, hx, hxenergy, hrigid, hstat⟩ :=
    ExplicitCanonicalEntry.canonical_entry_of_saturated_chart hm3 D hcanonN hz hmodel hsat
      henergy hrep.2.1 (by simpa only [s] using hbalanced)
  exact ⟨x, hx, hxenergy, hrigid, hstat⟩

/-- Canonical entry, with the energy field omitted. -/
theorem model_canonical_entry {m : ℕ} (hm3 : 3 ≤ m)
    (D : FixedSchurFiberData hm3) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    {δ : ℝ} (hδ : 0 < δ) (hfinite : FiniteImprovement m budgetConstant δ)
    (hn : actualThreshold δ ≤ 2 * m)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η)
    (hc : CenterBounds (by omega : 0 < m) β u)
    (hcombined : G (by omega : 0 < m) (polarConstraint (by omega) β u) +
      radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2)
    (hb : PointwiseBounds (by omega : 0 < m) β u)
    (hsat : ∀ i : Fin m, modelRadii m β u i = 1)
    (hactive : ∀ i : Fin m,
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2) ∨
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2))
    (hdef : deficit (by omega)
      (activePattern (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u)) ≤ budgetConstant / (2 * m : ℝ) ^ 2) :
    ∃ x : SchurParameters m,
      CanonicalRepresentative hm3 z x ∧
      DirectRigidRelabeling z (configuration (by omega) (canonicalPattern hm3) x.1 x.2) ∧
      FixedSchurStationaryUniqueness.Stationary (by omega) (canonicalPattern hm3) x := by
  obtain ⟨x, hx, _henergy, hrigid, hstat⟩ := model_canonical_entry_with_energy hm3 D
    hδ hfinite hn hz hmodel hc hcombined hb hsat hactive hdef
  exact ⟨x, hx, hrigid, hstat⟩

/-- Fully pointwise `CanonicalRigidEntry` from the real maximizer front end and
the finite active-word classification certificate. -/
theorem actual_canonicalRigidEntry {m : ℕ} (hm3 : 3 ≤ m)
    (D : FixedSchurFiberData hm3) {δ : ℝ} (hδ : 0 < δ)
    (hfinite : FiniteImprovement m budgetConstant δ)
    (hn : actualThreshold δ ≤ 2 * m) : CanonicalRigidEntry hm3 := by
  intro z hz
  have hcrossN : ExplicitMatchingCoordinates.crossingThreshold ≤ 2 * m :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  obtain ⟨hmp, σ, α, β, u, η, hmodel, hc, _hη, _hq, _hpressure,
      hcombined, hb, hsat, hactive, hdef⟩ :=
    ExplicitMatchingCoordinates.diameter_crossings_active hz hcrossN
  obtain ⟨x, hx, hrigid, _hstat⟩ := model_canonical_entry hm3 D hδ hfinite hn hz
    hmodel hc hcombined hb hsat hactive hdef
  obtain ⟨τ, a, b, hbunit, hzrep⟩ := hrigid
  exact ⟨x, τ, a, b, hx, hbunit, hzrep⟩

/-- A real maximizer has a canonical chart representative with its original
quantitative energy budget and exact rigid-motion relation. -/
theorem actual_canonical_entry_with_energy {m : ℕ} (hm3 : 3 ≤ m)
    (D : FixedSchurFiberData hm3) {δ : ℝ} (hδ : 0 < δ)
    (hfinite : FiniteImprovement m budgetConstant δ)
    (hn : actualThreshold δ ≤ 2 * m) {z : Points (2 * m)}
    (hz : ExtremalNormalization.DiameterExtremal z) :
    ∃ x : SchurParameters m,
      CanonicalRepresentative hm3 z x ∧
      pairEnergy (by omega) (fun j => (x.1 j : ℂ)) + pairEnergy (by omega) x.2 ≤
        actualChartEnergyConstant / (2 * m : ℝ) ^ 2 ∧
      DirectRigidRelabeling z (configuration (by omega) (canonicalPattern hm3) x.1 x.2) ∧
      FixedSchurStationaryUniqueness.Stationary (by omega) (canonicalPattern hm3) x := by
  have hcrossN : ExplicitMatchingCoordinates.crossingThreshold ≤ 2 * m :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  obtain ⟨hmp, σ, α, β, u, η, hmodel, hc, _hη, _hq, _hpressure,
      hcombined, hb, hsat, hactive, hdef⟩ :=
    ExplicitMatchingCoordinates.diameter_crossings_active hz hcrossN
  exact model_canonical_entry_with_energy hm3 D hδ hfinite hn hz
    hmodel hc hcombined hb hsat hactive hdef

end
end StructuralNote.ExplicitCanonicalEntrySelected

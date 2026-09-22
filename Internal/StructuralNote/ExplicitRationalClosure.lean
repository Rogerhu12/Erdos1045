import StructuralNote.ExplicitRationalRepresentation
import StructuralNote.FixedSchurRationalClosureMatrix
/-! Explicit crossing-coordinate bounds and rank-two rational closure. -/
namespace StructuralNote.ExplicitRationalClosure
open Erdos1045 Erdos1045.EventualExact Complex Filter
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open RationalCommonConfiguration RationalAngleBranch RationalChart
open CommonClosureEnergy CommonDomainClosure CommonDomainRadius CommonFiberGeometry
open CommonFiberSmallCoefficients
open EdgeCoordinates FixedSchurData FixedSchurLinear FixedSchurChart
open FixedSchurEdgeGeometry FixedSchurDomainBounds FixedSchurDomainSmallness
open FixedSchurHarmonicBounds FixedSchurChartSizes HessianErrorLimits
open FixedSchurRationalWindowEnergy FixedSchurRationalWindowDomain
open FixedSchurRationalWindowRepresentation FixedSchurRationalWindowAngleChart
open LensClosure
open scoped BigOperators Topology
open RationalChart RationalAngleBranch RationalCommonConfiguration
open CommonDomainRadius
open FixedSchurRationalWindowCrossingChart LensClosure
open Complex Filter Erdos1045.EventualExact
open Matrix
open RationalExpressions RationalConfigurationPolynomials RationalStationarySystem
open FixedSchurRationalWindowDomain FixedSchurRationalWindowClosureDerivative
open FixedSchurRationalWindowCrossingChart FixedSchurRationalWindowClosureDerivative
open FixedSchurRationalClosureMatrix
noncomputable section

theorem crossing_coefficient_small {n : ℕ}
    (hN : ExplicitHessianThreshold.orderThreshold ≤ n) :
    60 * (CommonDomainRadius.logOrder n : ℝ) * (1 + Real.log n) / n < 1 / 4 := by
  have hs := ExplicitHessianThreshold.log_monomial_div_small (j := 2) (c := 120)
    hN (by norm_num) (by norm_num)
  have hb := ExplicitHessianThreshold.logOrder_bound hN
  have hH := Erdos1045.ExplicitThreshold.logBudget_ge_one hN
  have hp := mul_le_mul_of_nonneg_right hb (by linarith only [hH] :
    0 ≤ Erdos1045.ExplicitThreshold.logBudget n)
  have hnum : 60 * (CommonDomainRadius.logOrder n : ℝ) * (1 + Real.log n) ≤
      120 * Erdos1045.ExplicitThreshold.logBudget n ^ 2 := by
    change 60 * (CommonDomainRadius.logOrder n : ℝ) * Erdos1045.ExplicitThreshold.logBudget n ≤ _
    nlinarith only [hp]
  exact (div_le_div_of_nonneg_right hnum (Nat.cast_nonneg n)).trans_lt
    (hs.trans (by norm_num))

private theorem normalized_crossing_eq_rational {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega : 0 < m))
    (Z : RationalConfiguration.Variables m → ℝ)
    (hclosure : RationalConfiguration.closure (by omega) (rationalSign s) Z = 0)
    (j : Fin m) :
    crossingVector hm (theta (by omega) Z)
        (normalizedCenter (by omega) (rationalSign s) Z)
        (FiniteBox.patternSign s) (halfIndex j) =
      unit (-angleMean (by omega) Z) *
        (2 * RationalConfiguration.crossingUnit Z j) := by
  have hdiff := normalizedCenter_half_difference (by omega : 0 < m)
    (rationalSign s) Z hclosure j
  have hsign : rationalSign s j = 1 ∨ rationalSign s j = -1 :=
    FiniteBox.patternSign_is_sign s _
  have hcore :
      RationalConfiguration.diameter (by omega) Z j +
          RationalConfiguration.diameter (by omega) Z (j.val + 1) +
        ((rationalSign s j : ℝ) : ℂ) *
          RationalConfiguration.increment (by omega) (rationalSign s) Z j =
        2 * RationalConfiguration.crossingUnit Z j := by
    unfold RationalConfiguration.increment RationalChart.crossingIncrement
    rcases hsign with hs | hs <;> rw [hs] <;> norm_num
  unfold crossingVector
  rw [normalized_diameter, normalized_diameter,
    successor_half_val (by omega : 0 < m) j]
  change unit (-angleMean (by omega) Z) *
        RationalConfiguration.diameter (by omega) Z j +
      unit (-angleMean (by omega) Z) *
        RationalConfiguration.diameter (by omega) Z (j.val + 1) +
      ((rationalSign s j : ℝ) : ℂ) * difference (by omega)
        (normalizedCenter (by omega) (rationalSign s) Z) (halfIndex j) = _
  rw [hdiff]
  calc
    _ = unit (-angleMean (by omega) Z) *
        (RationalConfiguration.diameter (by omega) Z j +
          RationalConfiguration.diameter (by omega) Z (j.val + 1) +
          ((rationalSign s j : ℝ) : ℂ) *
            RationalConfiguration.increment (by omega) (rationalSign s) Z j) := by
      ring
    _ = _ := by rw [hcore]

private theorem framed_normalized_crossing {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega : 0 < m))
    (Z : RationalConfiguration.Variables m → ℝ)
    (hclosure : RationalConfiguration.closure (by omega) (rationalSign s) Z = 0)
    (j : Fin m) :
    (starRingEnd ℂ) (frame (2 * m) (halfIndex j)) *
        crossingVector hm (theta (by omega) Z)
          (normalizedCenter (by omega) (rationalSign s) Z)
          (FiniteBox.patternSign s) (halfIndex j) =
      2 * (unit (-angleMean (by omega) Z) *
        rotation (RationalConfiguration.crossingParameter Z j)) := by
  rw [normalized_crossing_eq_rational hm s Z hclosure j,
    RationalConfiguration.crossingUnit]
  have hf : frame (2 * m) (halfIndex j) = unit (midpoint m j) :=
    BoxLensLift.frame_halfIndex j
  have hu : (starRingEnd ℂ) (unit (midpoint m j)) * unit (midpoint m j) = 1 := by
    rw [← hf]
    exact conj_frame_mul _ _
  rw [hf]
  calc
    _ = ((starRingEnd ℂ) (unit (midpoint m j)) * unit (midpoint m j)) *
        (2 * (unit (-angleMean (by omega) Z) *
          rotation (RationalConfiguration.crossingParameter Z j))) := by ring
    _ = _ := by rw [hu, one_mul]

private theorem framed_components {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega : 0 < m))
    (Z : RationalConfiguration.Variables m → ℝ)
    (hclosure : RationalConfiguration.closure (by omega) (rationalSign s) Z = 0)
    (v : Fin (2 * m) → ℂ) (q : Fin (2 * m) → ℝ)
    (hvq : constraint (by omega) v = 0)
    (hcenter : normalizedCenter (by omega) (rationalSign s) Z = center q v)
    (j : Fin m) :
    2 * (unit (-angleMean (by omega) Z) *
          rotation (RationalConfiguration.crossingParameter Z j)) =
      ((X (by omega) (theta (by omega) Z) (halfIndex j) +
          FiniteBox.patternSign s (halfIndex j) * epsilon (2 * m) * q (halfIndex j) : ℝ) : ℂ) +
        I * ((Y (by omega) (theta (by omega) Z) (halfIndex j) +
          FiniteBox.patternSign s (halfIndex j) * epsilon (2 * m) *
            (J q + tangent (by omega) v) (halfIndex j) : ℝ) : ℂ) := by
  have hfixed :
      crossingVector hm (theta (by omega) Z)
          (normalizedCenter (by omega) (rationalSign s) Z)
          (FiniteBox.patternSign s) (halfIndex j) =
        diameterVector (theta (by omega) Z) (halfIndex j) +
          diameterVector (theta (by omega) Z)
            (successor (by omega) (halfIndex j)) +
          ((FiniteBox.patternSign s (halfIndex j) : ℝ) : ℂ) *
            edgeIncrement q (J q + tangent (by omega) v) (halfIndex j) := by
    rw [hcenter]
    unfold crossingVector
    rw [show center q v (successor (by omega) (halfIndex j)) -
        center q v (halfIndex j) = difference (by omega) (center q v) (halfIndex j) by rfl,
      FixedSchurLinear.center_difference hm q v hvq]
  have hframe := framed_crossing (by omega : 0 < 2 * m)
    (theta (by omega) Z) q (J q + tangent (by omega) v)
    (FiniteBox.patternSign s) (halfIndex j)
  rw [← hfixed] at hframe
  rw [← hframe]
  exact (framed_normalized_crossing hm s Z hclosure j).symm

/-- The literal single window forces the actual rational crossing-unit
coordinate `X (.inr j)` into the same `1/(2m)` small window.  Positivity is
obtained from the represented fixed-Schur root, rather than assumed. -/

theorem selectedWindow_crossingParameter_small {m : ℕ} (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (Z : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s Z <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        RationalConfiguration.closure (by omega) (rationalSign s) Z = 0 →
        ∀ j : Fin m,
          |RationalConfiguration.crossingParameter Z j| < 1 / (2 * m : ℝ) := by
  have hbase : ExplicitHessianThreshold.orderThreshold ≤ 2 * m := (le_max_left _ _).trans hN
  have hcoefficient := crossing_coefficient_small hbase
  have hrepresentation := ExplicitRationalRepresentation.selectedWindow_representation hN
  have hdomain := ExplicitRationalWindow.selectedWindow_inDomain hbase
  have hproperties := ExplicitHessianThresholdFixedSchur.coordinate_properties hbase
  clear hbase
  clear hN
  intro hm s Z hwindow hclosure j
  let C := normalizedCenter (by omega : 0 < m) (rationalSign s) Z
  let v := projection (show 2 ≤ m by omega) C
  let q := coordinate (by omega) s (theta (by omega) Z) v
  let i : Fin (2 * m) := halfIndex j
  let α := angleMean (by omega : 0 < m) Z
  let y := RationalConfiguration.crossingParameter Z j
  let W := unit (-α) * rotation y
  let p := (J q + tangent (by omega) v) i
  let A := X (by omega : 0 < 2 * m) (theta (by omega) Z) i +
    FiniteBox.patternSign s i * epsilon (2 * m) * q i
  let B := Y (by omega : 0 < 2 * m) (theta (by omega) Z) i +
    FiniteBox.patternSign s i * epsilon (2 * m) * p
  let N : ℝ := 2 * m
  let L : ℝ := logOrder (2 * m)
  let H : ℝ := Real.log (2 * m : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hL : 0 ≤ L := by positivity
  have hH : 0 ≤ H := by
    dsimp [H]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * m by omega))
  have hdom := hdomain (show 2 ≤ m by omega) s Z hwindow
  have hrep := hrepresentation (show 2 ≤ m by omega) s Z hwindow hclosure
  dsimp only at hrep
  have hprops := hproperties (show 2 ≤ m by omega) s
    (theta (by omega) Z) v hdom
  have hcomponents := framed_components (show 2 ≤ m by omega) s Z hclosure v q
    hdom.2.2.1.2.2 (by simpa only [C, v, q] using hrep.2.1) j
  have hcomponents' : 2 * W = ((A : ℝ) : ℂ) + I * ((B : ℝ) : ℂ) := by
    simpa only [W, α, y, A, B, p, q, i] using hcomponents
  have him : 2 * W.im = B := by
    have h := congrArg Complex.im hcomponents'
    norm_num [Complex.mul_im, Complex.add_im] at h
    exact h
  have hre : 2 * W.re = A := by
    have h := congrArg Complex.re hcomponents'
    norm_num [Complex.mul_re, Complex.add_re] at h
    exact h
  have hpositive : 0 < W.re := by
    have hp := hprops.positive i
    change 0 < A at hp
    linarith
  have hY := domain_Y_bound (by omega : 0 < m) (theta (by omega) Z) v hdom i
  have hp := tangent_total_bound (by omega : 0 < m) (theta (by omega) Z) v hdom q
    hprops.norm_le i
  have hepsilon := epsilon_le (show 2 ≤ 2 * m by omega)
  have hepsilon' : epsilon (2 * m) ≤ 8 / N ^ 2 := by
    simpa only [N, Nat.cast_mul, Nat.cast_ofNat] using hepsilon
  have hsign : |FiniteBox.patternSign s i| = 1 := by
    rcases FiniteBox.patternSign_is_sign s i with hs | hs <;> simp [hs]
  have hB : |B| ≤
      8 * L * Real.sqrt H / N ^ 2 + 104 * L / N ^ 2 := by
    have hsum := abs_add_le
      (Y (by omega : 0 < 2 * m) (theta (by omega) Z) i)
      (FiniteBox.patternSign s i * epsilon (2 * m) * p)
    calc
      |B| ≤ |Y (by omega) (theta (by omega) Z) i| +
          |FiniteBox.patternSign s i * epsilon (2 * m) * p| := by
        simpa only [B] using hsum
      _ = |Y (by omega) (theta (by omega) Z) i| + epsilon (2 * m) * |p| := by
        rw [abs_mul, abs_mul, hsign, one_mul,
          abs_of_pos (epsilon_pos (show 2 ≤ 2 * m by omega))]
      _ ≤ 8 * L * Real.sqrt H / N ^ 2 + (8 / N ^ 2) * (13 * L) := by
        apply add_le_add
        · simpa only [L, H, N, Nat.cast_mul, Nat.cast_ofNat] using hY
        · exact mul_le_mul hepsilon' hp (abs_nonneg p) (by positivity)
      _ = _ := by ring
  have hWim : |W.im| ≤
      4 * L * Real.sqrt H / N ^ 2 + 52 * L / N ^ 2 := by
    have habs : |B| = 2 * |W.im| := by
      rw [← him, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [habs] at hB
    calc
      |W.im| = (2 * |W.im|) / 2 := by ring
      _ ≤ (8 * L * Real.sqrt H / N ^ 2 + 104 * L / N ^ 2) / 2 :=
        div_le_div_of_nonneg_right hB (by norm_num)
      _ = _ := by ring
  have hα : |α| ≤ 4 * L * Real.sqrt H / N ^ 2 := by
    have hzero := domain_theta_bound (by omega : 0 < m) (theta (by omega) Z) v hdom
      (⟨0, by omega⟩ : Fin (2 * m))
    have heq : theta (by omega : 0 < m) Z (⟨0, by omega⟩ : Fin (2 * m)) = -α := by
      simp [α, theta, RationalAngleBranch.angle, RationalConfiguration.angleParameter]
    rw [heq, abs_neg] at hzero
    simpa only [L, H, N, Nat.cast_mul, Nat.cast_ofNat] using hzero
  have hsqrt : Real.sqrt H ≤ 1 + H := by
    apply (Real.sqrt_le_iff).2
    constructor
    · linarith [Real.sqrt_nonneg H]
    · nlinarith [sq_nonneg H]
  have htotal : |α| + |W.im| ≤ 60 * L * (1 + H) / N ^ 2 := by
    calc
      _ ≤ 4 * L * Real.sqrt H / N ^ 2 +
          (4 * L * Real.sqrt H / N ^ 2 + 52 * L / N ^ 2) :=
        add_le_add hα hWim
      _ = 8 * L * Real.sqrt H / N ^ 2 + 52 * L / N ^ 2 := by ring
      _ ≤ 8 * L * (1 + H) / N ^ 2 + 52 * L * (1 + H) / N ^ 2 := by
        apply add_le_add
        · have hc : 0 ≤ 8 * L / N ^ 2 := by positivity
          calc
            8 * L * Real.sqrt H / N ^ 2 = (8 * L / N ^ 2) * Real.sqrt H := by ring
            _ ≤ (8 * L / N ^ 2) * (1 + H) :=
              mul_le_mul_of_nonneg_left hsqrt hc
            _ = _ := by ring
        · have hH1 : 1 ≤ 1 + H := by linarith
          have hc : 0 ≤ 52 * L / N ^ 2 := by positivity
          calc
            52 * L / N ^ 2 = (52 * L / N ^ 2) * 1 := by ring
            _ ≤ (52 * L / N ^ 2) * (1 + H) :=
              mul_le_mul_of_nonneg_left hH1 hc
            _ = _ := by ring
      _ = _ := by ring
  have hcoefficient' : 60 * L * (1 + H) / N < 1 / 4 := by
    simpa only [L, H, N, Nat.cast_mul, Nat.cast_ofNat] using hcoefficient
  have htotal' : |α| + |W.im| < 1 / (4 * N) := by
    have hdiv := div_lt_div_of_pos_right hcoefficient' hN
    have heq : 60 * L * (1 + H) / N ^ 2 =
        (60 * L * (1 + H) / N) / N := by ring
    apply htotal.trans_lt
    rw [heq]
    calc
      _ < (1 / 4) / N := hdiv
      _ = _ := by ring
  have hrotationDifference : ‖rotation y - W‖ ≤ |α| := by
    have heq : rotation y - W = (1 - unit (-α)) * rotation y := by
      dsimp [W]
      ring
    rw [heq, norm_mul, rotation_norm, mul_one]
    have hu := norm_unit_sub_le (-α) 0
    rw [show 1 - unit (-α) = -(unit (-α) - 1) by ring, norm_neg]
    simpa only [unit, ofReal_zero, zero_mul, Complex.exp_zero, sub_zero, abs_neg] using hu
  have hrotationIm : |(rotation y).im| < 1 / (4 * N) := by
    have himdiff := Complex.abs_im_le_norm (rotation y - W)
    have hsplit : (rotation y).im = (rotation y - W).im + W.im := by
      simp only [Complex.sub_im]
      ring
    rw [hsplit]
    exact (abs_add_le _ _).trans_lt (by
      have := hrotationDifference
      linarith)
  have hN16 : (16 : ℝ) ≤ N := by
    dsimp [N]
    exact_mod_cast (show 16 ≤ 2 * m by omega)
  have hsmallN : 1 / (4 * N) ≤ 1 / 64 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * N)
      (by norm_num : (0 : ℝ) < 64)).2
    nlinarith
  have hWimSmall : |W.im| < 1 / 64 := by
    have : |W.im| ≤ |α| + |W.im| := by
      linarith [abs_nonneg α]
    exact this.trans_lt (htotal'.trans_le hsmallN)
  have hWnorm : ‖W‖ = 1 := by
    dsimp [W]
    rw [norm_mul, norm_unit, rotation_norm, one_mul]
  have hWsq : W.re ^ 2 + W.im ^ 2 = 1 := by
    have hn := Complex.normSq_apply W
    rw [Complex.normSq_eq_norm_sq, hWnorm, one_pow] at hn
    simpa only [pow_two] using hn.symm
  have hWre : (3 / 4 : ℝ) < W.re := by
    have himsq : |W.im| ^ 2 < (1 / 64 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 64)).2 hWimSmall
    rw [sq_abs] at himsq
    nlinarith [hWsq]
  have hrotationRe : 0 < (rotation y).re := by
    have hrediff := Complex.abs_re_le_norm (rotation y - W)
    have hαsmall : |α| < 1 / 64 := by
      have : |α| ≤ |α| + |W.im| := by linarith [abs_nonneg W.im]
      exact this.trans_lt (htotal'.trans_le hsmallN)
    have hdiff : |(rotation y).re - W.re| < 1 / 64 := by
      have hreEq : (rotation y - W).re = (rotation y).re - W.re := rfl
      rw [hreEq] at hrediff
      exact hrediff.trans_lt (hrotationDifference.trans_lt hαsmall)
    linarith [(abs_lt.mp hdiff).1]
  change |y| < 1 / N
  rw [← recover_parameter y]
  have hden : 0 < 1 + (rotation y).re := by linarith
  rw [abs_div, abs_of_pos hden]
  have hdivide : |(rotation y).im| / (1 + (rotation y).re) ≤
      |(rotation y).im| := by
    apply (div_le_iff₀ hden).2
    calc
      |(rotation y).im| = |(rotation y).im| * 1 := by ring
      _ ≤ |(rotation y).im| * (1 + (rotation y).re) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  exact hdivide.trans_lt (hrotationIm.trans (by
    apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * N) hN).2
    nlinarith only [hN]))

/-- Vary exactly one literal crossing parameter `X (.inr j)`. -/

private theorem real_two_column_surjective {a b : ℂ}
    (hdet : complexDet a b ≠ 0) :
    Function.Surjective (fun u : ℝ × ℝ => (u.1 : ℂ) * a + (u.2 : ℂ) * b) := by
  intro z
  let D := complexDet a b
  have hD : D ≠ 0 := by simpa only [D] using hdet
  refine ⟨((z.re * b.im - z.im * b.re) / D,
    (a.re * z.im - a.im * z.re) / D), ?_⟩
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, ofReal_re, ofReal_im,
      zero_mul, sub_zero]
    field_simp [hD]
    dsimp [D, complexDet]
    ring
  · simp only [Complex.add_im, Complex.mul_im, ofReal_re, ofReal_im,
      zero_mul, add_zero]
    field_simp [hD]
    dsimp [D, complexDet]
    ring

/-- On the literal selected window, two actual `y` columns of the rational
closure derivative span the whole complex closure space.  Together with
`closure_crossingLine_hasDerivAt`, this is the manuscript's concrete
rank-two witness. -/

theorem selectedWindow_closure_y_rank_two {m : ℕ} (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (Z : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s Z <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        RationalConfiguration.closure (by omega) (rationalSign s) Z = 0 →
        let j₀ : Fin m := ⟨0, by omega⟩
        let k : Fin m := transverseCrossingIndex m (by omega)
        complexDet (closureCrossingColumn (rationalSign s) Z j₀)
            (closureCrossingColumn (rationalSign s) Z k) ≠ 0 ∧
          Function.Surjective (fun u : ℝ × ℝ =>
            (u.1 : ℂ) * closureCrossingColumn (rationalSign s) Z j₀ +
              (u.2 : ℂ) * closureCrossingColumn (rationalSign s) Z k) := by
  have hsmall := selectedWindow_crossingParameter_small hN
  clear hN
  intro hm s Z hwindow hclosure
  dsimp only
  let j₀ : Fin m := ⟨0, by omega⟩
  let k : Fin m := transverseCrossingIndex m (by omega)
  have hy := hsmall hm s Z hwindow hclosure
  have hunit := transverse_crossingUnits_det_pos hm Z hy
  have hs₀ : rationalSign s j₀ ≠ 0 := by
    rcases FiniteBox.patternSign_is_sign s ⟨j₀.val, by omega⟩ with hs | hs
    · simp [rationalSign, j₀, hs]
    · simp [rationalSign, j₀, hs]
  have hsk : rationalSign s k ≠ 0 := by
    rcases FiniteBox.patternSign_is_sign s ⟨k.val, by omega⟩ with hs | hs
    · simp [rationalSign, k, hs]
    · simp [rationalSign, k, hs]
  have hc₀ : 4 * rationalSign s j₀ /
      (1 + RationalConfiguration.crossingParameter Z j₀ ^ 2) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (by norm_num) hs₀) (by positivity)
  have hck : 4 * rationalSign s k /
      (1 + RationalConfiguration.crossingParameter Z k ^ 2) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (by norm_num) hsk) (by positivity)
  have hdet : complexDet (closureCrossingColumn (rationalSign s) Z j₀)
      (closureCrossingColumn (rationalSign s) Z k) ≠ 0 := by
    simp only [closureCrossingColumn]
    simp only [mul_assoc]
    rw [complexDet_real_scale, complexDet_mul_I]
    exact mul_ne_zero (mul_ne_zero hc₀ hck) (by
      simpa only [j₀, k] using hunit.ne')
  exact ⟨hdet, real_two_column_surjective hdet⟩

theorem selectedWindow_closure_hasFDerivAt_surjective {m : ℕ} (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (Z : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s Z <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        RationalConfiguration.closure (by omega) (rationalSign s) Z = 0 →
        HasFDerivAt
            (RationalConfiguration.closure (by omega) (rationalSign s))
            (closureFDeriv (by omega) (rationalSign s) Z) Z ∧
          Function.Surjective (closureFDeriv (by omega) (rationalSign s) Z) := by
  have hrank := selectedWindow_closure_y_rank_two hN
  clear hN
  intro hm s Z hwindow hclosure
  have hspan := (hrank hm s Z hwindow hclosure).2
  refine ⟨closure_hasFDerivAt (by omega) (rationalSign s) Z, ?_⟩
  intro z
  rcases hspan z with ⟨u, hu⟩
  let j₀ : Fin m := ⟨0, by omega⟩
  let k : Fin m := transverseCrossingIndex m (by omega)
  refine ⟨u.1 • crossingDirection j₀ + u.2 • crossingDirection k, ?_⟩
  rw [map_add, map_smul, map_smul,
    closureFDeriv_crossingDirection (by omega) (rationalSign s) Z j₀,
    closureFDeriv_crossingDirection (by omega) (rationalSign s) Z k]
  simpa only [j₀, k, Complex.real_smul] using hu

theorem selectedWindow_closureMatrix_surjective {m : ℕ} (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) : ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega)) (X : Vars m → ℝ),
      selectedWindowEnergy (by omega) s X <
        (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
      RationalConfiguration.closure (by omega) (rationalSign s) X = 0 →
      Function.Surjective (closureMatrix (by omega) (halfWord s) X).mulVec := by
  have hfull := selectedWindow_closure_hasFDerivAt_surjective hN
  clear hN
  intro hm s X hwindow hclosure
  apply closureMatrix_surjective
  rw [sign_halfWord]
  exact (hfull hm s X hwindow hclosure).2

end
end StructuralNote.ExplicitRationalClosure

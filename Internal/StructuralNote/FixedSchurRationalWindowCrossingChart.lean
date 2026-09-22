import StructuralNote.FixedSchurRationalWindowAngleChart
import StructuralNote.FixedSchurRationalWindowRepresentation
import StructuralNote.FixedSchurChartSizes

/-! The actual rational crossing parameters on the Section 11 window, and
the two crossing-coordinate columns which make the closure map a submersion.
The variables treated here are the literal `X (.inr j)` coordinates. -/

namespace StructuralNote.FixedSchurRationalWindowCrossingChart

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
noncomputable section

private theorem crossingSmallCoefficient_tendsto :
    Tendsto (fun m : ℕ =>
      60 * (logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) /
        (2 * m : ℝ)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  convert ((logOrder_log_div_power_tendsto (p := 1) (by norm_num)).const_mul 60).comp hnat using 1
  · funext m
    simp only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat, Real.rpow_one]
    ring
  · norm_num

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
theorem eventual_selectedWindow_crossingParameter_small :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (Z : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s Z <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        RationalConfiguration.closure (by omega) (rationalSign s) Z = 0 →
        ∀ j : Fin m,
          |RationalConfiguration.crossingParameter Z j| < 1 / (2 * m : ℝ) := by
  have hcoefficient := crossingSmallCoefficient_tendsto.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  filter_upwards [hcoefficient, eventual_selectedWindow_representation,
    eventual_selectedWindow_inDomain, eventual_coordinate_properties]
      with m hcoefficient hrepresentation hdomain hproperties
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
      simp [α, theta, angle, RationalConfiguration.angleParameter]
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
def crossingCoordinateLine {m : ℕ}
    (Z : RationalConfiguration.Variables m → ℝ) (j : Fin m) (t : ℝ) :
    RationalConfiguration.Variables m → ℝ :=
  Function.update Z (.inr j) (Z (.inr j) + t)

@[simp] theorem crossingParameter_crossingCoordinateLine {m : ℕ}
    (Z : RationalConfiguration.Variables m → ℝ) (j : Fin m) (t : ℝ) :
    RationalConfiguration.crossingParameter (crossingCoordinateLine Z j t) j =
      RationalConfiguration.crossingParameter Z j + t := by
  simp [crossingCoordinateLine, RationalConfiguration.crossingParameter]

theorem crossingParameter_crossingCoordinateLine_ne {m : ℕ}
    (Z : RationalConfiguration.Variables m → ℝ) {j k : Fin m} (hjk : k ≠ j) (t : ℝ) :
    RationalConfiguration.crossingParameter (crossingCoordinateLine Z j t) k =
      RationalConfiguration.crossingParameter Z k := by
  simp [crossingCoordinateLine, RationalConfiguration.crossingParameter, hjk]

@[simp] theorem angleParameter_crossingCoordinateLine {m : ℕ}
    (Z : RationalConfiguration.Variables m → ℝ) (j k : Fin m) (t : ℝ) :
    RationalConfiguration.angleParameter (crossingCoordinateLine Z j t) k =
      RationalConfiguration.angleParameter Z k := by
  unfold RationalConfiguration.angleParameter
  split <;> simp [crossingCoordinateLine]

@[simp] theorem diameter_crossingCoordinateLine {m : ℕ} (hm : 0 < m)
    (Z : RationalConfiguration.Variables m → ℝ) (j : Fin m) (t : ℝ) (r : ℕ) :
    RationalConfiguration.diameter hm (crossingCoordinateLine Z j t) r =
      RationalConfiguration.diameter hm Z r := by
  simp [RationalConfiguration.diameter]

theorem crossingUnit_crossingCoordinateLine {m : ℕ}
    (Z : RationalConfiguration.Variables m → ℝ) (j : Fin m) (t : ℝ) :
    RationalConfiguration.crossingUnit (crossingCoordinateLine Z j t) j =
      unit (midpoint m j) *
        rotation (RationalConfiguration.crossingParameter Z j + t) := by
  simp [RationalConfiguration.crossingUnit]

theorem crossingUnit_crossingCoordinateLine_ne {m : ℕ}
    (Z : RationalConfiguration.Variables m → ℝ) {j k : Fin m} (hjk : k ≠ j) (t : ℝ) :
    RationalConfiguration.crossingUnit (crossingCoordinateLine Z j t) k =
      RationalConfiguration.crossingUnit Z k := by
  simp [RationalConfiguration.crossingUnit,
    crossingParameter_crossingCoordinateLine_ne Z hjk t]

/-- Exact change of the actual rational closure when one `y_j` coordinate is
varied. -/
theorem closure_crossingCoordinateLine {m : ℕ} (hm : 0 < m)
    (σ : Fin m → ℝ) (Z : RationalConfiguration.Variables m → ℝ)
    (j : Fin m) (t : ℝ) :
    RationalConfiguration.closure hm σ (crossingCoordinateLine Z j t) =
      RationalConfiguration.closure hm σ Z +
        ((2 * σ j : ℝ) : ℂ) *
          (unit (midpoint m j) *
              rotation (RationalConfiguration.crossingParameter Z j + t) -
            RationalConfiguration.crossingUnit Z j) := by
  have hterm (k : Fin m) :
      RationalConfiguration.increment hm σ (crossingCoordinateLine Z j t) k -
          RationalConfiguration.increment hm σ Z k =
        if k = j then
          ((2 * σ j : ℝ) : ℂ) *
            (unit (midpoint m j) *
                rotation (RationalConfiguration.crossingParameter Z j + t) -
              RationalConfiguration.crossingUnit Z j)
        else 0 := by
    by_cases hkj : k = j
    · subst k
      simp only [RationalConfiguration.increment,
        RationalChart.crossingIncrement, diameter_crossingCoordinateLine,
        crossingUnit_crossingCoordinateLine]
      push_cast
      ring
    · rw [if_neg hkj]
      simp only [RationalConfiguration.increment, RationalChart.crossingIncrement,
        diameter_crossingCoordinateLine,
        crossingUnit_crossingCoordinateLine_ne Z hkj t]
      ring
  have hsum :
      RationalConfiguration.closure hm σ (crossingCoordinateLine Z j t) -
          RationalConfiguration.closure hm σ Z =
        ((2 * σ j : ℝ) : ℂ) *
          (unit (midpoint m j) *
              rotation (RationalConfiguration.crossingParameter Z j + t) -
            RationalConfiguration.crossingUnit Z j) := by
    rw [RationalConfiguration.closure, RationalConfiguration.closure,
      ← Finset.sum_sub_distrib]
    simp_rw [hterm]
    simp
  linear_combination hsum

/-- The actual `y_j` column of the rational closure derivative. -/
def closureCrossingColumn {m : ℕ} (σ : Fin m → ℝ)
    (Z : RationalConfiguration.Variables m → ℝ) (j : Fin m) : ℂ :=
  ((4 * σ j / (1 + RationalConfiguration.crossingParameter Z j ^ 2) : ℝ) : ℂ) *
    RationalConfiguration.crossingUnit Z j * I

/-- The literal rational closure has the displayed directional derivative
along each actual `y_j` coordinate line. -/
theorem closure_crossingLine_hasDerivAt {m : ℕ} (hm : 0 < m)
    (σ : Fin m → ℝ) (Z : RationalConfiguration.Variables m → ℝ) (j : Fin m) :
    HasDerivAt
      (fun t : ℝ => RationalConfiguration.closure hm σ
        (crossingCoordinateLine Z j t))
      (closureCrossingColumn σ Z j) 0 := by
  let y := RationalConfiguration.crossingParameter Z j
  let u := unit (midpoint m j)
  have hrot := rotationLine_hasDerivAt y 1
  have hunit : HasDerivAt (fun t : ℝ => u * rotation (y + t))
      (u * (rotation y * (((2 / (1 + y ^ 2) : ℝ) : ℂ) * I))) 0 := by
    simpa only [one_mul, mul_one] using hrot.const_mul u
  have hformula :
      (fun t : ℝ => RationalConfiguration.closure hm σ
        (crossingCoordinateLine Z j t)) =
      (fun t : ℝ => RationalConfiguration.closure hm σ Z +
        ((2 * σ j : ℝ) : ℂ) *
          (u * rotation (y + t) - RationalConfiguration.crossingUnit Z j)) := by
    funext t
    simpa only [u, y] using closure_crossingCoordinateLine hm σ Z j t
  rw [hformula]
  have hd := ((hunit.sub_const (RationalConfiguration.crossingUnit Z j)).const_mul
    (((2 * σ j : ℝ) : ℂ))).const_add (RationalConfiguration.closure hm σ Z)
  apply hd.congr_deriv
  simp only [closureCrossingColumn, RationalConfiguration.crossingUnit, y, u]
  push_cast
  ring

/-- Oriented real area of two complex vectors. -/
def complexDet (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

theorem complexDet_unit (a b : ℝ) :
    complexDet (unit a) (unit b) = Real.sin (b - a) := by
  simp only [complexDet, unit_re, unit_im, Real.sin_sub]
  ring

theorem complexDet_mul_I (z w : ℂ) :
    complexDet (z * I) (w * I) = complexDet z w := by
  simp only [complexDet, Complex.mul_re, Complex.mul_im, I_re, I_im,
    mul_zero, mul_one]
  ring

theorem complexDet_real_scale (a b : ℝ) (z w : ℂ) :
    complexDet (((a : ℝ) : ℂ) * z) (((b : ℝ) : ℂ) * w) =
      a * b * complexDet z w := by
  simp only [complexDet, Complex.mul_re, Complex.mul_im, ofReal_re, ofReal_im,
    zero_mul, sub_zero, add_zero]
  ring

theorem crossingUnit_eq_unit_angle {m : ℕ}
    (Z : RationalConfiguration.Variables m → ℝ) (j : Fin m) :
    RationalConfiguration.crossingUnit Z j =
      unit (midpoint m j +
        2 * Real.arctan (RationalConfiguration.crossingParameter Z j)) := by
  rw [RationalConfiguration.crossingUnit, rotation_eq_unit_arctan, unit_add]

/-- An index whose reference crossing direction is roughly a quarter turn
from the zeroth crossing direction. -/
def transverseCrossingIndex (m : ℕ) (hm : 0 < m) : Fin m :=
  ⟨m / 2, by omega⟩

/-- The two literal crossing units at indices `0` and `floor(m/2)` are
nonparallel throughout the rational small window. -/
theorem transverse_crossingUnits_det_pos {m : ℕ} (hm : 8 ≤ m)
    (Z : RationalConfiguration.Variables m → ℝ)
    (hy : ∀ j : Fin m,
      |RationalConfiguration.crossingParameter Z j| < 1 / (2 * m : ℝ)) :
    0 < complexDet
      (RationalConfiguration.crossingUnit Z ⟨0, by omega⟩)
      (RationalConfiguration.crossingUnit Z (transverseCrossingIndex m (by omega))) := by
  let j₀ : Fin m := ⟨0, by omega⟩
  let k : Fin m := transverseCrossingIndex m (by omega)
  let y₀ := RationalConfiguration.crossingParameter Z j₀
  let yk := RationalConfiguration.crossingParameter Z k
  let d := midpoint m k - midpoint m j₀
  let e := 2 * Real.arctan yk - 2 * Real.arctan y₀
  let δ := d + e
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hkNatLow : m ≤ 3 * (m / 2) := by omega
  have hkNatHigh : 2 * (m / 2) ≤ m := by omega
  have hkLow : (1 / 3 : ℝ) ≤ (k : ℕ) / (m : ℝ) := by
    apply (le_div_iff₀ hmR).2
    have hkR : (m : ℝ) ≤ 3 * (k : ℕ) := by
      dsimp [k, transverseCrossingIndex]
      exact_mod_cast hkNatLow
    nlinarith
  have hkHigh : ((k : ℕ) : ℝ) / m ≤ 1 / 2 := by
    apply (div_le_iff₀ hmR).2
    have hkR : 2 * ((k : ℕ) : ℝ) ≤ m := by
      dsimp [k, transverseCrossingIndex]
      exact_mod_cast hkNatHigh
    nlinarith
  have hdEq : d = Real.pi * (((k : ℕ) : ℝ) / m) := by
    dsimp [d, LensClosure.midpoint, j₀]
    push_cast
    field_simp
    ring
  have hdLow : Real.pi / 3 ≤ d := by
    rw [hdEq]
    have h := mul_le_mul_of_nonneg_left hkLow Real.pi_pos.le
    nlinarith
  have hdHigh : d ≤ Real.pi / 2 := by
    rw [hdEq]
    have h := mul_le_mul_of_nonneg_left hkHigh Real.pi_pos.le
    nlinarith
  have hy₀ := hy j₀
  have hyk := hy k
  have hat₀ := abs_arctan_le y₀
  have hatk := abs_arctan_le yk
  have heBound : |e| < 1 / 4 := by
    have hsub := abs_sub_le (2 * Real.arctan yk) 0 (2 * Real.arctan y₀)
    simp only [sub_zero, zero_sub, abs_neg, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsub
    have hmain : |e| < 4 * (1 / (2 * m : ℝ)) := by
      dsimp [e]
      calc
        _ ≤ 2 * |Real.arctan yk| + 2 * |Real.arctan y₀| := hsub
        _ ≤ 2 * |yk| + 2 * |y₀| :=
          add_le_add (mul_le_mul_of_nonneg_left hatk (by norm_num))
            (mul_le_mul_of_nonneg_left hat₀ (by norm_num))
        _ < 2 * (1 / (2 * m : ℝ)) + 2 * (1 / (2 * m : ℝ)) := by
          exact add_lt_add (mul_lt_mul_of_pos_left hyk (by norm_num))
            (mul_lt_mul_of_pos_left hy₀ (by norm_num))
        _ = _ := by ring
    have hmR8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
    exact hmain.trans_le (by
      rw [show 4 * (1 / (2 * m : ℝ)) = 4 / (2 * m : ℝ) by ring]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m)).2
      nlinarith)
  have hδpos : 0 < δ := by
    have helow := (abs_lt.mp heBound).1
    dsimp [δ]
    nlinarith [hdLow, Real.pi_gt_three]
  have hδpi : δ < Real.pi := by
    have hehigh := (abs_lt.mp heBound).2
    dsimp [δ]
    nlinarith [hdHigh, Real.pi_gt_three]
  rw [crossingUnit_eq_unit_angle, crossingUnit_eq_unit_angle, complexDet_unit]
  have hphase :
      (midpoint m k + 2 * Real.arctan yk) -
          (midpoint m j₀ + 2 * Real.arctan y₀) = δ := by
    dsimp [δ, d, e]
    ring
  rw [hphase]
  exact Real.sin_pos_of_pos_of_lt_pi hδpos hδpi

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
theorem eventual_selectedWindow_closure_y_rank_two :
    ∀ᶠ m : ℕ in atTop,
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
  filter_upwards [eventual_selectedWindow_crossingParameter_small] with m hsmall
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

end
end StructuralNote.FixedSchurRationalWindowCrossingChart

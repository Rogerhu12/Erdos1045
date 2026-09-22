import StructuralNote.ExplicitComparisonStability
import StructuralNote.ExplicitComparisonRotated
import StructuralNote.FixedSchurSecondSourceTools

/-! Explicit bounds for the linearized fixed-Schur equation and its first source. -/
namespace StructuralNote.ExplicitFixedSchurCoefficients
open Erdos1045.EventualExact FiniteBox SchurLiftBounds Complex SchurSpectrum
open CommonDomainClosure CommonDomainRadius CommonClosureEnergy CommonTangentialParameters
open FixedSchurData FixedSchurChart FixedSchurChartSizes FixedSchurDomainBounds
open FixedSchurNormalExpansion FixedSchurRotatedPath FixedSchurRotatedStability
open FixedSchurRotatedInverse HessianErrorLimits FixedSchurRotatedCoefficients
open FixedSchurFirstSource FixedSchurFirstSourceMoments FixedSchurFirstDerivativeBounds
open FixedSchurFirstSourceSup FixedSchurDirectionMoments CommonFiberBounds
open FixedSchurChartRadial CommonFiberNormalProjectionScaled EdgeCoordinates
open FixedSchurSecondSourceTools FixedSchurRadialAlgebra FixedSchurLinear
open scoped BigOperators Topology
noncomputable section

theorem logOrder_div_small {n : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ n) :
    144 * (CommonDomainRadius.logOrder n : ℝ) / n < 1 / 40 := by
  have h := ExplicitHessianThreshold.log_monomial_div_small (j := 1) (c := 288)
    hN (by norm_num) (by norm_num)
  have hb := ExplicitHessianThreshold.logOrder_bound hN
  have hh : 144 * (CommonDomainRadius.logOrder n : ℝ) / n ≤
      288 * Erdos1045.ExplicitThreshold.logBudget n / n := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    linarith only [hb]
  simp only [pow_one] at h
  linarith only [hh, h]

theorem actual_coefficients_small {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      ∀ j, |alpha (epsilon (2 * m)) (patternSign s j) (angleAverage (by omega) θ j)
        (rotatedS (by omega) θ v (coordinate (by omega) s θ v) j) - 1| ≤ (1 / 10 : ℝ) ∧
      |beta (epsilon (2 * m)) (patternSign s j) (angleAverage (by omega) θ j)
        (rotatedS (by omega) θ v (coordinate (by omega) s θ v) j)| ≤ (1 / 10 : ℝ) ∧
      1 ≤ H (epsilon (2 * m)) (rotatedS (by omega) θ v (coordinate (by omega) s θ v) j) := by
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties hN
  have havg := ExplicitComparisonStability.angleAverage_inv hN
  have hsmall := logOrder_div_small hN
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hsmall
  have hm20 : 20 ≤ m := by have := ExplicitHessianThreshold.two_fifty_six_le_order hN; omega
  clear hN
  intro hm s θ v hdom j
  have hn : (40 : ℝ) ≤ 2 * m := by exact_mod_cast (show 40 ≤ 2 * m by omega)
  have hnpos : (0 : ℝ) < 2 * m := by linarith
  have hb : |angleAverage (by omega) θ j| ≤ (1 / 40 : ℝ) := by
    apply (havg (by omega) θ v hdom j).trans
    exact (div_le_iff₀ hnpos).2 (by linarith)
  have hq := (hprops hm s θ v hdom).norm_le
  have hS := rotatedS_abs_le_log (by omega) θ v hdom _ hq j
  have heps := epsilon_le (show 2 ≤ 2 * m by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at heps
  have hy : |epsilon (2 * m) * rotatedS (by omega) θ v (coordinate (by omega) s θ v) j| ≤
      (1 / 40 : ℝ) := by
    rw [abs_mul, abs_of_pos (epsilon_pos (show 2 ≤ 2 * m by omega))]
    calc
      _ ≤ (8 / (2 * m : ℝ) ^ 2) * (18 * (logOrder (2 * m) : ℝ)) :=
        mul_le_mul heps hS (abs_nonneg _) (by positivity)
      _ = 144 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by ring
      _ ≤ 144 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
        apply div_le_div_of_nonneg_left (by positivity) hnpos
        nlinarith only [hn]
      _ ≤ 1 / 40 := hsmall.le
  exact scalar_coefficients_small (patternSign_is_sign s j) hb hy

theorem actual_solution_bounds {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      ∀ q : Fin (2 * m) → ℝ,
      (∑ j, |q j|) / (2 * m : ℝ) ≤
        2 * ((∑ j, |normalLinearization (by omega) s θ v q j|) / (2 * m : ℝ)) ∧
      Real.sqrt (meanSquare q) ≤
        2 * Real.sqrt (meanSquare (normalLinearization (by omega) s θ v q)) ∧
      ‖q‖ ≤ 2 * ‖normalLinearization (by omega) s θ v q‖ := by
  have hsmall := actual_coefficients_small hN
  clear hN
  intro hm s θ v hdom q
  have ha (j : Fin (2 * m)) : |coefficientA (by omega) s θ v j - 1| ≤ (1 / 10 : ℝ) :=
    (hsmall hm s θ v hdom j).1
  have hb (j : Fin (2 * m)) : |coefficientB (by omega) s θ v j| ≤ (1 / 10 : ℝ) :=
    (hsmall hm s θ v hdom j).2.1
  refine ⟨?_, solution_l2_bound (by omega) _ _ q ha hb,
    solution_sup_bound (by omega) _ _ q ha hb⟩
  simpa only [normalLinearization, Nat.cast_mul, Nat.cast_ofNat] using
    solution_l1_bound (by omega) _ _ q ha hb

theorem source_coefficients {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      ∀ j, |angularCoefficient (by omega) s θ j| ≤ 2 * (2 * m : ℝ) ∧
      |coefficientB (by omega) s θ v j| ≤ betaBudget (2 * m) / (2 * m : ℝ) ^ 2 ∧
      |rotationCoefficient (by omega) s θ v j| ≤ 36 * (logOrder (2 * m) : ℝ) := by
  have hcoeff := actual_coefficients_small hN
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties hN
  have hb := logOrder_div_small hN
  have hpos := ExplicitHessianThreshold.order_pos hN
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hb hpos
  have hsmall : 5 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) < 1 := by
    have hl : 0 ≤ (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by positivity
    rw [mul_div_assoc] at hb ⊢
    linarith only [hb, hl]
  clear hb hpos
  clear hN
  intro hm s θ v hdom j
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hL : 5 * (logOrder (2 * m) : ℝ) ≤ 2 * m :=
    (by simpa only [one_mul] using ((div_lt_iff₀ hn).mp hsmall).le)
  have hH := (hcoeff hm s θ v hdom j).2.2
  have hq := (hprops hm s θ v hdom).norm_le
  have hS := rotatedS_abs_le_log (by omega) θ v hdom _ hq j
  have hangle : |Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2| ≤
      5 / (2 * m : ℝ) := by
    have hd := domain_angle_difference (by omega) θ v hdom j
    have hp : Real.pi / (2 * m : ℝ) ≤ 4 / (2 * m : ℝ) :=
      div_le_div_of_nonneg_right Real.pi_lt_four.le hn.le
    have hLi : 5 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 ≤ 1 / (2 * m : ℝ) := by
      calc
        _ ≤ (2 * m : ℝ) / (2 * m : ℝ) ^ 2 := div_le_div_of_nonneg_right hL (sq_nonneg _)
        _ = _ := by field_simp
    have ha := abs_add_le (Real.pi / (2 * m : ℝ)) (angleDifference (by omega) θ j / 2)
    rw [abs_of_pos (by positivity : 0 < Real.pi / (2 * m : ℝ)),
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ha
    have hd' : |angleDifference (by omega) θ j| / 2 ≤ 1 / (2 * m : ℝ) := by
      calc
        _ ≤ (10 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2) / 2 :=
          div_le_div_of_nonneg_right hd (by norm_num)
        _ = 5 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by ring
        _ ≤ _ := hLi
    exact (ha.trans (add_le_add hp hd')).trans_eq (by ring)
  have hε := epsilon_pos (show 2 ≤ 2 * m by omega)
  have hκ := (scale_bounds (show 2 ≤ 2 * m by omega)).2
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hκ
  have hsign : |patternSign s j| = 1 := by
    rcases patternSign_is_sign s j with h | h <;> rw [h] <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · unfold angularCoefficient
    rw [abs_mul, abs_div, hsign, abs_of_pos hε, one_div, epsilon_inv (show 2 ≤ 2 * m by omega)]
    calc
      _ ≤ ((2 * m : ℝ) ^ 2 / 4) * (5 / (2 * m : ℝ)) :=
        mul_le_mul hκ (Real.abs_sin_le_abs.trans hangle) (abs_nonneg _) (by positivity)
      _ ≤ 2 * (2 * m : ℝ) := by field_simp; nlinarith
  · have hb := beta_abs_le (b := angleAverage (by omega) θ j) (patternSign_is_sign s j) hH
    have hθ := domain_angleAverage_bound_all (by omega) θ v hdom j
    have hep := epsilon_le (show 2 ≤ 2 * m by omega)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hep
    have hy : |epsilon (2 * m) * rotatedS (by omega) θ v (coordinate (by omega) s θ v) j| ≤
        144 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by
      rw [abs_mul, abs_of_pos hε]
      exact (mul_le_mul hep hS (abs_nonneg _) (by positivity)).trans_eq (by ring)
    exact (hb.trans (add_le_add hθ hy)).trans_eq (by
      unfold betaBudget
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      ring)
  · have hHpos : 0 < H (epsilon (2 * m))
        (rotatedS (by omega) θ v (coordinate (by omega) s θ v) j) := by linarith
    have hlen : |L (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2)| ≤ 2 := by
      unfold L
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith only [Real.abs_cos_le_one (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2)]
    unfold rotationCoefficient
    rw [abs_mul, abs_div, abs_of_pos hHpos]
    have hr : |L (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2)| /
        H (epsilon (2 * m)) (rotatedS (by omega) θ v (coordinate (by omega) s θ v) j) ≤ 2 :=
      (div_le_iff₀ hHpos).2 (by linarith only [hlen, hH])
    exact (mul_le_mul hr hS (abs_nonneg _) (by norm_num)).trans_eq (by ring)

theorem radialCoefficient_bound {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      ∀ j, |radialCoefficient (by omega) s θ v j| ≤ (5 / 2 : ℝ) := by
  have hrad := ExplicitComparisonRotated.coordinate_radial hN
  clear hN
  intro hm s θ v hdom j
  have hd := hrad hm s θ v hdom j
  rw [center_difference hm _ _ hdom.2.2.1.2.2, radial_edgeIncrement] at hd
  change |epsilon (2 * m) * radialCoefficient (by omega) s θ v j| ≤
    10 / (2 * m : ℝ) ^ 2 at hd
  have hε := epsilon_pos (show 2 ≤ 2 * m by omega)
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  rw [abs_mul, abs_of_pos hε] at hd
  have hscale := (scale_bounds (show 2 ≤ 2 * m by omega)).2
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hscale
  calc
    _ = (epsilon (2 * m))⁻¹ * (epsilon (2 * m) * |radialCoefficient (by omega) s θ v j|) := by
      field_simp
    _ ≤ (epsilon (2 * m))⁻¹ * (10 / (2 * m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hε.le)
    _ = scale (2 * m) * (10 / (2 * m : ℝ) ^ 2) := by rw [epsilon_inv (show 2 ≤ 2 * m by omega)]
    _ ≤ ((2 * m : ℝ) ^ 2 / 4) * (10 / (2 * m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hscale (by positivity)
    _ = 5 / 2 := by field_simp; ring

theorem source_meanSquare {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      (∑ j, (η j : ℂ) = 0) →
      meanSquare (source (by omega) s θ η v h) ≤
        20000 * pairEnergy (by omega) (fun j => (η j : ℂ)) / (2 * m : ℝ) +
        24 * betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 3 := by
  have hcoeff := source_coefficients hN
  have hrad := ExplicitHessianThreshold.energyRadius_le_inverse hN
  clear hN
  intro hm s θ η v h hdom hmean
  have hsource := source_meanSquare_of_coefficients (by omega) s θ η v h hmean
    (hcoeff hm s θ v hdom)
  have hE := pairEnergy_nonneg (show 0 < 2 * m by omega) (fun j => (η j : ℂ))
  have hA := pairEnergy_nonneg (show 0 < 2 * m by omega) h
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hfirst := mul_le_mul_of_nonneg_right hpi
    (show 0 ≤ pairEnergy (by omega) (fun j => (η j : ℂ)) / (2 * m : ℝ) by positivity)
  have hsecond := mul_le_mul_of_nonneg_right hpi
    (show 0 ≤ betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 3 by positivity)
  have hthird := mul_le_mul_of_nonneg_right hrad hE
  simp only [energyRadius, Nat.cast_mul, Nat.cast_ofNat] at hthird
  have hnonneg := div_nonneg hE hn.le
  ring_nf at hsource hfirst hsecond hthird hnonneg ⊢
  linarith only [hsource, hfirst, hsecond, hthird, hnonneg]

theorem first_solution_meanSquare {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      (∑ j, (η j : ℂ) = 0) → ∀ q : Fin (2 * m) → ℝ,
      normalLinearization (by omega) s θ v q = source (by omega) s θ η v h →
      meanSquare q ≤
        80000 * pairEnergy (by omega) (fun j => (η j : ℂ)) / (2 * m : ℝ) +
        96 * betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 3 := by
  have hsource := source_meanSquare hN
  have hcoeff := actual_coefficients_small hN
  clear hN
  intro hm s θ η v h hdom hmean q hq
  have hc := hcoeff hm s θ v hdom
  have hnorm := solution_meanSquare_bound (show 0 < 2 * m by omega)
    (coefficientA (by omega) s θ v) (coefficientB (by omega) s θ v) q
    (fun j => (hc j).1) (fun j => (hc j).2.1)
  change meanSquare q ≤ 4 * meanSquare (normalLinearization (by omega) s θ v q) at hnorm
  rw [hq] at hnorm
  exact (hnorm.trans (mul_le_mul_of_nonneg_left
    (hsource hm s θ η v h hdom hmean) (by norm_num))).trans_eq (by ring)

theorem first_solution_l2 {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      (∑ j, (η j : ℂ) = 0) → ∀ q : Fin (2 * m) → ℝ,
      normalLinearization (by omega) s θ v q = source (by omega) s θ η v h →
      Real.sqrt (meanSquare q) ≤ 2000 *
        (Real.sqrt (pairEnergy (by omega) (fun j => (η j : ℂ))) / Real.sqrt (2 * m : ℝ) +
          (logOrder (2 * m) : ℝ) * Real.sqrt (1 + Real.log (2 * m : ℝ)) *
            Real.sqrt (pairEnergy (by omega) h) / ((2 * m : ℝ) * Real.sqrt (2 * m : ℝ))) := by
  have hbound := first_solution_meanSquare hN
  clear hN
  intro hm s θ η v h hdom hmean q hq
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hE := pairEnergy_nonneg (show 0 < 2 * m by omega) (fun j => (η j : ℂ))
  have hA := pairEnergy_nonneg (show 0 < 2 * m by omega) h
  have hbase := sqrt_rate_bound hn (betaBudget_nonneg (2 * m)) hE hA
    (hbound hm s θ η v h hdom hmean q hq)
  have hb := betaBudget_le (show 1 ≤ 2 * m by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hb
  have hbr := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg (pairEnergy (by omega) h)))
    (show 0 ≤ (2 * m : ℝ) * Real.sqrt (2 * m : ℝ) by positivity)
  have hx : 0 ≤ Real.sqrt (pairEnergy (by omega) (fun j => (η j : ℂ))) /
      Real.sqrt (2 * m : ℝ) := by positivity
  have hy : 0 ≤ (logOrder (2 * m) : ℝ) * Real.sqrt (1 + Real.log (2 * m : ℝ)) *
      Real.sqrt (pairEnergy (by omega) h) / ((2 * m : ℝ) * Real.sqrt (2 * m : ℝ)) := by positivity
  ring_nf at hbase hbr hx hy ⊢
  linarith only [hbase, hbr, hx, hy]

theorem source_pointwise_sq {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      (∑ j, (η j : ℂ) = 0) → ∀ j,
      source (by omega) s θ η v h j ^ 2 ≤
        50000 * pairEnergy (by omega) (fun j => (η j : ℂ)) +
        24 * betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 2 := by
  have hcoeff := source_coefficients hN
  have hrad := ExplicitHessianThreshold.energyRadius_le_inverse hN
  clear hN
  intro hm s θ η v h hdom hmean j
  have hs := source_pointwise_sq_of_coefficients (by omega) s θ η v h hmean j (hcoeff hm s θ v hdom j)
  have hE := pairEnergy_nonneg (show 0 < 2 * m by omega) (fun j => (η j : ℂ))
  have hA := pairEnergy_nonneg (show 0 < 2 * m by omega) h
  have hn : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hnpos : (0 : ℝ) < 2 * m := by linarith
  have hlog : 0 ≤ Real.log (2 * m : ℝ) := Real.log_nonneg hn
  have hlogle : Real.log (2 * m : ℝ) / (2 * m : ℝ) ≤ 1 :=
    (div_le_iff₀ hnpos).2 (by linarith [Real.log_le_sub_one_of_pos hnpos])
  have hLlog := mul_le_mul_of_nonneg_right hrad hlog
  simp only [energyRadius, Nat.cast_mul, Nat.cast_ofNat] at hLlog
  have hratio : (logOrder (2 * m) : ℝ) ^ 2 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 ≤ 1 := by
    ring_nf at hLlog hlogle ⊢
    linarith only [hLlog, hlogle]
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hfirst := mul_le_mul_of_nonneg_right hpi hE
  have hsecond := mul_le_mul_of_nonneg_right hpi
    (show 0 ≤ betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 2 by positivity)
  have hthird := mul_le_mul_of_nonneg_right hratio hE
  ring_nf at hs hfirst hsecond hthird ⊢
  linarith only [hs, hfirst, hsecond, hthird, hE]

theorem first_solution_sup_sq {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      (∑ j, (η j : ℂ) = 0) → ∀ q : Fin (2 * m) → ℝ,
      normalLinearization (by omega) s θ v q = source (by omega) s θ η v h →
      ‖q‖ ^ 2 ≤
        200000 * pairEnergy (by omega) (fun j => (η j : ℂ)) +
        96 * betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 2 := by
  have hsource := source_pointwise_sq hN
  have hinv := actual_solution_bounds hN
  clear hN
  intro hm s θ η v h hdom hmean q heq
  have hE := pairEnergy_nonneg (show 0 < 2 * m by omega) (fun j => (η j : ℂ))
  have hA := pairEnergy_nonneg (show 0 < 2 * m by omega) h
  have hS := norm_sq_le_of_pointwise (source (by omega) s θ η v h) (by positivity)
    (hsource hm s θ η v h hdom hmean)
  have hnorm := (hinv hm s θ v hdom q).2.2
  rw [heq] at hnorm
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  ring_nf at hsq hS ⊢
  linarith only [hsq, hS]

theorem betaBudget_le_order {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    betaBudget (2 * m) ≤ (2 * m : ℝ) := by
  have hb := ExplicitHessianThreshold.logOrder_bound hN
  have hH := Erdos1045.ExplicitThreshold.logBudget_ge_one hN
  have hs := ExplicitHessianThreshold.log_monomial_div_small (j := 2) (c := 296)
    hN (by norm_num) (by norm_num)
  have hn := ExplicitHessianThreshold.order_pos hN
  have hn1 : 1 ≤ 2 * m := by have := ExplicitHessianThreshold.two_fifty_six_le_order hN; omega
  clear hN
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hb hH hs hn
  have hroot : Real.sqrt (Erdos1045.ExplicitThreshold.logBudget (2 * m)) ≤
      Erdos1045.ExplicitThreshold.logBudget (2 * m) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith only [hH]
    · nlinarith only [hH]
  have hbeta := betaBudget_le hn1
  have hnum : 296 * Erdos1045.ExplicitThreshold.logBudget (2 * m) ^ 2 ≤ (2 * m : ℕ) :=
    by simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      ((div_lt_one hn).mp (hs.trans (by norm_num))).le
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hbeta
  change betaBudget (2 * m) ≤ 148 * (logOrder (2 * m) : ℝ) *
    Real.sqrt (Erdos1045.ExplicitThreshold.logBudget (2 * m)) at hbeta
  have hprod := mul_le_mul hb hroot (Real.sqrt_nonneg _) (by linarith only [hH] :
    0 ≤ 2 * Erdos1045.ExplicitThreshold.logBudget (2 * m))
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hnum
  nlinarith only [hprod, hbeta, hnum]

theorem first_solution_coarse {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      (∑ j, (η j : ℂ) = 0) → ∀ q : Fin (2 * m) → ℝ,
      normalLinearization (by omega) s θ v q = source (by omega) s θ η v h →
      meanSquare q ≤ 80000 *
        (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) / (2 * m : ℝ) ∧
      ‖q‖ ^ 2 ≤ 200000 *
        (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) := by
  have hbeta := betaBudget_le_order hN
  have hms := first_solution_meanSquare hN
  have hsup := first_solution_sup_sq hN
  clear hN
  intro hm s θ η v h hdom hmean q heq
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hA := pairEnergy_nonneg (show 0 < 2 * m by omega) h
  have hE := pairEnergy_nonneg (show 0 < 2 * m by omega) (fun j => (η j : ℂ))
  have hb2 := pow_le_pow_left₀ (betaBudget_nonneg (2 * m)) hbeta 2
  have hmul := mul_le_mul_of_nonneg_right hb2 hA
  have h₁ : betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 3 ≤
      pairEnergy (by omega) h / (2 * m : ℝ) := by
    exact (div_le_div_of_nonneg_right hmul (by positivity)).trans_eq (by field_simp)
  have h₂ : betaBudget (2 * m) ^ 2 * pairEnergy (by omega) h / (2 * m : ℝ) ^ 2 ≤
      pairEnergy (by omega) h := by
    exact (div_le_div_of_nonneg_right hmul (sq_nonneg _)).trans_eq (by field_simp)
  have hfirst := hms hm s θ η v h hdom hmean q heq
  have hsecond := hsup hm s θ η v h hdom hmean q heq
  have hAdiv := div_nonneg hA hn.le
  constructor
  · ring_nf at hfirst h₁ hAdiv ⊢
    linarith only [hfirst, h₁, hAdiv]
  · ring_nf at hsecond h₂ ⊢
    linarith only [hsecond, h₂, hA]

end
end StructuralNote.ExplicitFixedSchurCoefficients

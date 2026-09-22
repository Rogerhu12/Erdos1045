import StructuralNote.ThirdSchwarzBoundary
import StructuralNote.ThirdSchwarzJet
import StructuralNote.FixedDualClassificationThirdFineBound

/-! The actual cubic first/third Fourier defect, and the sharp third-moment threshold. -/

namespace StructuralNote.ThirdSchwarzDefect

open Real Complex Set Metric MeasureTheory AddCircle FormalMultilinearSeries
open ThirdSchwarzBoundary ThirdSchwarzJet
open FixedDualClassificationHerglotz FixedDualClassificationHerglotzSeries
open FixedDualClassificationTanStrip FixedDualClassificationCircleShift
open FixedDualClassificationStep FixedDualClassificationPeriodicStep
open FixedDualClassificationCoefficientBound FixedDualClassificationThirdArithmetic
open FixedDualClassificationThirdFineBound FixedDualClassificationThirdCoarse
open FixedDualClassificationMultiplierLimit FixedDualClassificationStepEnergy
open Erdos1045.EventualExact Erdos1045.EventualExact.FiniteBox
noncomputable section

local instance period_pos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem analyticHalf_iteratedDeriv_coefficient {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1)
    (hmean : circleAverage f 0 1 = 0) (k : ℕ) :
    iteratedDeriv k (analyticHalf f) 0 / k.factorial =
      circleAverage (fun ζ => (f ζ : ℂ) / ζ ^ k) 0 1 := by
  have ha := analyticHalf_analytic hf 0 (by simp)
  have he := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff k)
    (ha.hasFPowerSeriesAt.eq_formalMultilinearSeries (analyticHalf_hasFPowerSeries hf hmean))
  simpa only [coeff_ofScalars, cauchy_coefficient] using he

theorem circle_coupling {F : Torus → ℝ} (hF : Measurable F)
    (hb : ∀ x, |F x| ≤ Real.pi / 2)
    (hanti : ∀ x, F (x + (Real.pi : ℝ)) = -F x) :
    let c := fourierCoeff (fun x => (F x : ℂ))
    ‖c 3 + c 1 ^ 3 / 3‖ ≤ 1 - ‖c 1‖ ^ 2 := by
  dsimp only
  have hi := boundary_integrable hF hb
  have hm := boundary_mean_zero hF hb hanti
  have hbox (ζ : ℂ) (_ : ζ ∈ sphere 0 1) : |boundary F ζ| ≤ Real.pi / 2 := hb _
  have hc (k : ℕ) := (analyticHalf_iteratedDeriv_coefficient hi hm k).trans (boundary_coefficient F k)
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  norm_num only [Nat.factorial, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat,
    mul_one, iteratedDeriv_one, div_one] at h1 h2 h3
  have hz2 := even_fourier_zero hanti 1
  norm_num only [Nat.cast_one, mul_one] at hz2
  have hsecond : iteratedDeriv 2 (analyticHalf (boundary F)) 0 = 0 := by
    rw [hz2] at h2
    exact (div_eq_zero_iff.mp h2).resolve_right (by norm_num)
  have hd : DifferentiableOn ℂ (Complex.tan ∘ analyticHalf (boundary F)) (ball 0 1) :=
    diskMap_differentiable hi hbox
  have hb' (z : ℂ) (hz : z ∈ ball 0 1) : ‖Complex.tan (analyticHalf (boundary F) z)‖ ≤ 1 := by
    exact mem_closedBall_zero_iff.mp (diskMap_mapsTo hi hbox hz)
  have h := tangent_third_coefficient_bound (analyticHalf_analytic hi 0 (by simp))
    (analyticHalf_zero hi hm) hsecond hd hb'
  rw [h1, h3] at h
  exact h

theorem circle_defect {F : Torus → ℝ} (hF : Measurable F)
    (hb : ∀ x, |F x| ≤ Real.pi / 2)
    (hanti : ∀ x, F (x + (Real.pi : ℝ)) = -F x) :
    let c := fourierCoeff (fun x => (F x : ℂ))
    ‖c 1‖ ^ 2 - ‖c 1‖ ^ 3 / 3 ≤ 1 - ‖c 3‖ := by
  let c := fourierCoeff (fun x => (F x : ℂ))
  have h := circle_coupling hF hb hanti
  change ‖c 3 + c 1 ^ 3 / 3‖ ≤ 1 - ‖c 1‖ ^ 2 at h
  have ht := norm_sub_le (c 3 + c 1 ^ 3 / 3) (c 1 ^ 3 / 3)
  rw [add_sub_cancel_right, norm_div, norm_pow] at ht
  norm_num only [Complex.norm_ofNat] at ht
  change ‖c 1‖ ^ 2 - ‖c 1‖ ^ 3 / 3 ≤ 1 - ‖c 3‖
  linarith

theorem normalized_cubic_defect {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ Q hm) :
    let c := profileCoefficient (stepProfile q (profileScale (2 * m)))
    cubicDefect ‖c 1‖ ≤ 1 - ‖c 3‖ := by
  have hA := amplitude_pos (n := 2 * m) (by omega)
  have hbox (x : Torus) : |circleProfile q (profileScale (2 * m)) x| ≤ Real.pi / 2 := by
    have h := circleProfile_bound q (profileScale (2 * m)) (amplitude (2 * m)) hA.le hq.2 x
    have hs : 0 < profileScale (2 * m) := by unfold profileScale; positivity
    rw [abs_of_pos hs, profileScale,
      div_mul_cancel₀ _ hA.ne'] at h
    exact h
  have h := circle_defect (circleProfile_measurable q (profileScale (2 * m))) hbox
    (circleProfile_antiperiodic hm q hq.1 _)
  dsimp only at h ⊢
  have he (p : ℤ) : fourierCoeff (fun x => (circleProfile q (profileScale (2 * m)) x : ℂ)) p =
      profileCoefficient (stepProfile q (profileScale (2 * m))) p := by
    rw [circleProfile_fourierCoeff (by omega), profileCoefficient_eq (by omega)]
  simpa only [he, cubicDefect] using h

theorem normalized_third_sharp {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ Q hm) (hV : (531 : ℝ) / 2000 < continuousEnergy q (profileScale (2 * m))) :
    (24 : ℝ) / 25 < ‖profileCoefficient (stepProfile q (profileScale (2 * m))) 3‖ := by
  let c := profileCoefficient (stepProfile q (profileScale (2 * m)))
  have hc := normalized_third_coarse hm q hq hV
  have hfine := normalized_fine_bound hm q hq
  have hdef := normalized_cubic_defect hm q hq
  have hb := normalized_coefficient_le_one hm q hq (by norm_num : 0 < (1 : ℕ))
  have hr := normalized_coefficient_le_one hm q hq (by norm_num : 0 < (3 : ℕ))
  change (21 : ℝ) / 25 < ‖c 3‖ at hc
  change continuousEnergy q (profileScale (2 * m)) ≤
    upperEnergy (Real.pi ^ 2 / 8) (1 - ‖c 3‖) ‖c 1‖ at hfine
  change cubicDefect ‖c 1‖ ≤ 1 - ‖c 3‖ at hdef
  change ‖c 1‖ ≤ 1 at hb
  change ‖c 3‖ ≤ 1 at hr
  change (24 : ℝ) / 25 < ‖c 3‖
  by_contra! h
  have hpi : Real.pi ^ 2 / 8 ≤ 121 / 98 := by nlinarith [pi_lt_d4, pi_pos]
  have hs := fine_test_from_cubic hpi
    (show 1 - ‖c 3‖ ∈ Icc (1 / 25) (4 / 25) from ⟨by linarith, by linarith⟩)
    (show ‖c 1‖ ∈ Icc 0 1 from ⟨norm_nonneg _, hb⟩) hdef
  linarith

end
end StructuralNote.ThirdSchwarzDefect

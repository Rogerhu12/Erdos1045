import Erdos1045.ExteriorGenerating
import Erdos1045.ClosedLaurent
import Mathlib.Analysis.SpecificLimits.Normed

namespace Erdos1045.ExteriorClassical

open scoped BigOperators
open ExteriorBoundary FaberFourier
noncomputable section

theorem character_eq_unit_inv_pow (m : ℕ) (t : ℝ) :
    character m t = (unit t)⁻¹ ^ m := by
  unfold character unit
  rw [← Complex.exp_neg, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem geometric_summable_proved (r : ℝ) (hr : 1 < r) (θ : ℝ) :
    Summable (fun k => ‖((1 / r : ℝ) : ℂ) ^ k * unit θ ^ k‖) := by
  have hr0 : 0 < r := by linarith
  have hq : |(1 / r : ℝ)| < 1 := by
    rw [abs_of_pos (by positivity)]
    exact (div_lt_one hr0).2 hr
  simpa [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    using (hasSum_geometric_of_norm_lt_one (ξ := (1 / r : ℝ)) (by simpa using hq)).summable

theorem geometric_identity_proved (r : ℝ) (hr : 1 < r) (θ t : ℝ) :
    series (fun k => ((1 / r : ℝ) : ℂ) ^ k * unit θ ^ k) t =
      ((r : ℂ) * unit t) / ((r : ℂ) * unit t - unit θ) := by
  have hr0 : 0 < r := by linarith
  let q : ℂ := ((1 / r : ℝ) : ℂ) * unit θ * (unit t)⁻¹
  have hq : ‖q‖ < 1 := by
    dsimp [q]
    simp only [norm_mul, norm_inv, norm_unit, inv_one, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / r)]
    exact (div_lt_one hr0).2 hr
  have ht : unit t ≠ 0 := by
    intro h
    have hnorm := norm_unit t
    rw [h, norm_zero] at hnorm
    norm_num at hnorm
  have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
  have hden := radial_difference_ne_zero hr θ t
  unfold series
  simp_rw [character_eq_unit_inv_pow, ← mul_pow]
  change (∑' k, q ^ k) = _
  rw [tsum_geometric_of_norm_lt_one hq]
  dsimp [q]
  push_cast
  field_simp

theorem derivative_summable_proved (a : ℕ → ℂ) (ha : SobolevCoefficients a)
    (c : ℝ) (hc : 0 < c) (r : ℝ) (hr : 1 < r) (θ : ℝ) :
    Summable (fun k => ‖radialCoefficients (1 / r)
      (firstOrder (coefficient c a (fun _ : Fin 1 => θ) 0)) k‖) := by
  have haabs := ClosedSeries.laurent_absolute a ha
  let A := ∑' m, ‖a m‖
  have hA : 0 ≤ A := tsum_nonneg (fun _ => norm_nonneg _)
  have htail (k : ℕ) : ‖series (tailCoefficients a k) θ‖ ≤ A := by
    have ht : Summable (fun m => ‖a (m + k)‖) :=
      haabs.comp_injective (fun _ _ h => Nat.add_right_cancel h)
    have hb : ‖series (tailCoefficients a k) θ‖ ≤ ∑' m, ‖a (m + k)‖ := by
      have hs : Summable (fun m => ‖a (m + k) * character m θ‖) := by
        simpa only [norm_mul, norm_character, mul_one] using ht
      simpa only [series, tailCoefficients, norm_mul, norm_character, mul_one] using
        norm_tsum_le_tsum_norm hs
    have he := haabs.sum_add_tsum_nat_add k
    have hn : 0 ≤ ∑ m ∈ Finset.range k, ‖a m‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    exact hb.trans (by dsimp [A]; linarith)
  have hcoef (k : ℕ) : ‖coefficient c a (fun _ : Fin 1 => θ) 0 k‖ ≤ A / c := by
    simp only [coefficient, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc, norm_character, mul_one]
    simpa [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left (htail k) (inv_nonneg.mpr hc.le)
  have hq : ‖(1 / r : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / r)]
    exact (div_lt_one (by linarith : 0 < r)).2 hr
  have hs : Summable (fun k : ℕ => (1 / r) ^ k * k * (A / c)) := by
    simpa only [pow_one, mul_comm, mul_left_comm, mul_assoc] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hq).mul_right (A / c)
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  simp only [radialCoefficients, firstOrder, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / r), Complex.norm_natCast]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hcoef k)
    (show (0 : ℝ) ≤ (1 / r) ^ k * (k : ℝ) by positivity)

/-- Only the differentiated Laurent difference-quotient identity remains. -/
structure RemainingLaurentSeries : Prop where
  divided_difference_derivative : ∀ a, SobolevCoefficients a →
    ∀ c : ℝ, 0 < c → ∀ r : ℝ, 1 < r → ∀ θ t : ℝ,
      series (radialCoefficients (1 / r)
        (firstOrder (coefficient c a (fun _ : Fin 1 => θ) 0))) t =
      let v := (r : ℂ) * unit t
      v * (laurentDerivative a v * (v - unit θ) - (laurent a v - laurent a (unit θ))) /
        ((c : ℂ) * (v - unit θ) ^ 2)

theorem RemainingLaurentSeries.toClassical (H : RemainingLaurentSeries) : ClassicalLaurentSeries where
  geometric_summable := geometric_summable_proved
  geometric_identity := geometric_identity_proved
  derivative_summable := derivative_summable_proved
  divided_difference_derivative := H.divided_difference_derivative

end
end Erdos1045.ExteriorClassical

import StructuralNote.FixedDualClassificationThirdReference

/-! Coupling of the fifth and seventh harmonics to the actual third-harmonic defect. -/

namespace StructuralNote.FixedDualClassificationThirdDefect

open Real MeasureTheory Set
open FixedDualClassificationStep FixedDualClassificationCoefficientBound
open FixedDualClassificationCosineNorm FixedDualClassificationThirdReference
open scoped ComplexConjugate
noncomputable section

theorem oscillation_norm (p t : ℝ) : ‖oscillation p t‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem oscillation_pair (p t θ : ℝ) :
    oscillation (-1) (2 * θ) * oscillation (-(p + 6)) t + oscillation (-p) t =
      (2 * cos (3 * t + θ) : ℝ) *
        (oscillation (-1) θ * oscillation (-(p + 3)) t) := by
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos, Complex.two_cos, add_mul]
  have hp : Complex.exp (((3 * t + θ : ℝ) : ℂ) * Complex.I) *
      (oscillation (-1) θ * oscillation (-(p + 3)) t) = oscillation (-p) t := by
    unfold oscillation
    rw [← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hn : Complex.exp (-((3 * t + θ : ℝ) : ℂ) * Complex.I) *
      (oscillation (-1) θ * oscillation (-(p + 3)) t) =
      oscillation (-1) (2 * θ) * oscillation (-(p + 6)) t := by
    unfold oscillation
    rw [← mul_assoc, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hp, hn, add_comm]

theorem coefficient_sub {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    {A B : ℝ} (hfb : ∀ t, |f t| ≤ A) (hgb : ∀ t, |g t| ≤ B) (p : ℤ) :
    coefficient (fun t => f t - g t) p = coefficient f p - coefficient g p := by
  simp only [coefficient, Complex.ofReal_sub, sub_mul]
  rw [intervalIntegral.integral_sub (oscillation_integrable hf hfb _ _ _)
    (oscillation_integrable hg hgb _ _ _), sub_div]

theorem coefficient_neg_frequency (f : ℝ → ℝ) (p : ℤ) :
    coefficient f (-p) = conj (coefficient f p) := by
  rw [coefficient, coefficient, map_div₀]
  simp only [Complex.conj_ofReal, map_mul, map_ofNat]
  simp only [intervalIntegral.integral_of_le two_pi_pos.le]
  rw [← integral_conj]
  congr 2
  funext t
  simp only [map_mul, Complex.conj_ofReal, oscillation, ← Complex.exp_conj, map_mul,
    Complex.conj_I, Int.cast_neg, neg_neg]
  congr 2
  push_cast
  ring

theorem coefficient_pair {d : ℝ → ℝ} (hd : Measurable d) {A : ℝ}
    (hbox : ∀ t, |d t| ≤ A) (p : ℤ) (θ : ℝ) :
    oscillation (-1) (2 * θ) * coefficient d (p + 6) + coefficient d p =
      (∫ t in 0..2 * Real.pi, (2 * d t * cos (3 * t + θ) : ℝ) *
        (oscillation (-1) θ * oscillation (-(p + 3)) t)) / (2 * Real.pi) := by
  have h1 := (oscillation_integrable hd hbox (-(p + 6)) 0 (2 * Real.pi)).const_mul
    (oscillation (-1) (2 * θ))
  have h2 := oscillation_integrable hd hbox (-p) 0 (2 * Real.pi)
  rw [coefficient, coefficient]
  push_cast
  rw [← mul_div_assoc, ← add_div,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add h1 h2]
  congr 2
  funext t
  have h := congrArg (fun z : ℂ => (d t : ℂ) * z) (oscillation_pair (p : ℝ) t θ)
  push_cast at h ⊢
  linear_combination h

theorem difference_pair_bound {f : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ t, |f t| ≤ Real.pi / 2) (p : ℤ) (θ : ℝ) :
    ‖oscillation (-1) (2 * θ) * coefficient (fun t => reference θ t - f t) (p + 6) +
      coefficient (fun t => reference θ t - f t) p‖ ≤
      2 * (1 - (oscillation (-1) θ * coefficient f 3).re) := by
  let d (t : ℝ) := reference θ t - f t
  have hd : Measurable d := (reference_measurable θ).sub hf
  have hb : ∀ t, |d t| ≤ Real.pi := reference_difference_bound hbox θ
  rw [coefficient_pair hd hb p θ, norm_div]
  have hn : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos]
  rw [hn]
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume)
    (f := fun t => (2 * d t * cos (3 * t + θ) : ℝ) *
      (oscillation (-1) θ * oscillation (-(p + 3)) t)) (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  have he : (fun t => ‖(2 * d t * cos (3 * t + θ) : ℝ) *
      (oscillation (-1) θ * oscillation (-(p + 3)) t)‖) =
      fun t => 2 * (d t * cos (3 * t + θ)) := by
    funext t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul,
      oscillation_norm, oscillation_norm, mul_one, mul_one,
      abs_of_nonneg (by have h := reference_difference_nonneg hbox θ t; dsimp [d]; nlinarith)]
    ring
  rw [he, intervalIntegral.integral_const_mul] at hnorm
  have hi := difference_cosine_integral hf hbox θ
  change (∫ t in 0..2 * Real.pi, d t * cos (3 * t + θ)) / (2 * Real.pi) = _ at hi
  calc
    _ ≤ (2 * ∫ t in 0..2 * Real.pi, d t * cos (3 * t + θ)) / (2 * Real.pi) :=
      div_le_div_of_nonneg_right hnorm (by positivity)
    _ = _ := by rw [mul_div_assoc, hi]

theorem coefficient_six_step {f : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ t, |f t| ≤ Real.pi / 2) {p : ℤ} (hp : ¬3 ∣ p) :
    ‖coefficient f (p + 6)‖ ≤ ‖coefficient f p‖ + 2 * (1 - ‖coefficient f 3‖) := by
  let θ := (coefficient f 3).arg
  have hp6 : ¬3 ∣ p + 6 := by omega
  have h := difference_pair_bound hf hbox p θ
  rw [coefficient_sub (reference_measurable θ) hf
      (fun t => (reference_abs θ t).le) hbox,
    coefficient_sub (reference_measurable θ) hf
      (fun t => (reference_abs θ t).le) hbox,
    reference_coefficient_zero θ hp6, reference_coefficient_zero θ hp,
    zero_sub, zero_sub, mul_neg, ← neg_add, norm_neg] at h
  have hphase : (oscillation (-1) θ * coefficient f 3).re = ‖coefficient f 3‖ := by
    rw [show θ = (coefficient f 3).arg by rfl, phase_align, Complex.ofReal_re]
  rw [hphase] at h
  have ht := norm_sub_le (oscillation (-1) (2 * θ) * coefficient f (p + 6) + coefficient f p)
    (coefficient f p)
  rw [add_sub_cancel_right, norm_mul, oscillation_norm, one_mul] at ht
  linarith

theorem coefficient_five_seven {f : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ t, |f t| ≤ Real.pi / 2) :
    ‖coefficient f 5‖ ≤ ‖coefficient f 1‖ + 2 * (1 - ‖coefficient f 3‖) ∧
    ‖coefficient f 7‖ ≤ ‖coefficient f 1‖ + 2 * (1 - ‖coefficient f 3‖) := by
  constructor
  · have h := coefficient_six_step hf hbox (p := -1) (by norm_num)
    norm_num only [show (-1 : ℤ) + 6 = 5 by norm_num] at h
    rw [coefficient_neg_frequency, Complex.norm_conj] at h
    exact h
  · simpa only [show (1 : ℤ) + 6 = 7 by norm_num] using
      coefficient_six_step hf hbox (p := 1) (by norm_num)

theorem normalized_five_seven {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ Erdos1045.EventualExact.FiniteBox.Q hm) :
    let f := stepProfile q (FixedDualClassificationMultiplierLimit.profileScale (2 * m))
    ‖profileCoefficient f 5‖ ≤ ‖profileCoefficient f 1‖ + 2 * (1 - ‖profileCoefficient f 3‖) ∧
    ‖profileCoefficient f 7‖ ≤ ‖profileCoefficient f 1‖ + 2 * (1 - ‖profileCoefficient f 3‖) := by
  dsimp only
  simp only [profileCoefficient_eq_interval (by omega : 0 < 2 * m)]
  exact coefficient_five_seven (stepProfile_measurable _ _) (stepProfile_normalized_bound hm q hq)

end
end StructuralNote.FixedDualClassificationThirdDefect

import StructuralNote.FixedDualClassificationCoefficientBound

/-! The exact three-lobed reference profile and its missing low harmonics. -/

namespace StructuralNote.FixedDualClassificationThirdReference

open Real MeasureTheory Set
open FixedDualClassificationStep FixedDualClassificationCoefficientBound
open FixedDualClassificationCosineNorm
noncomputable section

def reference (θ t : ℝ) : ℝ := if 0 ≤ cos (3 * t + θ) then Real.pi / 2 else -(Real.pi / 2)

theorem reference_measurable (θ : ℝ) : Measurable (reference θ) := by
  exact Measurable.ite (measurableSet_le measurable_const (by fun_prop))
    measurable_const measurable_const

theorem reference_abs (θ t : ℝ) : |reference θ t| = Real.pi / 2 := by
  unfold reference
  split_ifs <;> simp only [abs_neg, abs_of_pos (by positivity : 0 < Real.pi / 2)]

theorem reference_periodic (θ : ℝ) : Function.Periodic (reference θ) (2 * Real.pi / 3) := by
  intro t
  unfold reference
  rw [show 3 * (t + 2 * Real.pi / 3) + θ = (3 * t + θ) + 2 * Real.pi by ring,
    cos_add_two_pi]

theorem oscillation_integrable {f : ℝ → ℝ} (hf : Measurable f)
    {A : ℝ} (hbox : ∀ t, |f t| ≤ A) (p a b : ℝ) :
    IntervalIntegrable (fun t => (f t : ℂ) * oscillation p t) volume a b := by
  have h := bounded_intervalIntegrable hf hbox a b
  exact (show IntervalIntegrable (fun t => (f t : ℂ)) volume a b from
    ⟨h.1.ofReal, h.2.ofReal⟩).mul_continuousOn (oscillation_continuous p).continuousOn

theorem oscillation_two_pi (p : ℤ) : oscillation p (2 * Real.pi) = 1 := by
  unfold oscillation
  push_cast
  rw [show (p : ℂ) * (2 * Real.pi) * Complex.I =
      (p : ℂ) * (2 * Real.pi * Complex.I) by ring, Complex.exp_int_mul_two_pi_mul_I]

theorem coefficient_short_period {f : ℝ → ℝ} {T : ℝ}
    (hf : Function.Periodic f T) (hfull : Function.Periodic f (2 * Real.pi)) (p : ℤ)
    (hphase : oscillation (-p) T ≠ 1) : coefficient f p = 0 := by
  let g (t : ℝ) : ℂ := (f t : ℂ) * oscillation (-p) t
  have hg : Function.Periodic g (2 * Real.pi) := by
    intro t
    simp only [g, hfull t, oscillation_add]
    rw [← Int.cast_neg, oscillation_two_pi, one_mul]
  have he := hg.intervalIntegral_add_eq T 0
  have hshift := intervalIntegral.integral_comp_add_right g T (a := 0) (b := 2 * Real.pi)
  simp only [zero_add, add_comm (2 * Real.pi) T] at hshift
  rw [zero_add, ← hshift] at he
  have hscale : (∫ t in 0..2 * Real.pi, g (t + T)) =
      oscillation (-p) T * ∫ t in 0..2 * Real.pi, g t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [g]
    rw [hf t, oscillation_add]
    ring
  rw [hscale] at he
  have hz : (∫ t in 0..2 * Real.pi, g t) = 0 := by
    have hp : (oscillation (-p) T - 1) * (∫ t in 0..2 * Real.pi, g t) = 0 := by
      linear_combination he
    exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hphase)
  exact div_eq_zero_iff.mpr (Or.inl hz)

theorem oscillation_third_ne {p : ℤ} (hp : ¬3 ∣ p) :
    oscillation (-p) (2 * Real.pi / 3) ≠ 1 := by
  intro h
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
  have hi := congrArg Complex.im hk
  norm_num [Complex.mul_im] at hi
  have he : (p : ℝ) = 3 * (-k : ℤ) := by
    push_cast at hi ⊢
    have he : ((p : ℝ) + 3 * k) * Real.pi = 0 := by nlinarith [hi]
    have hz := (mul_eq_zero.mp he).resolve_right pi_ne_zero
    linarith
  apply hp
  exact ⟨-k, by exact_mod_cast he⟩

theorem reference_coefficient_zero (θ : ℝ) {p : ℤ} (hp : ¬3 ∣ p) :
    coefficient (reference θ) p = 0 := by
  have hpfull := (reference_periodic θ).nsmul 3
  rw [show (3 : ℕ) • (2 * Real.pi / 3) = 2 * Real.pi by simp only [nsmul_eq_mul]; ring] at hpfull
  exact coefficient_short_period (reference_periodic θ) hpfull p (oscillation_third_ne hp)

theorem reference_cosine (θ t : ℝ) :
    reference θ t * cos (3 * t + θ) = Real.pi / 2 * |cos (3 * t + θ)| := by
  unfold reference
  split_ifs with h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h)]
    ring

theorem reference_difference_nonneg {f : ℝ → ℝ}
    (hbox : ∀ t, |f t| ≤ Real.pi / 2) (θ t : ℝ) :
    0 ≤ (reference θ t - f t) * cos (3 * t + θ) := by
  rw [sub_mul, reference_cosine]
  apply sub_nonneg.mpr
  exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hbox t) (abs_nonneg _))

theorem reference_difference_bound {f : ℝ → ℝ}
    (hbox : ∀ t, |f t| ≤ Real.pi / 2) (θ t : ℝ) :
    |reference θ t - f t| ≤ Real.pi := by
  have h := (abs_sub (reference θ t) (f t)).trans
    (add_le_add (le_of_eq (reference_abs θ t)) (hbox t))
  linarith

theorem difference_cosine_integral {f : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ t, |f t| ≤ Real.pi / 2) (θ : ℝ) :
    (∫ t in 0..2 * Real.pi, (reference θ t - f t) * cos (3 * t + θ)) /
      (2 * Real.pi) = 1 - (oscillation (-1) θ * coefficient f 3).re := by
  have hc : Continuous (fun t : ℝ => cos (3 * t + θ)) := by fun_prop
  have hi := (bounded_intervalIntegrable hf hbox 0 (2 * Real.pi)).mul_continuousOn hc.continuousOn
  have ha : IntervalIntegrable (fun t => Real.pi / 2 * |cos (3 * t + θ)|)
      volume 0 (2 * Real.pi) := (hc.abs.intervalIntegrable _ _).const_mul _
  have he : (fun t => (reference θ t - f t) * cos (3 * t + θ)) =
      fun t => Real.pi / 2 * |cos (3 * t + θ)| - f t * cos (3 * t + θ) := by
    funext t
    rw [sub_mul, reference_cosine]
  have hcos := abs_cos_integral_affine (by norm_num : 0 < (3 : ℕ)) θ
  norm_num only [Nat.cast_ofNat] at hcos
  rw [he, intervalIntegral.integral_sub ha hi, intervalIntegral.integral_const_mul,
    hcos, coefficient_phase hf hbox]
  norm_num only [Int.cast_ofNat]
  field_simp
  ring

end
end StructuralNote.FixedDualClassificationThirdReference

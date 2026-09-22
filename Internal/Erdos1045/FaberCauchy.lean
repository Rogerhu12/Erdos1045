import Erdos1045.FaberCross

namespace Erdos1045.FaberFourier

open scoped BigOperators
noncomputable section

/-- Ordinary Cauchy--Schwarz for two arbitrary complex square-summable
sequences, including absolute convergence of their product series. -/
structure ClassicalSequenceFacts : Prop where
  cauchy : ∀ x y : ℕ → ℂ,
    Summable (fun m => ‖x m‖ ^ 2) → Summable (fun m => ‖y m‖ ^ 2) →
    Summable (fun m => ‖x m * y m‖) ∧
    ‖∑' m, x m * y m‖ ≤ Real.sqrt (∑' m, ‖x m‖ ^ 2) * Real.sqrt (∑' m, ‖y m‖ ^ 2)

def spectralSquareSum {n : ℕ} (θ : Fin n → ℝ) : ℝ :=
  (∑' k, KernelWeights.weight n k * ‖powerSum θ k‖ ^ 2) / (n : ℝ) ^ 2

def crossSeries {n : ℕ} (a : ℕ → ℂ) (θ : Fin n → ℝ) : ℂ :=
  ∑' m : ℕ, (crossWeight n (m + 1) : ℂ) * a (m + 1) * powerSum θ (m + 2)

/-- Equation (5.11), with the exact kernel weights proved in `FaberCross`. -/
theorem crossSeries_cauchy (classic : ClassicalSequenceFacts)
    {n : ℕ} (hn : 2 ≤ n) {c E : ℝ} (hc : 0 < c) (hE0 : 0 ≤ E)
    (a : ℕ → ℂ) (θ : Fin n → ℝ)
    (ha : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖a m‖ ^ 2))
    (hE : E ^ 2 = 2 * Real.pi * (∑' m : ℕ, (m : ℝ) ^ 2 * ‖a m‖ ^ 2))
    (hsp : Summable (fun k => KernelWeights.weight n k * ‖powerSum θ k‖ ^ 2)) :
    (crossSeries a θ).re / c ≤
      ((n : ℝ) * E / (c * Real.sqrt (2 * Real.pi))) * Real.sqrt (spectralSquareSum θ) := by
  let x : ℕ → ℂ := fun m => ((m + 1 : ℕ) : ℂ) * a (m + 1)
  let y : ℕ → ℂ := fun m => ((crossWeight n (m + 1) / ((m + 1 : ℕ) : ℝ)) : ℂ) *
    powerSum θ (m + 2)
  have hxterm (m : ℕ) : ‖x m‖ ^ 2 = ((m + 1 : ℕ) : ℝ) ^ 2 * ‖a (m + 1)‖ ^ 2 := by
    simp only [x, norm_mul, Complex.norm_natCast, mul_pow]
  have hyterm (m : ℕ) : ‖y m‖ ^ 2 = KernelWeights.weight n (m + 2) * ‖powerSum θ (m + 2)‖ ^ 2 := by
    simp only [y, norm_mul, norm_div, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs, div_pow]
    rw [crossWeight_sq_div hn (Nat.succ_pos m)]
  have hea := (coefficient_energies_summable ha).2
  have hxsum : Summable (fun m => ‖x m‖ ^ 2) := by
    simp_rw [hxterm]
    exact hea.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hysum : Summable (fun m => ‖y m‖ ^ 2) := by
    simp_rw [hyterm]
    exact hsp.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hxenergy : (∑' m, ‖x m‖ ^ 2) = ∑' m : ℕ, (m : ℝ) ^ 2 * ‖a m‖ ^ 2 := by
    simp_rw [hxterm]
    have h := hea.tsum_eq_zero_add
    simpa using h.symm
  have hyenergy : (∑' m, ‖y m‖ ^ 2) = ∑' k, KernelWeights.weight n k * ‖powerSum θ k‖ ^ 2 := by
    simp_rw [hyterm]
    have h := hsp.sum_add_tsum_nat_add 2
    simpa [Finset.sum_range_succ] using h
  have hprod (m : ℕ) : x m * y m =
      (crossWeight n (m + 1) : ℂ) * a (m + 1) * powerSum θ (m + 2) := by
    have hm : (((m + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    dsimp [x, y]
    push_cast
    field_simp
  have hcs := (classic.cauchy x y hxsum hysum).2
  simp_rw [hprod] at hcs
  change ‖crossSeries a θ‖ ≤ _ at hcs
  rw [hxenergy, hyenergy] at hcs
  have hsA : Real.sqrt (∑' m : ℕ, (m : ℝ) ^ 2 * ‖a m‖ ^ 2) = E / Real.sqrt (2 * Real.pi) := by
    apply (eq_div_iff (ne_of_gt (Real.sqrt_pos.2 (by positivity)))).2
    have h := congrArg Real.sqrt hE
    rw [Real.sqrt_sq hE0, Real.sqrt_mul (by positivity)] at h
    nlinarith
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hspEq : (∑' k, KernelWeights.weight n k * ‖powerSum θ k‖ ^ 2) =
      (n : ℝ) ^ 2 * spectralSquareSum θ := by
    unfold spectralSquareSum
    field_simp
  have hsP : Real.sqrt (∑' k, KernelWeights.weight n k * ‖powerSum θ k‖ ^ 2) =
      (n : ℝ) * Real.sqrt (spectralSquareSum θ) := by
    rw [hspEq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg n)]
  rw [hsA, hsP] at hcs
  have hreal := (Complex.re_le_norm (crossSeries a θ)).trans hcs
  have hdiv := div_le_div_of_nonneg_right hreal hc.le
  convert hdiv using 1 <;> first | rfl | ring

end

end Erdos1045.FaberFourier

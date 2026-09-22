import EventualExact.SchurOperatorBounds
import EventualExact.SchurWeightBounds

/-! Actual difference-quotient energy and the smoothing of the Schur operator. -/

namespace Erdos1045.EventualExact.SchurOperatorBounds

open Complex FourierMultiplier FiniteFourierLift SchurLiftBounds SchurSpectrum
open scoped BigOperators
noncomputable section

theorem character_frequency_mod {n : ℕ} (hn : 0 < n) (p j : ℕ) :
    character n (p % n) j = character n p j := by
  unfold character
  rw [Nat.mul_comm j (p % n), pow_mul, ← ClosedFourier.root_pow_mod hn p,
    ← pow_mul, Nat.mul_comm p j]

theorem centerCoefficient_eq_coefficient {n : ℕ} (hn : 0 < n)
    (c : Fin n → ℂ) (p : ℕ) :
    centerCoefficient hn c p = coefficient c ⟨(p + 1) % n, Nat.mod_lt _ hn⟩ := by
  rw [centerCoefficient_eq, coefficient]
  simp only [character_frequency_mod hn]

/-- The geometric pair energy uses the ordinary, unshifted Fourier frequencies. -/
theorem pairEnergy_spectral {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    pairEnergy hn c = (n : ℝ) / 2 *
      ∑ p : Fin n, (p : ℝ) * ((n : ℝ) - p) * normSq (coefficient c p) := by
  rw [pairEnergy, LocalDFT.energyA_eq_fourier ClosedFourier.dftInversion hn _
    (periodize_periodic hn c), ← LocalHessian.fullA_eq_geometric hn
      (ClosedFourier.orthogonality n hn)]
  change (n : ℝ) / 2 * (∑ p ∈ Finset.range n,
    ((p : ℝ) + 1) * ((n : ℝ) - ((p : ℝ) + 1)) * normSq (centerCoefficient hn c p)) = _
  simp_rw [centerCoefficient_eq_coefficient hn]
  let f : ℕ → ℝ := fun p => (p : ℝ) * ((n : ℝ) - p) *
    normSq (coefficient c ⟨p % n, Nat.mod_lt _ hn⟩)
  have hshift : (∑ p ∈ Finset.range n, f (p + 1)) = ∑ p ∈ Finset.range n, f p := by
    have he := Finset.sum_range_succ' f n
    rw [Finset.sum_range_succ] at he
    simpa only [f, Nat.cast_zero, zero_mul, sub_self, mul_zero, add_zero] using he.symm
  have hsum : (∑ p : Fin n, (p : ℝ) * ((n : ℝ) - p) * normSq (coefficient c p)) =
      ∑ p ∈ Finset.range n, f p := by
    rw [← Fin.sum_univ_eq_sum_range f n]
    apply Finset.sum_congr rfl
    intro p _
    simp only [f, Nat.mod_eq_of_lt p.isLt]
  rw [hsum]
  congr 1
  simpa only [f, Nat.cast_add, Nat.cast_one] using hshift

theorem pairEnergy_operator_le {n : ℕ} (hn : 0 < n) (heven : Even n) (q : Fin n → ℝ) :
    pairEnergy hn (fun j => (operator n q j : ℂ)) ≤ 2 * (n : ℝ) ^ 2 * meanSquare q := by
  rw [pairEnergy_spectral]
  have hpoint (p : Fin n) : (p : ℝ) * ((n : ℝ) - p) *
      normSq (realCoefficient (operator n q) p) ≤ 4 * n * normSq (realCoefficient q p) := by
    rw [coefficient_operator hn heven, normSq_mul, normSq_ofReal]
    calc
      _ = ((p : ℝ) * ((n : ℝ) - p) * SchurWeights.weight n p ^ 2) *
          normSq (realCoefficient q p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (SchurWeights.frequency_weight_sq_le p.isLt.le heven)
        (normSq_nonneg (realCoefficient q p))
  calc
    _ ≤ (n : ℝ) / 2 * ∑ p : Fin n, 4 * n * normSq (realCoefficient q p) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => hpoint p)
      positivity
    _ = _ := by rw [← Finset.mul_sum, realCoefficient_parseval hn]; ring

theorem norm_difference_ratio_le (x y z : ℂ) :
    normSq (((‖x‖ : ℝ) : ℂ) - (‖y‖ : ℝ)) / normSq z ≤ normSq (x - y) / normSq z := by
  apply div_le_div_of_nonneg_right _ (normSq_nonneg _)
  rw [← Complex.ofReal_sub, normSq_ofReal, normSq_eq_norm_sq]
  have h := (sq_le_sq₀ (abs_nonneg (‖x‖ - ‖y‖)) (norm_nonneg (x - y))).2
    (abs_norm_sub_norm_le x y)
  rw [sq_abs] at h
  nlinarith

/-- The modulus map is a contraction for every actual geometric difference quotient. -/
theorem pairEnergy_norm_le {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    pairEnergy hn (fun j => (‖c j‖ : ℂ)) ≤ pairEnergy hn c := by
  unfold pairEnergy LocalDFT.energyA
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Finset.sum_le_sum
  intro h _
  apply Finset.sum_le_sum
  intro j _
  simp only [LocalDFT.pairRatio, normSq_div, periodize]
  exact norm_difference_ratio_le _ _ _

theorem pairEnergy_abs_le {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    pairEnergy hn (fun j => ((|q j| : ℝ) : ℂ)) ≤ pairEnergy hn (fun j => (q j : ℂ)) := by
  simpa only [Complex.norm_real, Real.norm_eq_abs] using pairEnergy_norm_le hn (fun j => (q j : ℂ))

/-- Manuscript (4.8), with the absolute constant four and no supplied spectral hypothesis. -/
theorem operator_energy_smoothing {n : ℕ} (hn : 0 < n) (heven : Even n) (q : Fin n → ℝ) :
    pairEnergy hn (fun j => (operator n q j : ℂ)) +
      pairEnergy hn (fun j => ((|operator n q j| : ℝ) : ℂ)) ≤
        4 * (n : ℝ) ^ 2 * meanSquare q := by
  have hA := pairEnergy_operator_le hn heven q
  have habs := pairEnergy_abs_le hn (operator n q)
  linarith

end
end Erdos1045.EventualExact.SchurOperatorBounds

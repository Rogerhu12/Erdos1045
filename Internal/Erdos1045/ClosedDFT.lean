import Erdos1045.ClosedOrthogonality
import Mathlib.Data.Nat.Periodic

/-! Fourier inversion for the actual shifted coefficients, proved by finite
double summation and the constructed character orthogonality. -/

namespace Erdos1045.ClosedFourier

open Complex LocalPhase
open scoped BigOperators
noncomputable section

theorem shifted_sum_mul_conj {n : ℕ} (hn : 0 < n) (j l : ℕ) :
    (∑ r ∈ Finset.range n, regularRoot n ^ (j * (r + 1)) *
      (starRingEnd ℂ) (regularRoot n ^ (l * (r + 1)))) =
      if j % n = l % n then (n : ℂ) else 0 := by
  have he (r : ℕ) : regularRoot n ^ (j * (r + 1)) *
      (starRingEnd ℂ) (regularRoot n ^ (l * (r + 1))) =
      (regularRoot n ^ j * (starRingEnd ℂ) (regularRoot n ^ l)) *
        (regularRoot n ^ (r * j) * (starRingEnd ℂ) (regularRoot n ^ (r * l))) := by
    simp only [Nat.mul_add, Nat.mul_one, pow_add, map_mul, Nat.mul_comm j r, Nat.mul_comm l r]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, sum_mul_conj hn]
  split_ifs with hjl
  · have hp := (root_pow_eq_iff hn j l).mpr hjl
    have hnrm : ‖regularRoot n ^ l‖ = 1 := by rw [norm_pow, root_norm, one_pow]
    rw [hp, ← Complex.inv_eq_conj hnrm, mul_inv_cancel₀ (norm_ne_zero_iff.mp (by rw [hnrm]; norm_num)), one_mul]
  · rw [mul_zero]

theorem dftInversion : LocalDFT.ClassicalDFTInversion := by
  intro n hn u hu j
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum :
      (∑ r ∈ Finset.range n,
        (∑ l ∈ Finset.range n, u l * (starRingEnd ℂ) (regularRoot n ^ (l * (r + 1)))) *
          regularRoot n ^ (j * (r + 1))) =
        ∑ l ∈ Finset.range n, u l * (if j % n = l % n then (n : ℂ) else 0) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    rw [← shifted_sum_mul_conj hn j l, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have hsingle : (∑ l ∈ Finset.range n,
      u l * (if j % n = l % n then (n : ℂ) else 0)) = u (j % n) * n := by
    rw [Finset.sum_eq_single (j % n)]
    · simp
    · intro l hl hne
      have hlj : j % n ≠ l % n := by rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hl)]; omega
      simp [hlj]
    · exact fun h => False.elim (h (Finset.mem_range.mpr (Nat.mod_lt j hn)))
  unfold LocalFourier.displacement LocalDFT.coefficient
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [hsum, hsingle, mul_div_cancel_right₀ _ hn0, hu.map_mod_nat]

end
end Erdos1045.ClosedFourier

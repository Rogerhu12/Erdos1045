import StructuralNote.FixedDualClassificationKernelUniformAbel
import StructuralNote.FixedDualClassificationKernel

/-! Symmetric folding and the uniform tail bound for the actual finite kernel at grid points. -/

namespace StructuralNote.FixedDualClassificationKernelUniformFold

open Real Finset Erdos1045.EventualExact
open FixedDualClassificationKernel FixedDualClassificationKernelUniformAbel
open scoped BigOperators
noncomputable section

theorem sum_range_twice (f : ℕ → ℝ) (m : ℕ) :
    (∑ p ∈ range (2 * m), f p) = ∑ k ∈ range m, (f (2 * k) + f (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
      sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring

theorem weight_even_zero (n k : ℕ) : SchurWeights.weight n (2 * k) = 0 := by
  apply SchurWeights.weight_eq_zero
  intro h
  have hodd := Nat.odd_iff.mp h.1
  omega

theorem finiteKernel_odd (m : ℕ) (t : ℝ) :
    finiteKernel (2 * m) t = (1 / 2) *
      ∑ k ∈ range m, SchurWeights.weight (2 * m) (2 * k + 1) * cos ((2 * k + 1 : ℕ) * t) := by
  unfold finiteKernel
  change (1 / 2 : ℝ) * (∑ p : Fin (2 * m),
    (fun p : ℕ => SchurWeights.weight (2 * m) p * cos ((p : ℝ) * t)) p.val) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun p : ℕ => SchurWeights.weight (2 * m) p * cos ((p : ℝ) * t)) (2 * m), sum_range_twice]
  simp only [weight_even_zero, zero_mul, zero_add]

theorem folded_sum (f : ℕ → ℝ) {m : ℕ}
    (hsym : ∀ k < m, f (m - 1 - k) = f k) :
    (∑ k ∈ range m, f k) =
      (∑ k ∈ range (m / 2), f k) + ∑ k ∈ range ((m + 1) / 2), f k := by
  by_cases hm : m = 0
  · subst m; simp
  have he := sum_Ico_reflect f 0 (m := (m + 1) / 2) (n := m - 1) (by omega)
  have h1 : m - 1 + 1 - (m + 1) / 2 = m / 2 := by omega
  have h2 : m - 1 + 1 - 0 = m := by omega
  rw [Nat.Ico_zero_eq_range, h1, h2] at he
  have hreflect : (∑ k ∈ range ((m + 1) / 2), f (m - 1 - k)) =
      ∑ k ∈ range ((m + 1) / 2), f k := by
    apply sum_congr rfl
    intro k hk
    exact hsym k (by have := mem_range.mp hk; omega)
  rw [hreflect] at he
  rw [he, sum_range_add_sum_Ico f (by omega : m / 2 ≤ m)]

theorem grid_term_reflect {m r : ℕ} {t : ℝ}
    (ht : (2 * m : ℕ) * t = (r : ℝ) * (2 * Real.pi)) {k : ℕ} (hk : k < m) :
    SchurWeights.weight (2 * m) (2 * (m - 1 - k) + 1) *
        cos ((2 * (m - 1 - k) + 1 : ℕ) * t) =
      SchurWeights.weight (2 * m) (2 * k + 1) * cos ((2 * k + 1 : ℕ) * t) := by
  have hp : 2 * k + 1 ≤ 2 * m := by omega
  rw [show 2 * (m - 1 - k) + 1 = 2 * m - (2 * k + 1) by omega,
    SchurWeights.weight_reflect (even_two_mul m) hp]
  congr 1
  rw [Nat.cast_sub hp, sub_mul, ht, cos_nat_mul_two_pi_sub]

theorem finiteKernel_fold (m r : ℕ) {t : ℝ}
    (ht : (2 * m : ℕ) * t = (r : ℝ) * (2 * Real.pi)) :
    finiteKernel (2 * m) t = (1 / 2) *
      ((∑ k ∈ range (m / 2), SchurWeights.weight (2 * m) (2 * k + 1) *
          cos ((2 * k + 1 : ℕ) * t)) +
        ∑ k ∈ range ((m + 1) / 2), SchurWeights.weight (2 * m) (2 * k + 1) *
          cos ((2 * k + 1 : ℕ) * t)) := by
  rw [finiteKernel_odd, folded_sum _ (fun k hk => grid_term_reflect ht hk)]

theorem grid_kernel_tail {m r u : ℕ} (hu : 0 < u) (hum : u ≤ m / 2) {t : ℝ}
    (hgrid : (2 * m : ℕ) * t = (r : ℝ) * (2 * Real.pi)) (ht : sin t ≠ 0) :
    |finiteKernel (2 * m) t -
      ∑ k ∈ range u, SchurWeights.weight (2 * m) (2 * k + 1) * cos ((2 * k + 1 : ℕ) * t)| ≤
        1 / (((u : ℝ) + 1) * |sin t|) := by
  let f := fun k : ℕ => SchurWeights.weight (2 * m) (2 * k + 1) * cos ((2 * k + 1 : ℕ) * t)
  have htail (v : ℕ) (huv : u ≤ v) (hvm : v ≤ (m + 1) / 2) :
      |∑ k ∈ Ico u v, f k| ≤ 1 / (((u : ℝ) + 1) * |sin t|) := by
    rcases huv.eq_or_lt with rfl | huv
    · simp only [Ico_self, sum_empty, abs_zero]
      positivity
    · exact lower_half_tail (even_two_mul m) hu huv (by omega) ht
  have h1 := htail (m / 2) hum (by omega)
  have h2 := htail ((m + 1) / 2) (by omega) le_rfl
  have hs1 := sum_range_add_sum_Ico f hum
  have hs2 := sum_range_add_sum_Ico f (show u ≤ (m + 1) / 2 by omega)
  rw [finiteKernel_fold m r hgrid]
  change |(1 / 2 : ℝ) * ((∑ k ∈ range (m / 2), f k) +
    ∑ k ∈ range ((m + 1) / 2), f k) - ∑ k ∈ range u, f k| ≤ _
  rw [← hs1, ← hs2]
  have he : (1 / 2 : ℝ) * ((∑ k ∈ range u, f k) + (∑ k ∈ Ico u (m / 2), f k) +
      ((∑ k ∈ range u, f k) + ∑ k ∈ Ico u ((m + 1) / 2), f k)) - ∑ k ∈ range u, f k =
        (1 / 2 : ℝ) * ((∑ k ∈ Ico u (m / 2), f k) + ∑ k ∈ Ico u ((m + 1) / 2), f k) := by ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h := abs_add_le (∑ k ∈ Ico u (m / 2), f k) (∑ k ∈ Ico u ((m + 1) / 2), f k)
  linarith

end
end StructuralNote.FixedDualClassificationKernelUniformFold

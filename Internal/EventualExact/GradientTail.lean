import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Finite reciprocal-square tails and the near/far weighted estimate. -/

namespace Erdos1045.EventualExact.LocalGradient

open scoped BigOperators
noncomputable section

theorem reciprocal_square_step {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
  apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < x + 1))).2
  field_simp [hx.ne', (show x + 1 ≠ 0 by linarith)]
  nlinarith

theorem reciprocal_square_tail_aux {K N : ℕ} (hK : 0 < K) (hKN : K ≤ N) :
    (∑ h ∈ Finset.Ico (K + 1) (N + 1), 1 / (h : ℝ) ^ 2) ≤ 1 / (K : ℝ) - 1 / (N : ℝ) := by
  induction N, hKN using Nat.le_induction with
  | base => simp
  | succ N hKN ih =>
    rw [Finset.sum_Ico_succ_top (by omega : K + 1 ≤ N + 1)]
    have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hh := reciprocal_square_step hN
    push_cast
    linarith

theorem reciprocal_square_tail {K N : ℕ} (hK : 0 < K) :
    (∑ h ∈ Finset.Ico (K + 1) N, 1 / (h : ℝ) ^ 2) ≤ 1 / (K : ℝ) := by
  by_cases h : K < N
  · have hh := reciprocal_square_tail_aux hK (show K ≤ N - 1 by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ N)] at hh
    exact hh.trans (sub_le_self _ (by positivity))
  · rw [Finset.Ico_eq_empty_of_le (by omega)]
    simp

theorem weighted_interval_bound {n K : ℕ} (hK : 0 < K) (q : ℕ → ℝ) {η E : ℝ}
    (hη : 0 ≤ η) (hq : ∀ h ∈ Finset.Ico 1 n, 0 ≤ q h ∧ q h ≤ η)
    (hE : (∑ h ∈ Finset.Ico 1 n, q h ^ 2) ≤ E) :
    (∑ h ∈ Finset.Ico 1 n, q h / h) ≤
      η * (harmonic K : ℝ) + Real.sqrt E * Real.sqrt (1 / (K : ℝ)) := by
  let S := Finset.Ico 1 n
  let A := S.filter (fun h => h ≤ K)
  let B := S.filter (fun h => K < h)
  have hsplit : (∑ h ∈ S, q h / h) = (∑ h ∈ A, q h / h) + ∑ h ∈ B, q h / h := by
    simpa only [A, B, not_le] using (Finset.sum_filter_add_sum_filter_not S (fun h => h ≤ K) (fun h => q h / h)).symm
  have hnear : (∑ h ∈ A, q h / h) ≤ η * (harmonic K : ℝ) := by
    calc
      _ ≤ ∑ h ∈ A, η * (1 / (h : ℝ)) := by
        apply Finset.sum_le_sum
        intro h hh
        have hhS := (Finset.mem_filter.mp hh).1
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_right (hq h hhS).2 (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ ≤ ∑ h ∈ Finset.Icc 1 K, η * (1 / (h : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro h hh
          have ht := Finset.mem_filter.mp hh
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp ht.1).1, ht.2⟩
        · intro h _ _
          positivity
      _ = _ := by
        rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
        simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  have hBq : (∑ h ∈ B, q h ^ 2) ≤ E := by
    apply le_trans _ hE
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)
  have hBw : (∑ h ∈ B, (1 / (h : ℝ)) ^ 2) ≤ 1 / (K : ℝ) := by
    calc
      _ = ∑ h ∈ B, 1 / (h : ℝ) ^ 2 := by simp only [div_pow, one_pow]
      _ ≤ ∑ h ∈ Finset.Ico (K + 1) n, 1 / (h : ℝ) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro h hh
          have ht := Finset.mem_filter.mp hh
          exact Finset.mem_Ico.mpr ⟨by omega, (Finset.mem_Ico.mp ht.1).2⟩
        · intro _ _ _
          positivity
      _ ≤ _ := reciprocal_square_tail hK
  have hfar : (∑ h ∈ B, q h / h) ≤ Real.sqrt E * Real.sqrt (1 / (K : ℝ)) := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt B q (fun h => 1 / (h : ℝ))
    simp only [← div_eq_mul_one_div] at hcs
    apply hcs.trans
    exact mul_le_mul (Real.sqrt_le_sqrt hBq) (Real.sqrt_le_sqrt hBw)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  change (∑ h ∈ S, q h / h) ≤ _
  rw [hsplit]
  exact add_le_add hnear hfar


theorem sum_Ico_reflect {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    (∑ h ∈ Finset.Ico 1 n, f (n - h)) = ∑ h ∈ Finset.Ico 1 n, f h := by
  apply Finset.sum_bij (fun h _ => n - h)
  · intro h hh
    have := Finset.mem_Ico.mp hh
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro h hh k hk he
    have := Finset.mem_Ico.mp hh
    have := Finset.mem_Ico.mp hk
    omega
  · intro h hh
    have := Finset.mem_Ico.mp hh
    refine ⟨n - h, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    omega
  · intro h _
    rfl

theorem weighted_cycle_bound {n K : ℕ} (hK : 0 < K) (q : ℕ → ℝ) {η E : ℝ}
    (hη : 0 ≤ η) (hq : ∀ h ∈ Finset.Ico 1 n, 0 ≤ q h ∧ q h ≤ η)
    (hE : (∑ h ∈ Finset.Ico 1 n, q h ^ 2) ≤ E) :
    (∑ h ∈ Finset.Ico 1 n, q h * (1 / (h : ℝ) + 1 / ((n - h : ℕ) : ℝ))) ≤
      2 * (η * (harmonic K : ℝ) + Real.sqrt E * Real.sqrt (1 / (K : ℝ))) := by
  have hqr : ∀ h ∈ Finset.Ico 1 n, 0 ≤ q (n - h) ∧ q (n - h) ≤ η := by
    intro h hh
    have := Finset.mem_Ico.mp hh
    exact hq (n - h) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  have hEr : (∑ h ∈ Finset.Ico 1 n, q (n - h) ^ 2) ≤ E := by
    rw [sum_Ico_reflect n (fun h => q h ^ 2)]
    exact hE
  have hleft := weighted_interval_bound hK q hη hq hE
  have hright := weighted_interval_bound hK (fun h => q (n - h)) hη hqr hEr
  have he : (∑ h ∈ Finset.Ico 1 n, q h / ((n - h : ℕ) : ℝ)) =
      ∑ h ∈ Finset.Ico 1 n, q (n - h) / (h : ℝ) := by
    rw [← sum_Ico_reflect n (fun h => q (n - h) / (h : ℝ))]
    apply Finset.sum_congr rfl
    intro h hh
    have := Finset.mem_Ico.mp hh
    rw [show n - (n - h) = h by omega]
  simp_rw [mul_add, ← div_eq_mul_one_div]
  rw [Finset.sum_add_distrib, he]
  linarith

end
end Erdos1045.EventualExact.LocalGradient

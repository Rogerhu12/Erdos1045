import StructuralNote.FiniteCompressionGain
import Mathlib.Data.Nat.Dist

/-! The ordered-pair expression used by compression is exactly the full
self-interaction sum, including the diagonal. -/

namespace StructuralNote.FiniteCompressionInteraction

open Finset FiniteCompressionGain
open scoped BigOperators
noncomputable section

theorem interaction_eq_double_sum {ℓ : ℕ} (K : ℕ → ℝ) (e : ℕ → ℕ)
    (he : StrictMonoOn e (Set.Iio ℓ)) :
    interaction ℓ K e = ∑ i ∈ range ℓ, ∑ j ∈ range ℓ, K (Nat.dist (e i) (e j)) := by
  have hsplit (i j : ℕ) (hi : i ∈ range ℓ) (hj : j ∈ range ℓ) :
      K (Nat.dist (e i) (e j)) =
        (if i < j then K (e j - e i) else 0) +
        (if j < i then K (e i - e j) else 0) + (if i = j then K 0 else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · have h := (he (mem_range.mp hi) (mem_range.mp hj) hij).le
      rw [Nat.dist_eq_sub_of_le h]
      simp [hij, Nat.not_lt.mpr hij.le, hij.ne]
    · subst j
      simp
    · have h := (he (mem_range.mp hj) (mem_range.mp hi) hij).le
      rw [Nat.dist_eq_sub_of_le_right h]
      simp [hij, Nat.not_lt.mpr hij.le, hij.ne']
  have hsum := sum_congr rfl (fun i hi => sum_congr rfl (fun j hj => hsplit i j hi hj))
  have hswap : (∑ i ∈ range ℓ, ∑ j ∈ range ℓ, if j < i then K (e i - e j) else 0) =
      ∑ i ∈ range ℓ, ∑ j ∈ range ℓ, if i < j then K (e j - e i) else 0 := by
    rw [sum_comm]
  have hdiag : (∑ i ∈ range ℓ, ∑ j ∈ range ℓ, if i = j then K 0 else 0) =
      (ℓ : ℝ) * K 0 := by
    calc
      _ = ∑ _i ∈ range ℓ, K 0 := by
        apply sum_congr rfl
        intro i hi
        simp [mem_range.mp hi]
      _ = _ := by simp
  rw [interaction, rankPairs, sum_filter, sum_product]
  simp only [sum_add_distrib] at hsum
  rw [hswap, hdiag] at hsum
  linarith

end
end StructuralNote.FiniteCompressionInteraction

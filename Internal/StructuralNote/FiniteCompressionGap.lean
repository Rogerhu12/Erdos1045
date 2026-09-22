import StructuralNote.FixedDualClassificationRecurrenceWronskian
import Mathlib.Algebra.BigOperators.Intervals

/-! One-pass compression: every rank distance occurs across an internal hole.
The resulting telescoping kernel gain avoids a transport estimate. -/

namespace StructuralNote.FiniteCompressionGap

open Finset
open scoped BigOperators
noncomputable section

def crossPairs (ℓ a : ℕ) : Finset (ℕ × ℕ) := (range (a + 1)) ×ˢ Ico (a + 1) ℓ

def witness (ℓ a d : ℕ) : ℕ × ℕ :=
  (min a (ℓ - 1 - d), min a (ℓ - 1 - d) + d)

theorem witness_distance (ℓ a d : ℕ) : (witness ℓ a d).2 - (witness ℓ a d).1 = d := by
  simp [witness]

theorem witness_mem {ℓ a d : ℕ} (ha : a + 1 < ℓ) (hd : d ∈ Ico 1 ℓ) :
    witness ℓ a d ∈ crossPairs ℓ a := by
  rcases mem_Ico.mp hd with ⟨hd0, hdℓ⟩
  simp only [crossPairs, witness, mem_product, mem_range, mem_Ico]
  rcases le_total a (ℓ - 1 - d) with h | h
  · rw [min_eq_left h]
    omega
  · rw [min_eq_right h]
    omega

theorem witness_injective (ℓ a : ℕ) : Function.Injective (witness ℓ a) := by
  intro d e h
  simpa only [witness_distance] using congrArg (fun p : ℕ × ℕ => p.2 - p.1) h

theorem cross_telescoping {ℓ a : ℕ} (ha : a + 1 < ℓ) (K : ℕ → ℝ)
    (hmono : AntitoneOn K (Set.Icc 1 ℓ)) :
    K 1 - K ℓ ≤ ∑ p ∈ crossPairs ℓ a, (K (p.2 - p.1) - K (p.2 - p.1 + 1)) := by
  let S := (Ico 1 ℓ).image (witness ℓ a)
  have hsub : S ⊆ crossPairs ℓ a := by
    intro p hp
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hp
    exact witness_mem ha hd
  have hnon (p : ℕ × ℕ) (hp : p ∈ crossPairs ℓ a) :
      0 ≤ K (p.2 - p.1) - K (p.2 - p.1 + 1) := by
    rcases mem_product.mp hp with ⟨hi, hj⟩
    have hi' := mem_range.mp hi
    have hj' := mem_Ico.mp hj
    exact sub_nonneg.mpr (hmono ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega))
  have hsum := sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hnon p hp)
  have him : (∑ p ∈ S, (K (p.2 - p.1) - K (p.2 - p.1 + 1))) =
      ∑ d ∈ Ico 1 ℓ, (K d - K (d + 1)) := by
    dsimp only [S]
    rw [sum_image (fun _ _ _ _ h => witness_injective ℓ a h)]
    simp only [witness_distance]
  have htel : (∑ d ∈ Ico 1 ℓ, (K d - K (d + 1))) = K 1 - K ℓ := by
    have hh := sum_Ico_sub K (show 1 ≤ ℓ by omega)
    have he : (∑ d ∈ Ico 1 ℓ, (K d - K (d + 1))) =
        -(∑ d ∈ Ico 1 ℓ, (K (d + 1) - K d)) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro d _
      ring
    rw [he, hh]
    ring
  rwa [him, htel] at hsum

theorem rank_spacing {ℓ : ℕ} (e : ℕ → ℕ) (he : StrictMonoOn e (Set.Iio ℓ))
    {i j : ℕ} (hij : i ≤ j) (hj : j < ℓ) : j - i ≤ e j - e i := by
  have haux : ∀ d, i + d < ℓ → d ≤ e (i + d) - e i := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      intro hd
      have hh := ih (by omega)
      have hm := he (show i + d ∈ Set.Iio ℓ by change i + d < ℓ; omega)
        (show i + (d + 1) ∈ Set.Iio ℓ by exact hd) (by omega : i + d < i + (d + 1))
      have hbase := he.monotoneOn (show i ∈ Set.Iio ℓ by change i < ℓ; omega)
        (show i + d ∈ Set.Iio ℓ by change i + d < ℓ; omega) (by omega : i ≤ i + d)
      omega
  have hh := haux (j - i) (by omega)
  simpa only [Nat.add_sub_of_le hij] using hh

theorem gap_spacing {ℓ a : ℕ} (e : ℕ → ℕ) (he : StrictMonoOn e (Set.Iio ℓ))
    (ha : a + 1 < ℓ) (hgap : e a + 2 ≤ e (a + 1)) {i j : ℕ}
    (hi : i ≤ a) (hj : a < j) (hjℓ : j < ℓ) : j - i + 1 ≤ e j - e i := by
  have hleft := rank_spacing e he hi (by omega : a < ℓ)
  have hright := rank_spacing e he (show a + 1 ≤ j by omega) hjℓ
  have hmonoleft := he.monotoneOn (show i ∈ Set.Iio ℓ by change i < ℓ; omega)
    (show a ∈ Set.Iio ℓ by change a < ℓ; omega) hi
  have hmonoright := he.monotoneOn (show a + 1 ∈ Set.Iio ℓ from ha)
    (show j ∈ Set.Iio ℓ from hjℓ) (by omega : a + 1 ≤ j)
  omega

theorem exists_internal_gap {ℓ L : ℕ} (e : ℕ → ℕ) (he : StrictMonoOn e (Set.Iio ℓ))
    (hfirst : e 0 = L) (hnot : ∃ j < ℓ, e j ≠ L + j) :
    ∃ a, a + 1 < ℓ ∧ e a + 2 ≤ e (a + 1) := by
  by_contra hn
  have hstep (a : ℕ) (ha : a + 1 < ℓ) : e (a + 1) = e a + 1 := by
    have hm := he (show a ∈ Set.Iio ℓ by change a < ℓ; omega)
      (show a + 1 ∈ Set.Iio ℓ from ha) (by omega : a < a + 1)
    have hh : ¬e a + 2 ≤ e (a + 1) := fun h => hn ⟨a, ha, h⟩
    omega
  have hprefix : ∀ j, j < ℓ → e j = L + j := by
    intro j
    induction j with
    | zero => intro _; simpa using hfirst
    | succ j ih =>
      intro hj
      rw [hstep j hj, ih (by omega)]
      omega
  obtain ⟨j, hj, hne⟩ := hnot
  exact hne (hprefix j hj)

end
end StructuralNote.FiniteCompressionGap

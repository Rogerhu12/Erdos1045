import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! Disjoint forward intervals give a direct finite maximal weak estimate. -/

namespace Erdos1045.EventualExact.ForwardIntervals

open scoped BigOperators

def interval (length : ℕ → ℕ) (j : ℕ) : Finset ℕ := Finset.Ico j (j + length j)

/-- Greedy selection starts at the least uncovered index. Forward intervals need
no enlargement: the selected intervals themselves cover every requested start. -/
theorem disjoint_cover (length : ℕ → ℕ) (S : Finset ℕ) :
    (∀ j ∈ S, 0 < length j) →
    ∃ T : Finset ℕ, T ⊆ S ∧ S ⊆ T.biUnion (interval length) ∧
      (T : Set ℕ).PairwiseDisjoint (interval length) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hlength
    by_cases hS : S.Nonempty
    · let a := S.min' hS
      have ha : a ∈ S := Finset.min'_mem S hS
      have hla := hlength a ha
      let R := S.filter (fun j => a + length a ≤ j)
      have hRS : R ⊆ S := Finset.filter_subset _ _
      have haR : a ∉ R := by simp only [R, Finset.mem_filter]; omega
      have hproper : R ⊂ S := (Finset.ssubset_iff_subset_ne).2 ⟨hRS, by
        intro he
        exact haR (he.symm ▸ ha)⟩
      obtain ⟨T, hTR, hcover, hdisj⟩ := ih R hproper (fun j hj => hlength j (hRS hj))
      have hTstart (j : ℕ) (hj : j ∈ T) : a + length a ≤ j :=
        (Finset.mem_filter.mp (hTR hj)).2
      have hsep (j : ℕ) (hj : j ∈ T) :
          Disjoint (interval length a) (interval length j) := by
        apply Finset.disjoint_left.mpr
        intro x hx hy
        have hx' := Finset.mem_Ico.mp hx
        have hy' := Finset.mem_Ico.mp hy
        have hstart := hTstart j hj
        omega
      refine ⟨insert a T, Finset.insert_subset_iff.mpr ⟨ha, hTR.trans hRS⟩, ?_, ?_⟩
      · intro j hj
        by_cases hjR : j ∈ R
        · obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp (hcover hjR)
          exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_insert_of_mem hk, hjk⟩
        · have haj : a ≤ j := Finset.min'_le S j hj
          have hjlt : j < a + length a := by
            have hn : ¬a + length a ≤ j := by
              intro hh
              exact hjR (Finset.mem_filter.mpr ⟨hj, hh⟩)
            omega
          exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_insert_self _ _,
            Finset.mem_Ico.mpr ⟨haj, hjlt⟩⟩
      · intro i hi j hj hij
        rcases Finset.mem_insert.mp hi with rfl | hi
        · rcases Finset.mem_insert.mp hj with rfl | hj
          · exact (hij rfl).elim
          · exact hsep j hj
        · rcases Finset.mem_insert.mp hj with rfl | hj
          · exact (hsep i hi).symm
          · exact hdisj hi hj hij
    · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
      · simp only [Finset.not_nonempty_iff_eq_empty] at hS
        simp [hS]
      · simp

/-- A weak estimate for a finite set of large forward averages. The ambient
range ends at 2n because a start and its chosen length are both at most n. -/
theorem weak_bound {n : ℕ} (S : Finset ℕ) (length : ℕ → ℕ) (f : ℕ → ℝ)
    (hS : S ⊆ Finset.range n) (hpos : ∀ j ∈ S, 0 < length j)
    (hlength : ∀ j ∈ S, length j ≤ n) (hf : ∀ j, 0 ≤ f j)
    {t : ℝ} (ht : 0 ≤ t)
    (hlarge : ∀ j ∈ S, t * length j ≤ ∑ k ∈ interval length j, f k) :
    t * S.card ≤ ∑ k ∈ Finset.range (2 * n), f k := by
  classical
  obtain ⟨T, hTS, hcover, hdisj⟩ := disjoint_cover length S hpos
  have hsubset : T.biUnion (interval length) ⊆ Finset.range (2 * n) := by
    intro k hk
    obtain ⟨j, hj, hkj⟩ := Finset.mem_biUnion.mp hk
    have hjn := Finset.mem_range.mp (hS (hTS hj))
    have hjlength := hlength j (hTS hj)
    have hkl := Finset.mem_Ico.mp hkj
    exact Finset.mem_range.mpr (by omega)
  have hcard : S.card ≤ ∑ j ∈ T, length j := by
    have h := Finset.card_le_card hcover
    rw [Finset.card_biUnion hdisj] at h
    simpa only [interval, Nat.card_Ico, Nat.add_sub_cancel_left] using h
  have hcardR : (S.card : ℝ) ≤ ∑ j ∈ T, (length j : ℝ) := by exact_mod_cast hcard
  calc
    t * S.card ≤ t * ∑ j ∈ T, (length j : ℝ) := mul_le_mul_of_nonneg_left hcardR ht
    _ = ∑ j ∈ T, t * length j := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ T, ∑ k ∈ interval length j, f k :=
      Finset.sum_le_sum (fun j hj => hlarge j (hTS hj))
    _ = ∑ k ∈ T.biUnion (interval length), f k := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ k ∈ Finset.range (2 * n), f k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun k _ _ => hf k)

end Erdos1045.EventualExact.ForwardIntervals

import StructuralNote.FiniteCompressionDivergent

/-! Summation by parts controls an entire uncertain arc from its endpoint signs
and box bounds. No variation bound on the signs inside the arc is needed. -/

namespace StructuralNote.FiniteCompressionBackground

open Finset
open scoped BigOperators
noncomputable section

def contribution (k : ℕ) (φ b : ℕ → ℝ) : ℝ :=
  ∑ s ∈ range (k + 1), φ s * (b (s + 1) - b s)

theorem summation_by_parts (k : ℕ) (φ b : ℕ → ℝ) :
    contribution k φ b = φ k * b (k + 1) - φ 0 * b 0 -
      ∑ s ∈ range k, (φ (s + 1) - φ s) * b (s + 1) := by
  induction k with
  | zero => simp [contribution, mul_sub]
  | succ k ih =>
    have hstep : contribution (k + 1) φ b =
        contribution k φ b + φ (k + 1) * (b (k + 2) - b (k + 1)) := by
      exact sum_range_succ _ (k + 1)
    rw [show k + 1 = k.succ from rfl] at hstep
    rw [hstep, ih, sum_range_succ]
    ring

theorem interior_lower_bound (k : ℕ) (φ b : ℕ → ℝ) {A : ℝ}
    (hφ : MonotoneOn φ (Set.Icc 0 k)) (hb : ∀ s ≤ k + 1, |b s| ≤ A) :
    -A * (φ k - φ 0) ≤ ∑ s ∈ range k, (φ (s + 1) - φ s) * b (s + 1) := by
  have hterm (s : ℕ) (hs : s ∈ range k) :
      (φ (s + 1) - φ s) * (-A) ≤ (φ (s + 1) - φ s) * b (s + 1) := by
    have hs' := mem_range.mp hs
    apply mul_le_mul_of_nonneg_left (abs_le.mp (hb (s + 1) (by omega))).1
    exact sub_nonneg.mpr (hφ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega))
  have h := sum_le_sum hterm
  rw [← sum_mul, sum_range_sub] at h
  nlinarith

theorem ascending_arc_bound (k : ℕ) (φ b : ℕ → ℝ) {A : ℝ}
    (hφ : MonotoneOn φ (Set.Icc 0 k)) (hb : ∀ s ≤ k + 1, |b s| ≤ A)
    (hleft : b 0 = -A) (hright : b (k + 1) = A) :
    contribution k φ b ≤ 2 * A * φ k := by
  rw [summation_by_parts, hleft, hright]
  have h := interior_lower_bound k φ b hφ hb
  nlinarith

theorem descending_arc_bound (k : ℕ) (φ b : ℕ → ℝ) {A : ℝ}
    (hφ : MonotoneOn φ (Set.Icc 0 k)) (hb : ∀ s ≤ k + 1, |b s| ≤ A)
    (hleft : b 0 = A) (hright : b (k + 1) = -A) :
    contribution k φ b ≤ -2 * A * φ 0 := by
  rw [summation_by_parts, hleft, hright]
  have h := interior_lower_bound k φ b hφ hb
  nlinarith

theorem ascending_arc_nonpos (k : ℕ) (φ b : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hφ : MonotoneOn φ (Set.Icc 0 k)) (hb : ∀ s ≤ k + 1, |b s| ≤ A)
    (hleft : b 0 = -A) (hright : b (k + 1) = A) (hnegative : φ k ≤ 0) :
    contribution k φ b ≤ 0 :=
  (ascending_arc_bound k φ b hφ hb hleft hright).trans
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) hnegative)

theorem descending_arc_nonpos (k : ℕ) (φ b : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hφ : MonotoneOn φ (Set.Icc 0 k)) (hb : ∀ s ≤ k + 1, |b s| ≤ A)
    (hleft : b 0 = A) (hright : b (k + 1) = -A) (hpositive : 0 ≤ φ 0) :
    contribution k φ b ≤ 0 :=
  (descending_arc_bound k φ b hφ hb hleft hright).trans
    (mul_nonpos_of_nonpos_of_nonneg (by linarith) hpositive)

end
end StructuralNote.FiniteCompressionBackground

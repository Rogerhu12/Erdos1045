import StructuralNote.SolTerminalDistances

namespace StructuralNote.SolTerminalInteraction

open Finset
open scoped BigOperators
open SolTerminalDistances
open SolTerminalComponent SolTerminalTranslate

/-- Every ordered kernel term weakly increases under a left slide of a terminal block. -/
theorem kernel_term_le {K : ℕ → ℝ} {N L x y : ℕ}
    (hL : 0 < L)
    (hx : x < L ∨ L ≤ x) (hy : y < L ∨ L ≤ y)
    (hbound : Nat.dist x y ≤ N)
    (hmono : AntitoneOn K (Set.Icc 0 N)) :
    K (Nat.dist x y) ≤ K (Nat.dist (slideAt L x) (slideAt L y)) := by
  have hd : Nat.dist (slideAt L x) (slideAt L y) ≤ Nat.dist x y := by
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · simp [slide_fixed hx, slide_fixed hy]
    · have := slide_cross hx hy
      omega
    · rw [Nat.dist_comm (slideAt L x), Nat.dist_comm x]
      have := slide_cross hy hx
      omega
    · rw [slide_internal hL hx hy]
  apply hmono ⟨Nat.zero_le _, hd.trans hbound⟩ ⟨Nat.zero_le _, hbound⟩ hd

/-- The actual ordered double sum is nondecreasing under the terminal slide. -/
theorem ordered_interaction_nondecreasing (E : Finset ℕ) {K : ℕ → ℝ} {N L : ℕ}
    (hL : 0 < L)
    (hbound : ∀ x ∈ E, ∀ y ∈ E, Nat.dist x y ≤ N)
    (hmono : AntitoneOn K (Set.Icc 0 N)) :
    (∑ x ∈ E, ∑ y ∈ E, K (Nat.dist x y)) ≤
      ∑ x ∈ E, ∑ y ∈ E, K (Nat.dist (slideAt L x) (slideAt L y)) := by
  apply sum_le_sum
  intro x hx
  apply sum_le_sum
  intro y hy
  exact kernel_term_le hL (lt_or_ge x L) (lt_or_ge y L) (hbound x hx y hy) hmono

theorem translated_interaction_nondecreasing (E : Finset ℕ) (hE : E.Nonempty)
    {K : ℕ → ℝ} {N : ℕ} (hpos : 0 < terminalLeft E hE)
    (hbound : ∀ x ∈ E, ∀ y ∈ E, Nat.dist x y ≤ N)
    (hmono : AntitoneOn K (Set.Icc 0 N)) :
    (∑ x ∈ E, ∑ y ∈ E, K (Nat.dist x y)) ≤
      ∑ x ∈ translateTerminal E hE, ∑ y ∈ translateTerminal E hE,
        K (Nat.dist x y) := by
  have hinj := slideAt_injective_on hpos (before_left_not_mem E hE hpos)
  have himage := image_slide_eq_translate E hE hpos
  have hbase := ordered_interaction_nondecreasing E hpos hbound hmono
  rw [← himage]
  rw [sum_image hinj]
  simp_rw [sum_image hinj]
  exact hbase

end StructuralNote.SolTerminalInteraction

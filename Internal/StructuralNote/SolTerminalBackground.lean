import StructuralNote.SolTerminalTranslate

namespace StructuralNote.SolTerminalBackground

open Finset
open scoped BigOperators
open SolTerminalComponent SolTerminalTranslate

/-- A per-step background decrease telescopes across a terminal block. -/
theorem terminal_background_gain {b : ℕ → ℝ} {L R : ℕ} {gamma : ℝ}
    (hLR : L ≤ R) (hstep : ∀ k, L ≤ k → k ≤ R → gamma ≤ b k - b (k + 1)) :
    gamma * (R - L + 1) ≤ ∑ j ∈ range (R - L + 1), (b (L + j) - b (L + j + 1)) := by
  calc
    gamma * (R - L + 1) = ∑ _j ∈ range (R - L + 1), gamma := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      rw [Nat.cast_add, Nat.cast_sub hLR]
      ring_nf
    _ ≤ _ := sum_le_sum (fun j hj => hstep (L + j) (by omega) (by
      have := mem_range.mp hj
      omega))

theorem terminal_background_telescope {b : ℕ → ℝ} {L R : ℕ} (hLR : L ≤ R) :
    (∑ j ∈ range (R - L + 1), (b (L + j) - b (L + j + 1))) = b L - b (R + 1) := by
  have htel (n : ℕ) : (∑ j ∈ range n, (b (L + j) - b (L + j + 1))) =
      b L - b (L + n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      ring
  rw [htel]
  congr 2
  omega

/-- Sliding every site of `[L,R]` left gives the sum of its per-site gains. -/
theorem block_slide_background_gain {b : ℕ → ℝ} {L R : ℕ} {gamma : ℝ}
    (hLR : L ≤ R)
    (hstep : ∀ k, L ≤ k → k ≤ R → gamma ≤ b (k - 1) - b k) :
    gamma * (R - L + 1) ≤
      (∑ j ∈ range (R - L + 1), b (L + j - 1)) -
        ∑ j ∈ range (R - L + 1), b (L + j) := by
  rw [← sum_sub_distrib]
  calc
    gamma * (R - L + 1) = ∑ _j ∈ range (R - L + 1), gamma := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      rw [Nat.cast_add, Nat.cast_sub hLR]
      ring_nf
    _ ≤ _ := sum_le_sum (fun j hj => hstep (L + j) (by omega)
      (by have := mem_range.mp hj; omega))

theorem terminal_set_sum_difference {b : ℕ → ℝ} (E : Finset ℕ) (hE : E.Nonempty)
    (hpos : 0 < terminalLeft E hE) :
    (∑ x ∈ translateTerminal E hE, b x) - ∑ x ∈ E, b x =
      b (terminalLeft E hE - 1) - b (terminalRight E hE) := by
  have hn : terminalLeft E hE - 1 ∉ E.erase (terminalRight E hE) := by
    intro h
    exact before_left_not_mem E hE hpos (mem_of_mem_erase h)
  rw [translateTerminal, sum_insert hn]
  have he := sum_erase_add E b (right_mem E hE)
  linarith

theorem terminal_set_background_gain {b : ℕ → ℝ} (E : Finset ℕ) (hE : E.Nonempty)
    {gamma : ℝ} (hpos : 0 < terminalLeft E hE)
    (hstep : ∀ k, terminalLeft E hE ≤ k → k ≤ terminalRight E hE →
      gamma ≤ b (k - 1) - b k) :
    gamma * (terminalRight E hE - terminalLeft E hE + 1) ≤
      (∑ x ∈ translateTerminal E hE, b x) - ∑ x ∈ E, b x := by
  rw [terminal_set_sum_difference (b := b) E hE hpos]
  let L := terminalLeft E hE
  let R := terminalRight E hE
  have hLR : L ≤ R := terminalLeft_le_right E hE
  have htel (n : ℕ) :
      (∑ j ∈ range n, (b (L + j - 1) - b (L + j))) = b (L - 1) - b (L + n - 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      by_cases hn : n = 0
      · subst n; simp
      · have hLn : 0 < L + n := by omega
        have hend : L + (n + 1) - 1 = L + n := by omega
        rw [hend]
        ring
  have hg := block_slide_background_gain (b := b) hLR hstep
  rw [← sum_sub_distrib, htel] at hg
  have hend : L + (R - L + 1) - 1 = R := by omega
  simpa [L, R, hend] using hg

end StructuralNote.SolTerminalBackground

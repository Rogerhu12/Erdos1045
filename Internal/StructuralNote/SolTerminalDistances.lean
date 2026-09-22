import StructuralNote.SolTerminalTranslate

namespace StructuralNote.SolTerminalDistances

open Finset
open SolTerminalComponent SolTerminalTranslate

def slideAt (L x : ℕ) : ℕ := if L ≤ x then x - 1 else x

theorem slide_internal {L x y : ℕ} (hL : 0 < L) (hx : L ≤ x) (hy : L ≤ y) :
    Nat.dist (slideAt L x) (slideAt L y) = Nat.dist x y := by
  simp only [slideAt, if_pos hx, if_pos hy]
  unfold Nat.dist
  omega

theorem slide_fixed {L x : ℕ} (hx : x < L) : slideAt L x = x := by
  simp [slideAt, Nat.not_le.mpr hx]

theorem slide_cross {L x y : ℕ} (hx : x < L) (hy : L ≤ y) :
    Nat.dist (slideAt L x) (slideAt L y) + 1 = Nat.dist x y := by
  rw [slide_fixed hx]
  simp only [slideAt, if_pos hy]
  unfold Nat.dist
  omega

theorem slideAt_injective_on {L : ℕ} {E : Finset ℕ} (hL : 0 < L)
    (hgap : L - 1 ∉ E) : Set.InjOn (slideAt L) E := by
  intro x hx y hy hxy
  by_cases hxL : L ≤ x <;> by_cases hyL : L ≤ y
  · simp only [slideAt, if_pos hxL, if_pos hyL] at hxy
    have hxpos : 0 < x := lt_of_lt_of_le hL hxL
    have hypos : 0 < y := lt_of_lt_of_le hL hyL
    omega
  · have hy' : y < L := Nat.lt_of_not_ge hyL
    rw [slideAt, if_pos hxL, slideAt, if_neg hyL] at hxy
    have hxpos : 0 < x := lt_of_lt_of_le hL hxL
    have : y = L - 1 := by omega
    exact (hgap (this ▸ hy)).elim
  · have hx' : x < L := Nat.lt_of_not_ge hxL
    rw [slideAt, if_neg hxL, slideAt, if_pos hyL] at hxy
    have hypos : 0 < y := lt_of_lt_of_le hL hyL
    have : x = L - 1 := by omega
    exact (hgap (this ▸ hx)).elim
  · simpa [slideAt, hxL, hyL] using hxy

theorem image_slide_eq_translate (E : Finset ℕ) (hE : E.Nonempty)
    (hpos : 0 < terminalLeft E hE) :
    E.image (slideAt (terminalLeft E hE)) = translateTerminal E hE := by
  ext z
  simp only [mem_image, translateTerminal, mem_insert, mem_erase]
  constructor
  · rintro ⟨x, hxE, rfl⟩
    by_cases hxL : x < terminalLeft E hE
    · rw [slide_fixed hxL]
      exact Or.inr ⟨fun h => by
        subst x
        have := terminalLeft_le_right E hE
        omega, hxE⟩
    · have hLx : terminalLeft E hE ≤ x := by omega
      simp only [slideAt, if_pos hLx]
      by_cases hxEqL : x = terminalLeft E hE
      · left
        omega
      · right
        constructor
        · intro heq
          have hxmax : x ≤ terminalRight E hE := le_max' E x hxE
          have hxpos : 0 < x := hpos.trans_le hLx
          omega
        · apply terminal_interval E hE
          · have hxpos : 0 < x := hpos.trans_le hLx
            omega
          · have hxmax : x ≤ terminalRight E hE := le_max' E x hxE
            omega
  · intro hz
    rcases hz with hz | ⟨hzR, hzE⟩
    · refine ⟨terminalLeft E hE, terminalLeft_mem E hE, ?_⟩
      rw [slideAt, if_pos (le_refl _)]
      omega
    · by_cases hzL : z < terminalLeft E hE
      · exact ⟨z, hzE, slide_fixed hzL⟩
      · refine ⟨z + 1, ?_, ?_⟩
        · apply terminal_interval E hE (by omega)
          have hzmax : z ≤ terminalRight E hE := le_max' E z hzE
          omega
        · simp [slideAt, show terminalLeft E hE ≤ z + 1 by omega]

end StructuralNote.SolTerminalDistances

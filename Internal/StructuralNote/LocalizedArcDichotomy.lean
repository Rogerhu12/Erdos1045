import StructuralNote.FiniteCompressionRanked
import StructuralNote.SolTerminalComponent

/-! A purely finite dichotomy for the signs on one indexed arc. -/

namespace StructuralNote.LocalizedArcDichotomy

open Set
open Finset
open Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier
open StructuralNote.FiniteCompressionRanked
open StructuralNote.SolTerminalComponent
noncomputable section

private theorem patternSign_eq_neg_one_of_ne_one {m : ℕ} {hm : 0 < m}
    (s : SignPattern hm) (j : ℕ)
    (h : patternSign s (site hm j) ≠ 1) :
    patternSign s (site hm j) = -1 := by
  rcases patternSign_is_sign s (site hm j) with hpos | hneg
  · exact False.elim (h hpos)
  · exact hneg

theorem localized_arc_dichotomy {m : ℕ} {hm : 0 < m}
    (s : SignPattern hm) {L R : ℕ} (hLR : L ≤ R)
    (hleft : patternSign s (site hm L) = 1)
    (hright : patternSign s (site hm (R + 1)) = -1)
    (E : Finset ℕ)
    (hsupport : ∀ x ∈ E, L + 1 ≤ x ∧ x ≤ R)
    (hsign : ∀ j, L + 1 ≤ j → j ≤ R →
      (j ∈ E ↔ patternSign s (site hm j) = 1)) :
    (∃ hE : E.Nonempty,
        E ≠ natInterval (L + 1) (terminalRight E hE)) ∨
      ∃ cut ∈ Set.Icc L R, ∀ j ∈ Set.Icc L (R + 1),
        patternSign s (site hm j) = if j ≤ cut then 1 else -1 := by
  by_cases hE : E.Nonempty
  · by_cases hnot : E ≠ natInterval (L + 1) (terminalRight E hE)
    · exact Or.inl ⟨hE, hnot⟩
    · right
      have heq : E = natInterval (L + 1) (terminalRight E hE) :=
        not_ne_iff.mp hnot
      have hcutL : L ≤ terminalRight E hE := by
        have hx := hsupport _ (right_mem E hE)
        omega
      have hcutR : terminalRight E hE ≤ R := by
        have hx := hsupport _ (right_mem E hE)
        exact hx.2
      refine ⟨terminalRight E hE, ⟨hcutL, hcutR⟩, ?_⟩
      intro j hj
      rcases hj with ⟨hjlo, hjhi⟩
      by_cases hjR : j ≤ R
      · by_cases hjcut : j ≤ terminalRight E hE
        · rw [if_pos hjcut]
          by_cases hjL : j = L
          · simpa [hjL] using hleft
          · have hj1 : L + 1 ≤ j := by omega
            have hjE : j ∈ E := by
              rw [heq, mem_natInterval]
              exact ⟨hj1, hjcut⟩
            exact (hsign j hj1 hjR).mp hjE
        · rw [if_neg hjcut]
          have hj1 : L + 1 ≤ j := by omega
          have hjE : j ∉ E := by
            intro hmem
            have hmax : j ≤ terminalRight E hE := Finset.le_max' E j hmem
            omega
          have hne : patternSign s (site hm j) ≠ 1 :=
            (hsign j hj1 hjR).not.mp hjE
          exact patternSign_eq_neg_one_of_ne_one s j hne
      · have hjlast : j = R + 1 := by omega
        have hjcut : ¬j ≤ terminalRight E hE := by omega
        rw [if_neg hjcut]
        simpa [hjlast] using hright
  · right
    refine ⟨L, ?_, ?_⟩
    · exact ⟨le_rfl, hLR⟩
    · intro j hj
      rcases hj with ⟨hjlo, hjhi⟩
      by_cases hjcut : j ≤ L
      · rw [if_pos hjcut]
        have : j = L := by omega
        simpa [this] using hleft
      · rw [if_neg hjcut]
        by_cases hjR : j ≤ R
        · have hj1 : L + 1 ≤ j := by omega
          have hjE : j ∉ E := by
            intro hmem
            exact hE ⟨j, hmem⟩
          have hne : patternSign s (site hm j) ≠ 1 :=
            (hsign j hj1 hjR).not.mp hjE
          exact patternSign_eq_neg_one_of_ne_one s j hne
        · have : j = R + 1 := by omega
          simpa [this] using hright

end
end StructuralNote.LocalizedArcDichotomy

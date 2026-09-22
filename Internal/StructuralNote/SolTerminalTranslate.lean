import StructuralNote.SolTerminalComponent

namespace StructuralNote.SolTerminalTranslate

open Finset
open SolTerminalComponent

def translateTerminal (E : Finset ℕ) (hE : E.Nonempty) : Finset ℕ :=
  insert (terminalLeft E hE - 1) (erase E (terminalRight E hE))

theorem translate_eq (E : Finset ℕ) (hE : E.Nonempty) :
    translateTerminal E hE = (E \ {terminalRight E hE}) ∪ {terminalLeft E hE - 1} := by
  ext x
  simp [translateTerminal, and_comm]

theorem card_translate (E : Finset ℕ) (hE : E.Nonempty)
    (hpos : 0 < terminalLeft E hE) : (translateTerminal E hE).card = E.card := by
  have hn : terminalLeft E hE - 1 ∉ erase E (terminalRight E hE) := by
    intro hm
    exact before_left_not_mem E hE hpos (mem_of_mem_erase hm)
  have hc : 0 < E.card := card_pos.mpr hE
  simp [translateTerminal, hn, right_mem E hE]
  omega

theorem translate_subset_interval (E : Finset ℕ) (hE : E.Nonempty) {a b : ℕ}
    (hsub : ∀ x ∈ E, a ≤ x ∧ x ≤ b) (ha : a < terminalLeft E hE) :
    ∀ x ∈ translateTerminal E hE, a ≤ x ∧ x ≤ b := by
  intro x hx
  simp only [translateTerminal, mem_insert, mem_erase] at hx
  rcases hx with rfl | ⟨_, hx⟩
  · have hr := (hsub _ (terminalLeft_mem E hE)).2
    omega
  · exact hsub _ hx

theorem symmDiff_translate (E : Finset ℕ) (hE : E.Nonempty)
    (hpos : 0 < terminalLeft E hE) :
    (E \ translateTerminal E hE) ∪ (translateTerminal E hE \ E) =
      {terminalRight E hE, terminalLeft E hE - 1} := by
  ext x
  have hn : terminalLeft E hE - 1 ∉ E := before_left_not_mem E hE hpos
  have hr : terminalRight E hE ∈ E := right_mem E hE
  simp [translateTerminal]
  aesop

end StructuralNote.SolTerminalTranslate

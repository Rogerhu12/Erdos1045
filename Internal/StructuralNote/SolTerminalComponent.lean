import Mathlib

namespace StructuralNote.SolTerminalComponent

open Finset

def terminalRight (E : Finset ℕ) (hE : E.Nonempty) : ℕ := E.max' hE

def terminalStarts (E : Finset ℕ) (hE : E.Nonempty) : Finset ℕ :=
  E.filter fun l => ∀ k, l ≤ k → k ≤ terminalRight E hE → k ∈ E

theorem right_mem (E : Finset ℕ) (hE : E.Nonempty) : terminalRight E hE ∈ E :=
  max'_mem E hE

theorem right_is_start (E : Finset ℕ) (hE : E.Nonempty) :
    terminalRight E hE ∈ terminalStarts E hE := by
  rw [terminalStarts, mem_filter]
  refine ⟨right_mem E hE, ?_⟩
  intro k hk₁ hk₂
  have : k = terminalRight E hE := by omega
  simpa [this] using right_mem E hE

def terminalLeft (E : Finset ℕ) (hE : E.Nonempty) : ℕ :=
  (terminalStarts E hE).min' ⟨_, right_is_start E hE⟩

def natInterval (a b : ℕ) : Finset ℕ := (range (b + 1)).filter (a ≤ ·)

@[simp] theorem mem_natInterval {a b k : ℕ} : k ∈ natInterval a b ↔ a ≤ k ∧ k ≤ b := by
  simp [natInterval, and_comm]

theorem terminalLeft_mem (E : Finset ℕ) (hE : E.Nonempty) : terminalLeft E hE ∈ E := by
  exact (mem_filter.mp (min'_mem _ _)).1

theorem terminal_interval (E : Finset ℕ) (hE : E.Nonempty) {k : ℕ}
    (hkL : terminalLeft E hE ≤ k) (hkR : k ≤ terminalRight E hE) : k ∈ E := by
  exact (mem_filter.mp (min'_mem (terminalStarts E hE) _)).2 k hkL hkR

theorem terminalLeft_le_right (E : Finset ℕ) (hE : E.Nonempty) :
    terminalLeft E hE ≤ terminalRight E hE := by
  exact min'_le _ _ (right_is_start E hE)

theorem before_left_not_mem (E : Finset ℕ) (hE : E.Nonempty)
    (hpos : 0 < terminalLeft E hE) : terminalLeft E hE - 1 ∉ E := by
  intro hm
  have hs : terminalLeft E hE - 1 ∈ terminalStarts E hE := by
    rw [terminalStarts, mem_filter]
    refine ⟨hm, ?_⟩
    intro k hk hkR
    by_cases hk' : terminalLeft E hE ≤ k
    · exact terminal_interval E hE hk' hkR
    · have : k = terminalLeft E hE - 1 := by omega
      simpa [this] using hm
  have := min'_le (terminalStarts E hE) _ hs
  change terminalLeft E hE ≤ terminalLeft E hE - 1 at this
  omega

theorem other_sites_left (E : Finset ℕ) (hE : E.Nonempty) {x : ℕ}
    (hx : x ∈ E) (hxR : x ∉ Finset.Icc (terminalLeft E hE) (terminalRight E hE)) :
    x < terminalLeft E hE := by
  have hmax : x ≤ terminalRight E hE := le_max' E x hx
  simp only [mem_Icc, not_and_or] at hxR
  rcases hxR with hxL | hxR
  · omega
  · omega

/-- A non-initial finite set has a nonzero left endpoint for its rightmost component. -/
theorem terminal_component_of_not_initial (E : Finset ℕ) (hE : E.Nonempty)
    (hnot : E ≠ range (terminalRight E hE + 1)) :
    0 < terminalLeft E hE := by
  by_contra h
  have hL : terminalLeft E hE = 0 := by omega
  apply hnot
  ext k
  simp only [mem_range]
  constructor
  · intro hk
    exact Nat.lt_succ_of_le (le_max' E k hk)
  · intro hk
    exact terminal_interval E hE (by omega) (by omega)

/-- Relative form for an arbitrary ambient arc: a non-initial set has room to slide left. -/
theorem terminal_component_of_not_initial_from (E : Finset ℕ) (hE : E.Nonempty) (a : ℕ)
    (hlower : ∀ x ∈ E, a ≤ x)
    (hnot : E ≠ natInterval a (terminalRight E hE)) :
    a < terminalLeft E hE := by
  have hLa : a ≤ terminalLeft E hE := hlower _ (terminalLeft_mem E hE)
  by_contra h
  have hL : terminalLeft E hE = a := by omega
  apply hnot
  ext k
  rw [mem_natInterval]
  constructor
  · intro hk
    exact ⟨hlower k hk, le_max' E k hk⟩
  · rintro ⟨hak, hkR⟩
    exact terminal_interval E hE (by simpa [hL]) hkR

end StructuralNote.SolTerminalComponent

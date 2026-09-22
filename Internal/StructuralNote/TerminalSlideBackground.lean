import StructuralNote.FiniteCompressionBackgroundUniform
import StructuralNote.TerminalSlideUniform

/-! The terminal two-site improvement with the background-drop premise proved
from actual arc data. Global sign localization still has to produce these data. -/

namespace StructuralNote.TerminalSlideBackground

open Real Filter Finset Erdos1045.EventualExact FourierMultiplier FiniteBox
open FiniteCompressionBackgroundUniform TerminalSlideUniform
open SolTerminalActualGain SolTerminalComponent SolTerminalBoxMove
open SolWordHamming SolWordFlips FixedDualClassificationFinite
open FiniteCompressionRanked FiniteCompressionEnergy
open scoped Topology
noncomputable section

theorem eventually_two_site_improvement : ∃ η : ℝ, 0 < η ∧
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 0 < m) (E : Finset ℕ) (hE : E.Nonempty)
      (ell R : ℕ) (s : SignPattern hm),
      R < m → 2 * Real.pi * (R - ell : ℕ) / (2 * m : ℝ) ≤ Real.pi / 12 →
      E ≠ natInterval ell (terminalRight E hE) →
      (∀ x ∈ E, ell ≤ x ∧ x ≤ R) →
      (∀ x, ell ≤ x → x ≤ R → (x ∈ E ↔ patternSign s (site hm x) = 1)) →
      (∀ k, terminalLeft E hE ≤ k → k ≤ terminalRight E hE →
        Nonempty (BackgroundArcs hm
          (vertex (amplitude (2 * m)) s - patch hm (amplitude (2 * m)) (gridSites hm E))
          (k - 1))) →
      ∃ t : SignPattern hm, hamming s t ≤ 2 ∧
        η / (2 * m : ℕ) ^ 2 ≤
          normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) t) -
            normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) s) ∧
        0 ≤ deficit hm t ∧ deficit hm t + η / (2 * m : ℕ) ^ 2 ≤ deficit hm s := by
  obtain ⟨c, hc, hdrop⟩ := eventually_background_predecessor_drop
  refine ⟨4 * c, by positivity, ?_⟩
  filter_upwards [hdrop, eventually_actual_word_terminal_gain_on_arc] with m hd hslide
  intro hm E hE ell R s hR hspan hnot hEarc hsign harcs
  let A := amplitude (2 * m)
  let b := vertex A s - patch hm A (gridSites hm E)
  have hA : 1 ≤ A := amplitude_ge_one (by omega)
  have hbox : b ∈ Q hm := word_background_mem_Q hm s E (by
    intro x hx
    exact (hsign x (hEarc x hx).1 (hEarc x hx).2).mp hx)
  have hleft := terminal_component_of_not_initial_from E hE ell
    (fun x hx => (hEarc x hx).1) hnot
  have hstep : ∀ k, terminalLeft E hE ≤ k → k ≤ terminalRight E hE →
      c / (2 * m : ℕ) ≤ operator (2 * m) b (site hm (k - 1)) -
        operator (2 * m) b (site hm k) := by
    intro k hkL hkR
    obtain ⟨arcs⟩ := harcs k hkL hkR
    exact hd hm b hbox k (by omega) arcs
  obtain ⟨left, right, _, _, hh, hg⟩ := hslide hm E hE ell R s A (c / (2 * m : ℕ))
    hR hspan hnot hEarc hsign (by linarith) (by positivity) hstep
  let t := flipTwo s left right
  have hprice : (4 * c) / (2 * m : ℕ) ^ 2 ≤ 4 * A * (c / (2 * m : ℕ)) / (2 * m : ℝ) := by
    have hn : (0 : ℝ) < (2 * m : ℕ) ^ 2 := by positivity
    calc
      _ ≤ 4 * A * c / (2 * m : ℕ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ hn.le
        nlinarith [mul_le_mul_of_nonneg_right hA hc.le]
      _ = _ := by push_cast; ring
  have hgain := hprice.trans hg
  have hupper := energy_le_B hm (vertex_mem_box (amplitude_pos (by omega)).le t)
  refine ⟨t, hh, hgain, ?_, ?_⟩
  · exact sub_nonneg.mpr hupper
  · dsimp only [deficit]
    linarith

end
end StructuralNote.TerminalSlideBackground

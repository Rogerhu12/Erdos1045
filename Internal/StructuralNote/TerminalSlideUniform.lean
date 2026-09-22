import StructuralNote.SolTerminalActualGain
import StructuralNote.FiniteCompressionGeometric
import StructuralNote.FixedDualClassificationKernelSignsFinal

/-! Uniform terminal slides on a genuine short half-period arc.

The set of positive sites is kept explicit in the statement.  This makes the
two endpoint signs consequences of the arc sign condition, rather than extra
premises of the word move.  The background step is intentionally still an
input: its proof belongs to the background part of the argument.
-/

namespace StructuralNote.TerminalSlideUniform

open Finset
open scoped BigOperators
open StructuralNote.SolTerminalActualGain
open StructuralNote.SolTerminalComponent StructuralNote.SolTerminalTranslate
open StructuralNote.SolTerminalBoxMove StructuralNote.SolWordFlips
open StructuralNote.SolWordHamming
open StructuralNote.FiniteCompressionRanked
open StructuralNote.FiniteCompressionEnergy
open Erdos1045.EventualExact FourierMultiplier FixedDualClassificationKernel
open Erdos1045.EventualExact.FiniteBox
open StructuralNote.FiniteCompressionGeometric
open StructuralNote.FixedDualClassificationKernelSignsFinal

noncomputable section

/- The `0` endpoint is harmless: the actual sign package controls it too, so
the interaction hypothesis required by the older score lemma is available on
the closed interval, not only on the positive lags. -/
theorem eventually_actual_grid_kernel_antitone :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ N : ℕ,
      2 * Real.pi * N / (2 * m : ℝ) ≤ Real.pi / 12 →
      AntitoneOn (gridKernel (2 * m)) (Set.Icc 0 N) := by
  filter_upwards [eventually_compressionKernelSigns] with m hs N hN
  intro i hi j hj hij
  rw [gridKernel_eq, gridKernel_eq]
  apply near_antitone hs hij
  have hangle : (j : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤
      (N : ℝ) * (2 * Real.pi / (2 * m : ℕ)) := by
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hj.2
    · positivity
  have he : (N : ℝ) * (2 * Real.pi / (2 * m : ℕ)) =
      2 * Real.pi * N / (2 * m : ℝ) := by
    push_cast
    ring
  rw [← he] at hN
  exact hangle.trans hN

/- The arc sign condition used below is exactly the statement that `E` is the
positive part of `[ell,R]`; its complement in the arc is negative. -/
theorem eventually_actual_word_terminal_gain_on_arc :
    ∀ᶠ m : ℕ in Filter.atTop,
      ∀ (hm : 0 < m) (E : Finset ℕ) (hE : E.Nonempty)
        (ell R : ℕ) (s : SignPattern hm) (A gamma : ℝ),
    R < m →
    2 * Real.pi * (R - ell : ℕ) / (2 * m : ℝ) ≤ Real.pi / 12 →
    E ≠ natInterval ell (terminalRight E hE) →
    (∀ x ∈ E, ell ≤ x ∧ x ≤ R) →
    (∀ x, ell ≤ x → x ≤ R →
      (x ∈ E ↔ patternSign s (site hm x) = 1)) →
    0 ≤ A → 0 ≤ gamma →
    (∀ k, terminalLeft E hE ≤ k → k ≤ terminalRight E hE →
      gamma ≤ operator (2 * m)
          (vertex A s - patch hm A (gridSites hm E)) (site hm (k - 1)) -
        operator (2 * m) (vertex A s - patch hm A (gridSites hm E))
          (site hm k)) →
    ∃ left right : Fin m,
      left.val = terminalLeft E hE - 1 ∧
      right.val = terminalRight E hE ∧
      hamming s (flipTwo s left right) ≤ 2 ∧
      4 * A * gamma / (2 * m : ℝ) ≤
        normalizedBoxEnergy (operator (2 * m)) (vertex A (flipTwo s left right)) -
          normalizedBoxEnergy (operator (2 * m)) (vertex A s) := by
  filter_upwards [eventually_actual_grid_kernel_antitone] with m hK
  intro hm E hE ell R s A gamma hR hspan hnot hEarc hsign hA hgamma hstep
  have hsub : ∀ x ∈ E, ell ≤ x ∧ x ≤ R := hEarc
  have hleft_lt : ell < terminalLeft E hE :=
    terminal_component_of_not_initial_from E hE ell
      (fun x hx => (hsub x hx).1) hnot
  have hLmem := terminalLeft_mem E hE
  have hRmem := right_mem E hE
  have hleft_le_R : terminalLeft E hE ≤ R := (hsub _ hLmem).2
  have hright_le_R : terminalRight E hE ≤ R := (hsub _ hRmem).2
  have hpos : 0 < terminalLeft E hE := by omega
  have hFirst : ∀ x ∈ E, x < m := by
    intro x hx
    exact (hsub x hx).2.trans_lt hR
  have hnewsub : ∀ x ∈ translateTerminal E hE, ell ≤ x ∧ x ≤ R :=
    translate_subset_interval E hE hsub hleft_lt
  have hNewFirst : ∀ x ∈ translateTerminal E hE, x < m := by
    intro x hx
    exact (hnewsub x hx).2.trans_lt hR
  have hbound : ∀ x ∈ E, ∀ y ∈ E, Nat.dist x y ≤ R - ell := by
    intro x hx y hy
    have hx' := hsub x hx
    have hy' := hsub y hy
    by_cases hxy : x ≤ y
    · rw [Nat.dist_eq_sub_of_le hxy]
      omega
    · have hyx : y ≤ x := by omega
      rw [Nat.dist_eq_sub_of_le_right hyx]
      omega
  have hkernel := hK (R - ell) hspan
  have hleft_arc : ell ≤ terminalLeft E hE - 1 := by omega
  have hleft_not : terminalLeft E hE - 1 ∉ E :=
    before_left_not_mem E hE hpos
  have hleft_sign_site :
      patternSign s (site hm (terminalLeft E hE - 1)) = -1 := by
    have hiff := hsign (terminalLeft E hE - 1) hleft_arc
      (by omega : terminalLeft E hE - 1 ≤ R)
    have hne : patternSign s (site hm (terminalLeft E hE - 1)) ≠ 1 := by
      intro hs1
      exact hleft_not (hiff.mpr hs1)
    rcases patternSign_is_sign s (site hm (terminalLeft E hE - 1)) with hs1 | hs1
    · exact (hne hs1).elim
    · exact hs1
  have hright_sign_site :
      patternSign s (site hm (terminalRight E hE)) = 1 := by
    have hiff := hsign (terminalRight E hE) (hsub _ hRmem).1 hright_le_R
    exact hiff.mp hRmem
  have hsite_left :
      site hm (terminalLeft E hE - 1) =
        first ⟨terminalLeft E hE - 1, by
          have hx := hFirst _ hLmem
          omega⟩ := by
    apply Fin.ext
    rw [site_val hm]
    · rfl
    · have hx := hFirst _ hLmem
      omega
  have hsite_right :
      site hm (terminalRight E hE) =
        first ⟨terminalRight E hE, hFirst _ hRmem⟩ := by
    apply Fin.ext
    rw [site_val hm]
    · rfl
    · have hx := hFirst _ hRmem
      omega
  have hleft :
      patternSign s (first ⟨terminalLeft E hE - 1, by
        have hx := hFirst _ hLmem
        omega⟩) = -1 := by
    rw [← hsite_left]
    exact hleft_sign_site
  have hright :
      patternSign s (first ⟨terminalRight E hE, hFirst _ hRmem⟩) = 1 := by
    rw [← hsite_right]
    exact hright_sign_site
  have hg := actual_word_terminal_gain E hE hm hA hgamma hpos hFirst hNewFirst s
    hleft hright hstep hbound hkernel
  rcases hg with ⟨hgHam, hgGain⟩
  let left : Fin m := ⟨terminalLeft E hE - 1, by
    have hx := hFirst _ hLmem
    omega⟩
  let right : Fin m := ⟨terminalRight E hE, hFirst _ hRmem⟩
  refine ⟨left, right, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simpa [left, right] using hgHam
  · simpa [left, right] using hgGain

/- The amplitude used by the genuine finite box is the attained-box amplitude,
not an abstract auxiliary bound.  Consequently the same slide also gives a
nonnegative, nonincreasing true `B`-deficit. -/
theorem eventually_actual_word_terminal_box_gap_on_arc :
    ∀ᶠ m : ℕ in Filter.atTop,
      ∀ (hm : 0 < m) (E : Finset ℕ) (hE : E.Nonempty)
        (ell R : ℕ) (s : SignPattern hm) (gamma : ℝ),
    R < m →
    2 * Real.pi * (R - ell : ℕ) / (2 * m : ℝ) ≤ Real.pi / 12 →
    E ≠ natInterval ell (terminalRight E hE) →
    (∀ x ∈ E, ell ≤ x ∧ x ≤ R) →
    (∀ x, ell ≤ x → x ≤ R →
      (x ∈ E ↔ patternSign s (site hm x) = 1)) →
    0 ≤ gamma →
    (∀ k, terminalLeft E hE ≤ k → k ≤ terminalRight E hE →
      gamma ≤ operator (2 * m)
          (vertex (FiniteBox.amplitude (2 * m)) s -
            patch hm (FiniteBox.amplitude (2 * m)) (gridSites hm E))
          (site hm (k - 1)) -
        operator (2 * m)
          (vertex (FiniteBox.amplitude (2 * m)) s -
            patch hm (FiniteBox.amplitude (2 * m)) (gridSites hm E))
          (site hm k)) →
    ∃ left right : Fin m,
      left.val = terminalLeft E hE - 1 ∧
      right.val = terminalRight E hE ∧
      hamming s (flipTwo s left right) ≤ 2 ∧
      4 * FiniteBox.amplitude (2 * m) * gamma / (2 * m : ℝ) ≤
        normalizedBoxEnergy (operator (2 * m))
            (vertex (FiniteBox.amplitude (2 * m)) (flipTwo s left right)) -
          normalizedBoxEnergy (operator (2 * m))
            (vertex (FiniteBox.amplitude (2 * m)) s) ∧
      0 ≤ B hm - normalizedBoxEnergy (operator (2 * m))
            (vertex (FiniteBox.amplitude (2 * m)) (flipTwo s left right)) ∧
      B hm - normalizedBoxEnergy (operator (2 * m))
            (vertex (FiniteBox.amplitude (2 * m)) (flipTwo s left right)) ≤
        B hm - normalizedBoxEnergy (operator (2 * m))
            (vertex (FiniteBox.amplitude (2 * m)) s) := by
  filter_upwards [eventually_actual_word_terminal_gain_on_arc] with m hgain
  intro hm E hE ell R s gamma hR hspan hnot hEarc hsign hgamma hstep
  have hA : 0 ≤ FiniteBox.amplitude (2 * m) :=
    (FiniteBox.amplitude_pos (by omega)).le
  have hg := hgain hm E hE ell R s (FiniteBox.amplitude (2 * m)) gamma
    hR hspan hnot hEarc hsign hA hgamma hstep
  rcases hg with ⟨left, right, hleft, hright, hHam, hGain⟩
  have hOldBox : vertex (FiniteBox.amplitude (2 * m)) s ∈ Q hm := by
    exact vertex_mem_box hA s
  have hNewBox :
      vertex (FiniteBox.amplitude (2 * m)) (flipTwo s left right) ∈ Q hm := by
    have h := terminal_flip_vertex_box (FiniteBox.amplitude (2 * m)) s left right
    simpa [Q, abs_of_nonneg hA] using h
  have hOldLe := energy_le_B hm hOldBox
  have hNewLe := energy_le_B hm hNewBox
  have hGainNonneg :
      0 ≤ normalizedBoxEnergy (operator (2 * m))
            (vertex (FiniteBox.amplitude (2 * m)) (flipTwo s left right)) -
          normalizedBoxEnergy (operator (2 * m))
            (vertex (FiniteBox.amplitude (2 * m)) s) := by
    have hc :
        0 ≤ 4 * FiniteBox.amplitude (2 * m) * gamma / (2 * m : ℝ) := by
      positivity
    exact hc.trans hGain
  refine ⟨left, right, hleft, hright, hHam, hGain, ?_, ?_⟩
  · linarith
  · linarith

end
end StructuralNote.TerminalSlideUniform

import StructuralNote.SignPatternGridShift
import StructuralNote.SolThreeBlockWord
import StructuralNote.FiniteCompressionConvolutionBase

/-! Reconstruction of a canonical three-block word from three indexed jumps. -/

namespace StructuralNote.ThreeTransitionReconstruction

open Set
open Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier
open StructuralNote.FiniteCompressionRanked
open StructuralNote.FiniteCompressionConvolutionBase
open StructuralNote.SignPatternGridShift
open StructuralNote.SignPatternSymmetry
open StructuralNote.SolThreeBlockWord
noncomputable section

theorem transition_lengths {m L a b c : ℕ}
    (hLa : L ≤ a) (hab : a < b) (hbc : b < c) (hcm : c < L + m) :
    0 < b - a ∧ 0 < c - b ∧ 0 < m + a - c ∧
      (b - a) + (c - b) + (m + a - c) = m := by
  omega

theorem three_transition_reconstruction {m : ℕ} (hm : 0 < m)
    (s : SignPattern hm) {L a b c : ℕ}
    (hLa : L ≤ a) (hab : a < b) (hbc : b < c) (hcm : c < L + m)
    (hpattern : ∀ j ∈ Set.Icc L (L + m),
      patternSign s (site hm j) =
        if j ≤ a then 1 else if j ≤ b then -1 else if j ≤ c then 1 else -1) :
    ∃ hpos : 0 < b - a ∧ 0 < c - b ∧ 0 < m + a - c,
      ∃ hsum : (b - a) + (c - b) + (m + a - c) = m,
        globalNegate (rotatePattern (a + 1) s) =
          threeBlockPattern hm hpos hsum := by
  have hlen := transition_lengths hLa hab hbc hcm
  let r₁ : ℕ := b - a
  let r₂ : ℕ := c - b
  let r₃ : ℕ := m + a - c
  have hpos : 0 < r₁ ∧ 0 < r₂ ∧ 0 < r₃ := by
    dsimp [r₁, r₂, r₃]
    exact ⟨hlen.1, hlen.2.1, hlen.2.2.1⟩
  have hsum : r₁ + r₂ + r₃ = m := by
    dsimp [r₁, r₂, r₃]
    exact hlen.2.2.2
  let u : SignPattern hm := globalNegate (rotatePattern (a + 1) s)
  have hcanonical (j : ℕ) (hj : j < m) :
      patternSign u (site hm j) =
        if j < r₁ then 1 else if j < r₁ + r₂ then -1 else 1 := by
    have hu : patternSign u (site hm j) =
        -patternSign s (site hm (j + (a + 1))) := by
      dsimp [u]
      rw [patternSign_globalNegate, patternSign_rotatePattern_site]
    let q := j + (a + 1)
    by_cases hq : q ≤ L + m
    · have hqmem : q ∈ Set.Icc L (L + m) := by
        constructor
        · dsimp [q]
          omega
        · exact hq
      have hs := hpattern q hqmem
      have hqL : L < q := by
        dsimp [q]
        omega
      have hqa : ¬q ≤ a := by
        dsimp [q]
        omega
      have huq : patternSign u (site hm j) = -patternSign s (site hm q) := by
        simpa [q] using hu
      rw [huq, hs]
      by_cases hqb : q ≤ b
      · have hjr₁ : j < r₁ := by
          dsimp [r₁]
          omega
        have hqc : q ≤ c := by omega
        simp only [if_neg hqa, if_pos hqb, neg_neg]
        rw [if_pos hjr₁]
      · have hjr₁ : ¬j < r₁ := by
          dsimp [r₁]
          omega
        by_cases hqc : q ≤ c
        · have hjr₂ : j < r₁ + r₂ := by
            dsimp [r₁, r₂]
            omega
          simp only [if_neg hqa, if_neg hqb, if_pos hqc]
          rw [if_neg hjr₁, if_pos hjr₂]
        · have hjr₂ : ¬j < r₁ + r₂ := by
            dsimp [r₁, r₂]
            omega
          simp only [if_neg hqa, if_neg hqb, if_neg hqc, neg_neg]
          rw [if_neg hjr₁, if_neg hjr₂]
    · let q' := q - m
      have hq'mem : q' ∈ Set.Icc L (L + m) := by
        constructor
        · dsimp [q, q']
          omega
        · dsimp [q, q']
          omega
      have hs := hpattern q' hq'mem
      have hsite : site hm q = halfTurn hm (site hm q') := by
        dsimp [q, q']
        rw [site_halfTurn]
        congr 1
        omega
      have hqa : r₁ ≤ j := by
        dsimp [r₁, q, q'] at hq hsite hs ⊢
        omega
      have huq : patternSign u (site hm j) = -patternSign s (site hm q) := by
        simpa [q] using hu
      rw [huq, hsite, patternSign_antiperiodic]
      have hq'a : q' ≤ a := by
        dsimp [q, q']
        omega
      have hjr₂ : ¬j < r₁ + r₂ := by
        dsimp [r₁, r₂, q] at hq ⊢
        omega
      have hjr₁ : ¬j < r₁ := by omega
      rw [hs, if_pos hq'a, if_neg hjr₁]
      rw [if_neg hjr₂]
      norm_num
  have hpoint (j : Fin (2 * m)) :
      patternSign u j = patternSign (threeBlockPattern hm hpos hsum) j := by
    by_cases hj : j.val < m
    · have hjsite : site hm j.val = j := by
        apply Fin.ext
        simp [site, Nat.mod_eq_of_lt j.isLt]
      have hc := hcanonical j.val hj
      rw [hjsite] at hc
      have hraw : patternSign (threeBlockPattern hm hpos hsum) j =
          if j.val < r₁ then 1 else if j.val < r₁ + r₂ then -1 else 1 := by
        rw [patternSign_threeBlockPattern]
        by_cases h₁ : j.val < r₁
        · simp [threeBlockRaw, halfValue, hj, Nat.mod_eq_of_lt hj, h₁]
        · by_cases h₂ : j.val < r₁ + r₂
          · simp [threeBlockRaw, halfValue, hj, Nat.mod_eq_of_lt hj, h₁, h₂]
          · simp [threeBlockRaw, halfValue, hj, Nat.mod_eq_of_lt hj, h₁, h₂]
      calc
        patternSign u j = if j.val < r₁ then 1 else if j.val < r₁ + r₂ then -1 else 1 := hc
        _ = patternSign (threeBlockPattern hm hpos hsum) j := hraw.symm
    · let j' : Fin (2 * m) := halfTurn hm j
      have hj' : j'.val < m := (halfTurn_lt_iff hm j).2 hj
      have hhalf : halfTurn hm j' = j := by
        dsimp [j']
        exact SchurLift.halfTurn_involutive hm j
      have huanti := patternSign_antiperiodic u j'
      rw [hhalf] at huanti
      have hrawanti := threeBlockRaw_antiperiodic (r₁ := r₁) (r₂ := r₂) hm j'
      rw [hhalf] at hrawanti
      have hjsite : site hm j'.val = j' := by
        apply Fin.ext
        simp [site, Nat.mod_eq_of_lt j'.isLt]
      have hc0 := hcanonical j'.val hj'
      rw [hjsite] at hc0
      have hraw0 : patternSign (threeBlockPattern hm hpos hsum) j' =
          if j'.val < r₁ then 1 else if j'.val < r₁ + r₂ then -1 else 1 := by
        rw [patternSign_threeBlockPattern]
        by_cases h₁ : j'.val < r₁
        · simp [threeBlockRaw, halfValue, hj', Nat.mod_eq_of_lt hj', h₁]
        · by_cases h₂ : j'.val < r₁ + r₂
          · simp [threeBlockRaw, halfValue, hj', Nat.mod_eq_of_lt hj', h₁, h₂]
          · simp [threeBlockRaw, halfValue, hj', Nat.mod_eq_of_lt hj', h₁, h₂]
      have hc : patternSign u j' = patternSign (threeBlockPattern hm hpos hsum) j' :=
        hc0.trans hraw0.symm
      have hrawj : patternSign (threeBlockPattern hm hpos hsum) j =
          -patternSign (threeBlockPattern hm hpos hsum) j' := by
        rw [patternSign_threeBlockPattern, patternSign_threeBlockPattern]
        exact hrawanti
      calc
        patternSign u j = -patternSign u j' := huanti
        _ = -patternSign (threeBlockPattern hm hpos hsum) j' := by rw [hc]
        _ = patternSign (threeBlockPattern hm hpos hsum) j := hrawj.symm
  have heq : u = threeBlockPattern hm hpos hsum := by
    apply Subtype.ext
    funext j
    have hp := hpoint j
    change boolSign (u.val j) = boolSign ((threeBlockPattern hm hpos hsum).val j) at hp
    cases huj : u.val j <;> cases htj : (threeBlockPattern hm hpos hsum).val j <;>
      simp [boolSign, huj, htj] at hp ⊢ <;>
      norm_num at hp
  exact ⟨hpos, hsum, by simpa [u] using heq⟩

end
end StructuralNote.ThreeTransitionReconstruction

import StructuralNote.SignPatternGridShift

/-! Transport of finite one-transition arcs under grid rotation and global
negation.  The definitions retain only the local transition data needed by
the three-arc assembly. -/

namespace StructuralNote.ArcTransitionTransport

open Set
open Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open StructuralNote.FiniteCompressionRanked
open StructuralNote.SignPatternGridShift
open StructuralNote.SignPatternSymmetry

noncomputable section

def DescendingTransition {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (L R : ℕ) : Prop :=
  ∃ cut ∈ Icc L R, ∀ j ∈ Icc L (R + 1),
    patternSign s (site hm j) = if j ≤ cut then 1 else -1

def AscendingTransition {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (L R : ℕ) : Prop :=
  ∃ cut ∈ Icc L R, ∀ j ∈ Icc L (R + 1),
    patternSign s (site hm j) = if j ≤ cut then -1 else 1

theorem descending_of_rotate {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (k L R : ℕ) :
    DescendingTransition hm (rotatePattern k s) L R →
      DescendingTransition hm s (L + k) (R + k) := by
  intro h
  rcases h with ⟨cut, hcut, htrans⟩
  refine ⟨cut + k, ?_, ?_⟩
  · rcases (mem_Icc.mp hcut) with ⟨hL, hR⟩
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro j hj
    have hjL : L + k ≤ j := (mem_Icc.mp hj).1
    have hjR : j ≤ R + k + 1 := (mem_Icc.mp hj).2
    have hshift : L ≤ j - k ∧ j - k ≤ R + 1 := by
      omega
    have hlocal := htrans (j - k) (mem_Icc.mpr hshift)
    rw [patternSign_rotatePattern_site] at hlocal
    have hsum : j - k + k = j := by omega
    rw [hsum] at hlocal
    by_cases hcutj : j ≤ cut + k
    · have hcutj' : j - k ≤ cut := by omega
      simpa [hcutj, hcutj'] using hlocal
    · have hcutj' : ¬ j - k ≤ cut := by omega
      simpa [hcutj, hcutj'] using hlocal

theorem ascending_of_rotate {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (k L R : ℕ) :
    AscendingTransition hm (rotatePattern k s) L R →
      AscendingTransition hm s (L + k) (R + k) := by
  intro h
  rcases h with ⟨cut, hcut, htrans⟩
  refine ⟨cut + k, ?_, ?_⟩
  · rcases (mem_Icc.mp hcut) with ⟨hL, hR⟩
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro j hj
    have hjL : L + k ≤ j := (mem_Icc.mp hj).1
    have hjR : j ≤ R + k + 1 := (mem_Icc.mp hj).2
    have hshift : L ≤ j - k ∧ j - k ≤ R + 1 := by
      omega
    have hlocal := htrans (j - k) (mem_Icc.mpr hshift)
    rw [patternSign_rotatePattern_site] at hlocal
    have hsum : j - k + k = j := by omega
    rw [hsum] at hlocal
    by_cases hcutj : j ≤ cut + k
    · have hcutj' : j - k ≤ cut := by omega
      simpa [hcutj, hcutj'] using hlocal
    · have hcutj' : ¬ j - k ≤ cut := by omega
      simpa [hcutj, hcutj'] using hlocal

theorem ascending_of_negate {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (L R : ℕ) :
    DescendingTransition hm (globalNegate s) L R →
      AscendingTransition hm s L R := by
  intro h
  rcases h with ⟨cut, hcut, htrans⟩
  refine ⟨cut, hcut, ?_⟩
  intro j hj
  have hlocal := htrans j hj
  rw [patternSign_globalNegate] at hlocal
  by_cases hcutj : j ≤ cut
  · simp only [if_pos hcutj] at hlocal ⊢
    linarith
  · simp only [if_neg hcutj] at hlocal ⊢
    linarith

theorem descending_of_negate {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (L R : ℕ) :
    AscendingTransition hm (globalNegate s) L R →
      DescendingTransition hm s L R := by
  intro h
  rcases h with ⟨cut, hcut, htrans⟩
  refine ⟨cut, hcut, ?_⟩
  intro j hj
  have hlocal := htrans j hj
  rw [patternSign_globalNegate] at hlocal
  by_cases hcutj : j ≤ cut
  · simp only [if_pos hcutj] at hlocal ⊢
    linarith
  · simp only [if_neg hcutj] at hlocal ⊢
    linarith

end
end StructuralNote.ArcTransitionTransport

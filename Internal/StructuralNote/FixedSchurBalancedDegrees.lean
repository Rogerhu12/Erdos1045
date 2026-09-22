import StructuralNote.FixedSchurThreeBlockDegrees
import StructuralNote.FixedSchurWordConnected
import StructuralNote.FixedSchurCyclicEquivariance
import StructuralNote.FiniteWordClassification

/-! The degree counts hold for every balanced word, before choosing an
orientation or a cyclic starting point. -/

namespace StructuralNote.FixedSchurBalancedDegrees

open Erdos1045.EventualExact FiniteBox FourierMultiplier FiniteFourierLift SchurLift
open FixedSchurWordDegrees FixedSchurWordConnected FixedSchurThreeBlockDegrees
open FixedSchurCyclicEquivariance SignPatternSymmetry FiniteWordClassification

noncomputable section

def degreeCount {m : ℕ} (σ : Fin (2 * m) → ℝ) (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun j => (neighbors σ j).card = d)).card

theorem degreeCount_relabel {m : ℕ} (hm : 2 ≤ m)
    (s t : SignPattern (by omega : 0 < m)) (e : Equiv.Perm (Fin (2 * m)))
    (he : ∀ j, e (previous j) = previous (e j))
    (hw : ∀ j, patternSign s j = patternSign t (e j)) (d : ℕ) :
    degreeCount (patternSign s) d = degreeCount (patternSign t) d := by
  classical
  have hd (j : Fin (2 * m)) :
      (neighbors (patternSign s) j).card = (neighbors (patternSign t) (e j)).card := by
    rw [neighbors_card hm _ (patternSign_antiperiodic s),
      neighbors_card hm _ (patternSign_antiperiodic t), hw, hw, he]
  apply Finset.card_bijective e e.bijective
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hd]

theorem successor_previous {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    successor (by omega) (previous j) = j := by
  change cyclicAdvance (cyclicAdvance j (2 * m - 1)) 1 = j
  rw [advance_add, show 2 * m - 1 + 1 = 2 * m by omega]
  apply Fin.ext
  simp only [cyclicAdvance, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

theorem cyclicIndex_previous {m : ℕ} (hm : 0 < m) (k : ℕ) (j : Fin (2 * m)) :
    cyclicIndex (2 * m) k (previous j) = previous (cyclicIndex (2 * m) k j) := by
  apply (finRotate (2 * m)).injective
  rw [SignedPressureRemainder.finRotate_eq_successor (by omega),
    SignedPressureRemainder.finRotate_eq_successor (by omega),
    ← cyclicIndex_successor (by omega), successor_previous hm, successor_previous hm]

theorem degreeCount_rotate {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m)) (k d : ℕ) :
    degreeCount (patternSign (rotatePattern k s)) d = degreeCount (patternSign s) d := by
  apply degreeCount_relabel hm _ _ (cyclicIndex (2 * m) k)
  · exact cyclicIndex_previous (by omega) k
  · intro j
    exact patternSign_rotatePattern k s j

theorem degreeCount_negate {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m)) (d : ℕ) :
    degreeCount (patternSign (globalNegate s)) d = degreeCount (patternSign s) d := by
  let e : Equiv.Perm (Fin (2 * m)) :=
    Equiv.ofBijective (halfTurn (by omega)) (halfTurn_involutive (by omega)).bijective
  apply degreeCount_relabel hm _ _ e
  · intro j
    exact (previous_halfTurn (by omega) j).symm
  · intro j
    change patternSign (globalNegate s) j = patternSign s (halfTurn (by omega) j)
    rw [patternSign_globalNegate, patternSign_antiperiodic]

/-- A balanced word has exactly three leaves and three vertices of degree three. -/
theorem balanced_degree_counts {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m)) (hs : BalancedWord (by omega) s) :
    degreeCount (patternSign s) 1 = 3 ∧ degreeCount (patternSign s) 3 = 3 := by
  obtain ⟨k, a, b, c, hp, hsum, heq, _⟩ := hs
  have he (d : ℕ) : degreeCount (patternSign s) d =
      degreeCount (patternSign (SolThreeBlockWord.threeBlockPattern (by omega) hp hsum)) d := by
    rw [← heq, degreeCount_negate hm, degreeCount_rotate hm]
  constructor
  · rw [he]
    exact exactly_three_leaves hm hp hsum
  · rw [he]
    exact exactly_three_branches hm hp hsum

theorem vertex_degree_cases {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m)) (j : Fin (2 * m)) :
    (neighbors (patternSign s) j).card = 1 ∨
      (neighbors (patternSign s) j).card = 2 ∨ (neighbors (patternSign s) j).card = 3 := by
  rw [neighbors_card hm _ (patternSign_antiperiodic s)]
  split_ifs <;> norm_num

end
end StructuralNote.FixedSchurBalancedDegrees

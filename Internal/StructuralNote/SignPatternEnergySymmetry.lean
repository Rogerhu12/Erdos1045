import StructuralNote.SignPatternSymmetry
import StructuralNote.FiniteBoxEnergySymmetry
import StructuralNote.FixedDualClassificationFinite

/-! Energy and deficit transport for genuine antiperiodic sign patterns. -/

namespace StructuralNote.SignPatternEnergySymmetry

open Erdos1045.EventualExact FourierMultiplier FiniteBox
open SignPatternSymmetry FiniteBoxEnergySymmetry FixedDualClassificationFinite
open SolWordHamming
noncomputable section

theorem vertex_reindex {m : ℕ} {hm : 0 < m} (A : ℝ)
    (e : Equiv.Perm (Fin (2 * m))) (he : halfTurnCommuting hm e) (s : SignPattern hm) :
    vertex A (reindex e he s) = fun j => vertex A s (e j) := rfl

theorem vertex_globalNegate {m : ℕ} {hm : 0 < m} (A : ℝ) (s : SignPattern hm) :
    vertex A (globalNegate s) = fun j => -vertex A s j := by
  funext j
  change A * patternSign (globalNegate s) j = -(A * patternSign s j)
  rw [patternSign_globalNegate, mul_neg]

theorem energy_globalNegate {m : ℕ} {hm : 0 < m} (A : ℝ) (s : SignPattern hm) :
    normalizedBoxEnergy (operator (2 * m)) (vertex A (globalNegate s)) =
      normalizedBoxEnergy (operator (2 * m)) (vertex A s) := by
  rw [vertex_globalNegate, normalizedBoxEnergy_neg (by omega)]

theorem deficit_globalNegate {m : ℕ} (hm : 0 < m) (s : SignPattern hm) :
    deficit hm (globalNegate s) = deficit hm s := by
  unfold deficit
  rw [energy_globalNegate]

theorem energy_reindex_rotate_pow {m : ℕ} {hm : 0 < m} (A : ℝ) (k : ℕ)
    (he : halfTurnCommuting hm ((finRotate (2 * m)) ^ k)) (s : SignPattern hm) :
    normalizedBoxEnergy (operator (2 * m))
        (vertex A (reindex ((finRotate (2 * m)) ^ k) he s)) =
      normalizedBoxEnergy (operator (2 * m)) (vertex A s) := by
  rw [vertex_reindex]
  exact normalizedBoxEnergy_finRotate_iterate (by omega) (vertex A s) k

theorem energy_reindex_rotate_pow_inverse {m : ℕ} {hm : 0 < m} (A : ℝ) (k : ℕ)
    (he : halfTurnCommuting hm ((finRotate (2 * m)) ^ k)) (s : SignPattern hm) :
    normalizedBoxEnergy (operator (2 * m))
        (vertex A (reindex (((finRotate (2 * m)) ^ k).symm) (halfTurnCommuting_symm he) s)) =
      normalizedBoxEnergy (operator (2 * m)) (vertex A s) := by
  have h := energy_reindex_rotate_pow A k he
    (reindex (((finRotate (2 * m)) ^ k).symm) (halfTurnCommuting_symm he) s)
  rw [reindex_inverse] at h
  exact h.symm

/-- An improvement proved after a cyclic relabeling gives an improvement of
the original word with the same number of changed independent signs. -/
theorem improvement_transport_rotate {m : ℕ} {hm : 0 < m} (A : ℝ) (k : ℕ)
    (he : halfTurnCommuting hm ((finRotate (2 * m)) ^ k)) (s : SignPattern hm)
    {η : ℝ} {d : ℕ}
    (h : ∃ t : SignPattern hm,
      hamming (reindex ((finRotate (2 * m)) ^ k) he s) t ≤ d ∧
      η ≤ normalizedBoxEnergy (operator (2 * m)) (vertex A t) -
        normalizedBoxEnergy (operator (2 * m)) (vertex A (reindex ((finRotate (2 * m)) ^ k) he s))) :
    ∃ t : SignPattern hm, hamming s t ≤ d ∧
      η ≤ normalizedBoxEnergy (operator (2 * m)) (vertex A t) -
        normalizedBoxEnergy (operator (2 * m)) (vertex A s) := by
  obtain ⟨t, hd, hg⟩ := h
  let e := (finRotate (2 * m)) ^ k
  refine ⟨reindex e.symm (halfTurnCommuting_symm he) t, ?_, ?_⟩
  · have hh := hamming_reindex e he s (reindex e.symm (halfTurnCommuting_symm he) t)
    rw [reindex_inverse] at hh
    exact hh ▸ hd
  · rw [energy_reindex_rotate_pow_inverse A k he]
    rwa [energy_reindex_rotate_pow A k he] at hg

theorem energy_rotatePattern {m : ℕ} {hm : 0 < m} (A : ℝ) (k : ℕ)
    (s : SignPattern hm) :
    normalizedBoxEnergy (operator (2 * m)) (vertex A (rotatePattern k s)) =
      normalizedBoxEnergy (operator (2 * m)) (vertex A s) :=
  energy_reindex_rotate_pow A k (halfTurnCommuting_finRotate_pow hm k) s

theorem deficit_rotatePattern {m : ℕ} (hm : 0 < m) (k : ℕ) (s : SignPattern hm) :
    deficit hm (rotatePattern k s) = deficit hm s := by
  unfold deficit
  rw [energy_rotatePattern]

theorem improvement_transport_rotatePattern {m : ℕ} {hm : 0 < m} (A : ℝ) (k : ℕ)
    (s : SignPattern hm) {η : ℝ} {d : ℕ}
    (h : ∃ t : SignPattern hm, hamming (rotatePattern k s) t ≤ d ∧
      η ≤ normalizedBoxEnergy (operator (2 * m)) (vertex A t) -
        normalizedBoxEnergy (operator (2 * m)) (vertex A (rotatePattern k s))) :
    ∃ t : SignPattern hm, hamming s t ≤ d ∧
      η ≤ normalizedBoxEnergy (operator (2 * m)) (vertex A t) -
        normalizedBoxEnergy (operator (2 * m)) (vertex A s) :=
  improvement_transport_rotate A k (halfTurnCommuting_finRotate_pow hm k) s h

theorem improvement_transport_globalNegate {m : ℕ} {hm : 0 < m} (A : ℝ)
    (s : SignPattern hm) {η : ℝ} {d : ℕ}
    (h : ∃ t : SignPattern hm, hamming (globalNegate s) t ≤ d ∧
      η ≤ normalizedBoxEnergy (operator (2 * m)) (vertex A t) -
        normalizedBoxEnergy (operator (2 * m)) (vertex A (globalNegate s))) :
    ∃ t : SignPattern hm, hamming s t ≤ d ∧
      η ≤ normalizedBoxEnergy (operator (2 * m)) (vertex A t) -
        normalizedBoxEnergy (operator (2 * m)) (vertex A s) := by
  obtain ⟨t, hd, hg⟩ := h
  refine ⟨globalNegate t, ?_, ?_⟩
  · have hh : hamming (globalNegate s) t = hamming s (globalNegate t) := by
      unfold hamming
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, patternSign_globalNegate]
      constructor <;> intro h he <;> apply h <;> linarith
    exact hh ▸ hd
  · rw [energy_globalNegate]
    rwa [energy_globalNegate] at hg

end
end StructuralNote.SignPatternEnergySymmetry

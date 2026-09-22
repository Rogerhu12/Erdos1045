import StructuralNote.FixedSchurSimpleGraph

/-! Removing the three leaves leaves a connected graph of degree two. -/

namespace StructuralNote.FixedSchurNonleafGraph

open Erdos1045.EventualExact FiniteBox FourierMultiplier SchurLift
open FixedSchurWordDegrees FixedSchurWordConnected FixedSchurBalancedDegrees
open FixedSchurSimpleGraph FixedSchurChartGeometry

noncomputable section

theorem leaf_neighbor_iff {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m)) (j : Fin (2 * m))
    (hj : (neighbors (patternSign s) j).card = 1) (i : Fin (2 * m)) :
    WordEdge (patternSign s) i j ↔ i = halfTurn (by omega) j := by
  classical
  obtain ⟨hp, hn⟩ := (degree_one_iff hm s j).1 hj
  rw [wordEdge_iff hm _ (patternSign_antiperiodic s)]
  simp only [hp, hn, show (1 : ℝ) ≠ -1 by norm_num,
    show (-1 : ℝ) ≠ 1 by norm_num, and_false, or_false]
  rfl

theorem leaf_halfTurn_iff {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m)) (j : Fin (2 * m)) :
    (neighbors (patternSign s) (halfTurn (by omega) j)).card = 1 ↔
      (neighbors (patternSign s) j).card = 3 := by
  rw [degree_one_iff hm, degree_three_iff hm, previous_halfTurn,
    patternSign_antiperiodic, patternSign_antiperiodic]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem neighbor_leaf_iff {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m)) (i j : Fin (2 * m))
    (hij : WordEdge (patternSign s) i j) :
    (neighbors (patternSign s) i).card = 1 ↔
      i = halfTurn (by omega) j ∧ (neighbors (patternSign s) j).card = 3 := by
  constructor
  · intro hi
    have he := (leaf_neighbor_iff hm s i hi j).1 (wordEdge_symmetric hm _ hij)
    have hj : i = halfTurn (by omega) j := by
      rw [he, halfTurn_involutive (by omega) i]
    exact ⟨hj, (leaf_halfTurn_iff hm s j).1 (hj ▸ hi)⟩
  · rintro ⟨rfl, hj⟩
    exact (leaf_halfTurn_iff hm s j).2 hj

theorem nonleaf_neighbors_eq {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m)) (j : Fin (2 * m)) :
    (neighbors (patternSign s) j).filter (fun i => (neighbors (patternSign s) i).card ≠ 1) =
      if (neighbors (patternSign s) j).card = 3 then
        (neighbors (patternSign s) j).erase (halfTurn (by omega) j)
      else neighbors (patternSign s) j := by
  classical
  ext i
  by_cases hd : (neighbors (patternSign s) j).card = 3
  · rw [if_pos hd]
    simp only [Finset.mem_filter, Finset.mem_erase]
    by_cases hi : i ∈ neighbors (patternSign s) j
    · have hij : WordEdge (patternSign s) i j := (Finset.mem_filter.mp hi).2
      simp only [hi, true_and, and_true]
      exact not_congr (by simpa only [hd, and_true] using neighbor_leaf_iff hm s i j hij)
    · simp [hi]
  · rw [if_neg hd]
    simp only [Finset.mem_filter]
    by_cases hi : i ∈ neighbors (patternSign s) j
    · have hij : WordEdge (patternSign s) i j := (Finset.mem_filter.mp hi).2
      simp only [hi, true_and]
      exact iff_true_intro (fun he => hd ((neighbor_leaf_iff hm s i j hij).1 he).2)
    · simp [hi]

theorem nonleaf_neighbors_card {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m)) (j : Fin (2 * m))
    (hj : (neighbors (patternSign s) j).card ≠ 1) :
    ((neighbors (patternSign s) j).filter
      (fun i => (neighbors (patternSign s) i).card ≠ 1)).card = 2 := by
  classical
  rw [nonleaf_neighbors_eq hm s j]
  by_cases hthree : (neighbors (patternSign s) j).card = 3
  · rw [if_pos hthree, Finset.card_erase_of_mem, hthree]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, matching_edge hm s j⟩
  · rw [if_neg hthree]
    exact ((vertex_degree_cases hm s j).resolve_left hj).resolve_right hthree

theorem induced_degree_two {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m))
    (j : {j : Fin (2 * m) | (neighbors (patternSign s) j).card ≠ 1}) :
    ((graph hm (patternSign s)).induce
      {j | (neighbors (patternSign s) j).card ≠ 1}).degree j = 2 := by
  classical
  let S : Set (Fin (2 * m)) := {j | (neighbors (patternSign s) j).card ≠ 1}
  have hmap := (graph hm (patternSign s)).map_neighborFinset_induce (s := S) j
  have he : (graph hm (patternSign s)).neighborFinset j ∩ S.toFinset =
      (neighbors (patternSign s) j).filter (fun i => (neighbors (patternSign s) i).card ≠ 1) := by
    rw [graph_neighborFinset]
    ext i
    simp only [Finset.mem_inter, Set.mem_toFinset, S, Set.mem_ofPred_eq, Finset.mem_filter]
  rw [he] at hmap
  have hc := congrArg Finset.card hmap
  rw [Finset.card_map, nonleaf_neighbors_card hm s j j.property] at hc
  exact hc

end
end StructuralNote.FixedSchurNonleafGraph

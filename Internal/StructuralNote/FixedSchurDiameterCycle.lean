import StructuralNote.FixedSchurNonleafGraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-! The nonleaf diameter graph is one cycle, and its length is n-3 for a
balanced word. The cycle contains every edge of the induced graph. -/

namespace StructuralNote.FixedSchurDiameterCycle

open Erdos1045.EventualExact FiniteBox FourierMultiplier SchurLift
open FixedSchurWordDegrees FixedSchurBalancedDegrees FixedSchurSimpleGraph
open FixedSchurNonleafGraph FiniteWordClassification

noncomputable section

theorem finite_degree_two_cycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Preconnected)
    (hd : ∀ v, G.degree v = 2) (v : V) :
    ∃ p : G.Walk v v, p.IsHamiltonianCycle ∧
      ∀ a b, p.toSubgraph.Adj a b ↔ G.Adj a b := by
  classical
  have hc : G.IsCycles := by
    intro w _
    rw [Set.ncard_eq_toFinset_card']
    exact hd w
  have hn : (G.neighborSet v).Nonempty :=
    (G.degree_pos_iff_nonempty).1 (by rw [hd]; norm_num)
  have hv : v ∈ (G.connectedComponentMk v).supp := rfl
  obtain ⟨p, hp, hverts⟩ := hc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv hn
  have hall (w : V) : w ∈ p.toSubgraph.verts := by
    rw [hverts, SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq]
    exact hG w v
  have hmem (w : V) : w ∈ p.support := p.mem_verts_toSubgraph.mp (hall w)
  have htail (w : V) : w ∈ p.support.tail := by
    by_cases hw : w = v
    · subst w
      exact p.end_mem_tail_support hp.not_nil
    · have hh := hmem w
      rw [← p.cons_tail_support, List.mem_cons] at hh
      exact hh.resolve_left hw
  have hHamilton : p.IsHamiltonianCycle := by
    refine ⟨hp, hp.isPath_tail.isHamiltonian_of_mem ?_⟩
    intro w
    rw [p.support_tail_of_not_nil hp.not_nil]
    exact htail w
  exact ⟨p, hHamilton, fun a b => hp.adj_toSubgraph_iff_of_isCycles hc (hall a) b⟩

theorem nonleaf_card {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m)) (hs : BalancedWord (by omega) s) :
    Fintype.card {j : Fin (2 * m) // (neighbors (patternSign s) j).card ≠ 1} = 2 * m - 3 := by
  classical
  have hleaf : Fintype.card {j : Fin (2 * m) // (neighbors (patternSign s) j).card = 1} = 3 := by
    calc
      _ = (Finset.univ.filter (fun j => (neighbors (patternSign s) j).card = 1)).card :=
        Fintype.card_of_subtype _ (by intro j; simp)
      _ = 3 := (balanced_degree_counts hm s hs).1
  rw [Fintype.card_subtype_compl, Fintype.card_fin, hleaf]

theorem nonleaf_nonempty {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m)) :
    Nonempty {j : Fin (2 * m) // (neighbors (patternSign s) j).card ≠ 1} := by
  let j : Fin (2 * m) := ⟨0, by omega⟩
  by_cases hj : (neighbors (patternSign s) j).card = 1
  · refine ⟨⟨halfTurn (by omega) j, ?_⟩⟩
    rw [leaf_partner_degree_three hm s j hj]
    norm_num
  · exact ⟨⟨j, hj⟩⟩

/-- After deleting the three leaves, the entire remaining diameter graph is
one cycle of length n-3, not merely a graph containing such a cycle. -/
theorem balanced_diameter_cycle {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m)) (hs : BalancedWord (by omega) s) :
    let G := (graph hm (patternSign s)).induce
      {j | (neighbors (patternSign s) j).card ≠ 1}
    ∃ v, ∃ p : G.Walk v v, p.IsHamiltonianCycle ∧ p.length = 2 * m - 3 ∧
      ∀ a b, p.toSubgraph.Adj a b ↔ G.Adj a b := by
  classical
  dsimp only
  obtain ⟨v⟩ := nonleaf_nonempty hm s
  obtain ⟨p, hp, he⟩ := finite_degree_two_cycle _ (nonleaf_graph_preconnected hm s)
    (induced_degree_two hm s) v
  exact ⟨v, p, hp, hp.length_eq.trans (nonleaf_card hm s hs), he⟩

end
end StructuralNote.FixedSchurDiameterCycle

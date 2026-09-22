import Erdos1045.Statement
import StructuralNote.RewrittenGeometricCharacterization

open StructuralNote

/-! Bridge from the implementation modules to the dependency-free public
geometric statement. -/

namespace Erdos1045.Internal.Geometry

open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open FixedSchurChartGeometry FixedSchurSimpleGraph
open FixedSchurCanonicalWordSymmetry FixedSchurReflectionEquivariance
open FixedSchurCyclicEquivariance FixedSchurActualDiameterGraph
open MatchingActivityRadialIntegration
open SolThreeBlockWord
open scoped BigOperators Topology

noncomputable section

theorem canonicalSign_negative_iff {m : ℕ} (hm : 3 ≤ m)
    (j : Fin (2 * m)) :
    patternSign (canonicalPattern hm) j = -1 ↔
      Statement.canonicalNegative m j := by
  rw [canonicalPattern, patternSign_threeBlockPattern]
  unfold threeBlockRaw halfValue Statement.canonicalNegative
  change
    (if j.val < m then
      (if j.val % m < symmetricOuter m ∨
          symmetricOuter m + symmetricMiddle m ≤ j.val % m then 1 else -1)
    else
      -(if j.val % m < symmetricOuter m ∨
          symmetricOuter m + symmetricMiddle m ≤ j.val % m then 1 else -1)) = -1 ↔
    (if j.val < m then
      symmetricOuter m ≤ j.val % m ∧
        j.val % m < symmetricOuter m + symmetricMiddle m
    else
      j.val % m < symmetricOuter m ∨
        symmetricOuter m + symmetricMiddle m ≤ j.val % m)
  by_cases hj : j.val < m
  · by_cases hs : j.val % m < symmetricOuter m ∨
        symmetricOuter m + symmetricMiddle m ≤ j.val % m
    · have hn : ¬(symmetricOuter m ≤ j.val % m ∧
          j.val % m < symmetricOuter m + symmetricMiddle m) := by omega
      norm_num [hj, hs, hn]
    · have hy : symmetricOuter m ≤ j.val % m ∧
          j.val % m < symmetricOuter m + symmetricMiddle m := by omega
      norm_num [hj, hs, hy]
  · by_cases hs : j.val % m < symmetricOuter m ∨
        symmetricOuter m + symmetricMiddle m ≤ j.val % m <;>
      norm_num [hj, hs]

local instance canonicalNegative_decidable (m : ℕ) (j : Fin (2 * m)) :
    Decidable (Statement.canonicalNegative m j) := by
  unfold Statement.canonicalNegative
  infer_instance

theorem canonicalSign_eq {m : ℕ} (hm : 3 ≤ m) :
    (fun j : Fin (2 * m) =>
      if Statement.canonicalNegative m j then (-1 : ℝ) else 1) =
      patternSign (canonicalPattern hm) := by
  classical
  funext j
  by_cases hn : Statement.canonicalNegative m j
  · simp only [if_pos hn]
    exact (canonicalSign_negative_iff hm j).2 hn |>.symm
  · simp only [if_neg hn]
    rcases patternSign_is_sign (canonicalPattern hm) j with hp | hneg
    · exact hp.symm
    · exact (hn ((canonicalSign_negative_iff hm j).1 hneg)).elim

private theorem canonicalGraph_adj_iff {m : ℕ} (hm : 3 ≤ m)
    (i j : Fin (2 * m)) :
    (graph (show 2 ≤ m by omega) (patternSign (canonicalPattern hm))).Adj i j ↔
      Statement.CanonicalEvenDiameterAdj hm i j := by
  change WordEdge (patternSign (canonicalPattern hm)) j i ↔ _
  rw [wordEdge_generated (show 2 ≤ m by omega)]
  rw [canonicalSign_negative_iff hm i, canonicalSign_negative_iff hm j]
  rfl

private theorem reflectionIndex_eq_vertexReflection {n : ℕ} (hn : 0 < n)
    (j : Fin n) :
    Statement.reflectionIndex hn j = vertexReflection n j := by
  let _ : NeZero n := ⟨hn.ne'⟩
  apply Fin.ext
  simp only [Statement.reflectionIndex, vertexReflection_apply, Fin.val_neg]
  by_cases hj : j = 0
  · subst j
    simp
  · have hjv : j.val ≠ 0 := by
      intro h
      apply hj
      exact Fin.ext h
    rw [if_neg hj]
    rw [Nat.mod_eq_of_lt (by omega : n - j.val < n)]

private theorem cyclicShiftIndex_eq_cyclicIndex {m k : ℕ} (hm : 0 < m)
    (j : Fin (2 * m)) :
    Statement.cyclicShiftIndex (n := 2 * m) (by omega) k j =
      cyclicIndex (2 * m) k j := by
  apply Fin.ext
  exact FixedSchurCanonicalWordSymmetry.cyclicIndex_even_val hm k j
    |>.symm

private noncomputable def publicEvenGeometry_of_internal {m : ℕ}
    {z : Statement.Points (2 * m)}
    (g : RewrittenGeometricCharacterization.EvenGeometry m z) :
    Statement.EvenGeometry m z := by
  refine {
    large := g.large
    graphRelabeling := g.graphRelabeling
    graph_eq := ?_
    symmetryRelabeling := g.symmetryRelabeling
    reflectionCenter := g.reflectionCenter
    reflectionDirection := g.reflectionDirection
    reflectionDirection_unit := g.reflectionDirection_unit
    reflection := ?_
    thirdTurn := ?_ }
  · intro i j
    have h := congrArg (fun G : SimpleGraph (Fin (2 * m)) => G.Adj i j) g.graph_eq
    exact (Iff.of_eq h).trans (canonicalGraph_adj_iff g.large i j)
  · intro j
    simpa only [Statement.planeReflection,
      FixedSchurActualEuclideanSymmetry.planeReflection,
      reflectionIndex_eq_vertexReflection] using g.reflection j
  · intro hdiv
    have hm0 : 0 < m := lt_of_lt_of_le (by omega : 0 < 3) g.large
    have ht := g.thirdTurn hdiv
    dsimp only at ht ⊢
    refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_⟩
    intro j
    simpa only [Statement.regularRoot, Erdos1045.LocalPhase.regularRoot,
      Statement.rotationAbout, FixedSchurActualEuclideanSymmetry.rotationAbout,
      Statement.centroid, MatchingActivityRadialIntegration.average,
      cyclicShiftIndex_eq_cyclicIndex hm0] using ht.2.2.2 j

end
end Erdos1045.Internal.Geometry

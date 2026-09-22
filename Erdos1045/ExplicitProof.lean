import Erdos1045.ExplicitStatement
import Erdos1045.Internal.Algebraic
import StructuralNote.ExplicitEvenNumerical

/-! Proof of the concrete-threshold even-order statement. -/
namespace Erdos1045.Internal.Explicit
open StructuralNote

open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open FixedSchurChartGeometry FixedSchurSimpleGraph
open FixedSchurCanonicalWordSymmetry FixedSchurReflectionEquivariance
open FixedSchurCyclicEquivariance FixedSchurActualDiameterGraph
open MatchingActivityRadialIntegration
open SolThreeBlockWord
open scoped BigOperators Topology

open Erdos1045.Internal.Geometry
noncomputable section


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


theorem explicitEvenClaims : Internal.EvenThresholdClaims := by
  intro m hn
  have hN : ExplicitEvenThreshold.orderThreshold ≤ 2 * m :=
    ExplicitEvenNumerical.orderThreshold_le_concrete.trans hn
  obtain ⟨c⟩ := ExplicitEvenThreshold.certificate hN
  let p : Statement.Algebraic.Certificate m := Algebraic.publicCertificate_of_internal c
  refine ⟨?_, ?_, ?_, ⟨p⟩⟩
  · exact ⟨Statement.Algebraic.configuration (by have := p.large; omega)
      (Statement.Algebraic.canonicalHalfSign m) (Statement.Algebraic.coordinates p.root), p.extremal⟩
  · intro z w hz hw
    exact ExplicitEvenThreshold.actual_extremizers_unique hN hz hw
  · intro z hz
    obtain ⟨g⟩ := ExplicitEvenThreshold.even_geometry hN hz
    exact ⟨publicEvenGeometry_of_internal g⟩

end
end Erdos1045.Internal.Explicit

namespace Erdos1045

/-- Even-order rigid uniqueness, diameter geometry, and the selected algebraic branch above `2^(10^120)`. -/
theorem explicit_even : Internal.EvenThresholdClaims :=
  Internal.Explicit.explicitEvenClaims

end Erdos1045

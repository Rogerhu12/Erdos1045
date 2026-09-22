import StructuralNote.FixedSchurActualRigidEquivalence
import StructuralNote.FixedSchurCycleArcPartition

/-! The complete diameter graph of an actual extremizer, transported through
the genuine rigid normalization to the canonical balanced word graph. -/

namespace StructuralNote.FixedSchurActualDiameterGraph

open Complex Filter
open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox Erdos1045.EventualExact.FourierMultiplier
open CommonDomainClosure FixedSchurChart FixedSchurEquationSmooth FixedSchurChartSmooth
open FixedSchurChartGeometry
open FixedSchurActualCanonicalEntry FixedSchurActualRigidEquivalence
open FixedSchurCanonicalWordSymmetry FixedSchurBalancedAlignment
open FixedSchurWordDegrees FixedSchurWordConnected
open FixedSchurSimpleGraph FixedSchurBalancedDegrees FixedSchurNonleafGraph
open FixedSchurDiameterCycle FixedSchurCycleArcLengths FixedSchurCycleArcPartition
open FiniteWordClassification SolThreeBlockWord IntegerBalance SignPatternSymmetry
open scoped Topology

noncomputable section

/-- The graph whose edges are exactly the diameter pairs of a configuration. -/
def diameterGraph {n : ℕ} (z : Points n) : SimpleGraph (Fin n) where
  Adj i j := ‖z i - z j‖ = 2
  symm := ⟨by
    intro i j h
    rwa [norm_sub_rev]⟩
  loopless := ⟨by
    intro i
    simp⟩

/-- Pull the actual diameter graph back along a relabeling. -/
def relabeledDiameterGraph {n : ℕ} (z : Points n) (π : Equiv.Perm (Fin n)) :
    SimpleGraph (Fin n) where
  Adj i j := ‖z (π i) - z (π j)‖ = 2
  symm := ⟨by
    intro i j h
    rwa [norm_sub_rev]⟩
  loopless := ⟨by
    intro i
    simp⟩

instance diameterGraph_decidable {n : ℕ} (z : Points n) :
    DecidableRel (diameterGraph z).Adj := Classical.decRel _

instance relabeledDiameterGraph_decidable {n : ℕ} (z : Points n)
    (π : Equiv.Perm (Fin n)) : DecidableRel (relabeledDiameterGraph z π).Adj :=
  Classical.decRel _

/-- An explicit finite neighbor set, independent of typeclass choices for a
finite graph's adjacency relation. -/
noncomputable def finiteNeighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) (j : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun i => G.Adj j i)

noncomputable def finiteDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (j : V) : ℕ :=
  (finiteNeighbors G j).card

@[simp] theorem finiteNeighbors_wordGraph {m : ℕ} (hm : 2 ≤ m)
    (σ : Fin (2 * m) → ℝ) (j : Fin (2 * m)) :
    finiteNeighbors (graph hm σ) j = neighbors σ j := by
  classical
  ext i
  simp only [finiteNeighbors, neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

@[simp] theorem finiteDegree_wordGraph {m : ℕ} (hm : 2 ≤ m)
    (σ : Fin (2 * m) → ℝ) (j : Fin (2 * m)) :
    finiteDegree (graph hm σ) j = (neighbors σ j).card := by
  rw [finiteDegree, finiteNeighbors_wordGraph]

theorem directRigid_diameterGraph {n : ℕ} {z w : Points n}
    { π : Equiv.Perm (Fin n)} {a b : ℂ} (hb : ‖b‖ = 1)
    (hzw : ∀ j, z (π j) = a + b * w j) :
    relabeledDiameterGraph z π = diameterGraph w := by
  ext i j
  change (‖z (π i) - z (π j)‖ = 2) ↔ ‖w i - w j‖ = 2
  rw [hzw i, hzw j]
  have he : a + b * w i - (a + b * w j) = b * (w i - w j) := by ring
  rw [he, norm_mul, hb, one_mul]

theorem canonicalPattern_balanced {m : ℕ} (hm : 3 ≤ m) :
    BalancedWord (by omega) (canonicalPattern hm) := by
  refine ⟨m, symmetricOuter m, symmetricMiddle m, symmetricOuter m,
    symmetric_pos hm, symmetric_sum m, ?_, symmetric_balanced m⟩
  rw [rotatePattern_halfPeriod, globalNegate_involutive]
  rfl

theorem canonical_configuration_diameterGraph {m : ℕ} (hm : 3 ≤ m)
    (x : SchurParameters m)
    (hgeo : GeometricProperties (by omega) (canonicalPattern hm) x.1 x.2) :
    diameterGraph (configuration (by omega) (canonicalPattern hm) x.1 x.2) =
      graph (by omega) (patternSign (canonicalPattern hm)) := by
  ext i j
  change (‖configuration (by omega) (canonicalPattern hm) x.1 x.2 i -
    configuration (by omega) (canonicalPattern hm) x.1 x.2 j‖ = 2) ↔
      WordEdge (patternSign (canonicalPattern hm)) j i
  rw [hgeo.graph]
  constructor <;> intro h
  · exact wordEdge_symmetric (m := m) (by omega)
      (patternSign (canonicalPattern hm)) h
  · exact wordEdge_symmetric (m := m) (by omega)
      (patternSign (canonicalPattern hm)) h

/-- The transported graph has exactly three leaves and three branch vertices;
every other vertex has degree two. -/
theorem canonical_diameter_degree_structure {m : ℕ} (hm : 3 ≤ m)
    (G : SimpleGraph (Fin (2 * m)))
    (hG : G = graph (by omega) (patternSign (canonicalPattern hm))) :
    (Finset.univ.filter (fun j => finiteDegree G j = 1)).card = 3 ∧
      (Finset.univ.filter (fun j => finiteDegree G j = 3)).card = 3 ∧
      (∀ j, finiteDegree G j = 1 ∨ finiteDegree G j = 2 ∨ finiteDegree G j = 3) ∧
      (∀ j, finiteDegree G j = 1 →
        G.Adj j (halfTurn (by omega) j) ∧
          finiteDegree G (halfTurn (by omega) j) = 3) := by
  subst G
  have hb := canonicalPattern_balanced hm
  have hc := balanced_degree_counts (show 2 ≤ m by omega) (canonicalPattern hm) hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [degreeCount, finiteDegree_wordGraph] using hc.1
  · simpa only [degreeCount, finiteDegree_wordGraph] using hc.2
  · intro j
    simpa only [finiteDegree_wordGraph] using
      (vertex_degree_cases (show 2 ≤ m by omega) (canonicalPattern hm) j)
  · intro j hj
    have hj' : (neighbors (patternSign (canonicalPattern hm)) j).card = 1 := by
      simpa only [finiteDegree_wordGraph] using hj
    constructor
    · change WordEdge (patternSign (canonicalPattern hm)) (halfTurn (by omega) j) j
      exact matching_edge (show 2 ≤ m by omega) (canonicalPattern hm) j
    · simpa only [finiteDegree_wordGraph] using
        (leaf_partner_degree_three (show 2 ≤ m by omega)
          (canonicalPattern hm) j hj')

/-- Deleting the three leaves from the transported actual graph leaves one
simple cycle of length `2*m-3`, and that cycle contains every remaining edge. -/
theorem canonical_diameter_nonleaf_cycle {m : ℕ} (hm : 3 ≤ m)
    (G : SimpleGraph (Fin (2 * m)))
    (hG : G = graph (by omega) (patternSign (canonicalPattern hm))) :
    let H := G.induce
      {j | (neighbors (patternSign (canonicalPattern hm)) j).card ≠ 1}
    ∃ v, ∃ p : H.Walk v v, p.IsHamiltonianCycle ∧ p.length = 2 * m - 3 ∧
      ∀ a b, p.toSubgraph.Adj a b ↔ H.Adj a b := by
  subst G
  exact balanced_diameter_cycle (show 2 ≤ m by omega) (canonicalPattern hm)
    (canonicalPattern_balanced hm)

/-- The three branch-to-branch arcs in a transported three-block graph are
genuine simple paths, with the exact manuscript lengths `2*r_i-1`. -/
theorem transported_threeBlock_arcs {m a b c : ℕ} (hm : 2 ≤ m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m)
    (G : SimpleGraph (Fin (2 * m)))
    (hG : G = graph hm (patternSign (threeBlockPattern (by omega) hp hs))) :
    let s := threeBlockPattern (by omega) hp hs
    let S : Set (Fin (2 * m)) :=
      {x | (neighbors (patternSign s) x).card ≠ 1}
    let H := G.induce S
    let A : Fin (2 * m) := ⟨a, by omega⟩
    let B : Fin (2 * m) := ⟨m, by omega⟩
    let C : Fin (2 * m) := ⟨m + a + b, by omega⟩
    ∃ hA : (neighbors (patternSign s) A).card ≠ 1,
      ∃ hB : (neighbors (patternSign s) B).card ≠ 1,
        ∃ hC : (neighbors (patternSign s) C).card ≠ 1,
          (∃ p : H.Walk ⟨B, hB⟩ ⟨A, hA⟩,
            p.IsPath ∧ (∀ x, x ∈ p.support ↔ ArcSupport (by omega) B a x.1) ∧
              p.length = 2 * a - 1) ∧
          (∃ p : H.Walk ⟨A, hA⟩ ⟨C, hC⟩,
            p.IsPath ∧ (∀ x, x ∈ p.support ↔ ArcSupport (by omega) A b x.1) ∧
              p.length = 2 * b - 1) ∧
          (∃ p : H.Walk ⟨C, hC⟩ ⟨B, hB⟩,
            p.IsPath ∧ (∀ x, x ∈ p.support ↔ ArcSupport (by omega) C c x.1) ∧
              p.length = 2 * c - 1) := by
  subst G
  exact threeBlock_nonleaf_arc_lengths hm hp hs

/-- The three displayed arcs cover every nonleaf and meet pairwise only at
their prescribed common branch endpoint. -/
theorem canonical_diameter_arc_partition {m : ℕ} (hm : 3 ≤ m)
    (G : SimpleGraph (Fin (2 * m)))
    (hG : G = graph (by omega) (patternSign (canonicalPattern hm))) :
    let a := symmetricOuter m
    let b := symmetricMiddle m
    let c := symmetricOuter m
    let A : Fin (2 * m) := ⟨a, by
      have hs := symmetric_sum m
      have hp := symmetric_pos hm
      omega⟩
    let B : Fin (2 * m) := ⟨m, by omega⟩
    let C : Fin (2 * m) := ⟨m + a + b, by
      have hs := symmetric_sum m
      have hp := symmetric_pos hm
      omega⟩
    (∀ x, (ArcSupport (by omega) B a x ∨ ArcSupport (by omega) A b x ∨
      ArcSupport (by omega) C c x) ↔ finiteDegree G x ≠ 1) ∧
    (∀ x, (ArcSupport (by omega) B a x ∧ ArcSupport (by omega) A b x) ↔ x = A) ∧
    (∀ x, (ArcSupport (by omega) A b x ∧ ArcSupport (by omega) C c x) ↔ x = C) ∧
    (∀ x, (ArcSupport (by omega) C c x ∧ ArcSupport (by omega) B a x) ↔ x = B) := by
  subst G
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simpa only [canonicalPattern, finiteDegree_wordGraph] using
      (arcs_cover_nonleaves (show 2 ≤ m by omega) (symmetric_pos hm)
        (symmetric_sum m) x)
  · exact first_second_intersection (symmetric_pos hm) (symmetric_sum m)
  · exact second_third_intersection (symmetric_pos hm) (symmetric_sum m)
  · exact third_first_intersection (symmetric_pos hm) (symmetric_sum m)

/-- Every sufficiently large actual extremizer has, after its genuine rigid
relabeling, exactly the canonical balanced word graph as its diameter graph. -/
theorem eventual_actual_extremizer_diameterGraph :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 3 ≤ m) (x : SchurParameters m) (π : Equiv.Perm (Fin (2 * m)))
        (a b : ℂ),
        CanonicalRepresentative hm z x ∧ ‖b‖ = 1 ∧
        (∀ j, z (π j) = a + b *
          configuration (by omega) (canonicalPattern hm) x.1 x.2 j) ∧
        relabeledDiameterGraph z π =
          graph (by omega) (patternSign (canonicalPattern hm)) := by
  obtain ⟨m₀, hentry⟩ := eventual_actual_extremizer_canonical_directRigid
  obtain ⟨m₁, hgeo⟩ := eventually_atTop.1 eventual_geometric_properties
  refine ⟨max m₀ m₁, ?_⟩
  intro m hm z hz
  obtain ⟨hm3, x, hx, henergy, π, a, b, hb, hrigid⟩ := hentry m (by omega) z hz
  have hg := hgeo m (by omega) (by omega) (canonicalPattern hm3) x.1 x.2 hx.1
  refine ⟨hm3, x, π, a, b, hx, hb, hrigid, ?_⟩
  rw [directRigid_diameterGraph hb hrigid]
  exact canonical_configuration_diameterGraph hm3 x hg

end
end StructuralNote.FixedSchurActualDiameterGraph

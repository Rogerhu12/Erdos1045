import StructuralNote.RewrittenMaxima
import StructuralNote.FixedSchurActualEuclideanSymmetry

/-! A public geometric form of Theorem 1.1.

The even-order record keeps the actual relabeled diameter graph and the
Euclidean symmetries of the original configuration.  In the third-turn case
the rotation center is identified with the centroid of the actual points.
-/

namespace StructuralNote.RewrittenGeometricCharacterization

open Complex Filter
open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open MatchingActivityRadialIntegration
open FixedSchurChart FixedSchurCanonicalWordSymmetry
open FixedSchurCyclicEquivariance FixedSchurReflectionEquivariance
open FixedSchurSimpleGraph
open FixedSchurActualRigidEquivalence FixedSchurActualDiameterGraph
open FixedSchurActualEuclideanSymmetry
open RewrittenMaxima
open scoped BigOperators Topology

noncomputable section

local notation "conj" => (starRingEnd ℂ)

/-- A nontrivial rotation which permutes a nonempty finite point family is
centered at the family's centroid. -/
theorem rotation_center_eq_average {n : ℕ} (hn : 0 < n) (z : Points n)
    (π τ : Equiv.Perm (Fin n)) (a ρ : ℂ) (hρ : ρ ≠ 1)
    (hrotation : ∀ j, z (π j) = rotationAbout a ρ (z (π (τ j)))) :
    a = average z := by
  have hsum : (∑ j, z (π j)) =
      ∑ j, rotationAbout a ρ (z (π (τ j))) := by
    apply Finset.sum_congr rfl
    intro j _
    exact hrotation j
  have hperm : (∑ j, z (π (τ j))) = ∑ j, z j := by
    calc
      (∑ j, z (π (τ j))) = ∑ j, z (π j) := Equiv.sum_comp τ (fun j => z (π j))
      _ = ∑ j, z j := Equiv.sum_comp π z
  rw [Equiv.sum_comp π z] at hsum
  simp only [rotationAbout, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hsum' : (∑ j, z j) =
      (n : ℂ) * a + ρ * ((∑ j, z j) - (n : ℂ) * a) := by
    calc
      (∑ j, z j) = (n : ℂ) * a + ∑ j, ρ * (z (π (τ j)) - a) := hsum
      _ = (n : ℂ) * a + ρ * ∑ j, (z (π (τ j)) - a) := by
        rw [Finset.mul_sum]
      _ = (n : ℂ) * a + ρ *
          ((∑ j, z (π (τ j))) - ∑ _j : Fin n, a) := by
        rw [Finset.sum_sub_distrib]
      _ = (n : ℂ) * a + ρ * ((∑ j, z j) - (n : ℂ) * a) := by
        rw [hperm]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  have hfactor : (1 - ρ) * ((∑ j, z j) - (n : ℂ) * a) = 0 := by
    calc
      (1 - ρ) * ((∑ j, z j) - (n : ℂ) * a) =
          (∑ j, z j) - ((n : ℂ) * a + ρ * ((∑ j, z j) - (n : ℂ) * a)) := by
            ring
      _ = 0 := sub_eq_zero.mpr hsum'
  have hone : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  have hcenter : (∑ j, z j) - (n : ℂ) * a = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hone
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold average
  apply (eq_div_iff hn0).2
  calc
    a * (n : ℂ) = (n : ℂ) * a := mul_comm _ _
    _ = ∑ j, z j := (sub_eq_zero.mp hcenter).symm

/-- The complete even-order geometric data, stated for the original
configuration.  Its graph is the canonical balanced graph after a relabeling;
its third-turn, when present, is centered at the actual centroid. -/
structure EvenGeometry (m : ℕ) (z : Points (2 * m)) where
  large : 3 ≤ m
  graphRelabeling : Equiv.Perm (Fin (2 * m))
  graph_eq : relabeledDiameterGraph z graphRelabeling =
    graph (by omega) (patternSign (canonicalPattern large))
  symmetryRelabeling : Equiv.Perm (Fin (2 * m))
  reflectionCenter : ℂ
  reflectionDirection : ℂ
  reflectionDirection_unit : ‖reflectionDirection‖ = 1
  reflection : ∀ j, z (symmetryRelabeling j) =
    planeReflection reflectionCenter reflectionDirection
      (z (symmetryRelabeling (vertexReflection (2 * m) j)))
  thirdTurn : 3 ∣ m →
    let ρ := conj (LocalPhase.regularRoot (2 * m) ^ (2 * (m / 3)))
    ‖ρ‖ = 1 ∧ ρ ^ 3 = 1 ∧ ρ ≠ 1 ∧
      ∀ j, z (symmetryRelabeling j) =
        rotationAbout (average z) ρ
          (z (symmetryRelabeling (cyclicIndex (2 * m) (2 * (m / 3)) j)))

/-- Every sufficiently large actual even extremizer has the complete data in
`EvenGeometry`. -/
theorem eventual_even_geometry :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z → Nonempty (EvenGeometry m z) := by
  obtain ⟨m₀, hgraph⟩ := eventual_actual_extremizer_diameterGraph
  obtain ⟨m₁, hsymmetry⟩ := eventual_actual_extremizer_euclidean_symmetries
  refine ⟨max m₀ m₁, ?_⟩
  intro m hm z hz
  obtain ⟨hm3, x, πg, ag, bg, hxg, hbg, hzg, hgraphEq⟩ :=
    hgraph m (by omega) z hz
  obtain ⟨hm3', y, πs, a, b, hys, hb, hzs, hreflection, hthird⟩ :=
    hsymmetry m (by omega) z hz
  refine ⟨{
    large := hm3
    graphRelabeling := πg
    graph_eq := hgraphEq
    symmetryRelabeling := πs
    reflectionCenter := a
    reflectionDirection := b
    reflectionDirection_unit := hb
    reflection := hreflection
    thirdTurn := ?_ }⟩
  intro hdiv
  obtain ⟨hρnorm, hρcube, hρne, hrotation⟩ := hthird hdiv
  let ρ := conj (LocalPhase.regularRoot (2 * m) ^ (2 * (m / 3)))
  have ha : a = average z :=
    rotation_center_eq_average (show 0 < 2 * m by omega) z πs
      (cyclicIndex (2 * m) (2 * (m / 3))) a ρ hρne hrotation
  exact ⟨hρnorm, hρcube, hρne, by simpa only [ha] using hrotation⟩

/-- One common eventual threshold for existence, rigid uniqueness, the odd
regular formula, and the full canonical graph and symmetry description in
even order. -/
theorem eventual_diameter_geometric_characterization :
    ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n ≥ n₀,
      (∃ z : Points n, DiameterAtMost 2 z ∧ discriminant z = M n) ∧
      (∀ z w : Points n, DiameterAtMost 2 z → discriminant z = M n →
        DiameterAtMost 2 w → discriminant w = M n → DirectRigidRelabeling z w) ∧
      (Odd n →
        M n = (n : ℝ) ^ n /
          Real.cos (Real.pi / (2 * n)) ^ (n * (n - 1)) ∧
        ∀ z : Points n, DiameterAtMost 2 z → discriminant z = M n →
          Configuration.IsRegular z) ∧
      (∀ m : ℕ, n = 2 * m → ∀ z : Points (2 * m),
        ExtremalNormalization.DiameterExtremal z → Nonempty (EvenGeometry m z)) := by
  obtain ⟨n₀, hn₀, hmax⟩ := eventual_diameter_maximum_attained_unique
  obtain ⟨n₁, hn₁, hoddValue⟩ := eventual_odd_maximum
  obtain ⟨n₂, hn₂, hoddRegular⟩ := eventual_odd_maximizer_regular
  obtain ⟨m₀, heven⟩ := eventual_even_geometry
  refine ⟨max n₀ (max n₁ (max n₂ (2 * m₀))), by omega, ?_⟩
  intro n hn
  have hnmax : n₀ ≤ n := by omega
  obtain ⟨hexists, hunique⟩ := hmax n hnmax
  refine ⟨hexists, hunique, ?_, ?_⟩
  · intro hodd
    refine ⟨hoddValue n (by omega) hodd, ?_⟩
    intro z hz hdisc
    exact hoddRegular n (by omega) hodd z hz hdisc
  · intro m hnm z hz
    subst n
    exact heven m (by omega) z hz

end
end StructuralNote.RewrittenGeometricCharacterization

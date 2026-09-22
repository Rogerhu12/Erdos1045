import StructuralNote.ExplicitHessianThresholdFiber
import StructuralNote.FixedSchurActualEuclideanSymmetry

/-! Pointwise downstream consequences of a finite fixed-Schur strict-concavity
certificate.  The analytic and geometric inputs are explicit hypotheses, so
none of the conclusions uses an eventual threshold or chooses one. -/

namespace StructuralNote.ExplicitHessianThresholdDownstream

open Complex
open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox Erdos1045.EventualExact.FourierMultiplier
open CommonDomainClosure CommonFiberCanonicalPaths CommonFiberCanonicalDirections CommonDomainSegments
open FixedSchurChart FixedSchurEquationSmooth FixedSchurChartSmooth
open FixedSchurObjectivePaths FixedSchurStationaryUniqueness
open FixedSchurChartGeometry FixedSchurCyclicEquivariance FixedSchurReflectionEquivariance
open FixedSchurExtremalSymmetry FixedSchurCanonicalWordSymmetry
open FixedSchurActualCanonicalEntry FixedSchurActualRigidEquivalence
open FixedSchurActualEuclideanSymmetry SignPatternSymmetry
open scoped Topology ContDiff

noncomputable section

local notation "conj" => (starRingEnd ℂ)

/-- The finite data used after the analytic Hessian estimate has supplied
strict concavity.  The last three fields are the genuine chart-geometry and
equivariance inputs still needed by the rigid and symmetry conclusions. -/
structure FixedSchurFiberData {m : ℕ} (hm : 3 ≤ m) : Prop where
  strictConcavity : ∀ s : SignPattern (by omega : 0 < m),
    StrictConcaveOn ℝ (FixedSchurChartSmooth.domain (by omega))
      (FixedSchurObjectivePaths.objective (by omega) s)
  directionSmooth : ∀ (s : SignPattern (by omega : 0 < m))
      (x d : SchurParameters m),
    x ∈ FixedSchurChartSmooth.domain (by omega) → Admissible (by omega) d →
      ContDiffAt ℝ ∞ (fun t => FixedSchurObjectivePaths.objective (by omega) s
        (affinePath x d t)) 0
  geometry : ∀ (s : SignPattern (by omega : 0 < m))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
    InDomain (by omega) θ v → GeometricProperties (by omega) s θ v
  cyclicConfiguration : ∀ (k : ℕ) (s : SignPattern (by omega : 0 < m))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
    InDomain (by omega) θ v →
      configuration (by omega) (rotatePattern k s) (cyclicReal k θ) (cyclicCenter k v) =
        cyclicCenter k (configuration (by omega) s θ v)
  reflectionConfiguration : ∀ (s : SignPattern (by omega : 0 < m))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
    InDomain (by omega) θ v →
      configuration (by omega) (reflectPattern s) (reflectReal θ) (reflectCenter v) =
        reflectCenter (configuration (by omega) s θ v)

/-- On one fixed fiber, stationarity implies global maximality without an
eventual quantifier. -/
theorem stationary_global_max {m : ℕ} {hm : 3 ≤ m} (D : FixedSchurFiberData hm)
    (s : SignPattern (by omega : 0 < m)) (x : SchurParameters m)
    (hx : x ∈ FixedSchurChartSmooth.domain (by omega))
    (hstat : Stationary (by omega) s x) :
    IsMaxOn (FixedSchurObjectivePaths.objective (by omega) s)
      (FixedSchurChartSmooth.domain (by omega)) x := by
  intro y hy
  have hd : Admissible (by omega) (y - x) := difference_direction (by omega) x y hx hy
  have hdiff := (D.directionSmooth s x (y - x) hx hd).differentiableAt (by simp)
  have hz : HasDerivAt (fun t => FixedSchurObjectivePaths.objective (by omega) s
      (affinePath x (y - x) t)) 0 0 := by
    simpa only [hstat (y - x) hd] using hdiff.hasDerivAt
  have hconc := FixedSchurStationaryUniqueness.concave_affine_between (by omega) s
    (D.strictConcavity s).concaveOn x y hx hy
  have hbound := hconc.slope_le_of_hasDerivAt
    (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    (by norm_num : (0 : ℝ) < 1) hz
  have he0 : affinePath x (y - x) 0 = x := by simp only [affinePath, zero_smul, add_zero]
  have he1 : affinePath x (y - x) 1 = y := by simp only [affinePath, one_smul, add_sub_cancel]
  simp only [slope_def_field, sub_zero, div_one, he0, he1, sub_nonpos] at hbound
  exact hbound

theorem stationary_unique {m : ℕ} {hm : 3 ≤ m} (D : FixedSchurFiberData hm)
    (s : SignPattern (by omega : 0 < m)) (x y : SchurParameters m)
    (hx : x ∈ FixedSchurChartSmooth.domain (by omega))
    (hy : y ∈ FixedSchurChartSmooth.domain (by omega))
    (hxs : Stationary (by omega) s x) (hys : Stationary (by omega) s y) : x = y := by
  exact (D.strictConcavity s).eq_of_isMaxOn
    (stationary_global_max D s x hx hxs) (stationary_global_max D s y hy hys) hx hy

/-- Diameter extremality implies stationarity once the literal chart geometry
is supplied at this `m`. -/
theorem geometric_extremal_stationary {m : ℕ} {hm : 3 ≤ m}
    (D : FixedSchurFiberData hm) (s : SignPattern (by omega : 0 < m))
    (x : SchurParameters m) (hx : x ∈ FixedSchurChartSmooth.domain (by omega))
    (hmax : ExtremalNormalization.DiameterExtremal
      (configuration (by omega) s x.1 x.2)) : Stationary (by omega) s x := by
  apply FixedSchurStationaryUniqueness.global_max_stationary (by omega) s x hx
  intro y hy
  have hg := D.geometry s y.1 y.2 hy
  exact Real.log_le_log (Configuration.discriminant_pos _ hg.injective) (hmax.2 _ hg.diameter)

theorem same_word_extremal_unique {m : ℕ} {hm : 3 ≤ m}
    (D : FixedSchurFiberData hm) (s : SignPattern (by omega : 0 < m))
    (x y : SchurParameters m)
    (hx : x ∈ FixedSchurChartSmooth.domain (by omega))
    (hy : y ∈ FixedSchurChartSmooth.domain (by omega))
    (hxmax : ExtremalNormalization.DiameterExtremal
      (configuration (by omega) s x.1 x.2))
    (hymax : ExtremalNormalization.DiameterExtremal
      (configuration (by omega) s y.1 y.2)) : x = y := by
  exact stationary_unique D s x y hx hy
    (geometric_extremal_stationary D s x hx hxmax)
    (geometric_extremal_stationary D s y hy hymax)

/-- The finite replacement for `eventual_canonicalRepresentative_unique`. -/
theorem canonicalRepresentative_unique {m : ℕ} {hm : 3 ≤ m}
    (D : FixedSchurFiberData hm) {z w : Points (2 * m)} {x y : SchurParameters m}
    (hx : CanonicalRepresentative hm z x) (hy : CanonicalRepresentative hm w y) : x = y := by
  exact same_word_extremal_unique D (canonicalPattern hm) x y hx.1 hy.1 hx.2.1 hy.2.1

/-- The finite actual-entry hypothesis left for the localization and balanced
word stages.  Everything after this interface is pointwise. -/
def CanonicalRigidEntry {m : ℕ} (hm : 3 ≤ m) : Prop :=
  ∀ z : Points (2 * m), ExtremalNormalization.DiameterExtremal z →
    ∃ (x : SchurParameters m) (π : Equiv.Perm (Fin (2 * m))) (a b : ℂ),
      CanonicalRepresentative hm z x ∧ ‖b‖ = 1 ∧
      ∀ j, z (π j) = a + b * configuration (by omega) (canonicalPattern hm) x.1 x.2 j

/-- Pointwise rigid uniqueness of any two extremizers from the finite entry
and fiber certificates. -/
theorem actual_extremizers_directRigid {m : ℕ} {hm : 3 ≤ m}
    (D : FixedSchurFiberData hm) (hentry : CanonicalRigidEntry hm)
    {z w : Points (2 * m)} (hz : ExtremalNormalization.DiameterExtremal z)
    (hw : ExtremalNormalization.DiameterExtremal w) : DirectRigidRelabeling z w := by
  obtain ⟨x, π, a, b, hx, hb, hzrep⟩ := hentry z hz
  obtain ⟨y, τ, c, d, hy, hd, hwrep⟩ := hentry w hw
  have hxy := canonicalRepresentative_unique D hx hy
  subst y
  exact directRigidRelabeling_of_common ⟨π, a, b, hb, hzrep⟩ ⟨τ, c, d, hd, hwrep⟩

/-- Reflection symmetry of the canonical representative, derived pointwise
from same-word uniqueness and chart equivariance. -/
theorem canonical_reflection_symmetry {m : ℕ} {hm : 3 ≤ m}
    (D : FixedSchurFiberData hm) (x : SchurParameters m)
    (hx : x ∈ FixedSchurChartSmooth.domain (by omega))
    (hmax : ExtremalNormalization.DiameterExtremal
      (configuration (by omega) (canonicalPattern hm) x.1 x.2)) :
    configuration (by omega) (canonicalPattern hm) x.1 x.2 =
      reflectCenter (configuration (by omega) (canonicalPattern hm) x.1 x.2) := by
  have hcfg := D.reflectionConfiguration (canonicalPattern hm) x.1 x.2 hx
  rw [canonicalPattern_reflect hm] at hcfg
  have hy : (reflectReal x.1, reflectCenter x.2) ∈
      FixedSchurChartSmooth.domain (by omega) := inDomain_reflect (by omega) x.1 x.2 hx
  have hymax : ExtremalNormalization.DiameterExtremal
      (configuration (by omega) (canonicalPattern hm) (reflectReal x.1)
        (reflectCenter x.2)) := by
    rw [hcfg]
    exact diameterExtremal_reflectCenter hmax
  have hp := same_word_extremal_unique D (canonicalPattern hm)
    (reflectReal x.1, reflectCenter x.2) x hy hx hymax hmax
  have hp1 : reflectReal x.1 = x.1 := by simpa using congrArg Prod.fst hp
  have hp2 : reflectCenter x.2 = x.2 := by simpa using congrArg Prod.snd hp
  rw [hp1, hp2] at hcfg
  exact hcfg

/-- One-third-turn symmetry when `3 ∣ m`, again with no eventual premise. -/
theorem canonical_third_turn_symmetry {m : ℕ} {hm : 3 ≤ m}
    (D : FixedSchurFiberData hm) (hdiv : 3 ∣ m) (x : SchurParameters m)
    (hx : x ∈ FixedSchurChartSmooth.domain (by omega))
    (hmax : ExtremalNormalization.DiameterExtremal
      (configuration (by omega) (canonicalPattern hm) x.1 x.2)) :
    configuration (by omega) (canonicalPattern hm) x.1 x.2 =
      cyclicCenter (2 * (m / 3))
        (configuration (by omega) (canonicalPattern hm) x.1 x.2) := by
  let k := 2 * (m / 3)
  have hcfg := D.cyclicConfiguration k (canonicalPattern hm) x.1 x.2 hx
  rw [canonicalPattern_third_shift hm hdiv] at hcfg
  have hy : (cyclicReal k x.1, cyclicCenter k x.2) ∈
      FixedSchurChartSmooth.domain (by omega) := inDomain_cyclic (by omega) k x.1 x.2 hx
  have hymax : ExtremalNormalization.DiameterExtremal
      (configuration (by omega) (canonicalPattern hm) (cyclicReal k x.1)
        (cyclicCenter k x.2)) := by
    rw [hcfg]
    exact diameterExtremal_cyclicCenter k hmax
  have hp := same_word_extremal_unique D (canonicalPattern hm)
    (cyclicReal k x.1, cyclicCenter k x.2) x hy hx hymax hmax
  have hp1 : cyclicReal k x.1 = x.1 := by simpa using congrArg Prod.fst hp
  have hp2 : cyclicCenter k x.2 = x.2 := by simpa using congrArg Prod.snd hp
  rw [hp1, hp2] at hcfg
  exact hcfg

/-- The fully pointwise Euclidean-symmetry conclusion.  The only remaining
outer hypothesis is `CanonicalRigidEntry`, precisely the localization and
balanced-word input preceding strict concavity. -/
theorem actual_extremizer_euclidean_symmetries {m : ℕ} {hm : 3 ≤ m}
    (D : FixedSchurFiberData hm) (hentry : CanonicalRigidEntry hm)
    {z : Points (2 * m)} (hz : ExtremalNormalization.DiameterExtremal z) :
    ∃ (x : SchurParameters m) (π : Equiv.Perm (Fin (2 * m))) (a b : ℂ),
      CanonicalRepresentative hm z x ∧ ‖b‖ = 1 ∧
      (∀ j, z (π j) = a + b *
        configuration (by omega) (canonicalPattern hm) x.1 x.2 j) ∧
      (∀ j, z (π j) = planeReflection a b
        (z (π (vertexReflection (2 * m) j)))) ∧
      (3 ∣ m →
        let ρ := conj (LocalPhase.regularRoot (2 * m) ^ (2 * (m / 3)))
        ‖ρ‖ = 1 ∧ ρ ^ 3 = 1 ∧ ρ ≠ 1 ∧ ∀ j, z (π j) =
          rotationAbout a ρ (z (π (cyclicIndex (2 * m) (2 * (m / 3)) j)))) := by
  obtain ⟨x, π, a, b, hx, hb, hzw⟩ := hentry z hz
  let w : Points (2 * m) :=
    configuration (by omega) (canonicalPattern hm) x.1 x.2
  have href : w = reflectCenter w := canonical_reflection_symmetry D x hx.1 hx.2.1
  have hzref : ∀ j, z (π j) = planeReflection a b
      (z (π (vertexReflection (2 * m) j))) :=
    directRigid_reflection π a b hb hzw href
  refine ⟨x, π, a, b, hx, hb, hzw, hzref, ?_⟩
  intro hdiv
  have ht : w = cyclicCenter (2 * (m / 3)) w :=
    canonical_third_turn_symmetry D hdiv x hx.1 hx.2.1
  exact ⟨thirdTurnMultiplier_norm, thirdTurnMultiplier_cube hm hdiv,
    thirdTurnMultiplier_ne_one hm hdiv,
    directRigid_thirdTurn π a b hzw ht⟩

end
end StructuralNote.ExplicitHessianThresholdDownstream

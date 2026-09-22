import StructuralNote.ExplicitPolynomialSelection
import StructuralNote.ExplicitKernelSelection
import StructuralNote.ExplicitHessianThresholdFixedSchurConcavity
import StructuralNote.FixedSchurActualDiameterGraph
import StructuralNote.ExplicitEvenCertificate
import StructuralNote.RewrittenGeometricCharacterization

/-! The complete even-order conclusions at one explicitly defined threshold.
No eventual-order witness is an input to any theorem in this module. -/
namespace StructuralNote.ExplicitEvenThreshold
open Complex Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open FixedSchurActualCanonicalEntry FixedSchurActualRigidEquivalence
open FixedSchurActualEuclideanSymmetry FixedSchurActualDiameterGraph
open FixedSchurChart FixedSchurEquationSmooth FixedSchurCanonicalWordSymmetry
open FixedSchurSimpleGraph FiniteBox
open RationalStationarySystem RationalSystemAlgebraicity
open RationalExpressions RationalConfigurationPolynomials MvPolynomial
open FixedSchurRationalClosureMatrix FixedSchurRationalWindowDomain
open ExplicitHessianThresholdDownstream
open SignPatternSymmetry
open MatchingActivityRadialIntegration FixedSchurCyclicEquivariance FixedSchurReflectionEquivariance
noncomputable section

def orderThreshold : ℕ := max 16
  (max ExplicitHessianThreshold.orderThreshold
    (max (ExplicitActualRationalStationary.orderThreshold (16 / 25))
      (ExplicitKernelSelection.orderThreshold SinglePressureEstimate.budgetConstant)))

theorem eight_le {m : ℕ} (hN : orderThreshold ≤ 2 * m) : 8 ≤ m := by
  have hh : 16 ≤ 2 * m := (le_max_left _ _).trans hN
  omega

theorem threshold_data {m : ℕ} (hN : orderThreshold ≤ 2 * m) :
    ExplicitHessianThreshold.orderThreshold ≤ 2 * m ∧
    ExplicitActualRationalStationary.orderThreshold (16 / 25) ≤ 2 * m ∧
    ExplicitKernelSelection.orderThreshold SinglePressureEstimate.budgetConstant ≤ 2 * m := by
  exact ⟨(le_max_left _ _).trans ((le_max_right _ _).trans hN),
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN)),
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))⟩

theorem fiberData {m : ℕ} (hN : orderThreshold ≤ 2 * m) :
    FixedSchurFiberData (show 3 ≤ m from le_trans (by norm_num) (eight_le hN)) :=
  ExplicitHessianThresholdFixedSchurConcavity.fiberData (threshold_data hN).1 _

theorem finiteImprovement {m : ℕ} (hN : orderThreshold ≤ 2 * m) :
    ExplicitBalancedSelection.FiniteImprovement m SinglePressureEstimate.budgetConstant (16 / 25) :=
  ExplicitKernelSelection.finiteImprovement (threshold_data hN).2.2

theorem canonicalRigidEntry {m : ℕ} (hN : orderThreshold ≤ 2 * m) :
    CanonicalRigidEntry (show 3 ≤ m from le_trans (by norm_num) (eight_le hN)) := by
  exact ExplicitCanonicalEntrySelected.actual_canonicalRigidEntry _ (fiberData hN)
    (by norm_num : (0 : ℝ) < 16 / 25) (finiteImprovement hN)
    ((le_max_left _ _).trans (threshold_data hN).2.1)

theorem actual_extremizers_unique {m : ℕ} (hN : orderThreshold ≤ 2 * m)
    {z w : Points (2 * m)} (hz : ExtremalNormalization.DiameterExtremal z)
    (hw : ExtremalNormalization.DiameterExtremal w) : DirectRigidRelabeling z w :=
  ExplicitHessianThresholdDownstream.actual_extremizers_directRigid
    (fiberData hN) (canonicalRigidEntry hN) hz hw

theorem actual_extremizer_diameterGraph {m : ℕ} (hN : orderThreshold ≤ 2 * m)
    {z : Points (2 * m)} (hz : ExtremalNormalization.DiameterExtremal z) :
    ∃ (hm : 3 ≤ m) (x : SchurParameters m) (π : Equiv.Perm (Fin (2 * m))) (a b : ℂ),
      CanonicalRepresentative hm z x ∧ ‖b‖ = 1 ∧
      (∀ j, z (π j) = a + b * configuration (by omega) (canonicalPattern hm) x.1 x.2 j) ∧
      relabeledDiameterGraph z π = graph (by omega) (patternSign (canonicalPattern hm)) := by
  let hm3 : 3 ≤ m := le_trans (by norm_num) (eight_le hN)
  obtain ⟨x, π, a, b, hx, hb, hrigid⟩ := canonicalRigidEntry hN z hz
  refine ⟨hm3, x, π, a, b, hx, hb, hrigid, ?_⟩
  rw [directRigid_diameterGraph hb hrigid]
  exact canonical_configuration_diameterGraph hm3 x ((fiberData hN).geometry _ _ _ hx.1)


theorem actual_extremizer_euclidean_symmetries {m : ℕ} (hN : orderThreshold ≤ 2 * m)
    {z : Points (2 * m)} (hz : ExtremalNormalization.DiameterExtremal z) :
    ∃ (hm : 3 ≤ m) (x : SchurParameters m) (π : Equiv.Perm (Fin (2 * m))) (a b : ℂ),
      CanonicalRepresentative hm z x ∧ ‖b‖ = 1 ∧
      (∀ j, z (π j) = a + b *
        configuration (by omega) (canonicalPattern hm) x.1 x.2 j) ∧
      (∀ j, z (π j) = planeReflection a b
        (z (π (vertexReflection (2 * m) j)))) ∧
      (3 ∣ m →
        let ρ := (starRingEnd ℂ) (LocalPhase.regularRoot (2 * m) ^ (2 * (m / 3)))
        ‖ρ‖ = 1 ∧ ρ ^ 3 = 1 ∧ ρ ≠ 1 ∧ ∀ j, z (π j) =
          rotationAbout a ρ (z (π (cyclicIndex (2 * m) (2 * (m / 3)) j)))) := by
  exact ⟨le_trans (by norm_num) (eight_le hN),
    ExplicitHessianThresholdDownstream.actual_extremizer_euclidean_symmetries
      (fiberData hN) (canonicalRigidEntry hN) hz⟩


theorem even_maximum_single_polynomial_root {m : ℕ} (hN : orderThreshold ≤ 2 * m) :
      ∃ (hm : 3 ≤ m) (Y : RationalStationarySystem.Variables m → ℝ)
        (P : MvPolynomial (RationalConfiguration.Variables m) Coeff),
        let s := canonicalPattern hm
        Fintype.card (RationalStationarySystem.Variables m) = 2 * m + 1 ∧
        0 < aeval (coordinates Y) P ∧
        Stationary (by omega) (halfWord s) Y ∧
        (∀ Z : RationalStationarySystem.Variables m → ℝ,
          0 < aeval (coordinates Z) P →
          ((∀ q, aeval Z (polynomials (by omega) (halfWord s) q) = 0) ↔
            Stationary (by omega) (halfWord s) Z)) ∧
        (∀ Z : RationalStationarySystem.Variables m → ℝ,
          0 < aeval (coordinates Z) P →
          (∀ q, aeval Z (polynomials (by omega) (halfWord s) q) = 0) → Z = Y) ∧
        (RationalSystemAlgebraicity.jacobian
          (systemExpression (by omega) (halfWord s)) Y).det ≠ 0 ∧
        (∀ q, aeval Y (polynomials (by omega) (halfWord s) q) = 0) ∧
        (PolynomialAlgebraicity.jacobian
          (polynomials (by omega) (halfWord s)) Y).det ≠ 0 ∧
        (∀ q, IsAlgebraic ℚ (Y q)) ∧
        (∀ j, IsAlgebraic ℚ
            (RationalConfiguration.configuration (by omega) (rationalSign s)
              (coordinates Y) j).re ∧
          IsAlgebraic ℚ
            (RationalConfiguration.configuration (by omega) (rationalSign s)
              (coordinates Y) j).im) ∧
        (∀ i j, IsAlgebraic ℚ
          ‖RationalConfiguration.configuration (by omega) (rationalSign s)
                (coordinates Y) i -
            RationalConfiguration.configuration (by omega) (rationalSign s)
                (coordinates Y) j‖) ∧
        IsAlgebraic ℚ (discriminant
          (RationalConfiguration.configuration (by omega) (rationalSign s)
            (coordinates Y))) ∧
        M (2 * m) = discriminant
          (RationalConfiguration.configuration (by omega) (rationalSign s)
            (coordinates Y)) ∧
        IsAlgebraic ℚ (M (2 * m)) := by
  exact ExplicitPolynomialSelection.even_maximum_single_polynomial_root (eight_le hN)
    (fiberData hN) (by norm_num : (0 : ℝ) < 16 / 25) (finiteImprovement hN)
    (threshold_data hN).2.1

theorem certificate {m : ℕ} (hN : orderThreshold ≤ 2 * m) :
    Nonempty (RewrittenEvenCertificate.Certificate m) :=
  ExplicitEvenCertificate.certificate (eight_le hN) (fiberData hN)
    (by norm_num : (0 : ℝ) < 16 / 25) (finiteImprovement hN) (threshold_data hN).2.1

theorem even_geometry {m : ℕ} (hN : orderThreshold ≤ 2 * m)
    {z : Points (2 * m)} (hz : ExtremalNormalization.DiameterExtremal z) :
    Nonempty (RewrittenGeometricCharacterization.EvenGeometry m z) := by
  obtain ⟨hm3, x, πg, ag, bg, hxg, hbg, hzg, hgraphEq⟩ := actual_extremizer_diameterGraph hN hz
  obtain ⟨hm3', y, πs, a, b, hys, hb, hzs, hreflection, hthird⟩ :=
    actual_extremizer_euclidean_symmetries hN hz
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
  let ρ := (starRingEnd ℂ) (LocalPhase.regularRoot (2 * m) ^ (2 * (m / 3)))
  have ha : a = average z :=
    RewrittenGeometricCharacterization.rotation_center_eq_average (show 0 < 2 * m by omega)
      z πs (cyclicIndex (2 * m) (2 * (m / 3))) a ρ hρne hrotation
  exact ⟨hρnorm, hρcube, hρne, by simpa only [ha] using hrotation⟩

end
end StructuralNote.ExplicitEvenThreshold

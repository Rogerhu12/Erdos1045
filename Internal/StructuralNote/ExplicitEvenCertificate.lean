import StructuralNote.ExplicitPolynomialSelection
import StructuralNote.RewrittenEvenCertificate
/-! A complete explicit-order certificate for the actual algebraic maximizer. -/
namespace StructuralNote.ExplicitEvenCertificate

open Complex Filter
open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open RationalStationarySystem
open RationalCommonConfiguration
open FixedSchurChart FixedSchurChartGeometry
open FixedSchurCanonicalWordSymmetry
open FixedSchurRationalWindowDomain FixedSchurRationalWindowObjectiveTransfer
open FixedSchurRationalClosureMatrix CommonDomainRadius
open RewrittenEvenAlgebraicMaximum RewrittenMaxima
open scoped Topology

open MvPolynomial RationalExpressions RewrittenEvenCertificate
open ExplicitHessianThresholdDownstream FixedSchurActualCanonicalEntry
noncomputable section


theorem selectedWindow_diameterAtMost {m : ℕ}
    (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
      (X : RationalConfiguration.Variables m → ℝ),
      selectedWindowEnergy (by omega) s X <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
      RationalConfiguration.closure (by omega) (rationalSign s) X = 0 →
      DiameterAtMost 2
        (RationalConfiguration.configuration (by omega) (rationalSign s) X) := by
  have hdomain := ExplicitRationalWindow.selectedWindow_inDomain ((le_max_left _ _).trans hN)
  have hrigid := ExplicitRationalTransfer.fixed_configuration_eq_rigid hN
  have hgeometry := ExplicitHessianThresholdFixedSchurGeometry.geometric_properties ((le_max_left _ _).trans hN)
  clear hN
  intro hm s X hwindow hclosure
  let x := fixedSchurCoordinates (show 2 ≤ m by omega) s X
  let w := FixedSchurChart.configuration (by omega) s x.1 x.2
  let z := RationalConfiguration.configuration (by omega) (rationalSign s) X
  let u := LensClosure.unit (-angleMean (by omega) X)
  let c := centerMean (by omega) (rationalSign s) X
  have hx : x ∈ FixedSchurChartSmooth.domain (by omega) :=
    hdomain (show 2 ≤ m by omega) s X hwindow
  have hw : DiameterAtMost 2 w :=
    (hgeometry (show 2 ≤ m by omega) s x.1 x.2 hx).diameter
  have he : w = fun j => u * (z j - c) := by
    simpa only [x, w, z, u, c] using hrigid hm s X hwindow hclosure
  have hu : ‖u‖ = 1 := by
    simp only [u, LensClosure.norm_unit]
  intro i j
  calc
    ‖z i - z j‖ = ‖u * (z i - z j)‖ := by rw [norm_mul, hu, one_mul]
    _ = ‖u * (z i - c) - u * (z j - c)‖ := by congr 1; ring
    _ = ‖w i - w j‖ := by rw [congrFun he i, congrFun he j]
    _ ≤ 2 := hw i j

theorem certificate {m : ℕ} (hm : 8 ≤ m)
    (D : FixedSchurFiberData (show 3 ≤ m by omega))
    {δ : ℝ} (hδ : 0 < δ)
    (hfinite : ExplicitBalancedSelection.FiniteImprovement m SinglePressureEstimate.budgetConstant δ)
    (hN : ExplicitActualRationalStationary.orderThreshold δ ≤ 2 * m) :
    Nonempty (RewrittenEvenCertificate.Certificate m) := by
  have hreprN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨z, hz⟩ := WholeBoxLowerBound.exists_diameterExtremal (show 0 < 2 * m by omega)
  obtain ⟨hm3, x, Y, _hx, _htheta, _hcenter, hclosure, hwindow, hcoordinates,
      hstationary, hJ, hzero, hPJ, hunique, hYalg, hcfg, hdist, hdiscAlg, hdiscEq⟩ :=
    ExplicitRationalStationarySelection.actual_extremizer_unique_algebraic_root hm D hδ hfinite hN z hz
  let s := canonicalPattern hm3
  have hYwindow : selectedWindowEnergy (by omega) s (coordinates Y) <
      (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
    simpa only [hcoordinates] using hwindow
  have hYclosure : RationalConfiguration.closure (by omega) (rationalSign s) (coordinates Y) = 0 := by
    simpa only [hcoordinates] using hclosure
  obtain ⟨P, hP⟩ := ExplicitRationalPolynomial.exists_selectedWindowPolynomial
    ((le_max_left _ _).trans hreprN) (show 2 ≤ m by omega) s
  have hi := ExplicitPolynomialSelection.window_polynomial_system_iff hreprN hm s P hP
  have hM : M (2 * m) = discriminant
      (RationalConfiguration.configuration (by omega) (rationalSign s) (coordinates Y)) := by
    rw [hcoordinates, hdiscEq]
    exact (StructuralNote.M_eq_verified_diameterMaximum _).trans
      (WholeBoxLowerBound.diameterMaximum_eq_of_extremal hz)
  have hmax : ExtremalNormalization.DiameterExtremal
      (RationalConfiguration.configuration (by omega) (rationalSign s) (coordinates Y)) := by
    apply (diameterExtremal_iff_attains (show 0 < 2 * m by omega) _).2
    exact ⟨selectedWindow_diameterAtMost hreprN hm s _ hYwindow hYclosure, hM.symm⟩
  refine ⟨{
    large := hm3
    root := Y
    window := P
    dimension := variables_card (by omega)
    window_spec := hP
    in_window := (hP (coordinates Y)).1 hYwindow
    stationary := hstationary
    polynomial_root := hzero
    system_iff := hi
    unique_root := ?_
    rational_nonsingular := hJ
    polynomial_nonsingular := hPJ
    algebraic := hYalg
    geometric_algebraic := ?_
    distances_algebraic := ?_
    extremal := hmax
    maximum := hM
    maximum_algebraic := ?_ }⟩
  · intro Z hZwindow hZzero
    exact hunique Z ((hP (coordinates Z)).2 hZwindow) ((hi Z hZwindow).1 hZzero)
  · simpa only [hcoordinates] using hcfg
  · simpa only [hcoordinates] using hdist
  · rw [hM, hcoordinates]
    exact hdiscAlg

end
end StructuralNote.ExplicitEvenCertificate

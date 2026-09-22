import StructuralNote.ExplicitRationalTransfer
import StructuralNote.ExplicitRationalRecovery
import StructuralNote.FixedSchurActualRationalStationary
/-! Actual rational stationary coordinates at an explicit threshold. -/
namespace StructuralNote.ExplicitActualRationalStationary

open Filter Matrix Complex Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open RationalCommonConfiguration RationalStationarySystem
open FixedSchurRationalClosureMatrix FixedSchurRationalWindowClosureDerivative
open FixedSchurRationalClosurePaths FixedSchurRationalLagrangian
open FixedSchurRationalWindowEnergy FixedSchurRationalWindowDomain
open FixedSchurRationalWindowObjectiveTransfer FixedSchurRationalStationaryTransfer
open FixedSchurStationaryUniqueness FixedSchurActualCanonicalEntry
open FixedSchurActualRationalEntry FixedSchurLinear FixedSchurChart
open CommonDomainRadius
open scoped BigOperators Topology ContDiff

open ExplicitHessianThresholdDownstream
open ExplicitCanonicalEntrySelected ExplicitBalancedSelection
open MatchingActivityActualChart FourierMultiplier FixedSchurActualRationalStationary
open SchurSpectrum
noncomputable section

def orderThreshold (δ : ℝ) : ℕ :=
  max (ExplicitCanonicalEntrySelected.actualThreshold δ)
    (max (ExplicitRationalRecovery.orderThreshold (actualChartEnergyConstant + 1))
      ExplicitRationalRepresentation.orderThreshold)


theorem exists_rational_stationary_of_fixed_stationary {m : ℕ} {hm3 : 3 ≤ m}
    (D : FixedSchurFiberData hm3)
    (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
      ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        RationalConfiguration.closure (by omega) (rationalSign s) X = 0 →
        FixedSchurStationaryUniqueness.Stationary (by omega) s
          (fixedSchurCoordinates (show 2 ≤ m by omega) s X) →
        ∃ Y : RationalStationarySystem.Variables m → ℝ,
          RationalStationarySystem.coordinates Y = X ∧
          RationalStationarySystem.Stationary (by omega) (halfWord s) Y := by
  have hfull := ExplicitRationalClosure.selectedWindow_closure_hasFDerivAt_surjective hN
  have hcollision := ExplicitRationalTransfer.selectedWindow_collisionFree hN
  have hdomain := ExplicitRationalTransfer.fixedSchurCoordinates_inDomain hN
  have htransfer := ExplicitRationalTransfer.objective_path_eventuallyEq hN
  clear hN
  intro hm s X hwindow hclosure hstationary
  let x := fixedSchurCoordinates (show 2 ≤ m by omega) s X
  have hx : x ∈ FixedSchurChartSmooth.domain (by omega) :=
    hdomain hm s X hwindow
  have hmax : IsMaxOn (FixedSchurObjectivePaths.objective (by omega) s)
      (FixedSchurChartSmooth.domain (by omega)) x :=
    ExplicitHessianThresholdDownstream.stationary_global_max D s x hx hstationary
  have hfree : CollisionFree (by omega) (halfWord s) X :=
    hcollision hm s X hwindow hclosure
  let F : (RationalConfiguration.Variables m → ℝ) →L[ℝ] ℝ :=
    fderiv ℝ (RationalStationarySystem.objective (by omega) (halfWord s)) X
  let B : (RationalConfiguration.Variables m → ℝ) →L[ℝ] ℂ :=
    closureFDeriv (by omega) (rationalSign s) X
  have honto : Function.Surjective B :=
    (hfull hm s X hwindow hclosure).2
  have hker : ∀ u, B u = 0 → F u = 0 := by
    intro u hu
    obtain ⟨Z, hZ0, hZsmooth, hZclosed, hZderiv⟩ :=
      exists_smooth_closed_path (by omega) (rationalSign s) X u hclosure honto hu
    have henergy : ContinuousAt
        (fun t => selectedWindowEnergy (by omega) s (Z t)) 0 :=
      (selectedWindowEnergy_differentiable (by omega) s).continuous.continuousAt.comp
        hZsmooth.continuousAt
    have hwindowNear : ∀ᶠ t in nhds (0 : ℝ),
        selectedWindowEnergy (by omega) s (Z t) <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
      have hwindow0 : selectedWindowEnergy (by omega) s (Z 0) <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
        simpa only [hZ0] using hwindow
      exact henergy.tendsto.eventually (eventually_lt_nhds hwindow0)
    have heq := htransfer hm s Z 0 hZsmooth.continuousAt
      (by simpa only [hZ0] using hwindow) hZclosed
    have heq0 := heq.self_of_nhds
    have hlocal : IsLocalMax
        (fun t => RationalStationarySystem.objective (by omega) (halfWord s) (Z t)) 0 := by
      change ∀ᶠ t in nhds (0 : ℝ),
        RationalStationarySystem.objective (by omega) (halfWord s) (Z t) ≤
          RationalStationarySystem.objective (by omega) (halfWord s) (Z 0)
      filter_upwards [heq, hwindowNear] with t ht htw
      calc
        RationalStationarySystem.objective (by omega) (halfWord s) (Z t) =
            FixedSchurObjectivePaths.objective (by omega) s
              (fixedSchurCoordinates (show 2 ≤ m by omega) s (Z t)) := ht
        _ ≤ FixedSchurObjectivePaths.objective (by omega) s x :=
          hmax (hdomain hm s (Z t) htw)
        _ = FixedSchurObjectivePaths.objective (by omega) s
              (fixedSchurCoordinates (show 2 ≤ m by omega) s (Z 0)) := by
          simp only [hZ0, x]
        _ = RationalStationarySystem.objective (by omega) (halfWord s) (Z 0) :=
          heq0.symm
    have hzero : deriv (fun t => RationalStationarySystem.objective
        (by omega) (halfWord s) (Z t)) 0 = 0 := hlocal.deriv_eq_zero
    have hout : DifferentiableAt ℝ
        (RationalStationarySystem.objective (by omega) (halfWord s)) X :=
      (objective_contDiffAt (by omega) (halfWord s) X hfree).differentiableAt
        (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hchain : deriv (fun t => RationalStationarySystem.objective
        (by omega) (halfWord s) (Z t)) 0 = F u := by
      rw [show (fun t => RationalStationarySystem.objective
          (by omega) (halfWord s) (Z t)) =
        RationalStationarySystem.objective (by omega) (halfWord s) ∘ Z by rfl,
        fderiv_comp_deriv 0 (by simpa only [hZ0] using hout)
          (hZsmooth.differentiableAt (by simp)), hZ0, hZderiv]
    exact hchain.symm.trans hzero
  obtain ⟨μ, hμ⟩ := exists_complex_multiplier B F honto hker
  let Y : RationalStationarySystem.Variables m → ℝ := Sum.elim X μ
  refine ⟨Y, rfl, hclosure, ?_⟩
  intro i
  have hout : DifferentiableAt ℝ
      (RationalStationarySystem.objective (by omega) (halfWord s)) X :=
    (objective_contDiffAt (by omega) (halfWord s) X hfree).differentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0)
  have houter : HasFDerivAt
      (RationalStationarySystem.objective (by omega) (halfWord s)) F
      (Function.update X i (X i)) := by
    simpa only [Function.update_eq_self, F] using hout.hasFDerivAt
  have hline := houter.comp_hasDerivAt (X i) (hasDerivAt_update X i (X i))
  have hleft : deriv (fun t => RationalStationarySystem.objective
      (by omega) (halfWord s) (Function.update X i t)) (X i) =
      F (Pi.single i 1) := by
    rw [show (fun t => RationalStationarySystem.objective
        (by omega) (halfWord s) (Function.update X i t)) =
      RationalStationarySystem.objective (by omega) (halfWord s) ∘
        Function.update X i by rfl]
    simpa only [Function.update_eq_self, F] using hline.deriv
  rw [show RationalStationarySystem.coordinates Y = X by rfl, hleft]
  change F (Pi.single i 1) = ∑ k, μ k * closureMatrix (by omega) (halfWord s) X k i
  rw [hμ, Fin.sum_univ_two]
  simp only [closureMatrix_entry]
  rw [sign_halfWord]
  rfl


theorem actual_extremizer_rational_stationary {m : ℕ} (hm : 8 ≤ m)
    (D : FixedSchurFiberData (show 3 ≤ m by omega)) {δ : ℝ} (hδ : 0 < δ)
    (hfinite : FiniteImprovement m SinglePressureEstimate.budgetConstant δ)
    (hN : orderThreshold δ ≤ 2 * m) {z : Points (2 * m)}
    (hz : ExtremalNormalization.DiameterExtremal z) :
    ∃ (x : FixedSchurEquationSmooth.SchurParameters m)
      (Y : RationalStationarySystem.Variables m → ℝ),
      CanonicalRepresentative (show 3 ≤ m by omega) z x ∧
      let s := FixedSchurCanonicalWordSymmetry.canonicalPattern (show 3 ≤ m by omega)
      let C := center (FixedSchurChart.coordinate (by omega) s x.1 x.2) x.2
      let X := FixedSchurRationalRecovery.parameters (by omega) s x.1 C
      theta (by omega) X = x.1 ∧
      normalizedCenter (by omega) (rationalSign s) X = C ∧
      RationalConfiguration.closure (by omega) (rationalSign s) X = 0 ∧
      selectedWindowEnergy (by omega) s X <
        (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) ∧
      RationalStationarySystem.coordinates Y = X ∧
      RationalStationarySystem.Stationary (by omega) (halfWord s) Y := by
  have hentryN : ExplicitCanonicalEntrySelected.actualThreshold δ ≤ 2 * m :=
    (le_max_left _ _).trans hN
  have hrecN : ExplicitRationalRecovery.orderThreshold (actualChartEnergyConstant + 1) ≤ 2 * m :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hreprN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  clear hN
  obtain ⟨x, hx, henergy, _hrigid, hfixed⟩ :=
    actual_canonical_entry_with_energy (show 3 ≤ m by omega) D hδ hfinite hentryN hz
  let s := FixedSchurCanonicalWordSymmetry.canonicalPattern (show 3 ≤ m by omega)
  let C := center (FixedSchurChart.coordinate (by omega) s x.1 x.2) x.2
  let X := FixedSchurRationalRecovery.parameters (by omega) s x.1 C
  have hB : 0 ≤ actualChartEnergyConstant + 1 := by
    linarith [actualChartEnergyConstant_nonneg]
  have he : pairEnergy (by omega) (fun j => (x.1 j : ℂ)) + pairEnergy (by omega) x.2 ≤
      (actualChartEnergyConstant + 1) ^ 2 / (2 * m : ℝ) ^ 2 := by
    apply henergy.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith only [actualChartEnergyConstant_nonneg, sq_nonneg actualChartEnergyConstant]
  obtain ⟨htheta, hcenter, hclosure, hwindow⟩ :=
    ExplicitRationalRecovery.inner_rational_recovery (actualChartEnergyConstant + 1) hB hrecN
      (show 2 ≤ m by omega) s x.1 x.2 hx.1 he
  have hcoords : fixedSchurCoordinates (show 2 ≤ m by omega) s X = x := by
    apply Prod.ext
    · exact htheta
    · dsimp only [fixedSchurCoordinates]
      rw [hcenter]
      exact (ExplicitHessianThresholdFixedSchur.coordinate_properties
        ((le_max_left _ _).trans hreprN) (show 2 ≤ m by omega) s x.1 x.2 hx.1).free_projection
  have hfixedX : FixedSchurStationaryUniqueness.Stationary (by omega) s
      (fixedSchurCoordinates (show 2 ≤ m by omega) s X) := by
    rw [hcoords]
    exact hfixed
  obtain ⟨Y, hYX, hYstationary⟩ :=
    exists_rational_stationary_of_fixed_stationary D hreprN hm s X hwindow hclosure hfixedX
  exact ⟨x, Y, hx, htheta, hcenter, hclosure, hwindow, hYX, hYstationary⟩

end
end StructuralNote.ExplicitActualRationalStationary

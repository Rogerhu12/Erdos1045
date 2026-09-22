import StructuralNote.ExplicitRationalTransfer
import StructuralNote.ExplicitRationalRecovery
import StructuralNote.ExplicitCanonicalEntryObjectivePaths
import StructuralNote.ExplicitFixedSchurHessianEstimate
import StructuralNote.FixedSchurRationalStationaryTransfer

/-! Explicit pointwise transfer from the rational stationary system to the
chosen fixed-Schur chart. -/

namespace StructuralNote.ExplicitRationalStationaryTransfer

open Filter Matrix Complex Erdos1045 Erdos1045.EventualExact
open LensClosure FiniteFourierLift FourierMultiplier SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonRationalChart
open RationalCommonConfiguration RationalAngleBranch RationalChart
open RationalStationarySystem FixedSchurRationalClosureMatrix
open FixedSchurRationalLagrangian
open FixedSchurRationalClosurePaths FixedSchurRationalWindowClosureDerivative
open FixedSchurRationalRecovery FixedSchurRationalWindowObjectiveTransfer
open FixedSchurRationalWindowEnergy FixedSchurRationalWindowDomain FixedSchurEdgeGeometry
open FixedSchurRationalWindowRepresentation FixedSchurRationalRecoveryBounds
open FixedSchurChart FixedSchurChartSmooth FixedSchurLinear CommonDomainClosure
open CommonDomainRadius CommonFiberCanonicalDirections CommonFiberCanonicalPaths
open FixedSchurRationalStationaryTransfer
open scoped Topology ContDiff BigOperators

noncomputable section

theorem smooth_local_recovery {m : ℕ}
    (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m)
    (hm : 8 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
    (X : RationalConfiguration.Variables m → ℝ)
    (hwindow : selectedWindowEnergy (by omega) s X <
      (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2))
    (hclosure : RationalConfiguration.closure (by omega) (rationalSign s) X = 0) :
    let x := fixedSchurCoordinates (show 2 ≤ m by omega) s X
    ∃ g : FixedSchurEquationSmooth.SchurParameters m →
        FixedSchurEquationSmooth.SchurState m,
      ContDiffAt ℝ ∞ g x ∧
      modelRecovery (show 2 ≤ m by omega) s g x = X ∧
      ContDiffAt ℝ ∞ (modelRecovery (show 2 ≤ m by omega) s g) x ∧
      (∀ᶠ y in nhds x, y ∈ FixedSchurChartSmooth.domain (by omega) →
        RationalConfiguration.closure (by omega) (rationalSign s)
            (modelRecovery (show 2 ≤ m by omega) s g y) = 0 ∧
          fixedSchurCoordinates (show 2 ≤ m by omega) s
            (modelRecovery (show 2 ≤ m by omega) s g y) = y) ∧
      (∀ᶠ Y in nhds X,
        selectedWindowEnergy (by omega) s Y <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        RationalConfiguration.closure (by omega) (rationalSign s) Y = 0 →
        modelRecovery (show 2 ≤ m by omega) s g
          (fixedSchurCoordinates (show 2 ≤ m by omega) s Y) = Y) := by
  have hbase : ExplicitHessianThreshold.orderThreshold ≤ 2 * m :=
    (le_max_left _ _).trans hN
  let x := fixedSchurCoordinates (show 2 ≤ m by omega) s X
  have hx : x ∈ FixedSchurChartSmooth.domain (by omega) :=
    ExplicitRationalTransfer.fixedSchurCoordinates_inDomain hN hm s X hwindow
  obtain ⟨g, hgx, hg, hglocal⟩ :=
    ExplicitHessianThresholdFixedSchur.local_model hbase (by omega) s x hx
  have hrepresentation :=
    ExplicitRationalRepresentation.selectedWindow_representation hN
      (show 2 ≤ m by omega) s X hwindow hclosure
  have hCx : modelCenter g x =
      normalizedCenter (by omega) (rationalSign s) X := by
    change center (g x) x.2 = _
    rw [hgx]
    exact hrepresentation.2.1.symm
  have hangle (j : Fin m) :
      Real.cos (relativeAngle (by omega) x.1 j / 2) ≠ 0 := by
    have he : relativeAngle (by omega) x.1 j =
        RationalAngleBranch.angle (by omega) X j := by
      dsimp only [x, fixedSchurCoordinates]
      exact RationalSelectorRoundTrip.relativeAngle_theta (by omega) X j
    rw [he]
    unfold RationalAngleBranch.angle
    simp only [Nat.mod_eq_of_lt j.isLt]
    have he' : 2 * Real.arctan
        (RationalConfiguration.angleParameter X j) / 2 =
        Real.arctan (RationalConfiguration.angleParameter X j) := by ring
    rw [he', Real.cos_arctan]
    positivity
  have hden (j : Fin m) :
      1 + (relativeCrossing (show 2 ≤ m by omega) s x.1
        (modelCenter g x) j).re ≠ 0 := by
    rw [hCx]
    dsimp only [x, fixedSchurCoordinates]
    rw [relativeCrossing_normalized_eq_rotation (show 2 ≤ m by omega)
      s X hclosure]
    exact (RationalChart.one_add_rotation_re_pos _).ne'
  have hrecover : modelRecovery (show 2 ≤ m by omega) s g x = X := by
    unfold modelRecovery
    rw [hCx]
    dsimp only [x, fixedSchurCoordinates]
    exact physical_recovery_parameters_eq (show 2 ≤ m by omega) s X hclosure
  have hsmooth := modelRecovery_contDiffAt (show 2 ≤ m by omega)
    s g x hg hangle hden
  have hforward : ∀ᶠ y in nhds x,
      y ∈ FixedSchurChartSmooth.domain (by omega) →
      RationalConfiguration.closure (by omega) (rationalSign s)
          (modelRecovery (show 2 ≤ m by omega) s g y) = 0 ∧
        fixedSchurCoordinates (show 2 ≤ m by omega) s
          (modelRecovery (show 2 ≤ m by omega) s g y) = y := by
    filter_upwards [hglocal] with y hgy hy
    have hgeq : g y = coordinate (by omega) s y.1 y.2 := hgy.2.2 hy
    have hReq : modelRecovery (show 2 ≤ m by omega) s g y =
        parameters (show 2 ≤ m by omega) s y.1
          (center (coordinate (by omega) s y.1 y.2) y.2) := by
      simp only [modelRecovery, modelCenter, hgeq]
    have hd := ExplicitRationalRecovery.recovery_data hbase
      (show 2 ≤ m by omega) s y.1 y.2 hy
    dsimp only at hd
    rw [hReq]
    refine ⟨hd.2.2.1, ?_⟩
    apply Prod.ext
    · exact hd.1
    · dsimp only [fixedSchurCoordinates]
      rw [hd.2.1]
      exact (ExplicitHessianThresholdFixedSchur.coordinate_properties hbase
        (show 2 ≤ m by omega) s y.1 y.2 hy).free_projection
  have hcoordContinuous : ContinuousAt
      (fixedSchurCoordinates (show 2 ≤ m by omega) s) X :=
    (fixedSchurCoordinates_differentiable (show 2 ≤ m by omega) s X).continuousAt
  have hback : ∀ᶠ Y in nhds X,
      selectedWindowEnergy (by omega) s Y <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
      RationalConfiguration.closure (by omega) (rationalSign s) Y = 0 →
      modelRecovery (show 2 ≤ m by omega) s g
        (fixedSchurCoordinates (show 2 ≤ m by omega) s Y) = Y := by
    have hnear := hcoordContinuous.tendsto.eventually hglocal
    filter_upwards [hnear] with Y hY hYwindow hYclosure
    let y := fixedSchurCoordinates (show 2 ≤ m by omega) s Y
    have hy : y ∈ FixedSchurChartSmooth.domain (by omega) :=
      ExplicitRationalTransfer.fixedSchurCoordinates_inDomain hN
        hm s Y hYwindow
    have hgeq : g y = coordinate (by omega) s y.1 y.2 := hY.2.2 hy
    have hYrep := ExplicitRationalRepresentation.selectedWindow_representation
      hN (show 2 ≤ m by omega) s Y hYwindow hYclosure
    have hcenter : modelCenter g y =
        normalizedCenter (by omega) (rationalSign s) Y := by
      change center (g y) y.2 = _
      rw [hgeq]
      exact hYrep.2.1.symm
    unfold modelRecovery
    rw [hcenter]
    dsimp only [y, fixedSchurCoordinates]
    exact physical_recovery_parameters_eq (show 2 ≤ m by omega)
      s Y hYclosure
  exact ⟨g, hg, hrecover, hsmooth, hforward, hback⟩

theorem rational_stationary_fixed {m : ℕ}
    (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m)
    (hm : 8 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
    (Y : RationalStationarySystem.Variables m → ℝ)
    (hwindow : selectedWindowEnergy (by omega) s
      (RationalStationarySystem.coordinates Y) <
        (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2))
    (hstationary : RationalStationarySystem.Stationary
      (by omega) (halfWord s) Y) :
    FixedSchurStationaryUniqueness.Stationary (by omega) s
      (fixedSchurCoordinates (show 2 ≤ m by omega) s
        (RationalStationarySystem.coordinates Y)) := by
  let X := RationalStationarySystem.coordinates Y
  let x := fixedSchurCoordinates (show 2 ≤ m by omega) s X
  have hclosure : RationalConfiguration.closure (by omega)
      (rationalSign s) X = 0 := by
    rw [← sign_halfWord]
    exact hstationary.1
  obtain ⟨g, hg, hrecover, hsmooth, hforward, _⟩ :=
    smooth_local_recovery hN hm s X hwindow hclosure
  intro d hd
  let A : ℝ → FixedSchurEquationSmooth.SchurParameters m :=
    fun t => affinePath x d t
  let Z : ℝ → (RationalConfiguration.Variables m → ℝ) :=
    fun t => modelRecovery (show 2 ≤ m by omega) s g (A t)
  have hA : ContDiffAt ℝ ∞ A 0 := by
    dsimp only [A]
    exact affinePath_contDiff x d |>.contDiffAt
  have hA0 : A 0 = x := by
    simp only [A, affinePath, zero_smul, add_zero]
  have hx : x ∈ FixedSchurChartSmooth.domain (by omega) :=
    ExplicitRationalTransfer.fixedSchurCoordinates_inDomain hN
      hm s X hwindow
  have hAdom : ∀ᶠ t in nhds (0 : ℝ),
      A t ∈ FixedSchurChartSmooth.domain (by omega) := by
    simpa only [A, CommonFiberCanonical.domain, FixedSchurChartSmooth.domain] using
      affine_domain_near_zero (by omega) x d hx hd
  have hAto : Tendsto A (nhds 0) (nhds x) := by
    rw [← hA0]
    exact hA.continuousAt
  have hforwardA := hAto.eventually hforward
  have hclosed : ∀ᶠ t in nhds (0 : ℝ),
      RationalConfiguration.closure (by omega) (rationalSign s) (Z t) = 0 := by
    filter_upwards [hforwardA, hAdom] with t ht htdom
    exact (ht htdom).1
  have hcoords : ∀ᶠ t in nhds (0 : ℝ),
      fixedSchurCoordinates (show 2 ≤ m by omega) s (Z t) = A t := by
    filter_upwards [hforwardA, hAdom] with t ht htdom
    exact (ht htdom).2
  have hZ : ContDiffAt ℝ ∞ Z 0 := by
    have hsmooth' : ContDiffAt ℝ ∞
        (modelRecovery (show 2 ≤ m by omega) s g) (A 0) := by
      simpa only [hA0] using hsmooth
    exact hsmooth'.comp 0 hA
  have hZ0 : Z 0 = X := by
    dsimp only [Z]
    rw [hA0]
    exact hrecover
  have hfree : CollisionFree (by omega) (halfWord s) X :=
    ExplicitRationalTransfer.selectedWindow_collisionFree hN
      hm s X hwindow hclosure
  have hcrit := stationary_lagrangian_fderiv_zero
    (by omega) (halfWord s) Y hfree hstationary
  have hlagSmooth := lagrangianValue_contDiffAt (by omega) (halfWord s)
    (multiplier Y) X hfree
  have hlagDeriv : deriv (fun t => lagrangianValue (by omega) (halfWord s)
      (multiplier Y) (Z t)) 0 = 0 := by
    have houter : DifferentiableAt ℝ
        (lagrangianValue (by omega) (halfWord s) (multiplier Y)) (Z 0) := by
      simpa only [hZ0] using hlagSmooth.differentiableAt (by simp)
    rw [show (fun t => lagrangianValue (by omega) (halfWord s)
        (multiplier Y) (Z t)) =
      lagrangianValue (by omega) (halfWord s) (multiplier Y) ∘ Z by rfl,
      fderiv_comp_deriv 0 houter (hZ.differentiableAt (by simp)), hZ0, hcrit]
    exact _root_.zero_apply _
  have hlagObj : (fun t => lagrangianValue (by omega) (halfWord s)
      (multiplier Y) (Z t)) =ᶠ[nhds 0]
      fun t => RationalStationarySystem.objective
        (by omega) (halfWord s) (Z t) := by
    filter_upwards [hclosed] with t ht
    have hce : ∀ k, (closureCoordinate (by omega) (halfWord s) k).eval
        (Z t) = 0 := by
      apply (closure_equations_iff (by omega) (halfWord s) (Z t)).2
      rwa [sign_halfWord]
    unfold lagrangianValue
    simp only [hce, mul_zero, Finset.sum_const_zero, sub_zero]
  have hratZero : deriv (fun t => RationalStationarySystem.objective
      (by omega) (halfWord s) (Z t)) 0 = 0 := by
    rw [← hlagObj.deriv_eq]
    exact hlagDeriv
  have htransfer := ExplicitRationalTransfer.objective_path_deriv_eq hN
    hm s Z 0 hZ.continuousAt (by simpa only [hZ0] using hwindow) hclosed
  have hfixedAffine : (fun t => FixedSchurObjectivePaths.objective (by omega) s
      (fixedSchurCoordinates (show 2 ≤ m by omega) s (Z t))) =ᶠ[nhds 0]
      fun t => FixedSchurObjectivePaths.objective (by omega) s (A t) := by
    filter_upwards [hcoords] with t ht
    rw [ht]
  calc
    deriv (fun t => FixedSchurObjectivePaths.objective (by omega) s
        (affinePath x d t)) 0 =
        deriv (fun t => FixedSchurObjectivePaths.objective (by omega) s (A t)) 0 := by rfl
    _ = deriv (fun t => FixedSchurObjectivePaths.objective (by omega) s
        (fixedSchurCoordinates (show 2 ≤ m by omega) s (Z t))) 0 :=
      hfixedAffine.deriv_eq.symm
    _ = deriv (fun t => RationalStationarySystem.objective
        (by omega) (halfWord s) (Z t)) 0 := htransfer.symm
    _ = 0 := hratZero

theorem affine_strict_curvature {m : ℕ}
    (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m)
    (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
    (x d : FixedSchurEquationSmooth.SchurParameters m) (t : ℝ)
    (hx : affinePath x d t ∈ FixedSchurChartSmooth.domain (by omega))
    (hd : Admissible (by omega) d) (hne : d ≠ 0) :
    deriv (deriv (fun r => FixedSchurObjectivePaths.objective
      (by omega) s (affinePath x d r))) t < 0 := by
  have hbase : ExplicitHessianThreshold.orderThreshold ≤ 2 * m :=
    (le_max_left _ _).trans hN
  rw [ExplicitCanonicalEntryObjectivePaths.affine_deriv2_eq
    hbase hm s x d t hx hd]
  have hb := (ExplicitFixedSchurHessianEstimate.actual_hessian_estimate
    hbase hm s (affinePath x d t).1 d.1
      (affinePath x d t).2 d.2 hx hd).2
  have hsplit : d.1 ≠ 0 ∨ d.2 ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hne (Prod.ext hh.1 hh.2)
  have hp := HessianEnergyPositive.total_energy_pos
    (show 2 ≤ 2 * m by omega) d.1 d.2 hd.2.1 hd.2.2.2.1 hsplit
  exact hb.trans_lt (by linarith only [hp])

theorem rational_lagrangianHessian_negative {m : ℕ}
    (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m)
    (hm : 8 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
    (Y : RationalStationarySystem.Variables m → ℝ)
    (hwindow : selectedWindowEnergy (by omega) s
      (RationalStationarySystem.coordinates Y) <
        (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2))
    (hstationary : RationalStationarySystem.Stationary
      (by omega) (halfWord s) Y) :
    ∀ u : RationalConfiguration.Variables m → ℝ,
      closureMatrix (by omega) (halfWord s)
          (RationalStationarySystem.coordinates Y) *ᵥ u = 0 →
      u ≠ 0 →
      u ⬝ᵥ (RationalBorderedJacobian.lagrangianHessian
          (by omega) (halfWord s)
          (RationalStationarySystem.coordinates Y)
          (RationalStationarySystem.multiplier Y) *ᵥ u) < 0 := by
  intro u hukernel hune
  let X := RationalStationarySystem.coordinates Y
  let x := fixedSchurCoordinates (show 2 ≤ m by omega) s X
  have hclosure : RationalConfiguration.closure (by omega)
      (rationalSign s) X = 0 := by
    rw [← sign_halfWord]
    exact hstationary.1
  have honto : Function.Surjective
      (closureFDeriv (by omega) (rationalSign s) X) :=
    (ExplicitRationalClosure.selectedWindow_closure_hasFDerivAt_surjective
      hN hm s X hwindow hclosure).2
  have huclosure : closureFDeriv (by omega) (rationalSign s) X u = 0 := by
    rw [← sign_halfWord]
    exact closureFDeriv_eq_zero_of_matrix_mulVec_eq_zero
      (by omega) (halfWord s) X u hukernel
  obtain ⟨Z, hZ0, hZsmooth, hZclosed, hZderiv⟩ :=
    exists_smooth_closed_path (by omega) (rationalSign s) X u
      hclosure honto huclosure
  obtain ⟨g, hg, hrecover, hsmooth, hforward, hback⟩ :=
    smooth_local_recovery hN hm s X hwindow hclosure
  let P : ℝ → FixedSchurEquationSmooth.SchurParameters m :=
    fun t => fixedSchurCoordinates (show 2 ≤ m by omega) s (Z t)
  have hP0 : P 0 = x := by
    dsimp only [P, x]
    rw [hZ0]
  have hPdiff : DifferentiableAt ℝ P 0 := by
    have hout : DifferentiableAt ℝ
        (fixedSchurCoordinates (show 2 ≤ m by omega) s) (Z 0) :=
      fixedSchurCoordinates_differentiable (show 2 ≤ m by omega) s (Z 0)
    exact hout.comp 0 (hZsmooth.differentiableAt (by simp))
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
  have hPadmissible : ∀ᶠ t in nhds (0 : ℝ),
      Admissible (by omega) (P t) := by
    filter_upwards [hwindowNear] with t ht
    have hPt := ExplicitRationalTransfer.fixedSchurCoordinates_inDomain
      hN hm s (Z t) ht
    exact ⟨hPt.1, hPt.2.1, hPt.2.2.1⟩
  let d := deriv P 0
  have hd : Admissible (by omega) d :=
    admissible_deriv_of_eventually (by omega) P hPdiff hPadmissible
  let R : FixedSchurEquationSmooth.SchurParameters m →
      (RationalConfiguration.Variables m → ℝ) :=
    modelRecovery (show 2 ≤ m by omega) s g
  have hRdiff : DifferentiableAt ℝ R x := by
    simpa only [R, x] using hsmooth.differentiableAt (by simp)
  have hZto : Tendsto Z (nhds 0) (nhds X) := by
    rw [← hZ0]
    exact hZsmooth.continuousAt
  have hbackZ := hZto.eventually hback
  have hRP_eq_Z : (fun t => R (P t)) =ᶠ[nhds 0] Z := by
    filter_upwards [hbackZ, hwindowNear, hZclosed] with t hb hw hc
    exact hb hw hc
  have hR_d_eq_u : fderiv ℝ R x d = u := by
    calc
      fderiv ℝ R x d = deriv (fun t => R (P t)) 0 := by
        rw [show (fun t => R (P t)) = R ∘ P by rfl,
          fderiv_comp_deriv 0 (by simpa only [hP0] using hRdiff) hPdiff]
        simp only [hP0, d]
      _ = deriv Z 0 := hRP_eq_Z.deriv_eq
      _ = u := hZderiv
  have hdne : d ≠ 0 := by
    intro hdzero
    have hu0 : u = 0 := by
      rw [hdzero, map_zero] at hR_d_eq_u
      exact hR_d_eq_u.symm
    exact hune hu0
  let A : ℝ → FixedSchurEquationSmooth.SchurParameters m :=
    fun t => affinePath x d t
  let W : ℝ → (RationalConfiguration.Variables m → ℝ) :=
    fun t => R (A t)
  have hA : ContDiffAt ℝ ∞ A 0 := by
    dsimp only [A]
    exact affinePath_contDiff x d |>.contDiffAt
  have hA0 : A 0 = x := by
    simp only [A, affinePath, zero_smul, add_zero]
  have hx : x ∈ FixedSchurChartSmooth.domain (by omega) :=
    ExplicitRationalTransfer.fixedSchurCoordinates_inDomain hN
      hm s X hwindow
  have hAdom : ∀ᶠ t in nhds (0 : ℝ),
      A t ∈ FixedSchurChartSmooth.domain (by omega) := by
    simpa only [A, CommonFiberCanonical.domain, FixedSchurChartSmooth.domain] using
      affine_domain_near_zero (by omega) x d hx hd
  have hAto : Tendsto A (nhds 0) (nhds x) := by
    rw [← hA0]
    exact hA.continuousAt
  have hforwardA := hAto.eventually hforward
  have hWclosed : ∀ᶠ t in nhds (0 : ℝ),
      RationalConfiguration.closure (by omega) (rationalSign s) (W t) = 0 := by
    filter_upwards [hforwardA, hAdom] with t ht htdom
    exact (ht htdom).1
  have hWcoords : ∀ᶠ t in nhds (0 : ℝ),
      fixedSchurCoordinates (show 2 ≤ m by omega) s (W t) = A t := by
    filter_upwards [hforwardA, hAdom] with t ht htdom
    exact (ht htdom).2
  have hWsmooth : ContDiffAt ℝ ∞ W 0 := by
    have hsmooth' : ContDiffAt ℝ ∞ R (A 0) := by
      simpa only [hA0] using hsmooth
    exact hsmooth'.comp 0 hA
  have hW0 : W 0 = X := by
    dsimp only [W, R]
    rw [hA0]
    exact hrecover
  have hAderiv : deriv A 0 = d := by
    dsimp only [A, affinePath]
    simpa only [one_smul] using
      (((hasDerivAt_id' (0 : ℝ)).smul_const d).const_add x).deriv
  have hWderiv : deriv W 0 = u := by
    rw [show W = R ∘ A by rfl,
      fderiv_comp_deriv 0 (by simpa only [hA0] using hRdiff)
        (hA.differentiableAt (by simp)), hA0, hAderiv]
    exact hR_d_eq_u
  have hfree : CollisionFree (by omega) (halfWord s) X :=
    ExplicitRationalTransfer.selectedWindow_collisionFree hN
      hm s X hwindow hclosure
  have hcritical := stationary_lagrangian_fderiv_zero
    (by omega) (halfWord s) Y hfree hstationary
  have hlagSmooth := lagrangianValue_contDiffAt (by omega) (halfWord s)
    (multiplier Y) X hfree
  have hpathAffine := second_deriv_comp_eq_affine_of_critical
    (lagrangianValue (by omega) (halfWord s) (multiplier Y)) X u W
    (hlagSmooth.of_le
      (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
    (hWsmooth.of_le
      (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
    hW0 hWderiv hcritical
  have hlagObj : (fun t => lagrangianValue (by omega) (halfWord s)
      (multiplier Y) (W t)) =ᶠ[nhds 0]
      fun t => RationalStationarySystem.objective
        (by omega) (halfWord s) (W t) := by
    filter_upwards [hWclosed] with t ht
    apply lagrangianValue_eq_objective_of_closure
    rwa [sign_halfWord]
  have htransfer := ExplicitRationalTransfer.objective_path_second_deriv_eq
    hN hm s W 0 hWsmooth.continuousAt
      (by simpa only [hW0] using hwindow) hWclosed
  have hfixedAffine : (fun t => FixedSchurObjectivePaths.objective
      (by omega) s
      (fixedSchurCoordinates (show 2 ≤ m by omega) s (W t))) =ᶠ[nhds 0]
      fun t => FixedSchurObjectivePaths.objective (by omega) s (A t) := by
    filter_upwards [hWcoords] with t ht
    rw [ht]
  have hstrict : deriv (deriv (fun t => FixedSchurObjectivePaths.objective
      (by omega) s (A t))) 0 < 0 := by
    apply affine_strict_curvature hN (show 2 ≤ m by omega) s x d 0
    · simpa only [A, affinePath, zero_smul, add_zero] using hx
    · exact hd
    · exact hdne
  calc
    u ⬝ᵥ (RationalBorderedJacobian.lagrangianHessian
        (by omega) (halfWord s) X (multiplier Y) *ᵥ u) =
        deriv (deriv (fun t => lagrangianValue (by omega) (halfWord s)
          (multiplier Y) (FixedSchurRationalLagrangian.affineVariables X u t))) 0 :=
      lagrangianHessian_quadratic_eq_second (by omega) (halfWord s)
        (multiplier Y) X u hfree
    _ = deriv (deriv (fun t => lagrangianValue (by omega) (halfWord s)
          (multiplier Y) (W t))) 0 := hpathAffine.symm
    _ = deriv (deriv (fun t => RationalStationarySystem.objective
          (by omega) (halfWord s) (W t))) 0 := hlagObj.deriv.deriv_eq
    _ = deriv (deriv (fun t => FixedSchurObjectivePaths.objective
          (by omega) s
          (fixedSchurCoordinates (show 2 ≤ m by omega) s (W t)))) 0 := htransfer
    _ = deriv (deriv (fun t => FixedSchurObjectivePaths.objective
          (by omega) s (A t))) 0 := hfixedAffine.deriv.deriv_eq
    _ < 0 := hstrict

theorem selectedWindow_stationary_jacobian_nonsingular {m : ℕ}
    (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m)
    (hm : 8 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
    (Y : RationalStationarySystem.Variables m → ℝ)
    (hwindow : selectedWindowEnergy (by omega) s
      (RationalStationarySystem.coordinates Y) <
        (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2))
    (hstationary : RationalStationarySystem.Stationary
      (by omega) (halfWord s) Y) :
    (RationalSystemAlgebraicity.jacobian
      (RationalStationarySystem.systemExpression
        (by omega) (halfWord s)) Y).det ≠ 0 := by
  let X := RationalStationarySystem.coordinates Y
  have hclosure : RationalConfiguration.closure (by omega)
      (rationalSign s) X = 0 := by
    rw [← sign_halfWord]
    exact hstationary.1
  apply RationalBorderedJacobian.stationary_jacobian_nonsingular
  · exact ExplicitRationalTransfer.selectedWindow_collisionFree
      hN hm s X hwindow hclosure
  · exact ExplicitRationalClosure.selectedWindow_closureMatrix_surjective
      hN hm s X hwindow hclosure
  · intro u hu hune
    exact rational_lagrangianHessian_negative
      hN hm s Y hwindow hstationary u hu hune

end
end StructuralNote.ExplicitRationalStationaryTransfer

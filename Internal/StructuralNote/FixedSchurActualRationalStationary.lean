import StructuralNote.FixedSchurActualRationalEntry
import StructuralNote.FixedSchurRationalStationaryTransfer

/-! Existence of literal rational stationary coordinates at actual even-order
extremizers. -/

namespace StructuralNote.FixedSchurActualRationalStationary

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

noncomputable section

/-- A real functional that vanishes on the kernel of an onto complex-valued
linear map is a real linear combination of its real and imaginary parts. -/
theorem exists_complex_multiplier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] ℂ) (F : E →L[ℝ] ℝ)
    (hB : Function.Surjective B)
    (hker : ∀ u, B u = 0 → F u = 0) :
    ∃ μ : Fin 2 → ℝ, ∀ u,
      F u = μ 0 * (B u).re + μ 1 * (B u).im := by
  obtain ⟨e₀, he₀⟩ := hB 1
  obtain ⟨e₁, he₁⟩ := hB I
  let μ : Fin 2 → ℝ := fun k => if k.val = 0 then F e₀ else F e₁
  refine ⟨μ, ?_⟩
  intro u
  let w := u - (B u).re • e₀ - (B u).im • e₁
  have hwB : B w = 0 := by
    dsimp only [w]
    rw [map_sub, map_sub, map_smul, map_smul, he₀, he₁]
    apply Complex.ext <;> simp
  have hwF : F w = 0 := hker w hwB
  have heq : F u - (B u).re * F e₀ - (B u).im * F e₁ = 0 := by
    simpa only [w, map_sub, map_smul, smul_eq_mul] using hwF
  dsimp only [μ]
  norm_num
  linarith

/-- A strict-window rational point whose chosen fixed-Schur coordinates are
stationary admits actual real Lagrange multipliers for the two literal closure
equations. -/
theorem eventual_exists_rational_stationary_of_fixed_stationary :
    ∀ᶠ m : ℕ in atTop,
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
  filter_upwards [eventual_selectedWindow_closure_hasFDerivAt_surjective,
    eventual_selectedWindow_collisionFree,
    eventual_fixedSchurCoordinates_inDomain,
    eventual_objective_path_eventuallyEq,
    FixedSchurStationaryUniqueness.eventual_stationary_global_max] with
      m hfull hcollision hdomain htransfer hglobal
  intro hm s X hwindow hclosure hstationary
  let x := fixedSchurCoordinates (show 2 ≤ m by omega) s X
  have hx : x ∈ FixedSchurChartSmooth.domain (by omega) :=
    hdomain hm s X hwindow
  have hmax : IsMaxOn (FixedSchurObjectivePaths.objective (by omega) s)
      (FixedSchurChartSmooth.domain (by omega)) x :=
    hglobal (show 2 ≤ m by omega) s x hx hstationary
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

/-- Every sufficiently large actual even-order diameter extremizer therefore
has an explicit literal rational recovery together with two real multipliers
solving the genuine rational stationary system. -/
theorem eventual_actual_extremizer_rational_stationary :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 3 ≤ m) (x : FixedSchurEquationSmooth.SchurParameters m)
        (Y : RationalStationarySystem.Variables m → ℝ),
        CanonicalRepresentative hm z x ∧
        let s := FixedSchurCanonicalWordSymmetry.canonicalPattern hm
        let C := center (FixedSchurChart.coordinate (by omega) s x.1 x.2) x.2
        let X := FixedSchurRationalRecovery.parameters (by omega) s x.1 C
        theta (by omega) X = x.1 ∧
        normalizedCenter (by omega) (rationalSign s) X = C ∧
        RationalConfiguration.closure (by omega) (rationalSign s) X = 0 ∧
        selectedWindowEnergy (by omega) s X <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) ∧
        RationalStationarySystem.coordinates Y = X ∧
        RationalStationarySystem.Stationary (by omega) (halfWord s) Y := by
  obtain ⟨m₀, hentry⟩ := eventual_actual_extremizer_rational_recovery
  obtain ⟨m₁, hexists⟩ := eventually_atTop.1
    eventual_exists_rational_stationary_of_fixed_stationary
  obtain ⟨m₂, hgeometric⟩ := eventually_atTop.1
    FixedSchurGeometricStationarity.eventual_geometric_extremal_stationary
  obtain ⟨m₃, hproperties⟩ := eventually_atTop.1
    FixedSchurChart.eventual_coordinate_properties
  refine ⟨max 8 (max m₀ (max m₁ (max m₂ m₃))), ?_⟩
  intro m hm z hz
  obtain ⟨hm3, x, hx, htheta, hcenter, hclosure, hwindow⟩ :=
    hentry m (by omega) z hz
  let s := FixedSchurCanonicalWordSymmetry.canonicalPattern hm3
  let C := center (FixedSchurChart.coordinate (by omega) s x.1 x.2) x.2
  let X := FixedSchurRationalRecovery.parameters (by omega) s x.1 C
  have hfixed : FixedSchurStationaryUniqueness.Stationary (by omega) s x :=
    hgeometric m (by omega) (show 2 ≤ m by omega) s x hx.1 hx.2.1
  have hcoords : fixedSchurCoordinates (show 2 ≤ m by omega) s X = x := by
    apply Prod.ext
    · exact htheta
    · dsimp only [fixedSchurCoordinates]
      rw [hcenter]
      exact (hproperties m (by omega) (show 2 ≤ m by omega) s x.1 x.2 hx.1).free_projection
  have hfixedX : FixedSchurStationaryUniqueness.Stationary (by omega) s
      (fixedSchurCoordinates (show 2 ≤ m by omega) s X) := by
    rw [hcoords]
    exact hfixed
  obtain ⟨Y, hYX, hYstationary⟩ :=
    hexists m (by omega) (show 8 ≤ m by omega) s X hwindow hclosure hfixedX
  exact ⟨hm3, x, Y, hx, htheta, hcenter, hclosure, hwindow, hYX, hYstationary⟩

end
end StructuralNote.FixedSchurActualRationalStationary

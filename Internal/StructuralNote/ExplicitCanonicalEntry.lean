import StructuralNote.ExplicitThresholdFunctions
import StructuralNote.ExplicitHessianThresholdDownstream

/-! A finite, pointwise bridge from an actual balanced fixed-Schur chart to
the canonical fiber.  The only order condition is an explicit symbolic bound
which places the actual projected center in the common chart domain. -/

namespace StructuralNote.ExplicitCanonicalEntry

set_option maxHeartbeats 800000

open Complex
open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open Erdos1045.ExplicitThreshold
open Erdos1045.EventualExact.CommonLocalization
open Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.SchurLift
open Erdos1045.EventualExact.SchurSpectrum
open CommonDomainClosure CommonDomainRadius CommonTangentialParameters
open MatchingActivityRadialActual MatchingActivityRadialIntegration
open MatchingActivityNonlocalPairs NormalizedPolarRepresentation ExtremalPolarCenter
open StrongPointwiseCoordinates ActualCrossingGeometry
open FixedSchurLinear FixedSchurProjectionDomain FixedSchurChart
open FixedSchurEquationSmooth FixedSchurChartSmooth FixedSchurObjectivePaths
open FixedSchurCyclicEquivariance FixedSchurExtremalSymmetry
open FixedSchurCanonicalWordSymmetry FixedSchurCanonicalAlignment SignPatternSymmetry
open MatchingActivityActualChart MatchingActivityActualChartEntry
open MatchingActivityActualWordBalanced FiniteWordClassification
open FixedSchurActualCanonicalEntry FixedSchurActualRigidEquivalence
open ExplicitHessianThresholdDownstream
open scoped BigOperators

noncomputable section

/-- A literal threshold ensuring that `K / n²` lies in the logarithmic chart
ball.  It is deliberately left as an unevaluated natural-number expression. -/
def projectionThreshold (K : ℝ) : ℕ :=
  growthThreshold (Real.log 2 * (|K| + 1))

theorem fixed_energy_lt_radius {n : ℕ} {K : ℝ}
    (hn : projectionThreshold K ≤ n) :
    K / (n : ℝ) ^ 2 < energyRadius n := by
  have hn2 : 2 ≤ n := by
    have hg : growthThreshold (Real.log 2 * (|K| + 1)) ≤ n := hn
    exact (show 2 ≤ growthThreshold (Real.log 2 * (|K| + 1)) by
      unfold growthThreshold
      exact Nat.one_lt_two_pow (by omega)).trans hg
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hg := growth_log_gt hn
  have hc : Real.log n / Real.log 2 ≤ (CommonDomainRadius.logOrder n : ℝ) := Nat.le_ceil _
  have hh : |K| + 1 < (CommonDomainRadius.logOrder n : ℝ) := by
    apply lt_of_lt_of_le ?_ hc
    exact (lt_div_iff₀ hlog2).mpr (by simpa only [mul_comm] using hg)
  have hs : K < (CommonDomainRadius.logOrder n : ℝ) ^ 2 := by
    have ha := le_abs_self K
    have hz := abs_nonneg K
    nlinarith
  exact (div_lt_div_iff_of_pos_right (sq_pos_of_pos hnR)).mpr hs

/-- Pointwise replacement for `eventually_projection_inDomain`. -/
theorem projection_inDomain {m : ℕ} {K : ℝ}
    (hn : projectionThreshold K ≤ 2 * m) (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (C : Fin (2 * m) → ℂ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hθmean : (∑ j, (θ j : ℂ)) = 0)
    (hC : HalfPeriodic (by omega) C) (hCmean : (∑ j, C j) = 0)
    (henergy : pairEnergy (by omega) (fun j => (θ j : ℂ)) +
      pairEnergy (by omega) (projection hm C) ≤ K / (2 * m : ℝ) ^ 2) :
    InDomain (by omega) θ (projection hm C) := by
  refine ⟨hθ, hθmean, projection_parameterSpace hm hC hCmean,
    henergy.trans_lt ?_⟩
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    (fixed_energy_lt_radius (n := 2 * m) hn)

def orderThreshold : ℕ := projectionThreshold actualChartEnergyConstant

/-- Pointwise canonicalization of one actual chart.  The balanced-word stage
is an input; cyclic chart equivariance is supplied by the finite fiber data. -/
theorem canonical_entry_of_actual_chart {m : ℕ} (hm : 3 ≤ m)
    (D : FixedSchurFiberData hm) {z : Points (2 * m)}
    {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    {s : SignPattern (by omega : 0 < m)}
    (hn : orderThreshold ≤ 2 * m)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hmodel : NormalizedRelativeEdgeModel z π α β u η)
    (henergy : pairEnergy (by omega) (fun j => (normalizedAngle m u j : ℂ)) +
        pairEnergy (by omega)
          (projection (by omega : 2 ≤ m) (centerZero (actualCenter m β u))) ≤
      actualChartEnergyConstant / (2 * m : ℝ) ^ 2)
    (hconfig : (fun j => normalizedPoint m β u j - average (actualCenter m β u)) =
      configuration (by omega) s (normalizedAngle m u)
        (projection (by omega : 2 ≤ m) (centerZero (actualCenter m β u))))
    (hbalanced : BalancedWord (by omega) s) :
    ∃ x : SchurParameters m,
      CanonicalRepresentative hm z x ∧
      pairEnergy (by omega) (fun j => (x.1 j : ℂ)) + pairEnergy (by omega) x.2 ≤
        actualChartEnergyConstant / (2 * m : ℝ) ^ 2 ∧
      DirectRigidRelabeling z
        (configuration (by omega) (canonicalPattern hm) x.1 x.2) ∧
      FixedSchurStationaryUniqueness.Stationary (by omega) (canonicalPattern hm) x := by
  let θ : Fin (2 * m) → ℝ := normalizedAngle m u
  let C : Fin (2 * m) → ℂ := centerZero (actualCenter m β u)
  let v : Fin (2 * m) → ℂ := projection (by omega : 2 ≤ m) C
  have hθhalf : HalfPeriodic (by omega) (fun j => (θ j : ℂ)) := by
    intro j
    exact congrArg Complex.ofReal
      (normalizedAngle_halfPeriodic (by omega) u hmodel.periodic j)
  have hθmean : (∑ j, (θ j : ℂ)) = 0 := by
    dsimp only [θ]
    rw [← Complex.ofReal_sum, normalizedAngle_mean_zero (by omega) u]
    norm_num
  have hCbase : HalfPeriodic (by omega) (actualCenter m β u) :=
    actualCenter_halfPeriodic (by omega) β u hmodel.periodic
  have hChalf : HalfPeriodic (by omega) C :=
    centerZero_halfPeriodic (by omega) _ hCbase
  have hCmean : (∑ j, C j) = 0 := centerZero_sum (by omega) _
  have hdom : InDomain (by omega) θ v := by
    apply projection_inDomain hn (by omega) θ C hθhalf hθmean hChalf hCmean
    simpa only [θ, C, v, Nat.cast_mul, Nat.cast_ofNat] using henergy
  have hchart : ExtremalNormalization.DiameterExtremal
      (configuration (by omega) s θ v) := by
    have hext := diameterExtremal_sub_const (normalizedPoint m β u)
      (MatchingActivitySaturation.model_normalizedPoint_extremal hmodel hz)
      (average (actualCenter m β u))
    change (fun j => normalizedPoint m β u j - average (actualCenter m β u)) =
      configuration (by omega) s θ v at hconfig
    rw [← hconfig]
    exact hext
  have hdisc : discriminant (configuration (by omega) s θ v) = discriminant z := by
    calc
      discriminant (configuration (by omega) s θ v) =
          discriminant (fun j => normalizedPoint m β u j -
            average (actualCenter m β u)) := congrArg discriminant hconfig.symm
      _ = discriminant (normalizedPoint m β u) := discriminant_sub_const _ _
      _ = discriminant z := MatchingActivitySaturation.model_discriminant_normalizedPoint hmodel
  obtain ⟨k, hword⟩ := balancedWord_canonical_alignment hm s hbalanced
  let x : SchurParameters m := (cyclicReal k θ, cyclicCenter k v)
  have hxdom : x ∈ domain (by omega) := inDomain_cyclic (by omega) k θ v hdom
  have hcanConfig : configuration (by omega) (canonicalPattern hm) x.1 x.2 =
      cyclicCenter k (configuration (by omega) s θ v) := by
    dsimp only [x]
    rw [← hword]
    exact D.cyclicConfiguration k s θ v hdom
  have hxext : ExtremalNormalization.DiameterExtremal
      (configuration (by omega) (canonicalPattern hm) x.1 x.2) := by
    rw [hcanConfig]
    exact diameterExtremal_cyclicCenter k hchart
  have hxdisc : discriminant
      (configuration (by omega) (canonicalPattern hm) x.1 x.2) = discriminant z := by
    rw [hcanConfig, discriminant_cyclicCenter, hdisc]
  have hxenergy : pairEnergy (by omega) (fun j => (x.1 j : ℂ)) +
      pairEnergy (by omega) x.2 ≤ actualChartEnergyConstant / (2 * m : ℝ) ^ 2 := by
    dsimp only [x]
    rw [pairEnergy_cyclicReal (show 2 ≤ 2 * m by omega),
      pairEnergy_cyclicCenter (show 2 ≤ 2 * m by omega)]
    simpa only [θ, v, C, Nat.cast_mul, Nat.cast_ofNat] using henergy
  have hrigid : DirectRigidRelabeling z
      (configuration (by omega) (canonicalPattern hm) x.1 x.2) := by
    change (fun j => normalizedPoint m β u j - average (actualCenter m β u)) =
      configuration (by omega) s θ v at hconfig
    exact model_canonical_directRigid (m := m) (z := z) (π := π) (α := α)
      (β := β) (u := u) (η := η) (s := s) (t := canonicalPattern hm)
      (θ := θ) (v := v) (k := k) (by omega) hmodel hconfig hcanConfig
  have hstat : FixedSchurStationaryUniqueness.Stationary
      (by omega) (canonicalPattern hm) x :=
    geometric_extremal_stationary D (canonicalPattern hm) x hxdom hxext
  exact ⟨x, ⟨hxdom, hxext, hxdisc⟩, hxenergy, hrigid, hstat⟩

/-- Saturation turns a selected physical-center chart identity into the
mean-gauge identity required by `canonical_entry_of_actual_chart`. -/
theorem canonical_entry_of_saturated_chart {m : ℕ} (hm : 3 ≤ m)
    (D : FixedSchurFiberData hm) {z : Points (2 * m)}
    {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    {s : SignPattern (by omega : 0 < m)}
    (hn : orderThreshold ≤ 2 * m)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hmodel : NormalizedRelativeEdgeModel z π α β u η)
    (hsat : ∀ i : Fin m, modelRadii m β u i = 1)
    (henergy : pairEnergy (by omega) (fun j => (normalizedAngle m u j : ℂ)) +
        pairEnergy (by omega)
          (projection (by omega : 2 ≤ m) (centerZero (actualCenter m β u))) ≤
      actualChartEnergyConstant / (2 * m : ℝ) ^ 2)
    (hcenter : centerZero (actualCenter m β u) =
      center (coordinate (by omega) s (normalizedAngle m u)
        (projection (by omega : 2 ≤ m) (centerZero (actualCenter m β u))))
        (projection (by omega : 2 ≤ m) (centerZero (actualCenter m β u))))
    (hbalanced : BalancedWord (by omega) s) :
    ∃ x : SchurParameters m,
      CanonicalRepresentative hm z x ∧
      pairEnergy (by omega) (fun j => (x.1 j : ℂ)) + pairEnergy (by omega) x.2 ≤
        actualChartEnergyConstant / (2 * m : ℝ) ^ 2 ∧
      DirectRigidRelabeling z
        (configuration (by omega) (canonicalPattern hm) x.1 x.2) ∧
      FixedSchurStationaryUniqueness.Stationary (by omega) (canonicalPattern hm) x := by
  apply canonical_entry_of_actual_chart hm D hn hz hmodel henergy ?_ hbalanced
  rw [normalizedPoint_meanGauge_eq_vertex (by omega) β u hmodel.periodic hsat]
  unfold configuration
  exact congrArg (FixedSchurEdgeGeometry.vertex (normalizedAngle m u)) hcenter

/-- Uniform finite input for an order: every actual extremizer supplies a
saturated balanced selected chart. -/
def HasActualBalancedChartData {m : ℕ} (hm : 3 ≤ m) : Prop :=
  ∀ z : Points (2 * m), ExtremalNormalization.DiameterExtremal z →
    ∃ (π : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ)
      (s : SignPattern (by omega : 0 < m)),
      NormalizedRelativeEdgeModel z π α β u η ∧
      (∀ i : Fin m, modelRadii m β u i = 1) ∧
      pairEnergy (by omega) (fun j => (normalizedAngle m u j : ℂ)) +
          pairEnergy (by omega)
            (projection (by omega : 2 ≤ m) (centerZero (actualCenter m β u))) ≤
        actualChartEnergyConstant / (2 * m : ℝ) ^ 2 ∧
      centerZero (actualCenter m β u) =
        center (coordinate (by omega) s (normalizedAngle m u)
          (projection (by omega : 2 ≤ m) (centerZero (actualCenter m β u))))
          (projection (by omega : 2 ≤ m) (centerZero (actualCenter m β u))) ∧
      BalancedWord (by omega) s

/-- The finite actual-entry theorem consumed by the rigid downstream module. -/
theorem canonicalRigidEntry_of_balanced_chart_data {m : ℕ} (hm : 3 ≤ m)
    (D : FixedSchurFiberData hm) (hn : orderThreshold ≤ 2 * m)
    (H : HasActualBalancedChartData hm) : CanonicalRigidEntry hm := by
  intro z hz
  obtain ⟨π, α, β, u, η, s, hmodel, hsat, henergy, hcenter, hbalanced⟩ := H z hz
  obtain ⟨x, hx, _hxenergy, hrigid, _hstat⟩ :=
    canonical_entry_of_saturated_chart hm D hn hz hmodel hsat henergy hcenter hbalanced
  obtain ⟨τ, a, b, hb, hzrep⟩ := hrigid
  exact ⟨x, τ, a, b, hx, hb, hzrep⟩

end
end StructuralNote.ExplicitCanonicalEntry

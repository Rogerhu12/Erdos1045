import StructuralNote.FixedSchurCanonicalAlignment
import StructuralNote.MatchingActivityActualWordBalanced

/-! A concise canonical fixed-Schur entry theorem for arbitrary actual
diameter extremizers.

The physical active word and its original chart parameters are retained.
The theorem then applies one genuine cyclic relabeling to place the same
configuration in the fixed canonical balanced-word fiber.  Both chart points
are in the actual domain, and the canonical configuration has exactly the
same discriminant as the original extremizer.
-/

namespace StructuralNote.FixedSchurActualCanonicalEntry

open Complex Filter
open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open Erdos1045.EventualExact.CommonLocalization
open Erdos1045.EventualExact.FiniteBox Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.SchurLift Erdos1045.EventualExact.SchurSpectrum
open CommonDomainClosure CommonTangentialParameters
open MatchingActivityRadialActual MatchingActivityRadialIntegration
open MatchingActivityNonlocalPairs
open NormalizedPolarRepresentation ExtremalPolarCenter
open StrongPointwiseCoordinates ActualCrossingGeometry
open FixedSchurLinear FixedSchurProjectionDomain
open FixedSchurChart FixedSchurEquationSmooth FixedSchurChartSmooth
open FixedSchurCyclicEquivariance FixedSchurExtremalSymmetry
open FixedSchurCanonicalWordSymmetry FixedSchurCanonicalAlignment
open SignPatternSymmetry MatchingActivityActualChart
open MatchingActivityActualChartEntry MatchingActivityActualWordBalanced
open MatchingActivitySaturation FiniteWordClassification
open scoped BigOperators Topology

noncomputable section

theorem discriminant_sub_const {n : ℕ} (z : Points n) (a : ℂ) :
    discriminant (fun j => z j - a) = discriminant z := by
  have h := discriminant_affine z (-a) 1
  calc
    discriminant (fun j => z j - a) =
        discriminant (fun j => -a + 1 * z j) := by
      congr 1
      funext j
      ring
    _ = discriminant z := by simpa only [norm_one, one_pow, one_mul] using h

/-- Every sufficiently large actual even-order extremizer enters the one
canonical balanced fixed-Schur fiber.  The displayed discriminant equality is
the retained rigid-geometric link to the original labeled configuration. -/
theorem eventual_actual_extremizer_canonical_entry :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 3 ≤ m) (s : SignPattern (by omega))
        (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (k : ℕ),
        InDomain (by omega) θ v ∧
        pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
          actualChartEnergyConstant / (2 * m : ℝ) ^ 2 ∧
        BalancedWord (by omega) s ∧
        ExtremalNormalization.DiameterExtremal
          (configuration (by omega) s θ v) ∧
        discriminant (configuration (by omega) s θ v) = discriminant z ∧
        rotatePattern k s = canonicalPattern hm ∧
        InDomain (by omega) (cyclicReal k θ) (cyclicCenter k v) ∧
        pairEnergy (by omega) (fun j => (cyclicReal k θ j : ℂ)) +
            pairEnergy (by omega) (cyclicCenter k v) ≤
          actualChartEnergyConstant / (2 * m : ℝ) ^ 2 ∧
        ExtremalNormalization.DiameterExtremal
          (configuration (by omega) (canonicalPattern hm)
            (cyclicReal k θ) (cyclicCenter k v)) ∧
        configuration (by omega) (canonicalPattern hm)
            (cyclicReal k θ) (cyclicCenter k v) =
          cyclicCenter k (configuration (by omega) s θ v) ∧
        discriminant
            (configuration (by omega) (canonicalPattern hm)
              (cyclicReal k θ) (cyclicCenter k v)) = discriminant z := by
  obtain ⟨m₀, hentry⟩ := eventual_actual_maximizer_balanced_entry
  obtain ⟨m₁, hdomain⟩ := eventually_atTop.1
    (eventually_projection_inDomain actualChartEnergyConstant)
  obtain ⟨m₂, halign⟩ := eventually_atTop.1
    eventual_balanced_extremal_canonical_alignment
  refine ⟨max (max m₀ m₁) (max m₂ 3), ?_⟩
  intro m hm z hz
  have hm₀ : m₀ ≤ m := by omega
  have hm₁ : m₁ ≤ m := by omega
  have hm₂ : m₂ ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  obtain ⟨hmp, hm2, π, α, β, u, η, s, hmodel, hsat, hpressure,
      hcombined, henergy, hcross, hconstraint, hcenter, hconfig, hdef, hbalanced⟩ :=
    hentry m hm₀ z hz
  let θ : Fin (2 * m) → ℝ := normalizedAngle m u
  let C : Fin (2 * m) → ℂ := centerZero (actualCenter m β u)
  let v : Fin (2 * m) → ℂ := projection hm2 C
  have hθhalf : HalfPeriodic hmp (fun j => (θ j : ℂ)) := by
    intro j
    exact congrArg Complex.ofReal
      (normalizedAngle_halfPeriodic hmp u hmodel.periodic j)
  have hθmean : (∑ j, (θ j : ℂ)) = 0 := by
    dsimp only [θ]
    rw [← Complex.ofReal_sum, normalizedAngle_mean_zero hmp u]
    norm_num
  have hCbase : HalfPeriodic hmp (actualCenter m β u) :=
    actualCenter_halfPeriodic hmp β u hmodel.periodic
  have hChalf : HalfPeriodic hmp C := by
    exact centerZero_halfPeriodic hmp _ hCbase
  have hCmean : (∑ j, C j) = 0 := by
    exact centerZero_sum (by omega) _
  have hdom : InDomain hmp θ v := by
    exact hdomain m hm₁ hm2 θ C hθhalf hθmean hChalf hCmean henergy
  have hchart : ExtremalNormalization.DiameterExtremal
      (configuration hmp s θ v) := by
    have hext := diameterExtremal_sub_const (normalizedPoint m β u)
      (model_normalizedPoint_extremal hmodel hz) (average (actualCenter m β u))
    change (fun j => normalizedPoint m β u j - average (actualCenter m β u)) =
      configuration hmp s θ v at hconfig
    rw [← hconfig]
    exact hext
  have hdisc : discriminant (configuration hmp s θ v) = discriminant z := by
    calc
      discriminant (configuration hmp s θ v) =
          discriminant (fun j => normalizedPoint m β u j -
            average (actualCenter m β u)) := congrArg discriminant hconfig.symm
      _ = discriminant (normalizedPoint m β u) := discriminant_sub_const _ _
      _ = discriminant z := model_discriminant_normalizedPoint hmodel
  obtain ⟨k, hword, hcanDom, hcanExt, hcanConfig⟩ :=
    halign m hm₂ hm3 s (θ, v) hdom hchart hbalanced
  have hcanEnergy :
      pairEnergy (by omega) (fun j => (cyclicReal k θ j : ℂ)) +
          pairEnergy (by omega) (cyclicCenter k v) ≤
        actualChartEnergyConstant / (2 * m : ℝ) ^ 2 := by
    rw [pairEnergy_cyclicReal (show 2 ≤ 2 * m by omega),
      pairEnergy_cyclicCenter (show 2 ≤ 2 * m by omega)]
    exact henergy
  have hcanDisc : discriminant
      (configuration (by omega) (canonicalPattern hm3)
        (cyclicReal k θ) (cyclicCenter k v)) = discriminant z := by
    rw [hcanConfig, discriminant_cyclicCenter, hdisc]
  exact ⟨hm3, s, θ, v, k, hdom, henergy, hbalanced, hchart, hdisc,
    hword, hcanDom, hcanEnergy, hcanExt, hcanConfig, hcanDisc⟩

/-- The compact output used by subsequent uniqueness arguments. -/
def CanonicalRepresentative {m : ℕ} (hm : 3 ≤ m) (z : Points (2 * m))
    (x : SchurParameters m) : Prop :=
  x ∈ domain (by omega) ∧
    ExtremalNormalization.DiameterExtremal
      (configuration (by omega) (canonicalPattern hm) x.1 x.2) ∧
    discriminant (configuration (by omega) (canonicalPattern hm) x.1 x.2) =
      discriminant z

theorem eventual_actual_extremizer_has_canonicalRepresentative :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 3 ≤ m) (x : SchurParameters m),
        CanonicalRepresentative hm z x ∧
        pairEnergy (by omega) (fun j => (x.1 j : ℂ)) + pairEnergy (by omega) x.2 ≤
          actualChartEnergyConstant / (2 * m : ℝ) ^ 2 := by
  obtain ⟨m₀, hentry⟩ := eventual_actual_extremizer_canonical_entry
  refine ⟨m₀, ?_⟩
  intro m hm z hz
  obtain ⟨hm3, s, θ, v, k, hdom, henergy, hbalanced, hchart, hdisc,
      hword, hcanDom, hcanEnergy, hcanExt, hcanConfig, hcanDisc⟩ :=
    hentry m hm z hz
  exact ⟨hm3, (cyclicReal k θ, cyclicCenter k v),
    ⟨hcanDom, hcanExt, hcanDisc⟩, hcanEnergy⟩

/-- Canonical representatives of any two actual extremizers coincide.  This
is the coordinate-level rigid uniqueness statement after all genuine word and
geometric alignments have already been performed. -/
theorem eventual_canonicalRepresentative_unique : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 3 ≤ m) (z w : Points (2 * m)) (x y : SchurParameters m),
      CanonicalRepresentative hm z x → CanonicalRepresentative hm w y → x = y := by
  filter_upwards [FixedSchurGeometricStationarity.eventual_same_word_extremal_unique]
    with m huniq
  intro hm z w x y hx hy
  exact huniq (by omega) (canonicalPattern hm) x hx.1 y hy.1 hx.2.1 hy.2.1

theorem eventual_actual_extremizers_canonical_rigid_unique :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z w : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ExtremalNormalization.DiameterExtremal w →
      ∃ (hm : 3 ≤ m) (x y : SchurParameters m),
        CanonicalRepresentative hm z x ∧ CanonicalRepresentative hm w y ∧ x = y := by
  obtain ⟨m₀, hentry⟩ := eventual_actual_extremizer_has_canonicalRepresentative
  obtain ⟨m₁, huniq⟩ := eventually_atTop.1 eventual_canonicalRepresentative_unique
  refine ⟨max m₀ m₁, ?_⟩
  intro m hm z w hz hw
  obtain ⟨hm3, x, hx, _⟩ := hentry m (by omega) z hz
  obtain ⟨hm3', y, hy, _⟩ := hentry m (by omega) w hw
  have he : hm3' = hm3 := Subsingleton.elim _ _
  subst hm3'
  exact ⟨hm3, x, y, hx, hy, huniq m (by omega) hm3 z w x y hx hy⟩

end
end StructuralNote.FixedSchurActualCanonicalEntry

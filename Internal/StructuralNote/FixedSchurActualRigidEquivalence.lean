import StructuralNote.FixedSchurActualCanonicalEntry

/-! Actual extremizers are related to their canonical fixed-Schur model by
an honest Euclidean motion and a relabeling. -/

namespace StructuralNote.FixedSchurActualRigidEquivalence

open Complex Filter
open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open Erdos1045.EventualExact.CommonLocalization
open Erdos1045.EventualExact.FiniteBox Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.SchurLift Erdos1045.EventualExact.SchurSpectrum
open CommonDomainClosure CommonTangentialParameters
open MatchingActivityRadialActual MatchingActivityRadialIntegration
open MatchingActivityNonlocalPairs
open NormalizedPolarRepresentation ExtremalPolarCenter PolarCenterEnergy
open StrongPointwiseCoordinates ActualCrossingGeometry
open FixedSchurLinear FixedSchurProjectionDomain
open FixedSchurChart FixedSchurEquationSmooth FixedSchurChartSmooth
open FixedSchurCyclicEquivariance FixedSchurExtremalSymmetry
open FixedSchurCanonicalWordSymmetry FixedSchurCanonicalAlignment
open SignPatternSymmetry MatchingActivityActualChart
open MatchingActivityActualChartEntry MatchingActivityActualWordBalanced
open MatchingActivitySaturation FiniteWordClassification
open FixedSchurActualCanonicalEntry
open scoped BigOperators Topology

noncomputable section

/-- `z` is obtained from `w` by relabeling and an orientation-preserving
Euclidean isometry of the complex plane. -/
def DirectRigidRelabeling {n : ℕ} (z w : Points n) : Prop :=
  ∃ π : Equiv.Perm (Fin n), ∃ a b : ℂ, ‖b‖ = 1 ∧
    ∀ j, z (π j) = a + b * w j

/-- The original localization model, mean-center normalization, and cyclic
canonical alignment compose to one genuine rigid presentation. -/
theorem model_canonical_directRigid {m : ℕ} (hm : 0 < m)
    {z : Points (2 * m)} {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ}
    {u : ℕ → ℂ} {η : ℝ} {s t : SignPattern hm}
    {θ : Fin (2 * m) → ℝ} {v : Fin (2 * m) → ℂ} {k : ℕ}
    (hmodel : NormalizedRelativeEdgeModel z π α β u η)
    (hconfig : (fun j => normalizedPoint m β u j - average (actualCenter m β u)) =
      configuration hm s θ v)
    (hcan : configuration hm t (cyclicReal k θ) (cyclicCenter k v) =
      cyclicCenter k (configuration hm s θ v)) :
    DirectRigidRelabeling z
      (configuration hm t (cyclicReal k θ) (cyclicCenter k v)) := by
  let ρ : ℂ := LocalPhase.regularRoot (2 * m) ^ k
  let R : ℂ := (β / (‖β‖ : ℂ)) * phase (-meanAngle m u)
  let T : ℂ := average (actualCenter m β u)
  let A : ℂ := α + (β / (‖β‖ : ℂ)) * physicalTranslation m ‖β‖ u + R * T
  let τ : Equiv.Perm (Fin (2 * m)) := (cyclicIndex (2 * m) k).trans π
  refine ⟨τ, A, R * ρ, ?_, ?_⟩
  · rw [norm_mul]
    have hR : ‖R‖ = 1 := by
      exact normalizedRotation_norm hmodel.scale_ne_zero u
    have hρ : ‖ρ‖ = 1 := by
      dsimp only [ρ]
      rw [norm_pow, ClosedFourier.root_norm, one_pow]
    rw [hR, hρ, mul_one]
  · intro j
    have hq : configuration hm s θ v (cyclicIndex (2 * m) k j) =
        ρ * configuration hm t (cyclicReal k θ) (cyclicCenter k v) j := by
      have hc := congrFun hcan j
      dsimp only [cyclicCenter] at hc
      calc
        configuration hm s θ v (cyclicIndex (2 * m) k j) =
        ρ * ((starRingEnd ℂ) ρ * configuration hm s θ v
              (cyclicIndex (2 * m) k j)) := by
              rw [← mul_assoc, root_pow_mul_conj, one_mul]
        _ = ρ * configuration hm t (cyclicReal k θ) (cyclicCenter k v) j := by
              rw [hc]
    have hn := congrFun hconfig (cyclicIndex (2 * m) k j)
    have hz : z (π (cyclicIndex (2 * m) k j)) =
        (α + (β / (‖β‖ : ℂ)) * physicalTranslation m ‖β‖ u) +
          R * normalizedPoint m β u (cyclicIndex (2 * m) k j) := by
      have hh := model_normalized_coordinates hmodel (cyclicIndex (2 * m) k j)
      rw [← ActualPressureGap.polarCenter_eq_normalizedCenter m β u] at hh
      simpa only [R, normalizedPoint, phase, neg_neg, SignedPressureAngular.root,
        PolarRepresentation.reference, mul_assoc] using hh
    change z (π (cyclicIndex (2 * m) k j)) = _
    rw [hz]
    dsimp only [A, R, T]
    rw [show normalizedPoint m β u (cyclicIndex (2 * m) k j) =
        average (actualCenter m β u) +
          configuration hm s θ v (cyclicIndex (2 * m) k j) by
      calc
        normalizedPoint m β u (cyclicIndex (2 * m) k j) =
            (normalizedPoint m β u (cyclicIndex (2 * m) k j) -
              average (actualCenter m β u)) + average (actualCenter m β u) := by ring
        _ = configuration hm s θ v (cyclicIndex (2 * m) k j) +
              average (actualCenter m β u) := by rw [hn]
        _ = _ := by ring, hq]
    ring

theorem directRigidRelabeling_of_common {n : ℕ} {z w x : Points n}
    (hz : DirectRigidRelabeling z x) (hw : DirectRigidRelabeling w x) :
    DirectRigidRelabeling z w := by
  obtain ⟨π, a, b, hb, hz⟩ := hz
  obtain ⟨τ, c, d, hd, hw⟩ := hw
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd
    norm_num at hd
  refine ⟨τ.symm.trans π, a - (b / d) * c, b / d, ?_, ?_⟩
  · rw [norm_div, hb, hd, div_one]
  · intro j
    have hwj := hw (τ.symm j)
    simp only [Equiv.apply_symm_apply] at hwj
    have hx : x (τ.symm j) = (w j - c) / d := by
      apply (eq_div_iff hd0).2
      rw [hwj]
      ring
    change z (π (τ.symm j)) = _
    rw [hz, hx]
    field_simp
    ring

/-- Every sufficiently large actual extremizer has a canonical chart
representative related to the original labeled points by a genuine rigid
motion and relabeling. -/
theorem eventual_actual_extremizer_canonical_directRigid :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 3 ≤ m) (x : SchurParameters m),
        CanonicalRepresentative hm z x ∧
        pairEnergy (by omega) (fun j => (x.1 j : ℂ)) + pairEnergy (by omega) x.2 ≤
          actualChartEnergyConstant / (2 * m : ℝ) ^ 2 ∧
        DirectRigidRelabeling z
          (configuration (by omega) (canonicalPattern hm) x.1 x.2) := by
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
  have hrigid : DirectRigidRelabeling z
      (configuration (by omega) (canonicalPattern hm3)
        (cyclicReal k θ) (cyclicCenter k v)) := by
    exact model_canonical_directRigid hmp hmodel hconfig hcanConfig
  exact ⟨hm3, (cyclicReal k θ, cyclicCenter k v),
    ⟨hcanDom, hcanExt, hcanDisc⟩, hcanEnergy, hrigid⟩

/-- Any two sufficiently large actual even-order extremizers differ by a
relabeling followed by an orientation-preserving Euclidean isometry. -/
theorem eventual_actual_extremizers_directRigid :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z w : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ExtremalNormalization.DiameterExtremal w →
      DirectRigidRelabeling z w := by
  obtain ⟨m₀, hentry⟩ := eventual_actual_extremizer_canonical_directRigid
  obtain ⟨m₁, huniq⟩ := eventually_atTop.1 eventual_canonicalRepresentative_unique
  refine ⟨max m₀ m₁, ?_⟩
  intro m hm z w hz hw
  obtain ⟨hm3, x, hx, _, hrz⟩ := hentry m (by omega) z hz
  obtain ⟨hm3', y, hy, _, hrw⟩ := hentry m (by omega) w hw
  have he : hm3' = hm3 := Subsingleton.elim _ _
  subst hm3'
  have hxy : x = y := huniq m (by omega) hm3 z w x y hx hy
  subst y
  exact directRigidRelabeling_of_common hrz hrw

end
end StructuralNote.FixedSchurActualRigidEquivalence

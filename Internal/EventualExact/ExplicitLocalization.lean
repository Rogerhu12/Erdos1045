import EventualExact.ExplicitInitialBounds
import EventualExact.LocalizationPerimeter
import StructuralNote.ExplicitThresholdFunctions
import Erdos1045.LocalNormalization

/-! Fully pointwise localization with a symbolic, evaluable natural-number threshold. -/

namespace Erdos1045.EventualExact.ExplicitLocalization

set_option maxRecDepth 65536

open Configuration HullGeometry ExteriorClassical ExteriorBoundary MatrixDefect GlobalProof
open ExteriorSupport PhysicalAngularGeometry CyclicAngles FiniteCircleRigidity
open PhysicalForceBudget GapRigidityLimit CommonLocalization CanonicalPolarEdges CoarseFekete
open CyclicForceBudget
open ExtremalNormalization
open ExplicitInitial ExplicitThreshold
noncomputable section

def radialCoefficient : ℝ := 6 * Real.sqrt energyConstant

def geometricConstant : ℝ := 48 * Real.sqrt (6 * Real.sqrt energyConstant)

def physicalSeparation : ℝ := radiusScale / (8 * Real.exp radiusScale)

def angularSeparation : ℝ := physicalSeparation / 8

def rigidityBudget : ℝ :=
  PhysicalForceBudget.rigidityBudgetConstant angularSeparation geometricConstant

def gapCoefficient : ℝ := GapRigidityLimit.rigidityConstant rigidityBudget

def edgeTarget (ε : ℝ) : ℝ := min (1 / 2) (ε / 4)

def gapTarget (ε : ℝ) : ℝ := edgeTarget ε / (10 * Real.pi)

def radialTarget (ε : ℝ) : ℝ := edgeTarget ε / (104 * Real.pi)

/-- Every entry is an explicit arithmetic expression.  No eventual witness is used. -/
def localizationThreshold (ε : ℝ) : ℕ :=
  max coarseThreshold
    (max (inverseThreshold radialCoefficient (1 / 4))
      (max (inverseThreshold radialCoefficient ((radialTarget ε) ^ 2))
        (max (inverseSqrtThreshold (geometricConstant * Real.pi) 1)
          (max (decayThreshold geometricConstant 1)
            (decayThreshold gapCoefficient ((gapTarget ε) ^ 3))))))

theorem radialCoefficient_nonneg : 0 ≤ radialCoefficient := by
  unfold radialCoefficient
  positivity

theorem geometricConstant_nonneg : 0 ≤ geometricConstant := by
  unfold geometricConstant
  positivity

theorem physicalSeparation_pos : 0 < physicalSeparation := by
  unfold physicalSeparation
  exact div_pos radiusScale_pos (by positivity)

theorem angularSeparation_pos : 0 < angularSeparation := by
  unfold angularSeparation
  exact div_pos physicalSeparation_pos (by norm_num)

theorem rigidityBudget_nonneg : 0 ≤ rigidityBudget := by
  unfold rigidityBudget
  exact PhysicalForceBudget.rigidityBudgetConstant_nonneg angularSeparation_pos
    geometricConstant_nonneg

theorem gapCoefficient_nonneg : 0 ≤ gapCoefficient := by
  unfold gapCoefficient GapRigidityLimit.rigidityConstant
  have := rigidityBudget_nonneg
  positivity

theorem edgeTarget_pos {ε : ℝ} (hε : 0 < ε) : 0 < edgeTarget ε := by
  unfold edgeTarget
  exact lt_min (by norm_num) (by positivity)

theorem gapTarget_pos {ε : ℝ} (hε : 0 < ε) : 0 < gapTarget ε := by
  unfold gapTarget
  exact div_pos (edgeTarget_pos hε) (mul_pos (by norm_num) Real.pi_pos)

theorem radialTarget_pos {ε : ℝ} (hε : 0 < ε) : 0 < radialTarget ε := by
  unfold radialTarget
  exact div_pos (edgeTarget_pos hε) (mul_pos (by norm_num) Real.pi_pos)

theorem localizationThreshold_conditions {n : ℕ} {ε : ℝ}
    (hn : localizationThreshold ε ≤ n) :
    coarseThreshold ≤ n ∧
      inverseThreshold radialCoefficient (1 / 4) ≤ n ∧
      inverseThreshold radialCoefficient ((radialTarget ε) ^ 2) ≤ n ∧
      inverseSqrtThreshold (geometricConstant * Real.pi) 1 ≤ n ∧
      decayThreshold geometricConstant 1 ≤ n ∧
      decayThreshold gapCoefficient ((gapTarget ε) ^ 3) ≤ n := by
  unfold localizationThreshold at hn
  obtain ⟨hcoarse, hrest⟩ := max_le_iff.mp hn
  obtain ⟨hquarter, hrest⟩ := max_le_iff.mp hrest
  obtain ⟨hradial, hrest⟩ := max_le_iff.mp hrest
  obtain ⟨hsqrt, hrest⟩ := max_le_iff.mp hrest
  obtain ⟨hlog, hgap⟩ := max_le_iff.mp hrest
  exact ⟨hcoarse, hquarter, hradial, hsqrt, hlog, hgap⟩

/-- A finite-dimensional replacement for the eventual polar-rigidity step. -/
theorem pointwise_physical_localization {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) {ε : ℝ} (hε : 0 < ε)
    (hn : localizationThreshold ε ≤ n)
    (hinj : Function.Injective z) (hF : Fekete z)
    (hΔ : (n : ℝ) ^ n ≤ discriminant z) :
    ∃ (σ : Equiv.Perm (Fin n)) (a : Angles n) (slope : Fin n → ℝ),
      PhysicalGeometry d σ a ∧
      (∀ k : ℤ, angularSeparation / n ≤ a.angle (k + 1) - a.angle k) ∧
      (∀ i, |slope i| ≤ geometricEpsilon d) ∧
      (∀ i, polarForceExpression (height d σ) (angleVector a) i (slope i) = 0) ∧
      ‖gapDeviation a‖ < gapTarget ε ∧
      errorRadius d < (radialTarget ε) ^ 2 := by
  let B := classicalBackground_proved.toClassicalAnalysis
  obtain ⟨hcoarse, hquarter, hradial, hsqrt, hlog, hgap⟩ :=
    localizationThreshold_conditions hn
  have hn4 : 4 ≤ n := (coarseThreshold_conditions hcoarse).1
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  obtain ⟨hc, _hsampling, _hcap, henergy, _hmatrix⟩ :=
    coarse_bounds d HF hcoarse hinj hF hΔ
  have hρle : errorRadius d ≤ radialCoefficient / n := by
    simpa only [radialCoefficient] using errorRadius_le_inverse d hn0 henergy
  have hρquarter : errorRadius d ≤ 1 / 4 := by
    exact hρle.trans (inverse_small (by norm_num : (0 : ℝ) < 1 / 4) hquarter).le
  have hρsmall : errorRadius d < (radialTarget ε) ^ 2 := by
    exact hρle.trans_lt (inverse_small (sq_pos_of_pos (radialTarget_pos hε)) hradial)
  have hgeo : geometricEpsilon d ≤
      geometricConstant * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    simpa only [geometricConstant] using geometricEpsilon_le_half_power d hn0 henergy
  have hinitial : (n : ℝ) * d.energySquared ≤ initialEnergy := by
    simpa only [initialEnergy] using
      d.initial_energy_bound B.circle B.hadamard HF (by omega) hΔ
  have hscale : 256 * initialEnergy ≤ radiusScale := by
    unfold radiusScale
    calc
      256 * initialEnergy = 16 * (4 : ℝ) ^ 2 * initialEnergy := by ring
      _ ≤ max 1 (16 * (4 : ℝ) ^ 2 * initialEnergy) := le_max_right _ _
  have hphysical : ∀ i k : Fin n, i ≠ k →
      physicalSeparation / n ≤ ‖z i - z k‖ := by
    intro i k hik
    simpa only [physicalSeparation] using
      PhysicalSeparation.separated d HF (by omega) hinj hF radiusScale_pos hc
        hinitial hscale i k hik
  obtain ⟨σ, a, slope, hgeometry, hangles, hslope, hstationary⟩ :=
    exists_physical_stationary_geometry d HF (by omega) hinj hF hc hρquarter hphysical
  have hangles' : ∀ k : ℤ, angularSeparation / n ≤
      a.angle (k + 1) - a.angle k := by
    simpa only [angularSeparation] using hangles
  have hrpow : (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt n := by
    rw [Real.rpow_neg hnR.le, Real.sqrt_eq_rpow]
    simp only [one_div]
  have hsmall : geometricEpsilon d * Real.pi ≤ 1 := by
    have hu := inverse_sqrt_small (C := geometricConstant * Real.pi) (ε := 1)
      (by norm_num) hsqrt
    have hm := mul_le_mul_of_nonneg_right hgeo Real.pi_pos.le
    rw [hrpow] at hm
    have heq : geometricConstant * (1 / Real.sqrt n) * Real.pi =
        (geometricConstant * Real.pi) / Real.sqrt n := by ring
    rw [heq] at hm
    exact hm.trans hu.le
  have hlogsmall : geometricEpsilon d * (1 + Real.log n) ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hΛ : 0 ≤ 1 + Real.log n := by linarith [Real.log_nonneg hn1]
    have hm := mul_le_mul_of_nonneg_right hgeo hΛ
    have hu := sqrt_monomial_small (C := geometricConstant) (ε := 1)
      geometricConstant_nonneg (by norm_num) (j := 1) (by omega) hlog
    rw [hrpow] at hm
    have heq : geometricConstant * (1 / Real.sqrt n) * (1 + Real.log n) =
        geometricConstant * logBudget (n : ℝ) ^ 1 / Real.sqrt n := by
      simp [logBudget]
      ring
    rw [heq] at hm
    exact hm.trans hu.le
  have hforce := PhysicalForceBudget.force_bounds_of_half_power a hn0 angularSeparation_pos
    (geometricEpsilon_nonneg d) geometricConstant_nonneg hsmall hlogsmall hangles'
    (fun i k _ => hgeometry.height_bound i k) hslope hstationary hgeo
  have hforce' :
      forceSquareSum a ≤ rigidityBudget * (1 + Real.log n) ^ 2 ∧
      ‖circleForce (angleVector a)‖ ≤ rigidityBudget *
        (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    simpa only [rigidityBudget] using hforce
  have hcube := GapRigidityLimit.gapDeviation_cube_le a (by omega)
    rigidityBudget_nonneg hforce'.1 hforce'.2
  have hdecay := monomial_small gapCoefficient_nonneg
    (pow_pos (gapTarget_pos hε) 3) (j := 8) (by omega)
    (by norm_num : (1 / 4 : ℝ) ≤ 1 / 4) hgap
  have hcube' : ‖gapDeviation a‖ ^ 3 < gapTarget ε ^ 3 := by
    exact hcube.trans_lt (by simpa only [gapCoefficient, logBudget] using hdecay)
  have hgap_small : ‖gapDeviation a‖ < gapTarget ε :=
    lt_of_pow_lt_pow_left₀ 3 (gapTarget_pos hε).le hcube'
  exact ⟨σ, a, slope, hgeometry, hangles', hslope, hstationary, hgap_small, hρsmall⟩

/-- The explicit pointwise relative-edge model before removing similarity modes. -/
theorem relative_edge_localization {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) {ε : ℝ} (hε : 0 < ε)
    (hn : localizationThreshold ε ≤ n)
    (hinj : Function.Injective z) (hF : Fekete z)
    (hΔ : (n : ℝ) ^ n ≤ discriminant z) :
    ∃ (σ : Equiv.Perm (Fin n)) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
      RelativeEdgeModel z σ α β u η ∧
      boundaryLength (fun i => z (σ i)) ≤ hullPerimeter z ∧
      η < edgeTarget ε := by
  obtain ⟨σ, a, slope, hgeometry, _hangles, _hslope, _hstationary, hgap, hρ⟩ :=
    pointwise_physical_localization d HF hε hn hinj hF hΔ
  have hn4 : 4 ≤ n := (coarseThreshold_conditions
    (localizationThreshold_conditions hn).1).1
  have hn0 : 0 < n := by omega
  have hconditions := localizationThreshold_conditions hn
  have hcoarse := coarse_bounds d HF hconditions.1 hinj hF hΔ
  have hc := hcoarse.1
  have hρquarter : errorRadius d ≤ 1 / 4 := by
    have hρle : errorRadius d ≤ radialCoefficient / n := by
      simpa only [radialCoefficient] using
        errorRadius_le_inverse d hn0 hcoarse.2.2.2.1
    exact hρle.trans
      (inverse_small (by norm_num : (0 : ℝ) < 1 / 4) hconditions.2.1).le
  let R := radii d σ hn0
  let u := RadialEdges.perturbation a R d.capacity
  let η := RadialEdges.edgeError a (errorRadius d)
  have hradpos := radialTarget_pos hε
  have hsqrt : Real.sqrt (errorRadius d) < radialTarget ε :=
    (Real.sqrt_lt' hradpos).2 hρ
  have hetapos := edgeTarget_pos hε
  have he_le : edgeTarget ε ≤ 1 / 2 := min_le_left _ _
  have hs_lt_one : radialTarget ε < 1 := by
    unfold radialTarget
    have hp := Real.pi_gt_three
    apply (div_lt_iff₀ (by positivity : 0 < 104 * Real.pi)).2
    nlinarith only [he_le, hp]
  have hρlt : errorRadius d < radialTarget ε := by
    have hsq : radialTarget ε ^ 2 < radialTarget ε := by
      nlinarith only [hradpos, hs_lt_one, sq_nonneg (radialTarget ε)]
    exact hρ.trans hsq
  have hg_lt_one : ‖gapDeviation a‖ < 1 := by
    have ht : gapTarget ε < 1 := by
      unfold gapTarget
      have hp := Real.pi_gt_three
      apply (div_lt_iff₀ (by positivity : 0 < 10 * Real.pi)).2
      nlinarith only [he_le, hp]
    exact hgap.trans ht
  have hgap_term : 5 * Real.pi / 2 * ‖gapDeviation a‖ < edgeTarget ε / 4 := by
    calc
      _ < 5 * Real.pi / 2 * gapTarget ε :=
        mul_lt_mul_of_pos_left hgap (by positivity)
      _ = _ := by unfold gapTarget; field_simp [Real.pi_ne_zero]; ring
  have hradial_sum : 12 * Real.sqrt (errorRadius d) + errorRadius d <
      13 * radialTarget ε := by nlinarith only [hsqrt, hρlt]
  have hradial_prod :
      (12 * Real.sqrt (errorRadius d) + errorRadius d) *
          (1 + ‖gapDeviation a‖) < 26 * radialTarget ε := by
    calc
      _ < (13 * radialTarget ε) * (1 + ‖gapDeviation a‖) :=
        mul_lt_mul_of_pos_right hradial_sum (by positivity)
      _ < (13 * radialTarget ε) * 2 :=
        mul_lt_mul_of_pos_left (show 1 + ‖gapDeviation a‖ < 2 by linarith)
          (by positivity [radialTarget_pos hε])
      _ = _ := by ring
  have hradial_term : Real.pi *
      (12 * Real.sqrt (errorRadius d) + errorRadius d) *
        (1 + ‖gapDeviation a‖) < edgeTarget ε / 4 := by
    calc
      _ < Real.pi * (26 * radialTarget ε) := by
        rw [mul_assoc]
        exact mul_lt_mul_of_pos_left hradial_prod Real.pi_pos
      _ = _ := by unfold radialTarget; field_simp [Real.pi_ne_zero]; ring
  have hηsmall : η < edgeTarget ε := by
    dsimp [η, RadialEdges.edgeError]
    linarith
  have hperimeter := PhysicalBoundaryOrder.physical_boundaryLength_le d HF (by omega)
    (by linarith [hc, hρquarter]) σ a hgeometry.polar
  refine ⟨σ, center d, ((d.capacity : ℂ) * unit (a.angle 0)), u, η, ?_,
    hperimeter, hηsmall⟩
  refine ⟨RadialEdges.perturbation_periodic a hn0 R
      (radii_periodic d σ hn0) d.capacity, ?_, ?_,
    RadialEdges.edgeError_nonneg a (errorRadius_nonneg d), ?_⟩
  · apply mul_ne_zero (Complex.ofReal_ne_zero.mpr d.capacity_pos.ne')
    exact norm_ne_zero_iff.mp (by rw [norm_unit]; norm_num)
  · intro i
    have hi : index hn0 (i : ℕ) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    simpa only [u, R, hi] using actual_coordinates d σ a hn0 hgeometry.polar i
  · exact relative_edges d HF σ a (by omega) hc
      hρquarter hgeometry.polar

/-- A genuinely finite and explicit form of normalized relative-edge localization. -/
theorem normalized_relative_edge_localization {n : ℕ} {z : Points n}
    (d : ExteriorData z) (HF : FaberIdentities d) {ε : ℝ} (hε : 0 < ε)
    (hn : localizationThreshold ε ≤ n)
    (hinj : Function.Injective z) (hF : Fekete z)
    (hΔ : (n : ℝ) ^ n ≤ discriminant z) :
    ∃ (σ : Equiv.Perm (Fin n)) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
      NormalizedRelativeEdgeModel z σ α β u η ∧
      boundaryLength (fun i => z (σ i)) ≤ hullPerimeter z ∧ η < ε := by
  obtain ⟨σ, α, β, u, η, hmodel, hperimeter, hη⟩ :=
    relative_edge_localization d HF hε hn hinj hF hΔ
  have hn4 : 4 ≤ n := (coarseThreshold_conditions
    (localizationThreshold_conditions hn).1).1
  have heta_half : η < 1 / 2 := hη.trans_le (min_le_left _ _)
  have heta_eps : η < ε / 4 := hη.trans_le (min_le_right _ _)
  have hden : 0 < 1 - η := by linarith
  have hnormalized : 2 * η / (1 - η) < ε := by
    apply (div_lt_iff₀ hden).2
    have hleft : 2 * η < ε / 2 := by linarith
    have hhalf : ε / 2 < ε * (1 - η) := by
      have hm := mul_lt_mul_of_pos_left (show (1 / 2 : ℝ) < 1 - η by linarith) hε
      nlinarith
    exact hleft.trans hhalf
  exact ⟨σ, α + β * LocalNormalization.mean n u,
    β * (1 + LocalNormalization.first n u), LocalNormalization.normalized n u,
    2 * η / (1 - η), hmodel.normalize hn4 (by linarith), hperimeter, hnormalized⟩

/-- Exterior data and its ordering are constructed internally from a normalized
Fekete configuration; the returned ordering is for the original labels. -/
theorem normalized_fekete_localization {n : ℕ} {z : Points n}
    (hz : NormalizedFekete z) {ε : ℝ} (hε : 0 < ε)
    (hn : localizationThreshold ε ≤ n) :
    ∃ (σ : Equiv.Perm (Fin n)) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
      NormalizedRelativeEdgeModel z σ α β u η ∧
      boundaryLength (fun i => z (σ i)) ≤ hullPerimeter z ∧ η < ε := by
  have hn4 : 4 ≤ n := (coarseThreshold_conditions
    (localizationThreshold_conditions hn).1).1
  obtain ⟨τ, hdata⟩ := classicalBackground_proved.exterior.model n (by omega) z
    hz.injective hz.perimeter_eq hz.fekete
  rcases hdata with ⟨⟨d, HF⟩⟩
  have hinj : Function.Injective (z ∘ τ) := hz.injective.comp τ.injective
  have hF : Fekete (z ∘ τ) := CoarseFekete.fekete_perm hz.fekete τ
  have hΔ : (n : ℝ) ^ n ≤ discriminant (z ∘ τ) := by
    rw [discriminant_perm]
    exact hz.discriminant_ge
  obtain ⟨σ, α, β, u, η, hmodel, hperimeter, hη⟩ :=
    normalized_relative_edge_localization d HF hε hn hinj hF hΔ
  refine ⟨σ.trans τ, α, β, u, η, hmodel.relabel, ?_, hη⟩
  change boundaryLength (fun i => z (τ (σ i))) ≤ hullPerimeter (z ∘ τ) at hperimeter
  rw [hullPerimeter_perm_proved] at hperimeter
  exact hperimeter

/-- Direct finite localization for an actual diameter or perimeter maximizer.
The similarity normalization is removed in the returned model. -/
theorem extremal_localization {n : ℕ} {z : Points n}
    (hz : DiameterExtremal z ∨ PerimeterExtremal n z)
    {ε : ℝ} (hε : 0 < ε) (hn : localizationThreshold ε ≤ n) :
    ∃ (σ : Equiv.Perm (Fin n)) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
      NormalizedRelativeEdgeModel z σ α β u η ∧
      boundaryLength (fun i => z (σ i)) ≤ hullPerimeter z ∧ η < ε := by
  have hn4 : 4 ≤ n := (coarseThreshold_conditions
    (localizationThreshold_conditions hn).1).1
  have hnormalized := extremal_normalized hn4 hz
  obtain ⟨σ, α, β, u, η, hmodel, hperimeter, hη⟩ :=
    normalized_fekete_localization hnormalized hε hn
  let c : ℂ := ((2 * Real.pi / hullPerimeter z : ℝ) : ℂ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hD : 0 < discriminant z := by
    rcases hz with hd | hp
    · exact (pow_pos hnR _).trans_le (hd.discriminant_ge (by omega))
    · exact (pow_pos hnR _).trans_le
        (perimeterExtremal_normalized hn4 hp).discriminant_ge
  have hPpos := perimeter_pos_of_discriminant_pos (by omega : 2 ≤ n) hD
  have hc : c ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos (by positivity) hPpos).ne'
  have hmodel' : NormalizedRelativeEdgeModel z σ (α / c) (β / c) u η := by
    change NormalizedRelativeEdgeModel (fun i => c * z i) σ α β u η at hmodel
    exact hmodel.unscale hc
  refine ⟨σ, α / c, β / c, u, η, hmodel', ?_, hη⟩
  have hL := boundaryLength_affine (fun i => z (σ i)) 0 c
  simp only [zero_add] at hL
  have hP := classicalBackground_proved.toClassicalAnalysis.geometry.affine n z 0 c
  simp only [zero_add] at hP
  have hb := hperimeter
  change boundaryLength (fun i => c * z (σ i)) ≤
    hullPerimeter (fun i => c * z i) at hb
  rw [hL, hP] at hb
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  nlinarith

end
end Erdos1045.EventualExact.ExplicitLocalization

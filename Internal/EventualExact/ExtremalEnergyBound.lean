import EventualExact.LocalizationPerimeter
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Actual diameter extremizers have a uniformly bounded local quadratic energy.
The objective budget uses the proved physical boundary order. -/

namespace Erdos1045.EventualExact.ExtremalEnergyBound

open Filter Configuration HullGeometry ExteriorLocalBridge CommonLocalization
open scoped Topology BigOperators
noncomputable section

def halfAngle (n : ℕ) : ℝ := Real.pi / (2 * n)

def diameterBudget (n : ℕ) : ℝ := Real.pi ^ 2 / (8 * Real.cos (halfAngle n))

def totalEnergy (n : ℕ) (u : ℕ → ℂ) : ℝ :=
  LocalDFT.energyA n u + (n : ℝ) * LocalDFT.energyB n u

theorem halfAngle_bounds {n : ℕ} (hn : 4 ≤ n) :
    0 < halfAngle n ∧ halfAngle n ≤ 1 / 2 := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  unfold halfAngle
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).2
    nlinarith [Real.pi_lt_four]

theorem cos_halfAngle_lower {n : ℕ} (hn : 4 ≤ n) :
    1 / 2 ≤ Real.cos (halfAngle n) := by
  have hx := halfAngle_bounds hn
  have hc := Real.one_sub_sq_div_two_le_cos (x := halfAngle n)
  nlinarith

theorem neg_log_cos_le {x : ℝ} (hc : 0 < Real.cos x) :
    -Real.log (Real.cos x) ≤ x ^ 2 / (2 * Real.cos x) := by
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hc)
  rw [Real.log_inv] at hlog
  have hcos := Real.one_sub_sq_div_two_le_cos (x := x)
  have h : (Real.cos x)⁻¹ - 1 ≤ x ^ 2 / (2 * Real.cos x) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.cos x)).2
    field_simp [hc.ne']
    nlinarith
  exact hlog.trans h

theorem logsec_exponent_le_budget {n : ℕ} (hn : 4 ≤ n) :
    (exponent n : ℝ) * (-Real.log (Real.cos (halfAngle n))) ≤ diameterBudget n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc : 0 < Real.cos (halfAngle n) := lt_of_lt_of_le (by norm_num) (cos_halfAngle_lower hn)
  have h := mul_le_mul_of_nonneg_left (neg_log_cos_le hc)
    (Nat.cast_nonneg (exponent n) : (0 : ℝ) ≤ _)
  refine h.trans ?_
  have heq : (exponent n : ℝ) * (halfAngle n ^ 2 / (2 * Real.cos (halfAngle n))) =
      ((n : ℝ) - 1) / n * diameterBudget n := by
    unfold exponent
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    change (n : ℝ) * ((n : ℝ) - 1) * ((Real.pi / (2 * n)) ^ 2 /
      (2 * Real.cos (halfAngle n))) = ((n : ℝ) - 1) / n *
        (Real.pi ^ 2 / (8 * Real.cos (halfAngle n)))
    field_simp [hnR.ne', hc.ne']
    ring
  rw [heq]
  apply mul_le_of_le_one_left
  · exact div_nonneg (sq_nonneg _) (by positivity)
  · exact (div_le_iff₀ hnR).2 (by linarith)

theorem diameterBudget_le {n : ℕ} (hn : 4 ≤ n) : diameterBudget n ≤ Real.pi ^ 2 / 4 := by
  have hc := cos_halfAngle_lower hn
  unfold diameterBudget
  apply (div_le_iff₀ (by linarith : 0 < 8 * Real.cos (halfAngle n))).2
  nlinarith [sq_nonneg Real.pi]

theorem diameterBudget_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto (fun j => diameterBudget (N j)) atTop (𝓝 (Real.pi ^ 2 / 8)) := by
  have hinv : Tendsto (fun j => (N j : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hx : Tendsto (fun j => halfAngle (N j)) atTop (𝓝 0) := by
    simpa only [halfAngle, mul_inv_rev, div_eq_mul_inv, mul_zero, zero_mul, mul_assoc, mul_comm, mul_left_comm] using
      hinv.const_mul (Real.pi / 2)
  have hc : ContinuousAt (fun x : ℝ => Real.pi ^ 2 / (8 * Real.cos x)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  simpa only [diameterBudget, Function.comp_def, Real.cos_zero, mul_one] using hc.tendsto.comp hx

theorem diameter_perimeter_bound {n : ℕ} (hn : 3 ≤ n) {z : Points n}
    (hz : DiameterAtMost 2 z) : hullPerimeter z ≤ 2 * diameterPerimeterBound n := by
  have hd : DiameterAtMost 1 (ExtremalNormalization.scale (1 / 2) z) := by
    change DiameterAtMost 1 (fun i => ((1 / 2 : ℝ) : ℂ) * z i)
    simpa using diameter_affine hz 0 ((1 / 2 : ℝ) : ℂ)
  have h := ExtremalNormalization.provedGeometry.reinhardt n hn _ hd
  have hp := ExtremalNormalization.provedGeometry.affine n z 0 (((1 / 2 : ℝ) : ℂ))
  simp only [zero_add] at hp
  norm_num at hp
  change hullPerimeter (fun i => (((1 / 2 : ℝ) : ℂ)) * z i) ≤ _ at h
  norm_num at h
  rw [hp] at h
  linarith

theorem circlePerimeter_eq_cos_mul {n : ℕ} :
    circlePerimeter n = (2 * diameterPerimeterBound n) * Real.cos (halfAngle n) := by
  unfold circlePerimeter diameterPerimeterBound halfAngle
  rw [show Real.pi / (n : ℝ) = 2 * (Real.pi / (2 * n)) by ring, Real.sin_two_mul]
  ring

/-- The concrete scale-invariant objective deficit of a diameter extremizer. -/
theorem objective_deficit_le {n : ℕ} (hn : 4 ≤ n) {z : Points n}
    (hz : DiameterAtMost 2 z) (hD : (n : ℝ) ^ n ≤ discriminant z)
    (hboundary : boundaryLength z ≤ hullPerimeter z) :
    objective (regular n) - objective z ≤ diameterBudget n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hDpos := (pow_pos hnR n).trans_le hD
  have hLpos := boundaryLength_pos_of_injective (by omega) (injective_of_discriminant_pos hDpos)
  have hc : 0 < Real.cos (halfAngle n) := lt_of_lt_of_le (by norm_num) (cos_halfAngle_lower hn)
  have hcircle := circlePerimeter_pos (show 3 ≤ n by omega)
  have hLb : boundaryLength z ≤ circlePerimeter n / Real.cos (halfAngle n) := by
    rw [circlePerimeter_eq_cos_mul, mul_div_cancel_right₀ _ hc.ne']
    exact hboundary.trans (diameter_perimeter_bound (by omega) hz)
  have hlogL := Real.log_le_log hLpos hLb
  rw [Real.log_div hcircle.ne' hc.ne'] at hlogL
  have hlogD := Real.log_le_log (pow_pos hnR n) hD
  have hexp : 0 ≤ (exponent n : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hlogL hexp
  have hgeom : objective (regular n) - objective z ≤
      (exponent n : ℝ) * (-Real.log (Real.cos (halfAngle n))) := by
    unfold objective
    rw [ExtremalNormalization.provedGeometry.regular_discriminant n (by omega),
      regular_boundaryLength (by omega)]
    nlinarith
  exact hgeom.trans (logsec_exponent_le_budget hn)

theorem model_deficit_eq {n : ℕ} {z : Points n} {σ : Equiv.Perm (Fin n)}
    {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hn : 4 ≤ n) (hη : η ≤ 1 / 4) :
    objective (regular n) - objective (z ∘ σ) = -LocalMaximum.gain n u := by
  let p : Points n := fun i => LocalObjective.perturbedVertices n u i
  have hinj : Function.Injective p := LocalConfiguration.small_perturbation_injective
    ClosedFourier.geometricSine hn u h.periodic h.error_nonneg hη h.relative_edges
  have hp := LocalConfiguration.objective_eq (show 2 ≤ n by omega)
    (LocalObjective.perturbedVertices n u)
    (LocalConfiguration.periodic_of_perturbed (by omega) u h.periodic) hinj
  have hrep : z ∘ σ = fun i => α + β * p i := funext h.coordinates
  have hobj : objective (z ∘ σ) = objective p := by
    rw [hrep]
    exact objective_affine p α β h.scale_ne_zero (discriminant_pos p hinj)
      (boundaryLength_pos_of_injective (by omega) hinj)
  have hregp : Function.Periodic (LocalObjective.regularVertices n) n := by
    intro j
    simp [LocalObjective.regularVertices, pow_add, LocalDFT.regularRoot_pow (by omega : 0 < n)]
  have he : (fun i : Fin n => LocalObjective.regularVertices n i) = regular n := by
    funext i
    exact LocalRigidity.root_power_eq_regular n i
  have hreg := LocalConfiguration.objective_eq (show 2 ≤ n by omega)
    (LocalObjective.regularVertices n) hregp
    (by rw [he]; exact LocalConfiguration.regular_injective hn ClosedFourier.geometricSine)
  rw [he] at hreg
  have hg := LocalObjective.objective_difference_eq_gain ClosedFourier.geometricSine hn u
    h.periodic h.error_nonneg hη h.relative_edges
  rw [hp, hreg] at hg
  rw [hobj]
  linarith

theorem totalEnergy_nonneg (n : ℕ) (u : ℕ → ℂ) : 0 ≤ totalEnergy n u :=
  add_nonneg (LocalMaximum.energyA_nonneg n u)
    (mul_nonneg (Nat.cast_nonneg _) (LocalMaximum.energyB_nonneg n u))

/-- The true diameter objective gives the quadratic budget in the chosen local coordinates. -/
theorem model_energy_bound {n : ℕ} {z : Points n} {σ : Equiv.Perm (Fin n)}
    {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hn : 4 ≤ n) (hη : η ≤ 1 / 1000)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hboundary : boundaryLength (z ∘ σ) ≤ hullPerimeter z) :
    -LocalMaximum.gain n u ≤ diameterBudget n ∧
      totalEnergy n u ≤ 32 * Real.pi ^ 2 ∧
      LocalDFT.positiveQuadratic n u ≤ diameterBudget n + 128 * Real.pi ^ 2 * η := by
  have hd : DiameterAtMost 2 (z ∘ σ) := fun i j => hz.1 (σ i) (σ j)
  have hD : (n : ℝ) ^ n ≤ discriminant (z ∘ σ) := by
    rw [discriminant_perm]
    exact hz.discriminant_ge (by omega)
  have hL : boundaryLength (z ∘ σ) ≤ hullPerimeter (z ∘ σ) := by
    rw [hullPerimeter_perm_proved]
    exact hboundary
  have hbudget := objective_deficit_le hn hd hD hL
  rw [model_deficit_eq h hn (by linarith)] at hbudget
  have hcoercive := LocalMaximum.local_maximum_bound ClosedFourier.dftInversion
    ClosedFourier.geometricSine LocalNonlinear.scalarLogTaylor hn
    (ClosedFourier.orthogonality n (by omega)) u h.periodic h.mean_zero h.similarity_zero
    h.error_nonneg hη h.relative_edges
  change LocalMaximum.gain n u ≤ -totalEnergy n u / 128 at hcoercive
  have he : totalEnergy n u ≤ 32 * Real.pi ^ 2 := by
    have hB := diameterBudget_le hn
    linarith
  refine ⟨hbudget, he, ?_⟩
  have hupper := LocalMaximum.gain_upper ClosedFourier.dftInversion
    ClosedFourier.geometricSine LocalNonlinear.scalarLogTaylor hn
    (ClosedFourier.orthogonality n (by omega)) u h.periodic h.similarity_zero
    h.error_nonneg (by linarith : η ≤ 1 / 4) h.relative_edges
  change LocalMaximum.gain n u ≤ -LocalDFT.positiveQuadratic n u + 4 * η * totalEnergy n u at hupper
  have hmul := mul_le_mul_of_nonneg_left he (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) h.error_nonneg)
  nlinarith

/-- The coarse part of (3.9), with no local-energy premise. -/
theorem diameter_sequence_energy {N : ℕ → ℕ} (hN4 : ∀ j, 4 ≤ N j)
    (hN : Tendsto N atTop atTop) (z : ∀ j, Points (N j))
    (hz : ∀ j, ExtremalNormalization.DiameterExtremal (z j)) :
    ∃ (σ : ∀ j, Equiv.Perm (Fin (N j))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ),
      Tendsto η atTop (𝓝 0) ∧ ∀ᶠ j in atTop,
        NormalizedRelativeEdgeModel (z j) (σ j) (α j) (β j) (u j) (η j) ∧
        boundaryLength (z j ∘ σ j) ≤ hullPerimeter (z j) ∧
        -LocalMaximum.gain (N j) (u j) ≤ diameterBudget (N j) ∧
        totalEnergy (N j) (u j) ≤ 32 * Real.pi ^ 2 ∧
        LocalDFT.positiveQuadratic (N j) (u j) ≤ diameterBudget (N j) + 128 * Real.pi ^ 2 * η j := by
  obtain ⟨σ, α, β, u, η, hη, hm⟩ := extremal_sequence_localization_with_perimeter hN4 hN z
    (fun j => Or.inl (hz j))
  refine ⟨σ, α, β, u, η, hη, ?_⟩
  filter_upwards [hm, hη.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 1000))]
    with j hj hs
  exact ⟨hj.1, hj.2, model_energy_bound hj.1 (hN4 j) hs.le (hz j) hj.2⟩

end
end Erdos1045.EventualExact.ExtremalEnergyBound



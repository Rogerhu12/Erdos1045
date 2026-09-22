import EventualExact.WholeBoxObjective
import EventualExact.NonlocalFeasibility
import EventualExact.WholeBoxFeasibility
import EventualExact.NormalizedExtremalFekete
import Erdos1045.LocalConfiguration
import Erdos1045.ClosedRegularGeometry

/-! The actual discriminant and diameter extremum lower bound from the finite box. -/

noncomputable section

open scoped BigOperators

namespace Erdos1045.EventualExact.WholeBoxLowerBound

open Complex Configuration FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open BoxLensLift WholeBoxObjective LocalObjective NonlocalFeasibility

theorem regular_logDistanceProduct {n : ℕ} (hn : 4 ≤ n) :
    logDistanceProduct n (regularVertices n) = (n : ℝ) * Real.log n := by
  have hp : Function.Periodic (regularVertices n) n := by
    intro j
    simp [regularVertices, pow_add, LocalDFT.regularRoot_pow (by omega : 0 < n)]
  have he : (fun j : Fin n => regularVertices n j) = regular n := by
    funext j
    exact (ClosedRegularGeometry.regular_eq_root_power n j).symm
  rw [LocalConfiguration.logDistanceProduct_eq_sum _ hp]
  have hi := LocalConfiguration.regular_injective hn ClosedFourier.geometricSine
  have hl := LocalConfiguration.logDiscriminant_eq_sum (regular n) hi
  rw [← he] at hl
  rw [← hl, he, ClosedRegularGeometry.regular_discriminant n (by omega), Real.log_pow]

theorem lifted_injective {m : ℕ} (hm : 32 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    Function.Injective (vertices (liftedCenter (by omega) q hq)) := by
  have hnR : (64 : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast (show 64 ≤ 2 * m by omega)
  have hη : 9 / ((2 * m : ℕ) : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < (2 * m : ℕ))).2
    linarith
  have hi := LocalConfiguration.small_perturbation_injective ClosedFourier.geometricSine
    (by omega : 4 ≤ 2 * m) (periodize (by omega) (liftedCenter (by omega) q hq))
    (periodize_periodic _ _) (η := 9 / ((2 * m : ℕ) : ℝ)) (by positivity) hη
    (lifted_relative_step (by omega) q hq)
  intro i j hij
  apply hi
  exact (vertices_nat (by omega) _ i).symm.trans (hij.trans (vertices_nat (by omega) _ j))

theorem lifted_log_discriminant {m : ℕ} (hm : 32 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    Real.log (discriminant (vertices (liftedCenter (by omega) q hq))) =
      logDistanceProduct (2 * m)
        (perturbedVertices (2 * m) (periodize (by omega) (liftedCenter (by omega) q hq))) := by
  rw [LocalConfiguration.logDiscriminant_eq_sum _ (lifted_injective hm q hq),
    LocalConfiguration.logDistanceProduct_eq_sum _
      (LocalConfiguration.periodic_of_perturbed (by omega) _ (periodize_periodic _ _))]
  simp only [vertices_nat (by omega : 0 < 2 * m)]

theorem whole_box_discriminant {m : ℕ} (hm : 32 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    |Real.log (discriminant (vertices (liftedCenter (by omega) q hq))) -
      ((2 * m : ℕ) : ℝ) * Real.log (2 * m : ℕ) - normalizedBoxEnergy (operator (2 * m)) q| ≤
      1000000 / ((2 * m : ℕ) : ℝ) ^ 2 := by
  rw [lifted_log_discriminant hm, ← regular_logDistanceProduct (by omega : 4 ≤ 2 * m)]
  exact whole_box_objective hm q hq

theorem whole_box_log_ratio {m : ℕ} (hm : 32 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    |Real.log (discriminant (vertices (liftedCenter (by omega) q hq)) /
      ((2 * m : ℕ) : ℝ) ^ (2 * m)) - normalizedBoxEnergy (operator (2 * m)) q| ≤
      1000000 / ((2 * m : ℕ) : ℝ) ^ 2 := by
  have hD := discriminant_pos _ (lifted_injective hm q hq)
  have hnR : (0 : ℝ) < (2 * m : ℕ) := by exact_mod_cast (show 0 < 2 * m by omega)
  rw [Real.log_div hD.ne' (pow_pos hnR _).ne', Real.log_pow]
  exact whole_box_discriminant hm q hq

theorem exists_box_maximizer_lower {m : ℕ} (hm : 32 ≤ m) :
    ∃ q : Fin (2 * m) → ℝ, ∃ hq : q ∈ FiniteBox.Q (by omega),
      FiniteBox.B (by omega : 0 < m) - 1000000 / ((2 * m : ℕ) : ℝ) ^ 2 ≤
        Real.log (discriminant (vertices (liftedCenter (by omega) q hq)) /
          ((2 * m : ℕ) : ℝ) ^ (2 * m)) := by
  obtain ⟨q, hq, he, _⟩ := FiniteBox.B_attained (by omega : 0 < m)
  refine ⟨q, hq, ?_⟩
  have h := whole_box_log_ratio hm q hq
  rw [he] at h
  have hl := (abs_le.mp h).1
  linarith

/-- Translation anchoring makes the true diameter-constrained problem compact. -/
theorem exists_diameterExtremal {n : ℕ} (hn : 0 < n) :
    ∃ z : Points n, ExtremalNormalization.DiameterExtremal z := by
  let i₀ : Fin n := ⟨0, hn⟩
  let s : Set (Points n) := {z | z i₀ = 0 ∧ DiameterAtMost 2 z}
  have hdclosed : IsClosed {z : Points n | DiameterAtMost 2 z} := by
    have h : IsClosed (⋂ i : Fin n, ⋂ j : Fin n, {z : Points n | ‖z i - z j‖ ≤ 2}) := by
      apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro j
      exact isClosed_le (by fun_prop) continuous_const
    simpa only [DiameterAtMost, Set.ofPred_forall] using h
  have hsclosed : IsClosed s :=
    (isClosed_eq (continuous_apply i₀) continuous_const).inter hdclosed
  have hsub : s ⊆ Metric.closedBall (0 : Points n) 2 := by
    intro z hz
    apply Metric.mem_closedBall.mpr
    rw [dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
    intro i
    simpa only [hz.1, sub_zero] using hz.2 i i₀
  have hscompact : IsCompact s :=
    (isCompact_closedBall (0 : Points n) 2).of_isClosed_subset hsclosed hsub
  have hsnonempty : s.Nonempty := by
    refine ⟨0, rfl, ?_⟩
    intro i j
    simp
  obtain ⟨z, hz, hmax⟩ := hscompact.exists_isMaxOn hsnonempty
    (HullGeometry.continuous_discriminant n).continuousOn
  refine ⟨z, hz.2, ?_⟩
  intro w hw
  let v : Points n := fun i => -w i₀ + w i
  have hvdiam : DiameterAtMost 2 v := by
    simpa only [v, norm_one, one_mul] using diameter_affine hw (-w i₀) 1
  have hv : v ∈ s := ⟨by simp [v], hvdiam⟩
  have hD : discriminant v = discriminant w := by
    simpa only [v, norm_one, one_pow, one_mul] using discriminant_affine w (-w i₀) 1
  have he := hmax hv
  change discriminant v ≤ discriminant z at he
  rwa [hD] at he

/-- The true maximum over all diameter-two configurations, rather than a conjectural formula. -/
def diameterMaximum (n : ℕ) : ℝ :=
  sSup (discriminant '' {z : Points n | DiameterAtMost 2 z})

theorem diameterMaximum_eq_of_extremal {n : ℕ} {z : Points n}
    (hz : ExtremalNormalization.DiameterExtremal z) : diameterMaximum n = discriminant z := by
  have hmem : discriminant z ∈ discriminant '' {w : Points n | DiameterAtMost 2 w} :=
    ⟨z, hz.1, rfl⟩
  have hb : BddAbove (discriminant '' {w : Points n | DiameterAtMost 2 w}) := by
    refine ⟨discriminant z, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hz.2 w hw
  apply le_antisymm
  · apply csSup_le ⟨_, hmem⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hz.2 w hw
  · exact le_csSup hb hmem

theorem diameterMaximum_attained {n : ℕ} (hn : 0 < n) :
    ∃ z : Points n, DiameterAtMost 2 z ∧ discriminant z = diameterMaximum n := by
  obtain ⟨z, hz⟩ := exists_diameterExtremal hn
  exact ⟨z, hz.1, (diameterMaximum_eq_of_extremal hz).symm⟩

theorem discriminant_le_diameterMaximum {n : ℕ} (hn : 0 < n) (z : Points n)
    (hz : DiameterAtMost 2 z) : discriminant z ≤ diameterMaximum n := by
  obtain ⟨w, hw⟩ := exists_diameterExtremal hn
  rw [diameterMaximum_eq_of_extremal hw]
  exact hw.2 z hz

theorem diameterMaximum_pos {n : ℕ} (hn : 3 ≤ n) : 0 < diameterMaximum n := by
  obtain ⟨z, hz⟩ := exists_diameterExtremal (by omega : 0 < n)
  rw [diameterMaximum_eq_of_extremal hz]
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact (pow_pos hp n).trans_le (hz.discriminant_ge hn)

theorem diameterExtremal_iff_eq_maximum {n : ℕ} (hn : 0 < n) (z : Points n) :
    ExtremalNormalization.DiameterExtremal z ↔
      DiameterAtMost 2 z ∧ discriminant z = diameterMaximum n := by
  constructor
  · intro hz
    exact ⟨hz.1, (diameterMaximum_eq_of_extremal hz).symm⟩
  · rintro ⟨hz, he⟩
    refine ⟨hz, fun w hw => ?_⟩
    rw [he]
    exact discriminant_le_diameterMaximum hn w hw

/-- A genuine feasible competitor realizing the finite-box lower estimate. -/
theorem exists_feasible_lower {m : ℕ} (hm : 256 ≤ 2 * m) :
    ∃ z : Points (2 * m), DiameterAtMost 2 z ∧ Function.Injective z ∧
      FiniteBox.B (by omega : 0 < m) - 1000000 / ((2 * m : ℕ) : ℝ) ^ 2 ≤
        Real.log (discriminant z / ((2 * m : ℕ) : ℝ) ^ (2 * m)) := by
  obtain ⟨q, hq, hvalue⟩ := exists_box_maximizer_lower (by omega : 32 ≤ m)
  exact ⟨vertices (liftedCenter (by omega) q hq),
    WholeBoxFeasibility.liftedCenter_diameterAtMost hm q hq,
    lifted_injective (by omega) q hq, hvalue⟩

/-- Manuscript (4.14), with Mn defined as the attained maximum of the original
diameter problem and Bn defined by the attained finite box maximum. -/
theorem diameterMaximum_log_lower {m : ℕ} (hm : 256 ≤ 2 * m) :
    FiniteBox.B (by omega : 0 < m) - 1000000 / ((2 * m : ℕ) : ℝ) ^ 2 ≤
      Real.log (diameterMaximum (2 * m) / ((2 * m : ℕ) : ℝ) ^ (2 * m)) := by
  obtain ⟨z, hz, hi, hl⟩ := exists_feasible_lower hm
  have hD := discriminant_pos z hi
  have hnR : (0 : ℝ) < (2 * m : ℕ) := by exact_mod_cast (show 0 < 2 * m by omega)
  have hcomp := discriminant_le_diameterMaximum (by omega) z hz
  refine hl.trans (Real.log_le_log (div_pos hD (pow_pos hnR _)) ?_)
  exact div_le_div_of_nonneg_right hcomp (pow_pos hnR _).le

theorem diameterExtremal_log_lower {m : ℕ} (hm : 256 ≤ 2 * m)
    (z : Points (2 * m)) (hz : ExtremalNormalization.DiameterExtremal z) :
    ((2 * m : ℕ) : ℝ) * Real.log (2 * m : ℕ) + FiniteBox.B (by omega : 0 < m) -
      1000000 / ((2 * m : ℕ) : ℝ) ^ 2 ≤ Real.log (discriminant z) := by
  have he := diameterMaximum_log_lower hm
  rw [diameterMaximum_eq_of_extremal hz] at he
  have hnR : (0 : ℝ) < (2 * m : ℕ) := by exact_mod_cast (show 0 < 2 * m by omega)
  have hD : 0 < discriminant z :=
    (pow_pos hnR (2 * m)).trans_le (hz.discriminant_ge (by omega))
  rw [Real.log_div hD.ne' (pow_pos hnR _).ne', Real.log_pow] at he
  linarith

end Erdos1045.EventualExact.WholeBoxLowerBound

import StructuralNote.RadialInterpolationQuotients
import StructuralNote.RadialObjectivePrice

/-! Uniform gradient control on the actual radial interpolation. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.ActualRadialGradient

open Erdos1045 Erdos1045.EventualExact Complex Filter Configuration CommonLocalization
open PolarAngleControl PolarRepresentation RadialDeficitControl RadialInterpolationQuotients
open LocalGradient

theorem eventually_uniform_gradient {N : ℕ → ℕ} {η : ℕ → ℝ} {C : ℝ}
    (hη : Tendsto η atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ u : ℕ → ℂ, 0 < N k → Function.Periodic u (N k) → 0 ≤ η k →
      (∀ i : Fin (N k), ∀ h ∈ Finset.Ico 1 (N k), ‖LocalDFT.pairRatio (N k) u i h‖ ≤ η k) →
      LocalDFT.energyA (N k) u ≤ C → gradientError (N k) u ≤ ε := by
  have htail : Tendsto (fun K : ℕ => 2 * Real.sqrt (2 * C) * Real.sqrt (1 / (K : ℝ)))
      atTop (𝓝 0) := by
    have hi : Tendsto (fun K : ℕ => 1 / (K : ℝ)) atTop (𝓝 0) := by
      simpa only [one_div, Function.comp_def] using
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero] using
      ((Real.continuous_sqrt.tendsto 0).comp hi).const_mul (2 * Real.sqrt (2 * C))
  obtain ⟨K, hKbound, hK⟩ := ((htail.eventually
    (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by linarith))).and (eventually_gt_atTop 0)).exists
  have hnear : Tendsto (fun k => 2 * η k * (harmonic K : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (hη.const_mul 2).mul_const (harmonic K : ℝ)
  filter_upwards [hnear.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by linarith)),
    hη.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with k hk hs
  intro u hn hu hη0 hp hE
  have hb := gradientError_bound hn hK u hu hη0 hs.le hp
  have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 2))
  have hmul := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg (1 / (K : ℝ)))
  nlinarith only [hb, hmul, hk, hKbound]

theorem radial_path_identity (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (t : ℝ) :
    RadialObjectivePrice.path (fun j : Fin (2 * m) => angle m u j)
      (fun j => deficit m r u j) (fun j => deangledCenter m r u j) t =
      fun j : Fin (2 * m) => LocalPhase.regularRoot (2 * m) ^ (j : ℕ) + pathSequence m r u t j := by
  funext j
  have he := RadialInterpolationEnergy.path_identity m r u t j
  change reference m j + pathSequence m r u t j = _ at he
  simpa only [RadialObjectivePrice.path, PolarCenterEnergy.phase, GapRigidity.circle,
    neg_neg, ExteriorBoundary.unit, reference] using he.symm

theorem eventual_model_path_gradient {M : ℕ → ℕ} (hM : Tendsto M atTop atTop)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ (z : Points (2 * M k)) (σ : Equiv.Perm (Fin (2 * M k)))
      (α β : ℂ) (u : ℕ → ℂ),
      NormalizedRelativeEdgeModel z σ α β u (η k) → ExtremalNormalization.DiameterExtremal z →
      ExtremalEnergyBound.totalEnergy (2 * M k) u ≤ 32 * Real.pi ^ 2 →
      PolarBounds (M k) u (η k) → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        RadialObjectivePrice.gradientDeviation (RadialObjectivePrice.path
          (fun j : Fin (2 * M k) => angle (M k) u j) (fun j => deficit (M k) ‖β‖ u j)
          (fun j => deangledCenter (M k) ‖β‖ u j) t) ≤ ε := by
  have hN : Tendsto (fun k => 2 * M k) atTop atTop := tendsto_atTop_mono (fun _ => by omega) hM
  have hg := eventually_uniform_gradient (N := fun k => 2 * M k)
    (C := 32768 * Real.pi ^ 4 + 2688 * Real.pi ^ 2) (pairBudget_tendsto hN hη) hε
  filter_upwards [hg, hM.eventually_ge_atTop 2,
    hη.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)] with k hk hm he
  intro z σ α β u hmodel hz hE hp t ht
  rw [radial_path_identity, RadialObjectivePrice.gradientDeviation_eq_gradientError]
  apply hk (pathSequence (M k) ‖β‖ u t) (by omega)
    (pathSequence_periodic (by omega) ‖β‖ u hmodel.periodic t)
  · unfold pairBudget
    have := hmodel.error_nonneg
    positivity
  · intro i h hh
    exact model_path_pair_le hm hmodel he hz hE hp ht (by have := (Finset.mem_Ico.mp hh).1; omega)
      (Finset.mem_Ico.mp hh).2 i
  · exact model_path_sequence_energy hm hmodel he hz hE hp ht

end StructuralNote.ActualRadialGradient

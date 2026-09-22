import EventualExact.PolarAngleEnergy
import EventualExact.ExtremalSchurGap

/-! The antipodal angle and center bounds are consequences of genuine maximality. -/

namespace Erdos1045.EventualExact.PolarAngleControl

open Complex AntipodalDecomposition CommonLocalization Configuration
open Filter ExtremalEnergyBound SchurSpectrum
open scoped BigOperators Topology
noncomputable section

theorem model_pair_energy_le {n : ℕ} (u : ℕ → ℂ)
    (hE : totalEnergy n u ≤ 32 * Real.pi ^ 2) : LocalDFT.energyA n u ≤ 32 * Real.pi ^ 2 := by
  have hb := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (LocalMaximum.energyB_nonneg n u)
  unfold totalEnergy at hE
  linarith

theorem model_even_size {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (hmean : (∑ j ∈ Finset.range (2 * m), u j) = 0)
    (hE : totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2) (j : ℕ) :
    ‖evenSequence m u j‖ ^ 2 ≤ sizeBudget (2 * m) := by
  have he : Function.Periodic (evenSequence m u) (2 * m) := by
    intro k
    rw [show k + 2 * m = k + m + m by omega, evenSequence_periodic m u hu,
      evenSequence_periodic m u hu]
  have hem : (∑ k : Fin (2 * m), evenSequence m u k) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (evenSequence m u)]
    exact evenSequence_mean_zero hm u hu hmean
  have hs := DiscreteSobolev.pointwise_sq_le (by omega : 2 ≤ 2 * m)
    (fun k : Fin (2 * m) => evenSequence m u k) hem ⟨j % (2 * m), Nat.mod_lt _ (by omega)⟩
  rw [pairEnergy_restrict (by omega) _ he, ← CyclicAngles.periodic_mod _ he j] at hs
  have hA := (even_energyA_le hm u hu).trans (model_pair_energy_le u hE)
  have hlog : 0 ≤ Real.log ((2 * m : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * m by omega))
  have hb := hs.trans (mul_le_mul_of_nonneg_left hA (by positivity :
    0 ≤ 12 * Real.log ((2 * m : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ) ^ 2))
  unfold sizeBudget
  convert hb using 1 <;> first | rfl | ring

theorem odd_step_le (m : ℕ) (u : ℕ → ℂ) {ε : ℝ}
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ ε) (j : ℕ) :
    ‖oddSequence m u (j + 1) - oddSequence m u j‖ ≤ ε := by
  have he : oddSequence m u (j + 1) - oddSequence m u j =
      ((u (j + 1) - u j) - (u ((j + m) + 1) - u (j + m))) / 2 := by
    unfold oddSequence
    rw [show j + 1 + m = j + m + 1 by omega]
    ring
  rw [he, norm_div]
  norm_num
  have h := (norm_sub_le (u (j + 1) - u j) (u ((j + m) + 1) - u (j + m))).trans
    (add_le_add (hstep j) (hstep (j + m)))
  linarith

theorem root_adjacent_norm (n j : ℕ) :
    ‖LocalPhase.regularRoot n ^ (j + 1) - LocalPhase.regularRoot n ^ j‖ =
      ‖LocalPhase.regularRoot n - 1‖ := by
  rw [show LocalPhase.regularRoot n ^ (j + 1) - LocalPhase.regularRoot n ^ j =
      LocalPhase.regularRoot n ^ j * (LocalPhase.regularRoot n - 1) by rw [pow_succ]; ring,
    norm_mul, norm_pow, LocalChord.root_norm, one_pow, one_mul]

def angleStepBudget (n : ℕ) (η : ℝ) : ℝ := 4 * Real.pi * (η + Real.sqrt (sizeBudget n))

theorem angleStepBudget_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun k => angleStepBudget (N k) (η k)) atTop (𝓝 0) := by
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp (sizeBudget_tendsto hN)
  have h := (hη.add hs).const_mul (4 * Real.pi)
  simpa only [angleStepBudget, Real.sqrt_zero, add_zero, mul_zero, Function.comp_def] using h

theorem model_angle_step {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) {η : ℝ} (hη : 0 ≤ η)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot (2 * m) - 1‖)
    (hsmall : ∀ j, ‖oddSequence m u j‖ ≤ 1 / 2)
    (hsize : ∀ j, ‖oddSequence m u j‖ ^ 2 ≤ sizeBudget (2 * m)) (j : ℕ) :
    (2 * m : ℝ) * |angle m u (j + 1) - angle m u j| ≤ angleStepBudget (2 * m) η := by
  have ha := angle_difference_bound u j (j + 1) (hsmall j) (hsmall (j + 1))
  rw [root_adjacent_norm] at ha
  have hd := odd_step_le m u hstep j
  have ho := Real.le_sqrt_of_sq_le (hsize j)
  have hnR : (0 : ℝ) < 2 * m := by positivity
  have he := DiscreteEnergy.symbol_norm_upper (2 * m) 1
  simp only [FiniteFourierLift.differenceSymbol, pow_one, Nat.cast_one, mul_one] at he
  have hed : (2 * m : ℝ) * ‖LocalPhase.regularRoot (2 * m) - 1‖ ≤ 2 * Real.pi := by
    have hn := (le_div_iff₀ hnR).mp (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using he)
    nlinarith
  have h1 : |angle m u (j + 1) - angle m u j| ≤
      2 * (η + Real.sqrt (sizeBudget (2 * m))) * ‖LocalPhase.regularRoot (2 * m) - 1‖ := by
    have hm' := mul_le_mul_of_nonneg_right ho (norm_nonneg (LocalPhase.regularRoot (2 * m) - 1))
    nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 hnR.le
  have h3 := mul_le_mul_of_nonneg_left hed
    (show 0 ≤ 2 * (η + Real.sqrt (sizeBudget (2 * m))) by positivity)
  unfold angleStepBudget
  nlinarith

structure PolarBounds (m : ℕ) (u : ℕ → ℂ) (η : ℝ) : Prop where
  angle_period : Function.Periodic (angle m u) m
  odd_small : ∀ j, ‖oddSequence m u j‖ ≤ 1 / 2
  even_size : ∀ j, ‖evenSequence m u j‖ ^ 2 ≤ sizeBudget (2 * m)
  odd_size : ∀ j, ‖oddSequence m u j‖ ^ 2 ≤ sizeBudget (2 * m)
  angle_size : ∀ j, |angle m u j| ^ 2 ≤ 4 * sizeBudget (2 * m)
  angle_energy : LocalDFT.energyA (2 * m) (fun j => (angle m u j : ℂ)) ≤ 512 * Real.pi ^ 2
  angle_step : ∀ j, (2 * m : ℝ) * |angle m u (j + 1) - angle m u j| ≤ angleStepBudget (2 * m) η

theorem model_polar_bounds {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hE : totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2)
    (hsize : sizeBudget (2 * m) ≤ 1 / 4) : PolarBounds m u η := by
  have hodd := model_odd_size (by omega) u h.periodic hE
  have hsmall (j : ℕ) : ‖oddSequence m u j‖ ≤ 1 / 2 := by
    have hs := (hodd j).trans hsize
    nlinarith [norm_nonneg (oddSequence m u j)]
  refine ⟨angle_periodic (by omega) u h.periodic, hsmall,
    model_even_size (by omega) u h.periodic h.mean_zero hE, hodd, ?_, ?_, ?_⟩
  · intro j
    have ha := angle_bound u j (hsmall j)
    have hs := pow_le_pow_left₀ (abs_nonneg _) ha 2
    nlinarith [hodd j]
  · have ha := angle_energy_le (by omega) u h.periodic hsmall
    linarith [model_pair_energy_le u hE]
  · exact model_angle_step (by omega) u h.error_nonneg h.relative_edges hsmall hodd

/-- These polar bounds, scale and matching budgets, and the strict original-center
Schur gap all hold in the same coordinates chosen for genuine extremizers. -/
theorem diameter_sequence_polar_bounds {M : ℕ → ℕ} (hM2 : ∀ k, 2 ≤ M k)
    (hM : Tendsto M atTop atTop) (z : ∀ k, Points (2 * M k))
    (hz : ∀ k, ExtremalNormalization.DiameterExtremal (z k)) :
    ∃ (σ : ∀ k, Equiv.Perm (Fin (2 * M k))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ),
      Tendsto η atTop (𝓝 0) ∧
      Tendsto (fun k => sizeBudget (2 * M k)) atTop (𝓝 0) ∧
      Tendsto (fun k => angleStepBudget (2 * M k) (η k)) atTop (𝓝 0) ∧
      ∀ᶠ k in atTop,
        NormalizedRelativeEdgeModel (z k) (σ k) (α k) (β k) (u k) (η k) ∧
        totalEnergy (2 * M k) (u k) ≤ 32 * Real.pi ^ 2 ∧
        PolarBounds (M k) (u k) (η k) ∧
        ‖β k‖ ≤ 1 ∧ (2 * M k : ℝ) ^ 2 * (1 - ‖β k‖ ^ 2) ≤ 256 * Real.pi ^ 2 ∧
        (2 * M k : ℝ) * (∑ j, (1 - ‖oddPart (FourierMultiplier.halfTurn (by have := hM2 k; omega))
          (z k ∘ σ k) j‖)) ≤ 256 * Real.pi ^ 2 ∧
        ‖FourierMultiplier.operator (2 * M k) (ExtremalSchurGap.evenConstraint (M k) (u k))‖ ≤ 7 * Real.pi / 8 := by
  have hN : Tendsto (fun k => 2 * M k) atTop atTop := tendsto_atTop_mono (fun _ => by omega) hM
  obtain ⟨σ, α, β, u, η, hη, hm, _⟩ := ExtremalSchurGap.diameter_sequence_schur_gap hM2 hM z hz
  refine ⟨σ, α, β, u, η, hη, sizeBudget_tendsto hN, angleStepBudget_tendsto hN hη, ?_⟩
  filter_upwards [hm, (sizeBudget_tendsto hN).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4),
    hη.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)] with k hk hs he
  have hE := hk.2.2.1
  have hscale := ExtremalScaleBound.model_matching_deficit_bound (hM2 k) hk.1 he (hz k) hE
  exact ⟨hk.1, hE, model_polar_bounds (hM2 k) hk.1 hE hs, hscale.1, hscale.2.1,
    hscale.2.2, hk.2.2.2.2.2.2.1⟩

end
end Erdos1045.EventualExact.PolarAngleControl

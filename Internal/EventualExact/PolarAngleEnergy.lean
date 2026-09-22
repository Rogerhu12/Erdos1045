import EventualExact.PolarAngleControl
import EventualExact.DiscretePoincare
import EventualExact.DiscreteSobolev
import EventualExact.ExtremalScaleBound

/-! Bounded angle energy and quantitative size for the actual antipodal coordinates. -/

namespace Erdos1045.EventualExact.PolarAngleControl

open Complex AntipodalDecomposition SchurSpectrum DiscreteEnergy
open scoped BigOperators
noncomputable section

theorem periodize_restrict {n : ℕ} (hn : 0 < n) (u : ℕ → ℂ) (hu : Function.Periodic u n) :
    periodize hn (fun j : Fin n => u j) = u := by
  funext j
  exact (CyclicAngles.periodic_mod u hu j).symm

theorem pairEnergy_restrict {n : ℕ} (hn : 0 < n) (u : ℕ → ℂ) (hu : Function.Periodic u n) :
    pairEnergy hn (fun j : Fin n => u j) = LocalDFT.energyA n u := by
  unfold pairEnergy
  rw [periodize_restrict hn u hu]

theorem oddSequence_mean_zero {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) :
    (∑ j ∈ Finset.range (2 * m), oddSequence m u j) = 0 := by
  simp only [oddSequence, ← Finset.sum_div, Finset.sum_sub_distrib,
    sum_half_shift hm u hu, sub_self, zero_div]

theorem oddSequence_poincare {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) :
    ((2 * m : ℝ) - 1) / 2 * (∑ j ∈ Finset.range (2 * m), normSq (oddSequence m u j)) ≤
      LocalDFT.energyA (2 * m) (oddSequence m u) := by
  have hmean : (∑ j : Fin (2 * m), oddSequence m u j) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (oddSequence m u)]
    exact oddSequence_mean_zero hm u hu
  have hp := mean_zero_poincare (by omega : 2 ≤ 2 * m) (fun j : Fin (2 * m) => oddSequence m u j) hmean
  rw [pairEnergy_restrict (by omega) _ (oddSequence_periodic m u hu),
    Fin.sum_univ_eq_sum_range (fun j => normSq (oddSequence m u j))] at hp
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hp

theorem angle_energy_le {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (hsmall : ∀ j, ‖oddSequence m u j‖ ≤ 1 / 2) :
    LocalDFT.energyA (2 * m) (fun j => (angle m u j : ℂ)) ≤ 16 * LocalDFT.energyA (2 * m) u := by
  have ha := angle_energy_bound hm u hsmall
  have hp := oddSequence_poincare hm u hu
  have ho := odd_energyA_le hm u hu
  linarith

theorem oddSequence_pointwise_sq {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (j : ℕ) :
    ‖oddSequence m u j‖ ^ 2 ≤
      12 * Real.log (2 * m) / (2 * m : ℝ) ^ 2 * LocalDFT.energyA (2 * m) u := by
  have hmean : (∑ i : Fin (2 * m), oddSequence m u i) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (oddSequence m u)]
    exact oddSequence_mean_zero hm u hu
  have hp := DiscreteSobolev.pointwise_sq_le (by omega : 2 ≤ 2 * m)
    (fun i : Fin (2 * m) => oddSequence m u i) hmean ⟨j % (2 * m), Nat.mod_lt _ (by omega)⟩
  rw [pairEnergy_restrict (by omega) _ (oddSequence_periodic m u hu),
    ← CyclicAngles.periodic_mod (oddSequence m u) (oddSequence_periodic m u hu) j] at hp
  have hl : 0 ≤ Real.log (2 * m : ℝ) := Real.log_nonneg (by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith)
  have hmul := mul_le_mul_of_nonneg_left (odd_energyA_le hm u hu)
    (show 0 ≤ 12 * Real.log (2 * m) / (2 * m : ℝ) ^ 2 by positivity)
  push_cast at hp
  exact hp.trans hmul

theorem angle_pointwise_sq {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (hsmall : ∀ j, ‖oddSequence m u j‖ ≤ 1 / 2) (j : ℕ) :
    |angle m u j| ^ 2 ≤
      48 * Real.log (2 * m) / (2 * m : ℝ) ^ 2 * LocalDFT.energyA (2 * m) u := by
  have ha := angle_bound u j (hsmall j)
  have hs := pow_le_pow_left₀ (abs_nonneg _) ha 2
  have hp := oddSequence_pointwise_sq hm u hu j
  calc
    _ ≤ 4 * ‖oddSequence m u j‖ ^ 2 := by nlinarith
    _ ≤ 4 * (12 * Real.log (2 * m) / (2 * m : ℝ) ^ 2 * LocalDFT.energyA (2 * m) u) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

def sizeBudget (n : ℕ) : ℝ := 384 * Real.pi ^ 2 * Real.log n / (n : ℝ) ^ 2

theorem sizeBudget_tendsto {N : ℕ → ℕ} (hN : Filter.Tendsto N Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun j => sizeBudget (N j)) Filter.atTop (nhds 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2)).tendsto_div_nhds_zero
  have hr : Filter.Tendsto (fun j => (N j : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hh := (h.comp hr).const_mul (384 * Real.pi ^ 2)
  simpa only [sizeBudget, Real.rpow_two, mul_zero, mul_div_assoc, Function.comp_def] using hh

theorem model_odd_size {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m))
    (hE : ExtremalEnergyBound.totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2) (j : ℕ) :
    ‖oddSequence m u j‖ ^ 2 ≤ sizeBudget (2 * m) := by
  have hA : LocalDFT.energyA (2 * m) u ≤ 32 * Real.pi ^ 2 := by
    have hb := LocalMaximum.energyB_nonneg (2 * m) u
    have hmR : (0 : ℝ) ≤ 2 * m := by positivity
    unfold ExtremalEnergyBound.totalEnergy at hE
    nlinarith
  have hlog : 0 ≤ Real.log (2 * m : ℝ) := Real.log_nonneg (by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith)
  have hp := (oddSequence_pointwise_sq hm u hu j).trans
    (mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ 12 * Real.log (2 * m) / (2 * m : ℝ) ^ 2))
  unfold sizeBudget
  push_cast
  convert hp using 1 <;> first | rfl | ring

end
end Erdos1045.EventualExact.PolarAngleControl

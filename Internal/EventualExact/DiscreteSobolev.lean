import EventualExact.DiscreteEnergyBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A logarithmic sup estimate for mean-zero columns on the finite circle. -/

noncomputable section
open scoped BigOperators

namespace Erdos1045.EventualExact.DiscreteSobolev

open Complex FourierMultiplier FiniteFourierLift SchurSpectrum DiscreteEnergy

theorem inverse_weight_sum_le {n : ℕ} (hn : 0 < n) :
    (∑ p : Fin n, (weight n p)⁻¹) ≤ 2 / (n : ℝ) * (1 + Real.log n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have herase : (Finset.range n).erase 0 = Finset.Ico 1 n := by
    ext p
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
    omega
  have hstart : (∑ p : Fin n, (weight n p)⁻¹) = ∑ p ∈ Finset.Ico 1 n, (weight n p)⁻¹ := by
    rw [Fin.sum_univ_eq_sum_range (fun p => (weight n p)⁻¹),
      ← Finset.sum_erase_add _ _ (Finset.mem_range.mpr hn), herase]
    simp [weight]
  have hterm (p : ℕ) (hp : p ∈ Finset.Ico 1 n) :
      (weight n p)⁻¹ = (1 / (n : ℝ)) * ((p : ℝ)⁻¹ + ((n - p : ℕ) : ℝ)⁻¹) := by
    obtain ⟨hp1, hpn⟩ := Finset.mem_Ico.mp hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hnp : (0 : ℝ) < (n : ℝ) - p := sub_pos.mpr (by exact_mod_cast hpn)
    rw [Nat.cast_sub hpn.le, weight]
    field_simp
    ring
  have hreflect : (∑ p ∈ Finset.Ico 1 n, ((n - p : ℕ) : ℝ)⁻¹) =
      ∑ p ∈ Finset.Ico 1 n, (p : ℝ)⁻¹ := by
    have he := Finset.sum_Ico_reflect (fun p : ℕ => (p : ℝ)⁻¹) 1 (m := n) (n := n) (by omega)
    simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel] using he
  have hH : (∑ p ∈ Finset.Ico 1 n, (p : ℝ)⁻¹) ≤ (harmonic n : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have h := Finset.mem_Ico.mp hp
      exact Finset.mem_Icc.mpr ⟨h.1, h.2.le⟩
    · intro p _ _
      positivity
  rw [hstart, Finset.sum_congr rfl (fun p hp => hterm p hp), ← Finset.mul_sum,
    Finset.sum_add_distrib, hreflect]
  calc
    _ = 2 / (n : ℝ) * ∑ p ∈ Finset.Ico 1 n, (p : ℝ)⁻¹ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hH.trans (harmonic_le_one_add_log n)) (by positivity)

theorem inverse_rootWeight_sum_le {n : ℕ} (hn : 2 ≤ n) :
    (∑ p : Fin n, (rootWeight n p)⁻¹ ^ 2) ≤ 12 * Real.log n / (n : ℝ) ^ 2 := by
  have hn0 : 0 < n := by omega
  have hterm (p : Fin n) : (rootWeight n p)⁻¹ ^ 2 =
      2 / (n : ℝ) * (weight n p)⁻¹ := by
    rw [inv_pow, rootWeight_sq p.isLt.le, mul_inv_rev, inv_div]
    ring
  rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.mul_sum]
  have hsum := mul_le_mul_of_nonneg_left (inverse_weight_sum_le hn0) (by positivity : 0 ≤ 2 / (n : ℝ))
  have hlog : (1 : ℝ) ≤ 2 * Real.log n := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hn : (2 : ℝ) ≤ n)
    linarith [Real.log_two_gt_d9]
  calc
    _ ≤ _ := hsum
    _ = 4 / (n : ℝ) ^ 2 * (1 + Real.log n) := by ring
    _ ≤ 4 / (n : ℝ) ^ 2 * (3 * Real.log n) := by gcongr; linarith
    _ = _ := by ring

theorem coefficient_norm_sum_bound {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (j : Fin n) :
    ‖c j‖ ≤ ∑ p : Fin n, ‖coefficient c p‖ := by
  rw [← synthesis_coefficient hn c j]
  unfold synthesis
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro p _
  simp [character, norm_pow, ClosedFourier.root_norm]

/-- Manuscript (3.12), with the concrete universal constant twelve. -/
theorem pointwise_sq_le {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ)
    (hmean : ∑ j, c j = 0) (j : Fin n) :
    ‖c j‖ ^ 2 ≤ 12 * Real.log n / (n : ℝ) ^ 2 * pairEnergy (by omega) c := by
  let : NeZero n := ⟨by omega⟩
  have hn0 : 0 < n := by omega
  have hzero : coefficient c 0 = 0 := by rw [coefficient_zero, hmean, zero_div]
  let x (p : Fin n) := rootWeight n p * ‖coefficient c p‖
  let y (p : Fin n) := (rootWeight n p)⁻¹
  have hterm (p : Fin n) : x p * y p = ‖coefficient c p‖ := by
    by_cases hp : p = 0
    · simp [x, y, hp, hzero]
    · have hp0 : 0 < p.val := by have := Fin.val_ne_zero_iff.mpr hp; omega
      have hw : 0 < rootWeight n p := Real.sqrt_pos.mpr
        (mul_pos (by positivity) (weight_pos hp0 p.isLt))
      dsimp [x, y]
      field_simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hxy : (∑ p : Fin n, x p * y p) = ∑ p : Fin n, ‖coefficient c p‖ :=
    Finset.sum_congr rfl (fun p _ => hterm p)
  have hx : (∑ p : Fin n, x p ^ 2) = pairEnergy hn0 c := (pairEnergy_squares hn0 c).symm
  rw [hxy, hx] at hcs
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (coefficient_norm_sum_bound hn0 c j) 2
  have hm := mul_le_mul_of_nonneg_left (inverse_rootWeight_sum_le hn) (pairEnergy_nonneg hn0 c)
  calc
    _ ≤ _ := hnorm.trans hcs
    _ ≤ _ := hm
    _ = _ := by ring

theorem sup_sq_le {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ)
    (hmean : ∑ j, c j = 0) :
    ‖c‖ ^ 2 ≤ 12 * Real.log n / (n : ℝ) ^ 2 * pairEnergy (by omega) c := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hD : 0 ≤ 12 * Real.log n / (n : ℝ) ^ 2 * pairEnergy (by omega) c :=
    mul_nonneg (by positivity) (pairEnergy_nonneg (by omega) c)
  have hb : ‖c‖ ≤ Real.sqrt (12 * Real.log n / (n : ℝ) ^ 2 * pairEnergy (by omega) c) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    exact Real.le_sqrt_of_sq_le (pointwise_sq_le hn c hmean j)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rwa [Real.sq_sqrt hD] at hs

end Erdos1045.EventualExact.DiscreteSobolev

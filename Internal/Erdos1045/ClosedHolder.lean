import Erdos1045.ClosedSobolev
import Erdos1045.KernelFrequencyTail
import Mathlib.Analysis.Real.Pi.Bounds

namespace Erdos1045.ClosedSeries

open scoped BigOperators
open ExteriorClassical
noncomputable section

theorem norm_pow_sub_pow_le {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (m : ℕ) :
    ‖u ^ m - v ^ m‖ ≤ (m : ℝ) * ‖u - v‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have heq : u ^ (m + 1) - v ^ (m + 1) = u * (u ^ m - v ^ m) + (u - v) * v ^ m := by ring
    rw [heq]
    calc
      _ ≤ ‖u * (u ^ m - v ^ m)‖ + ‖(u - v) * v ^ m‖ := norm_add_le _ _
      _ = ‖u‖ * ‖u ^ m - v ^ m‖ + ‖u - v‖ * ‖v‖ ^ m := by rw [norm_mul, norm_mul, norm_pow]
      _ ≤ 1 * ((m : ℝ) * ‖u - v‖) + ‖u - v‖ * 1 :=
        add_le_add (mul_le_mul hu ih (norm_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg v) hv) (norm_nonneg _))
      _ = _ := by push_cast; ring

theorem norm_pow_sub_pow_le_two {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (m : ℕ) :
    ‖u ^ m - v ^ m‖ ≤ 2 := by
  have h := norm_sub_le (u ^ m) (v ^ m)
  rw [norm_pow, norm_pow] at h
  have hu' := pow_le_one₀ (norm_nonneg u) hu (n := m)
  have hv' := pow_le_one₀ (norm_nonneg v) hv (n := m)
  linarith

def powerKernel (u v : ℂ) (m : ℕ) : ℝ := ‖u ^ m - v ^ m‖ ^ 2 / (m : ℝ) ^ 2

theorem powerKernel_le_reciprocal {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (m : ℕ) :
    powerKernel u v m ≤ 4 * (1 / (m : ℝ) ^ 2) := by
  have hb := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2
    (norm_pow_sub_pow_le_two hu hv m)
  have h := div_le_div_of_nonneg_right hb (sq_nonneg (m : ℝ))
  simpa only [powerKernel, div_eq_mul_inv, one_mul, show (2 : ℝ) ^ 2 = 4 by norm_num] using h

theorem powerKernel_summable {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    Summable (powerKernel u v) :=
  Summable.of_nonneg_of_le (fun _m => div_nonneg (sq_nonneg _) (sq_nonneg _))
    (powerKernel_le_reciprocal hu hv) (hasSum_zeta_two.summable.mul_left 4)

theorem powerKernel_le_distance {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (m : ℕ) :
    powerKernel u v m ≤ ‖u - v‖ ^ 2 := by
  by_cases hm : m = 0
  · simp [powerKernel, hm]
  · have hm' : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero hm)
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_pow_sub_pow_le hu hv m) 2
    apply (div_le_iff₀ (sq_pos_of_pos hm')).2
    simpa only [mul_pow, mul_comm] using h

theorem reciprocal_square_tail {N : ℕ} (hN : 0 < N) :
    (∑' m : ℕ, 1 / (((m + (N + 1) : ℕ) : ℝ) ^ 2)) ≤ 1 / (N : ℝ) := by
  have h := KernelWeights.tsum_shifted_weight_le (n := 2) (L := N + 2) (by omega) (by omega)
  have heq (m : ℕ) : KernelWeights.weight 2 (m + (N + 2)) =
      1 / (((m + (N + 1) : ℕ) : ℝ) ^ 2) := by
    rw [KernelWeights.weight_of_gt (by omega) (by omega)]
    have hi : m + (N + 2) - 1 = m + (N + 1) := by omega
    simp only [hi, Nat.reduceSub, Nat.cast_one, one_pow]
  simp_rw [heq] at h
  simpa only [Nat.reduceSub, Nat.cast_one, one_pow, Nat.add_sub_cancel] using h

theorem powerKernel_bound {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    (∑' m, powerKernel u v m) ≤ 16 * ‖u - v‖ := by
  let d : ℝ := ‖u - v‖
  have hd0 : 0 ≤ d := norm_nonneg _
  by_cases hz : d = 0
  · have huv : u = v := sub_eq_zero.mp (norm_eq_zero.mp hz)
    simp [huv, powerKernel]
  have hd : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hz)
  by_cases hsmall : d ≤ 1
  · let N := Nat.ceil (1 / d)
    have hN : 0 < N := Nat.one_le_ceil_iff.mpr (one_div_pos.mpr hd)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hNl : 1 / d ≤ (N : ℝ) := Nat.le_ceil _
    have hNu : (N : ℝ) < 1 / d + 1 := Nat.ceil_lt_add_one (one_div_nonneg.mpr hd.le)
    have hprefix : (∑ m ∈ Finset.range (N + 1), powerKernel u v m) ≤ ((N : ℝ) + 1) * d ^ 2 := by
      calc
        _ ≤ ∑ _m ∈ Finset.range (N + 1), d ^ 2 :=
          Finset.sum_le_sum (fun m _ => powerKernel_le_distance hu hv m)
        _ = _ := by simp
    have htail : (∑' m, powerKernel u v (m + (N + 1))) ≤ 4 / (N : ℝ) := by
      have hs : Summable (fun m : ℕ => powerKernel u v (m + (N + 1))) :=
        (powerKernel_summable hu hv).comp_injective (fun _ _ h => Nat.add_right_cancel h)
      have hz₀ : Summable (fun m : ℕ => 1 / (((m + (N + 1) : ℕ) : ℝ) ^ 2)) :=
        hasSum_zeta_two.summable.comp_injective (fun _ _ h => Nat.add_right_cancel h)
      have hz := hz₀.mul_left 4
      have ht := hs.tsum_le_tsum (fun m => powerKernel_le_reciprocal hu hv (m + (N + 1))) hz
      rw [tsum_mul_left] at ht
      have hb := mul_le_mul_of_nonneg_left (reciprocal_square_tail hN) (by norm_num : (0 : ℝ) ≤ 4)
      exact ht.trans (by simpa only [mul_one_div] using hb)
    rw [← (powerKernel_summable hu hv).sum_add_tsum_nat_add (N + 1)]
    have hpre : ((N : ℝ) + 1) * d ^ 2 ≤ 3 * d := by
      have hmul := mul_le_mul_of_nonneg_right hNu.le (sq_nonneg d)
      have hi : (1 / d + 2) * d ^ 2 = d + 2 * d ^ 2 := by field_simp
      nlinarith
    have ht : 4 / (N : ℝ) ≤ 4 * d := by
      apply (div_le_iff₀ hN0).2
      have hmul := (div_le_iff₀ hd).1 hNl
      nlinarith
    change (∑ m ∈ Finset.range (N + 1), powerKernel u v m) +
      (∑' m, powerKernel u v (m + (N + 1))) ≤ 16 * d
    linarith
  · have hb := (powerKernel_summable hu hv).tsum_le_tsum
      (powerKernel_le_reciprocal hu hv) (hasSum_zeta_two.summable.mul_left 4)
    rw [tsum_mul_left, hasSum_zeta_two.tsum_eq] at hb
    change (∑' m, powerKernel u v m) ≤ 16 * d
    nlinarith [Real.pi_pos, Real.pi_lt_four]

theorem laurent_series_summable (a : ℕ → ℂ) (ha : SobolevCoefficients a)
    {w : ℂ} (hw : 1 ≤ ‖w‖) : Summable (fun m => a m * w⁻¹ ^ m) := by
  have hi : ‖w⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hw
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) _ (laurent_absolute a ha)
  intro m
  rw [norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hi) (norm_nonneg _)).trans_eq (mul_one _)

theorem inverse_distance_le {u v : ℂ} (hu : 1 ≤ ‖u‖) (hv : 1 ≤ ‖v‖) :
    ‖u⁻¹ - v⁻¹‖ ≤ ‖u - v‖ := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by linarith : ‖u‖ ≠ 0)
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by linarith : ‖v‖ ≠ 0)
  have heq : u⁻¹ - v⁻¹ = (v - u) / (u * v) := by field_simp
  rw [heq, norm_div, norm_mul, norm_sub_rev]
  exact div_le_self (norm_nonneg _) (by nlinarith)

theorem laurent_holder_bound (a : ℕ → ℂ) (ha : SobolevCoefficients a)
    (u v : ℂ) (hu : 1 ≤ ‖u‖) (hv : 1 ≤ ‖v‖) :
    ‖laurent a u - laurent a v‖ ≤
      4 * Real.sqrt (sobolevEnergySquared a) * Real.sqrt ‖u - v‖ := by
  have hui : ‖u⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hu
  have hvi : ‖v⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hv
  let x : ℕ → ℂ := fun m => (m : ℂ) * a m
  let y : ℕ → ℂ := fun m => (u⁻¹ ^ m - v⁻¹ ^ m) / (m : ℂ)
  have hxterm (m : ℕ) : ‖x m‖ ^ 2 = (m : ℝ) ^ 2 * ‖a m‖ ^ 2 := by
    simp only [x, norm_mul, Complex.norm_natCast, mul_pow]
  have hyterm (m : ℕ) : ‖y m‖ ^ 2 = powerKernel u⁻¹ v⁻¹ m := by
    simp only [y, norm_div, Complex.norm_natCast, div_pow, powerKernel]
  have hx : Summable (fun m => ‖x m‖ ^ 2) := by
    simp_rw [hxterm]
    exact (FaberFourier.coefficient_energies_summable ha.2).2
  have hy : Summable (fun m => ‖y m‖ ^ 2) := by
    simp_rw [hyterm]
    exact powerKernel_summable hui hvi
  have hp := (complex_sequence_cauchy x y hx hy).2
  have hprod (m : ℕ) : x m * y m = a m * u⁻¹ ^ m - a m * v⁻¹ ^ m := by
    by_cases hm : m = 0
    · simp [x, y, hm]
    · have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
      dsimp only [x, y]
      field_simp
  have hsum : (∑' m, x m * y m) = laurent a u - laurent a v := by
    simp_rw [hprod]
    exact (laurent_series_summable a ha hu).tsum_sub (laurent_series_summable a ha hv)
  rw [hsum] at hp
  simp_rw [hxterm, hyterm] at hp
  have hk : (∑' m, powerKernel u⁻¹ v⁻¹ m) ≤ 16 * ‖u - v‖ :=
    (powerKernel_bound hui hvi).trans (mul_le_mul_of_nonneg_left (inverse_distance_le hu hv) (by norm_num))
  have he0 : 0 ≤ ∑' m : ℕ, (m : ℝ) ^ 2 * ‖a m‖ ^ 2 :=
    tsum_nonneg (fun m => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have he : (∑' m : ℕ, (m : ℝ) ^ 2 * ‖a m‖ ^ 2) ≤ sobolevEnergySquared a := by
    unfold sobolevEnergySquared
    nlinarith [Real.pi_gt_three]
  calc
    ‖laurent a u - laurent a v‖ ≤ _ := hp
    _ ≤ Real.sqrt (sobolevEnergySquared a) * Real.sqrt (16 * ‖u - v‖) :=
      mul_le_mul (Real.sqrt_le_sqrt he) (Real.sqrt_le_sqrt hk) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]; norm_num; ring

theorem laurentHolder : ∃ H : ℝ, 0 < H ∧ ∀ a, SobolevCoefficients a →
    ∀ u v : ℂ, 1 ≤ ‖u‖ → 1 ≤ ‖v‖ →
      ‖laurent a u - laurent a v‖ ≤
        H * Real.sqrt (sobolevEnergySquared a) * Real.sqrt ‖u - v‖ :=
  ⟨4, by norm_num, laurent_holder_bound⟩

theorem laurentAnalysis : ClassicalLaurentAnalysis :=
  ⟨laurent_absolute, laurentHolder, laurent_interval_sobolev, laurent_hardy_evaluation⟩

end
end Erdos1045.ClosedSeries

import Erdos1045.ClosedLaurent
import Erdos1045.ExteriorClassical
import Mathlib.NumberTheory.ZetaValues

namespace Erdos1045.ClosedSeries

open scoped BigOperators ComplexConjugate
open ExteriorClassical FaberFourier ExteriorBoundary
noncomputable section

theorem cosine_inverse_square_hasSum {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 2 * Real.pi) :
    HasSum (fun m : ℕ => Real.cos ((m : ℝ) * d) / (m : ℝ) ^ 2)
      (Real.pi ^ 2 / 6 - Real.pi * d / 2 + d ^ 2 / 4) := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  have hx : d / (2 * Real.pi) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hd hp.le, (div_le_one hp).2 hd'⟩
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
  norm_num only [Nat.mul_one, Nat.reduceAdd, neg_one_sq, one_mul, Nat.factorial_two] at h
  change HasSum _ (_ * bernoulliFun 2 (d / (2 * Real.pi))) at h
  rw [bernoulliFun_two] at h
  convert h using 1 <;> try rfl
  · funext m
    have heq : 2 * Real.pi * (m : ℝ) * (d / (2 * Real.pi)) = (m : ℝ) * d := by field_simp
    rw [heq]
    ring
  · field_simp
    ring

theorem character_re (m : ℕ) (t : ℝ) : (character m t).re = Real.cos ((m : ℝ) * t) := by
  simp [character, Complex.exp_re]

theorem character_mul_conj (m : ℕ) (s t : ℝ) :
    character m t * conj (character m s) = character m (t - s) := by
  unfold character
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_neg, map_natCast, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub]
  ring

theorem character_sub_sq (m : ℕ) (s t : ℝ) :
    ‖character m t - character m s‖ ^ 2 = 2 - 2 * Real.cos ((m : ℝ) * (t - s)) := by
  rw [Complex.sq_norm, Complex.normSq_sub, character_mul_conj, character_re]
  simp only [Complex.normSq_eq_norm_sq, norm_character, one_pow]
  ring

theorem character_sub_le_two (m : ℕ) (s t : ℝ) : ‖character m t - character m s‖ ≤ 2 := by
  simpa only [norm_character, one_add_one_eq_two] using norm_sub_le (character m t) (character m s)

theorem difference_kernel_summable (s t : ℝ) :
    Summable (fun m : ℕ => ‖character m t - character m s‖ ^ 2 / (m : ℝ) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun m => div_nonneg (sq_nonneg _) (sq_nonneg _)) _
    (hasSum_zeta_two.summable.mul_left 4)
  intro m
  have hb := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2 (character_sub_le_two m s t)
  have h := div_le_div_of_nonneg_right hb (sq_nonneg (m : ℝ))
  simpa only [div_eq_mul_inv, one_mul, show (2 : ℝ) ^ 2 = 4 by norm_num] using h

theorem difference_kernel_bound (s t : ℝ) :
    (∑' m : ℕ, ‖character m t - character m s‖ ^ 2 / (m : ℝ) ^ 2) ≤ 2 * Real.pi * |t - s| := by
  by_cases hsmall : |t - s| ≤ 2 * Real.pi
  · have hc := cosine_inverse_square_hasSum (abs_nonneg (t - s)) hsmall
    have h := (hasSum_zeta_two.mul_left 2).sub (hc.mul_left 2)
    have heq (m : ℕ) : Real.cos ((m : ℝ) * |t - s|) = Real.cos ((m : ℝ) * (t - s)) := by
      by_cases hd : 0 ≤ t - s
      · rw [abs_of_nonneg hd]
      · rw [abs_of_neg (lt_of_not_ge hd), mul_neg, Real.cos_neg]
    have hh : HasSum (fun m : ℕ => ‖character m t - character m s‖ ^ 2 / (m : ℝ) ^ 2)
        (Real.pi * |t - s| - |t - s| ^ 2 / 2) := by
      convert h using 1 <;> try rfl
      · funext m
        rw [character_sub_sq, heq]
        ring
      · ring
    rw [hh.tsum_eq]
    have hp : 0 ≤ Real.pi * |t - s| := mul_nonneg Real.pi_pos.le (abs_nonneg _)
    nlinarith [sq_nonneg |t - s|]
  · have hbound : (∑' m : ℕ, ‖character m t - character m s‖ ^ 2 / (m : ℝ) ^ 2) ≤
        4 * (Real.pi ^ 2 / 6) := by
      have h := (difference_kernel_summable s t).tsum_le_tsum
        (g := fun m : ℕ => 4 * (1 / (m : ℝ) ^ 2))
        (fun m => by
          have hb := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2 (character_sub_le_two m s t)
          have h := div_le_div_of_nonneg_right hb (sq_nonneg (m : ℝ))
          simpa only [div_eq_mul_inv, one_mul, show (2 : ℝ) ^ 2 = 4 by norm_num] using h)
        (hasSum_zeta_two.summable.mul_left 4)
      simpa only [tsum_mul_left, hasSum_zeta_two.tsum_eq] using h
    have hlarge : 2 * Real.pi < |t - s| := lt_of_not_ge hsmall
    nlinarith [Real.pi_pos]

theorem laurent_unit_eq_series (a : ℕ → ℂ) (t : ℝ) : laurent a (unit t) = series a t := by
  apply tsum_congr
  intro m
  congr 1
  unfold unit character
  rw [← Complex.exp_neg, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem laurent_interval_sobolev (a : ℕ → ℂ) (ha : SobolevCoefficients a) (s t : ℝ) :
    ‖laurent a (unit t) - laurent a (unit s)‖ ≤
      Real.sqrt (sobolevEnergySquared a) * Real.sqrt |t - s| := by
  let x : ℕ → ℂ := fun m => (m : ℂ) * a m
  let y : ℕ → ℂ := fun m => (character m t - character m s) / (m : ℂ)
  have hxterm (m : ℕ) : ‖x m‖ ^ 2 = (m : ℝ) ^ 2 * ‖a m‖ ^ 2 := by
    simp only [x, norm_mul, Complex.norm_natCast, mul_pow]
  have hyterm (m : ℕ) : ‖y m‖ ^ 2 = ‖character m t - character m s‖ ^ 2 / (m : ℝ) ^ 2 := by
    simp only [y, norm_div, Complex.norm_natCast, div_pow]
  have hx : Summable (fun m => ‖x m‖ ^ 2) := by
    simp_rw [hxterm]
    exact (coefficient_energies_summable ha.2).2
  have hy : Summable (fun m => ‖y m‖ ^ 2) := by
    simp_rw [hyterm]
    exact difference_kernel_summable s t
  have hp := (complex_sequence_cauchy x y hx hy).2
  have hprod (m : ℕ) : x m * y m = a m * character m t - a m * character m s := by
    by_cases hm : m = 0
    · simp [x, y, hm, character]
    · have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
      dsimp only [x, y]
      field_simp
  have hsum : (∑' m, x m * y m) = series a t - series a s := by
    simp_rw [hprod]
    exact (series_summable (laurent_absolute a ha) t).tsum_sub
      (series_summable (laurent_absolute a ha) s)
  rw [hsum, ← laurent_unit_eq_series, ← laurent_unit_eq_series] at hp
  simp_rw [hxterm, hyterm] at hp
  have hb := Real.sqrt_le_sqrt (difference_kernel_bound s t)
  have hmul := mul_le_mul_of_nonneg_left hb
    (Real.sqrt_nonneg (∑' m : ℕ, (m : ℝ) ^ 2 * ‖a m‖ ^ 2))
  apply hp.trans
  convert hmul using 1
  rw [sobolevEnergySquared, Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi),
    Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  ring

end
end Erdos1045.ClosedSeries

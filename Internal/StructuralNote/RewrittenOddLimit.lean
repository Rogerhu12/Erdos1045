import StructuralNote.ReusedEndpoints
import EventualExact.ExtremalEnergyBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! The normalized odd-order limit for the actual diameter maximum. -/

namespace StructuralNote.RewrittenOddLimit

open Erdos1045 Erdos1045.EventualExact Configuration Filter
open ExtremalEnergyBound
open scoped Topology

noncomputable section

def logsec (n : ℕ) : ℝ :=
  (exponent n : ℝ) * (-Real.log (Real.cos (halfAngle n)))

theorem lower_identity {n : ℕ} (hn : 1 ≤ n) :
    (exponent n : ℝ) * (1 - Real.cos (halfAngle n)) =
      (Real.pi ^ 2 / 8) * (1 - 1 / (n : ℝ)) *
        Real.sinc (Real.pi / (4 * n)) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx : Real.pi / (4 * n) ≠ 0 := by positivity
  have hc : 1 - Real.cos (halfAngle n) = 2 * Real.sin (Real.pi / (4 * n)) ^ 2 := by
    have he : halfAngle n = 2 * (Real.pi / (4 * n)) := by unfold halfAngle; ring
    rw [he, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / (4 * n))]
  rw [hc, Real.sinc_of_ne_zero hx]
  simp only [exponent, Nat.cast_mul, Nat.cast_sub hn, Nat.cast_one]
  field_simp
  ring

theorem lower_tendsto :
    Tendsto (fun n : ℕ => (exponent n : ℝ) * (1 - Real.cos (halfAngle n)))
      atTop (𝓝 (Real.pi ^ 2 / 8)) := by
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hx : Tendsto (fun n : ℕ => Real.pi / (4 * n)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm,
      mul_zero, zero_mul] using hinv.const_mul (Real.pi / 4)
  have hs : Tendsto (fun n : ℕ => Real.sinc (Real.pi / (4 * n))) atTop (𝓝 1) := by
    simpa only [Real.sinc_zero, Function.comp_def] using (Real.continuous_sinc.tendsto 0).comp hx
  have hfactor : Tendsto (fun n : ℕ => (Real.pi ^ 2 / 8) * (1 - 1 / (n : ℝ)) *
      Real.sinc (Real.pi / (4 * n)) ^ 2) atTop (𝓝 (Real.pi ^ 2 / 8)) := by
    simpa only [one_div, sub_zero, one_pow, mul_one] using
      ((((tendsto_const_nhds (x := (1 : ℝ))).sub hinv).const_mul (Real.pi ^ 2 / 8)).mul (hs.pow 2))
  apply hfactor.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (lower_identity hn).symm

theorem logsec_tendsto : Tendsto logsec atTop (𝓝 (Real.pi ^ 2 / 8)) := by
  have hlo : ∀ᶠ n : ℕ in atTop,
      (exponent n : ℝ) * (1 - Real.cos (halfAngle n)) ≤ logsec n := by
    filter_upwards [eventually_ge_atTop 4] with n hn
    have hc : 0 < Real.cos (halfAngle n) :=
      lt_of_lt_of_le (by norm_num) (cos_halfAngle_lower hn)
    have hh := Real.log_le_sub_one_of_pos hc
    exact mul_le_mul_of_nonneg_left (by linarith : 1 - Real.cos (halfAngle n) ≤
      -Real.log (Real.cos (halfAngle n))) (Nat.cast_nonneg (exponent n))
  have hhi : ∀ᶠ n : ℕ in atTop, logsec n ≤ diameterBudget n := by
    filter_upwards [eventually_ge_atTop 4] with n hn
    exact logsec_exponent_le_budget hn
  have hup := diameterBudget_tendsto (N := id) tendsto_id
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [lower_tendsto.eventually (lt_mem_nhds ha), hlo] with n hn hb
    exact hn.trans_le hb
  · intro a ha
    filter_upwards [hup.eventually (gt_mem_nhds ha), hhi] with n hn hb
    exact hb.trans_lt hn

theorem exp_logsec {n : ℕ} (hn : 4 ≤ n) :
    Real.exp (logsec n) = (Real.cos (halfAngle n) ^ exponent n)⁻¹ := by
  have hc : 0 < Real.cos (halfAngle n) :=
    lt_of_lt_of_le (by norm_num) (cos_halfAngle_lower hn)
  rw [logsec, mul_neg, ← Real.log_pow, Real.exp_neg, Real.exp_log (pow_pos hc _)]

/-- Corollary 1.3 along odd integers, for the supremum M itself. -/
theorem odd_normalized_maximum_tendsto :
    Tendsto (fun m : ℕ => M (2 * m + 1) / (2 * m + 1 : ℝ) ^ (2 * m + 1))
      atTop (𝓝 (Real.exp (Real.pi ^ 2 / 8))) := by
  have hN : Tendsto (fun m : ℕ => 2 * m + 1) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m + 1) tendsto_id
  have he := (Real.continuous_exp.tendsto _).comp (logsec_tendsto.comp hN)
  obtain ⟨n₀, hn₀, hM⟩ := eventual_odd_maximum
  apply he.congr'
  filter_upwards [hN.eventually (eventually_ge_atTop n₀)] with m hm
  have hn4 : 4 ≤ 2 * m + 1 := hn₀.trans hm
  have hnR : (2 * m + 1 : ℝ) ≠ 0 := by positivity
  change Real.exp (logsec (2 * m + 1)) = _
  rw [exp_logsec hn4, hM _ hm ⟨m, rfl⟩]
  simp only [halfAngle, exponent, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  field_simp

end
end StructuralNote.RewrittenOddLimit

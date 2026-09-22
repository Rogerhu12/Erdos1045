import StructuralNote.CommonClosureEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Ring

/-! The literal logarithmic radius in (9.5), including its containment in the
energy ball on which the quantitative closure theorem applies. -/

namespace StructuralNote.CommonDomainRadius

open Filter Real
open scoped Topology
noncomputable section

def logOrder (n : ℕ) : ℕ := ⌈Real.log n / Real.log 2⌉₊

def energyRadius (n : ℕ) : ℝ := (logOrder n : ℝ) ^ 2 / (n : ℝ) ^ 2

theorem logOrder_le {n : ℕ} (hn : 2 ≤ n) : (logOrder n : ℝ) ≤ 4 * Real.log n := by
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hlogpos : 0 ≤ Real.log n := by linarith
  have hc := Nat.ceil_lt_add_one (show 0 ≤ Real.log n / Real.log 2 by positivity)
  have hd : Real.log n / Real.log 2 ≤ 2 * Real.log n := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    nlinarith
  dsimp [logOrder]
  linarith

theorem eventual_radius_le_inverse : ∀ᶠ n : ℕ in atTop, energyRadius n ≤ 1 / n := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have ht : Tendsto (fun n : ℕ => 16 * (Real.log n ^ 2 / (n : ℝ))) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    simpa only [Real.rpow_two, Real.rpow_one, Function.comp_def, mul_zero] using (h.comp hn).const_mul 16
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_ge_atTop 2] with n hb hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL := logOrder_le hn
  have hsq : (logOrder n : ℝ) ^ 2 ≤ 16 * Real.log n ^ 2 := by
    have hc := pow_le_pow_left₀ (Nat.cast_nonneg (logOrder n)) hL 2
    nlinarith only [hc]
  have hb' : 16 * Real.log n ^ 2 < n := by
    have hx : (16 * Real.log n ^ 2) / (n : ℝ) < 1 := by
      simpa only [mul_div_assoc] using hb
    simpa only [one_mul] using (div_lt_iff₀ hnR).mp hx
  have hi : 1 / (n : ℝ) = (n : ℝ) / (n : ℝ) ^ 2 := by field_simp
  rw [energyRadius, hi]
  exact div_le_div_of_nonneg_right (hsq.trans hb'.le) (sq_nonneg _)

theorem fixed_inner_radius_eventually_lt (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K / (n : ℝ) ^ 2 < energyRadius n := by
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_gt_atTop (Real.log 2 * (|K| + 1)),
    eventually_ge_atTop 2] with n hn hn2
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : Real.log n / Real.log 2 ≤ (logOrder n : ℝ) := Nat.le_ceil _
  have hh : |K| + 1 < (logOrder n : ℝ) := by
    apply lt_of_lt_of_le ?_ hc
    exact (lt_div_iff₀ hlog2).mpr (by simpa only [mul_comm] using hn)
  have hs : K < (logOrder n : ℝ) ^ 2 := by
    have ha := le_abs_self K
    have hz := abs_nonneg K
    nlinarith
  exact (div_lt_div_iff_of_pos_right (sq_pos_of_pos hnR)).mpr hs

end
end StructuralNote.CommonDomainRadius

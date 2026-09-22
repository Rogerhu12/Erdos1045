import Erdos1045.LocalPhase
import Mathlib.Tactic

namespace Erdos1045.LocalChord

open LocalPhase LocalFourier LocalTrigonometry
open scoped BigOperators
noncomputable section

theorem root_norm (n : ℕ) : ‖regularRoot n‖ = 1 := by
  simp [regularRoot, Complex.norm_exp]

theorem norm_chain (u : ℕ → ℂ) {L : ℝ}
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ L) (j m : ℕ) :
    ‖u (j + m) - u j‖ ≤ m * L := by
  induction m with
  | zero => simp
  | succ m ih =>
      have htri : ‖u (j + (m + 1)) - u j‖ ≤
          ‖u (j + m + 1) - u (j + m)‖ + ‖u (j + m) - u j‖ := by
        rw [show u (j + (m + 1)) - u j =
          (u (j + m + 1) - u (j + m)) + (u (j + m) - u j) by
            rw [Nat.add_assoc]; ring]
        exact norm_add_le _ _
      have hs := hstep (j + m)
      simp only [Nat.cast_add, Nat.cast_one]
      linarith

theorem norm_geom_eq_mode (HS : ClassicalGeometricSine) {n m : ℕ}
    (hn : 2 ≤ n) (hm : 0 < m) (hmn : m < n) :
    ‖geom m (regularRoot n)‖ = mode n m := by
  have hform := HS n hn m hm
  rw [hform, norm_mul]
  have hphase : ‖phase n (m - 1)‖ = 1 := by
    simp [phase, Complex.norm_exp]
  rw [hphase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mode_pos (by exact_mod_cast (show 1 < n by omega))
      (by exact_mod_cast hm) (by exact_mod_cast hmn))]

theorem vertex_distance (HS : ClassicalGeometricSine) {n m : ℕ}
    (hn : 2 ≤ n) (hm : 0 < m) (hmn : m < n) (j : ℕ) :
    ‖regularRoot n ^ (j + m) - regularRoot n ^ j‖ =
      mode n m * ‖regularRoot n - 1‖ := by
  have hid : regularRoot n ^ (j + m) - regularRoot n ^ j =
      regularRoot n ^ j * (geom m (regularRoot n) * (regularRoot n - 1)) := by
    rw [geom_mul_sub_one, pow_add]
    ring
  rw [hid, norm_mul, norm_pow, root_norm, one_pow, one_mul,
    norm_mul, norm_geom_eq_mode HS hn hm hmn]

theorem short_quotient_bound (HS : ClassicalGeometricSine) {n m : ℕ}
    (hn : 4 ≤ n) (hm : 0 < m) (hshort : 2 * m ≤ n)
    (hroot : regularRoot n ≠ 1) (u : ℕ → ℂ) {η : ℝ} (hη : 0 ≤ η)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖regularRoot n - 1‖) (j : ℕ) :
    ‖(u (j + m) - u j) / (regularRoot n ^ (j + m) - regularRoot n ^ j)‖ ≤ 2 * η := by
  have hmn : m < n := by omega
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmode := mode_pos hnR hmR (by exact_mod_cast hmn)
  have hbase : 0 < ‖regularRoot n - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hroot)
  have hden := vertex_distance HS (by omega : 2 ≤ n) hm hmn j
  have hlow := mode_lower_half hnR hmR.le (by exact_mod_cast hshort)
  have hpi := Real.pi_lt_four
  have hmode2 : (m : ℝ) ≤ 2 * mode n m := by
    have hpi0 := Real.pi_pos
    have hlow' := (div_le_iff₀ hpi0).mp hlow
    nlinarith
  rw [norm_div, hden]
  apply (div_le_iff₀ (mul_pos hmode hbase)).mpr
  have hchain := norm_chain u hstep j m
  have hmul := mul_le_mul_of_nonneg_right hmode2 (mul_nonneg hη hbase.le)
  nlinarith

/-- Any nonzero cyclic separation is controlled by the shorter boundary chain. -/
theorem quotient_bound (HS : ClassicalGeometricSine) {n h : ℕ}
    (hn : 4 ≤ n) (hh : 0 < h) (hhn : h < n)
    (hroot : regularRoot n ≠ 1) (hrootn : regularRoot n ^ n = 1)
    (u : ℕ → ℂ) (hperiod : ∀ j, u (j + n) = u j)
    {η : ℝ} (hη : 0 ≤ η)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖regularRoot n - 1‖) (j : ℕ) :
    ‖(u (j + h) - u j) / (regularRoot n ^ (j + h) - regularRoot n ^ j)‖ ≤ 2 * η := by
  by_cases hshort : 2 * h ≤ n
  · exact short_quotient_bound HS hn hh hshort hroot u hη hstep j
  · have hrev := short_quotient_bound HS hn (show 0 < n - h by omega)
      (show 2 * (n - h) ≤ n by omega) hroot u hη hstep (j + h)
    have hind : j + h + (n - h) = j + n := by omega
    have hvertex : regularRoot n ^ (j + n) = regularRoot n ^ j := by
      rw [pow_add, hrootn, mul_one]
    rw [hind, hperiod, hvertex] at hrev
    have heq : (u j - u (j + h)) / (regularRoot n ^ j - regularRoot n ^ (j + h)) =
        (u (j + h) - u j) / (regularRoot n ^ (j + h) - regularRoot n ^ j) := by
      rw [show u j - u (j + h) = -(u (j + h) - u j) by ring,
        show regularRoot n ^ j - regularRoot n ^ (j + h) =
          -(regularRoot n ^ (j + h) - regularRoot n ^ j) by ring, neg_div_neg_eq]
    rwa [heq] at hrev

end
end Erdos1045.LocalChord

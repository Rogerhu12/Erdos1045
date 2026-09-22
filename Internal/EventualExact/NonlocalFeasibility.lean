import EventualExact.GeometricLogRemainder
import EventualExact.PolarForceBounds
import EventualExact.CyclicDistance
import Erdos1045.ClosedCircle

/-! Strict nonlocal distance bounds from the actual half-periodic center increments. -/

namespace Erdos1045.EventualExact.NonlocalFeasibility

open Complex FourierMultiplier FiniteFourierLift SchurSpectrum
open scoped BigOperators
noncomputable section

def baseRadius (n : ℕ) : ℝ := 2 * (1 - Real.cos (Real.pi / n))

def stepBudget (n : ℕ) (C : ℝ) : ℝ := Real.sqrt 3 * baseRadius n + C / (n : ℝ) ^ 4

theorem baseRadius_nonneg (n : ℕ) : 0 ≤ baseRadius n := by
  unfold baseRadius
  nlinarith [Real.cos_le_one (Real.pi / n)]

theorem cos_deficit_quadratic {x : ℝ} (hx : 0 ≤ x) (hxp : x ≤ Real.pi / 2) :
    x ^ 2 / 3 ≤ 1 - Real.cos x := by
  have hy0 : 0 ≤ x / 2 := by positivity
  have hy1 : x / 2 ≤ 1 := by linarith [Real.pi_lt_four]
  have hy2 : (x / 2) ^ 2 ≤ 1 := by nlinarith
  have hy3 := mul_le_mul_of_nonneg_right hy2 hy0
  have hs := Real.sin_ge_sub_cube hy0
  have hslow : 5 * (x / 2) / 6 ≤ Real.sin (x / 2) := by nlinarith
  have hsnonneg : 0 ≤ Real.sin (x / 2) := by linarith
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 5 * (x / 2) / 6) hsnonneg).mpr hslow
  rw [one_sub_cos_eq_two_sin_sq]
  nlinarith [sq_nonneg x]

theorem baseRadius_scaled {n : ℕ} (hn : 8 ≤ n) :
    4 ≤ (n : ℝ) ^ 2 * baseRadius n ∧
    (n : ℝ) ^ 2 * baseRadius n ≤ Real.pi ^ 2 ∧
    7 / 8 ≤ Real.cos (Real.pi / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 ≤ Real.pi / n := by positivity
  have ha' : Real.pi / n ≤ 1 / 2 := by
    apply (div_le_iff₀ hn0).mpr
    linarith [Real.pi_lt_four]
  have haπ : |Real.pi / n| ≤ Real.pi := by rw [abs_of_nonneg ha]; linarith [Real.pi_gt_three]
  have he : (n : ℝ) ^ 2 * (Real.pi / n) ^ 2 = Real.pi ^ 2 := by field_simp
  have hlo := one_sub_cos_lower_quadratic haπ
  have hlow := mul_le_mul_of_nonneg_left hlo (sq_nonneg (n : ℝ))
  have hlow' : (n : ℝ) ^ 2 * (2 * (Real.pi / n) ^ 2 / Real.pi ^ 2) = 2 := by
    field_simp
  rw [hlow'] at hlow
  have hhi := Real.one_sub_sq_div_two_le_cos (x := Real.pi / n)
  have hhigh := mul_le_mul_of_nonneg_left hhi (sq_nonneg (n : ℝ))
  unfold baseRadius
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem stepBudget_scaled {n : ℕ} (hn : 8 ≤ n) {C : ℝ}
    (hlarge : 16 * C ≤ (n : ℝ) ^ 2) :
    (n : ℝ) ^ 2 * stepBudget n C ≤ (7 / 4) * Real.pi ^ 2 + 1 / 16 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hroot : Real.sqrt 3 ≤ 7 / 4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have herr : (n : ℝ) ^ 2 * (C / (n : ℝ) ^ 4) ≤ 1 / 16 := by
    have he : (n : ℝ) ^ 2 * (C / (n : ℝ) ^ 4) = C / (n : ℝ) ^ 2 := by field_simp
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
    linarith
  have hrad := (baseRadius_scaled hn).2.1
  have hm := mul_le_mul hroot hrad
    (mul_nonneg (sq_nonneg (n : ℝ)) (baseRadius_nonneg n)) (by norm_num : (0 : ℝ) ≤ 7 / 4)
  unfold stepBudget
  nlinarith

theorem scalar_slack {n k : ℕ} (hn : 8 ≤ n) (hk : 2 ≤ k) (hkn : 2 * k ≤ n)
    {C : ℝ} (hlarge : 16 * C ≤ (n : ℝ) ^ 2) :
    2 * Real.cos (k * Real.pi / n) + k * stepBudget n C ≤
      2 - (k : ℝ) * (k - 1) / (16 * (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hknR : 2 * (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hbudget := stepBudget_scaled hn hlarge
  have hscaled : (k : ℝ) * (k - 1) / 16 ≤
      (n : ℝ) ^ 2 * (2 - (2 * Real.cos (k * Real.pi / n) + k * stepBudget n C)) := by
    by_cases hkexact : k = 2
    · subst k
      obtain ⟨hrlo, _, hc⟩ := baseRadius_scaled hn
      have hr := baseRadius_nonneg n
      have hsqrt : Real.sqrt 3 ≤ 7 / 4 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
      have hgap : 2 - 2 * Real.cos (2 * (Real.pi / n)) - 2 * Real.sqrt 3 * baseRadius n =
          2 * baseRadius n * (1 + Real.cos (Real.pi / n) - Real.sqrt 3) := by
        rw [Real.cos_two_mul, baseRadius]
        ring
      have hlower : baseRadius n / 4 ≤
          2 - 2 * Real.cos (2 * (Real.pi / n)) - 2 * Real.sqrt 3 * baseRadius n := by
        rw [hgap]
        nlinarith [mul_nonneg hr (show 0 ≤ 1 + Real.cos (Real.pi / n) - Real.sqrt 3 - 1 / 8 by linarith)]
      have hm := mul_le_mul_of_nonneg_left hlower (sq_nonneg (n : ℝ))
      have herr : (n : ℝ) ^ 2 * (C / (n : ℝ) ^ 4) ≤ 1 / 16 := by
        have he : (n : ℝ) ^ 2 * (C / (n : ℝ) ^ 4) = C / (n : ℝ) ^ 2 := by field_simp
        rw [he]
        apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
        linarith
      simp only [Nat.cast_ofNat, stepBudget]
      rw [show 2 * Real.pi / n = 2 * (Real.pi / n) by ring]
      nlinarith
    · have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (show 3 ≤ k by omega)
      have harg : (k : ℝ) * Real.pi / n ≤ Real.pi / 2 := by
        apply (div_le_iff₀ hn0).mpr
        nlinarith [Real.pi_pos]
      have hcos := cos_deficit_quadratic (by positivity : 0 ≤ (k : ℝ) * Real.pi / n) harg
      have hm := mul_le_mul_of_nonneg_left hcos (show 0 ≤ 2 * (n : ℝ) ^ 2 by positivity)
      have he : (n : ℝ) ^ 2 * ((k : ℝ) * Real.pi / n) ^ 2 = (k : ℝ) ^ 2 * Real.pi ^ 2 := by
        field_simp
      have hb := mul_le_mul_of_nonneg_left hbudget hk0
      have hpoly : (k : ℝ) * (k - 1) / 8 ≤ (2 / 3) * (k : ℝ) ^ 2 - (7 / 4) * k := by
        nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hk3)]
      have hpoly' := mul_le_mul_of_nonneg_right hpoly (sq_nonneg Real.pi)
      have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      have hpi' := mul_le_mul_of_nonneg_left hpi
        (show 0 ≤ (k : ℝ) * (k - 1) / 8 from
          div_nonneg (mul_nonneg hk0 (by linarith)) (by norm_num))
      nlinarith
  have hdiv : ((k : ℝ) * (k - 1) / 16) / (n : ℝ) ^ 2 ≤
      2 - (2 * Real.cos (k * Real.pi / n) + k * stepBudget n C) :=
    (div_le_iff₀ (sq_pos_of_pos hn0)).mpr (by nlinarith [hscaled])
  rw [show ((k : ℝ) * (k - 1) / 16) / (n : ℝ) ^ 2 =
    (k : ℝ) * (k - 1) / (16 * (n : ℝ) ^ 2) by ring] at hdiv
  linarith

theorem root_power_circlePoint (n j : ℕ) : LocalPhase.regularRoot n ^ j =
    CircleMatrix.circlePoint (2 * Real.pi * j / n) := by
  unfold LocalPhase.regularRoot CircleMatrix.circlePoint
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem cross_root_distance {m k : ℕ} (hm : 0 < m) (hk : k ≤ m) (j : ℕ) :
    ‖LocalPhase.regularRoot (2 * m) ^ (j + (m + k)) - LocalPhase.regularRoot (2 * m) ^ j‖ =
      2 * Real.cos (k * Real.pi / (2 * m)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (k : ℝ) ≤ m := by exact_mod_cast hk
  rw [root_power_circlePoint, root_power_circlePoint, CircleMatrix.circlePoint_chord]
  have he : (2 * Real.pi * ((j + (m + k) : ℕ) : ℝ) / (2 * m : ℕ) -
      2 * Real.pi * j / (2 * m : ℕ)) / 2 = Real.pi / 2 + k * Real.pi / (2 * m) := by
    push_cast
    field_simp
    ring
  rw [he, add_comm (Real.pi / 2), Real.sin_add_pi_div_two]
  apply abs_of_nonneg
  apply mul_nonneg (by norm_num)
  apply Real.cos_nonneg_of_mem_Icc
  constructor
  · have : (0 : ℝ) ≤ k * Real.pi / (2 * m) := by positivity
    linarith [Real.pi_pos]
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m)).mpr
    nlinarith [Real.pi_pos]

theorem periodize_step_bound {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) {B : ℝ}
    (hstep : ∀ i, ‖difference hn c i‖ ≤ B) (j : ℕ) :
    ‖periodize hn c (j + 1) - periodize hn c j‖ ≤ B := by
  let i : Fin n := ⟨j % n, Nat.mod_lt _ hn⟩
  have h := hstep i
  simpa [difference, successor, periodize, i, Nat.add_mod] using h

def vertices {n : ℕ} (c : Fin n → ℂ) (j : Fin n) : ℂ := LocalPhase.regularRoot n ^ j.val + c j

theorem vertices_advance {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (j : Fin n) (r : ℕ) :
    vertices c (cyclicAdvance j r) =
      LocalObjective.perturbedVertices n (periodize hn c) (j.val + r) := by
  unfold vertices cyclicAdvance LocalObjective.perturbedVertices LocalObjective.regularVertices periodize
  rw [ClosedFourier.root_pow_mod hn (j.val + r)]

theorem vertices_nat {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (j : Fin n) :
    vertices c j = LocalObjective.perturbedVertices n (periodize hn c) j.val := by
  simp [vertices, LocalObjective.perturbedVertices, LocalObjective.regularVertices, periodize_fin]

theorem forward_cross_bound {m k : ℕ} (hm : 4 ≤ m) (hk : 2 ≤ k) (hkm : k ≤ m)
    (c : Fin (2 * m) → ℂ) (hc : HalfPeriodic (by omega) c) {C : ℝ}
    (hlarge : 16 * C ≤ ((2 * m : ℕ) : ℝ) ^ 2)
    (hstep : ∀ i, ‖difference (by omega) c i‖ ≤ stepBudget (2 * m) C)
    (j : Fin (2 * m)) :
    ‖vertices c (cyclicAdvance j (m + k)) - vertices c j‖ ≤
      2 - (k : ℝ) * (k - 1) / (16 * ((2 * m : ℕ) : ℝ) ^ 2) := by
  let u := periodize (by omega : 0 < 2 * m) c
  have hhalf := AntipodalLog.periodize_half_periodic (by omega) c hc
  have hchain := LocalChord.norm_chain u (periodize_step_bound (by omega) c hstep) j.val k
  have he : u (j.val + (m + k)) = u (j.val + k) := by
    dsimp only [u]
    rw [show j.val + (m + k) = (j.val + k) + m by omega, hhalf]
  rw [vertices_advance (by omega), vertices_nat (by omega)]
  change ‖(LocalPhase.regularRoot (2 * m) ^ (j.val + (m + k)) + u (j.val + (m + k))) -
    (LocalPhase.regularRoot (2 * m) ^ j.val + u j.val)‖ ≤ _
  rw [he, show (LocalPhase.regularRoot (2 * m) ^ (j.val + (m + k)) + u (j.val + k)) -
    (LocalPhase.regularRoot (2 * m) ^ j.val + u j.val) =
    (LocalPhase.regularRoot (2 * m) ^ (j.val + (m + k)) - LocalPhase.regularRoot (2 * m) ^ j.val) +
      (u (j.val + k) - u j.val) by ring]
  calc
    _ ≤ ‖LocalPhase.regularRoot (2 * m) ^ (j.val + (m + k)) -
        LocalPhase.regularRoot (2 * m) ^ j.val‖ + ‖u (j.val + k) - u j.val‖ := norm_add_le _ _
    _ ≤ 2 * Real.cos (k * Real.pi / ((2 * m : ℕ) : ℝ)) + k * stepBudget (2 * m) C := by
      rw [cross_root_distance (by omega) hkm]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        add_le_add (le_refl (2 * Real.cos (k * Real.pi / (2 * m)))) hchain
    _ ≤ _ := scalar_slack (by omega) hk (by omega) hlarge

theorem advance_back_forward {m k : ℕ} (hkm : k ≤ m) (j : Fin (2 * m)) :
    cyclicAdvance (cyclicAdvance j (m - k)) (m + k) = j := by
  apply Fin.ext
  simp only [cyclicAdvance, Nat.mod_add_mod]
  rw [show j.val + (m - k) + (m + k) = j.val + 2 * m by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

theorem backward_cross_bound {m k : ℕ} (hm : 4 ≤ m) (hk : 2 ≤ k) (hkm : k ≤ m)
    (c : Fin (2 * m) → ℂ) (hc : HalfPeriodic (by omega) c) {C : ℝ}
    (hlarge : 16 * C ≤ ((2 * m : ℕ) : ℝ) ^ 2)
    (hstep : ∀ i, ‖difference (by omega) c i‖ ≤ stepBudget (2 * m) C)
    (j : Fin (2 * m)) :
    ‖vertices c (cyclicAdvance j (m - k)) - vertices c j‖ ≤
      2 - (k : ℝ) * (k - 1) / (16 * ((2 * m : ℕ) : ℝ) ^ 2) := by
  have h := forward_cross_bound hm hk hkm c hc hlarge hstep (cyclicAdvance j (m - k))
  rw [advance_back_forward hkm, norm_sub_rev] at h
  exact h

theorem nonlocal_cross_strict {m k : ℕ} (hm : 4 ≤ m) (hk : 2 ≤ k) (hkm : k ≤ m)
    (c : Fin (2 * m) → ℂ) (hc : HalfPeriodic (by omega) c) {C : ℝ}
    (hlarge : 16 * C ≤ ((2 * m : ℕ) : ℝ) ^ 2)
    (hstep : ∀ i, ‖difference (by omega) c i‖ ≤ stepBudget (2 * m) C)
    (j : Fin (2 * m)) :
    ‖vertices c (cyclicAdvance j (m + k)) - vertices c j‖ < 2 ∧
      ‖vertices c (cyclicAdvance j (m - k)) - vertices c j‖ < 2 := by
  have hpos : 0 < (k : ℝ) * (k - 1) / (16 * ((2 * m : ℕ) : ℝ) ^ 2) := by
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hk1 : (0 : ℝ) < k - 1 := by linarith
    positivity
  have hp := forward_cross_bound hm hk hkm c hc hlarge hstep j
  have hn := backward_cross_bound hm hk hkm c hc hlarge hstep j
  constructor <;> linarith

/-- The two forms cover every cyclic offset except the matching and adjacent cross offsets. -/
theorem nonlocal_offset_strict {m r : ℕ} (hm : 4 ≤ m) (hr : r < 2 * m)
    (hne : r ≠ m - 1 ∧ r ≠ m ∧ r ≠ m + 1)
    (c : Fin (2 * m) → ℂ) (hc : HalfPeriodic (by omega) c) {C : ℝ}
    (hlarge : 16 * C ≤ ((2 * m : ℕ) : ℝ) ^ 2)
    (hstep : ∀ i, ‖difference (by omega) c i‖ ≤ stepBudget (2 * m) C)
    (j : Fin (2 * m)) : ‖vertices c (cyclicAdvance j r) - vertices c j‖ < 2 := by
  by_cases hrm : r ≤ m
  · have h := (nonlocal_cross_strict hm (show 2 ≤ m - r by omega) (by omega)
      c hc hlarge hstep j).2
    rw [Nat.sub_sub_self hrm] at h
    exact h
  · have h := (nonlocal_cross_strict hm (show 2 ≤ r - m by omega) (by omega)
      c hc hlarge hstep j).1
    rw [Nat.add_sub_of_le (show m ≤ r by omega)] at h
    exact h

end
end Erdos1045.EventualExact.NonlocalFeasibility

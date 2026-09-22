import EventualExact.PolarForceBounds
import Erdos1045.CyclicAngles
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.NumberTheory.Harmonic.Bounds

/-! The harmonic reciprocal-angle bound for an actual separated cyclic lift. -/

namespace Erdos1045.EventualExact.AngularHarmonicBound

open scoped BigOperators
open CyclicAngles

noncomputable section

def principalDistance (t : ℝ) : ℝ := |(t : Real.Angle).toReal|

def shortAngle {n : ℕ} (a : Angles n) (i j : Fin n) : ℝ :=
  ((a.angle i - a.angle j : ℝ) : Real.Angle).toReal

@[simp] theorem principalDistance_zero : principalDistance 0 = 0 := by
  simp [principalDistance]

theorem principalDistance_neg (t : ℝ) : principalDistance (-t) = principalDistance t := by
  simp [principalDistance, Real.Angle.coe_neg]

theorem principalDistance_add_two_pi (t : ℝ) :
    principalDistance (t + 2 * Real.pi) = principalDistance t := by
  simp [principalDistance, Real.Angle.coe_add, Real.Angle.coe_two_pi]

theorem principalDistance_eq_min {t : ℝ} (ht : 0 ≤ t) (htp : t ≤ 2 * Real.pi) :
    principalDistance t = min t (2 * Real.pi - t) := by
  unfold principalDistance
  by_cases h : t ≤ Real.pi
  · rw [Real.Angle.toReal_coe_eq_self_iff.mpr ⟨by linarith [Real.pi_pos], h⟩,
      abs_of_nonneg ht, min_eq_left (by linarith)]
  · rw [Real.Angle.toReal_coe_eq_self_sub_two_pi_iff.mpr
      ⟨lt_of_not_ge h, by linarith [Real.pi_pos]⟩,
      abs_of_nonpos (by linarith), min_eq_right (by linarith)]
    ring

theorem shortAngle_abs_le_pi {n : ℕ} (a : Angles n) (i j : Fin n) :
    |shortAngle a i j| ≤ Real.pi := Real.Angle.abs_toReal_le_pi _

theorem shortAngle_cos {n : ℕ} (a : Angles n) (i j : Fin n) :
    Real.cos (shortAngle a i j) = Real.cos (a.angle i - a.angle j) := by
  unfold shortAngle
  rw [Real.Angle.cos_toReal, Real.Angle.cos_coe]

theorem shortAngle_sin {n : ℕ} (a : Angles n) (i j : Fin n) :
    Real.sin (shortAngle a i j) = Real.sin (a.angle i - a.angle j) := by
  unfold shortAngle
  rw [Real.Angle.sin_toReal, Real.Angle.sin_coe]

theorem shortAngle_abs_comm {n : ℕ} (a : Angles n) (i j : Fin n) :
    |shortAngle a i j| = |shortAngle a j i| := by
  change principalDistance (a.angle i - a.angle j) = principalDistance (a.angle j - a.angle i)
  rw [show a.angle i - a.angle j = -(a.angle j - a.angle i) by ring, principalDistance_neg]

theorem shortAngle_ne_zero {n : ℕ} (a : Angles n) {i j : Fin n} (hij : i ≠ j) :
    shortAngle a i j ≠ 0 := by
  have hpos {i j : Fin n} (hij : i < j) : 0 < |shortAngle a i j| := by
    have hl : 0 < a.angle j - a.angle i := sub_pos.mpr (a.increasing (by exact_mod_cast hij))
    have hu : a.angle j - a.angle i < 2 * Real.pi := by
      have hh := a.increasing (show (j : ℤ) < (i : ℤ) + n by omega)
      rw [a.period] at hh
      linarith
    change 0 < principalDistance (a.angle i - a.angle j)
    rw [show a.angle i - a.angle j = -(a.angle j - a.angle i) by ring,
      principalDistance_neg, principalDistance_eq_min hl.le hu.le]
    exact lt_min hl (by linarith)
  apply abs_pos.mp
  rcases lt_or_gt_of_ne hij with h | h
  · exact hpos h
  · rw [shortAngle_abs_comm]
    exact hpos h

/-- Adjacent separation is summed along an actual integer window. -/
theorem angle_window_lower {n : ℕ} (a : Angles n) {δ : ℝ}
    (hsep : ∀ z : ℤ, δ ≤ a.angle (z + 1) - a.angle z) (i : ℤ) (m : ℕ) :
    δ * m ≤ a.angle (i + m) - a.angle i := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hh := hsep (i + m)
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_add, Nat.cast_one]
    rw [show i + ((m : ℤ) + 1) = (i + m) + 1 by ring]
    nlinarith

theorem window_complement {n : ℕ} (a : Angles n) {m : ℕ} (hm : m ≤ n) (i : ℕ) :
    2 * Real.pi - window a m i = window a (n - m) (i + m) := by
  unfold window
  rw [Nat.cast_add, Nat.cast_sub hm]
  rw [show (i : ℤ) + m + ((n : ℤ) - m) = (i : ℤ) + n by ring, a.period]
  ring

theorem inverse_window_bound {n : ℕ} (a : Angles n) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ z : ℤ, δ ≤ a.angle (z + 1) - a.angle z)
    {m : ℕ} (hm : m < n) (i : ℕ) :
    1 / principalDistance (window a m i) ≤
      (1 / δ) * (1 / (m : ℝ) + 1 / ((n - m : ℕ) : ℝ)) := by
  by_cases hm0 : m = 0
  · subst m
    simp only [window, Nat.cast_zero, add_zero, sub_self, principalDistance_zero, div_zero,
      zero_add, Nat.sub_zero]
    positivity
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hp := window_pos a hmpos i
  have hu := window_lt_two_pi a hm i
  have h₁ := angle_window_lower a hsep (i : ℤ) m
  change δ * m ≤ window a m i at h₁
  have h₂ := angle_window_lower a hsep ((i + m : ℕ) : ℤ) (n - m)
  change δ * (n - m : ℕ) ≤ window a (n - m) (i + m) at h₂
  rw [← window_complement a hm.le i] at h₂
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hnreal : (0 : ℝ) < (n - m : ℕ) := by exact_mod_cast (show 0 < n - m by omega)
  rw [principalDistance_eq_min hp.le hu.le]
  have hleft : 1 / window a m i ≤ 1 / (δ * m) :=
    one_div_le_one_div_of_le (mul_pos hδ hmreal) h₁
  have hright : 1 / (2 * Real.pi - window a m i) ≤ 1 / (δ * (n - m : ℕ)) :=
    one_div_le_one_div_of_le (mul_pos hδ hnreal) h₂
  have hsum : 1 / min (window a m i) (2 * Real.pi - window a m i) ≤
      1 / (δ * m) + 1 / (δ * (n - m : ℕ)) := by
    rcases le_total (window a m i) (2 * Real.pi - window a m i) with h | h
    · rw [min_eq_left h]
      exact hleft.trans (le_add_of_nonneg_right (by positivity))
    · rw [min_eq_right h]
      exact hright.trans (le_add_of_nonneg_left (by positivity))
  convert hsum using 1
  ring

theorem reciprocal_range_le_log (n : ℕ) :
    (∑ k ∈ Finset.range n, 1 / (k : ℝ)) ≤ 1 + Real.log n := by
  have hle : (∑ k ∈ Finset.range n, 1 / (k : ℝ)) ≤
      ∑ k ∈ Finset.range (n + 1), 1 / (k : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ n))
      (fun _ _ _ => by positivity)
  have he : (∑ k ∈ Finset.range (n + 1), 1 / (k : ℝ)) = (harmonic n : ℝ) := by
    rw [Finset.sum_range_succ']
    simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [he] at hle
  exact hle.trans (harmonic_le_one_add_log n)

theorem reciprocal_reverse_range_eq_harmonic (n : ℕ) :
    (∑ k ∈ Finset.range n, 1 / ((n - k : ℕ) : ℝ)) = (harmonic n : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  refine Finset.sum_bij (fun k _ => n - k) ?_ ?_ ?_ ?_
  · intro k hk
    have := Finset.mem_range.mp hk
    simp only [Finset.mem_Icc]
    omega
  · intro k hk l hl hkl
    have := Finset.mem_range.mp hk
    have := Finset.mem_range.mp hl
    omega
  · intro l hl
    have hh := Finset.mem_Icc.mp hl
    exact ⟨n - l, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k _
    simp

theorem inverseDistanceSum_eq_lags {n : ℕ} (a : Angles n) (i : Fin n) :
    polarInverseDistanceSum (shortAngle a i) i =
      ∑ m ∈ Finset.range n, 1 / principalDistance (window a m i.val) := by
  let f : ℕ → ℝ := fun j => 1 / principalDistance (a.angle j - a.angle i)
  have hfull : polarInverseDistanceSum (shortAngle a i) i = ∑ j : Fin n, f j.val := by
    have he := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun j => 1 / |shortAngle a i j|) (Finset.mem_univ i)
    have hz : 1 / |shortAngle a i i| = 0 := by simp [shortAngle]
    rw [hz, add_zero] at he
    unfold polarInverseDistanceSum
    rw [he]
    apply Finset.sum_congr rfl
    intro j _
    change 1 / principalDistance (a.angle i - a.angle j) = f j.val
    rw [show a.angle i - a.angle j = -(a.angle j - a.angle i) by ring, principalDistance_neg]
  rw [hfull, ← Finset.sum_range f]
  have hper : ∀ j, f (j + n) = f j + 0 := by
    intro j
    simp only [f, Nat.cast_add, a.period, add_zero]
    rw [show a.angle j + 2 * Real.pi - a.angle i =
      (a.angle j - a.angle i) + 2 * Real.pi by ring, principalDistance_add_two_pi]
  have hshift := sum_shift_of_drift f 0 hper i.val
  simp only [mul_zero, add_zero] at hshift
  rw [← hshift]
  apply Finset.sum_congr rfl
  intro m _
  simp only [f, window, Nat.cast_add]
  rw [add_comm (m : ℤ) (i : ℤ)]

/-- A separated cyclic lift supplies its own logarithmic reciprocal-distance bound. -/
theorem inverseDistanceSum_le {n : ℕ} (a : Angles n) (i : Fin n) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ z : ℤ, δ ≤ a.angle (z + 1) - a.angle z) :
    polarInverseDistanceSum (shortAngle a i) i ≤ (2 / δ) * (1 + Real.log n) := by
  rw [inverseDistanceSum_eq_lags]
  calc
    _ ≤ ∑ m ∈ Finset.range n,
        (1 / δ) * (1 / (m : ℝ) + 1 / ((n - m : ℕ) : ℝ)) :=
      Finset.sum_le_sum fun m hm => inverse_window_bound a hδ hsep (Finset.mem_range.mp hm) i.val
    _ = (1 / δ) * ((∑ m ∈ Finset.range n, 1 / (m : ℝ)) + harmonic n) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, reciprocal_reverse_range_eq_harmonic]
    _ ≤ (1 / δ) * ((1 + Real.log n) + (1 + Real.log n)) :=
      mul_le_mul_of_nonneg_left (add_le_add (reciprocal_range_le_log n) (harmonic_le_one_add_log n))
        (by positivity)
    _ = _ := by ring

theorem inverseDistanceSum_le_scaled {n : ℕ} (a : Angles n) (i : Fin n) {γ : ℝ} (hγ : 0 < γ)
    (hsep : ∀ z : ℤ, γ / n ≤ a.angle (z + 1) - a.angle z) :
    polarInverseDistanceSum (shortAngle a i) i ≤ (2 / γ) * n * (1 + Real.log n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  convert inverseDistanceSum_le a i (div_pos hγ hn) hsep using 1
  field_simp

end
end Erdos1045.EventualExact.AngularHarmonicBound

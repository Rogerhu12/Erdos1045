import EventualExact.ForceWeightBounds
import EventualExact.CyclicForceBudget
import EventualExact.CyclicDistance

/-! The actual circle force is a weighted Laplacian of the actual relative gaps.
Weights are cotangent secants on intervals strictly inside one turn. This avoids
an integral at the poles and includes coincident secant endpoints. -/

namespace Erdos1045.EventualExact

open scoped BigOperators
open CyclicAngles CyclicCosecant CyclicForceBudget

noncomputable section

def shiftedAngleVector {n : ℕ} (a : Angles n) (k : ℕ) : Fin n → ℝ :=
  fun i => a.angle ((i : ℤ) + k)

def liftedAngleDistance {n : ℕ} (a : Angles n) (k : ℕ) (i j : Fin n) : ℝ :=
  |a.angle ((j : ℤ) + k) - a.angle ((i : ℤ) + k)|

def circleForceWeight {n : ℕ} (a : Angles n) (i j : Fin n) : ℝ :=
  if i = j then 0 else
    (2 * Real.pi / (n : ℝ) ^ 2) *
      CotangentSecant.slope (liftedAngleDistance a 0 i j) (liftedAngleDistance a 1 i j)

theorem liftedAngleDistance_comm {n : ℕ} (a : Angles n) (k : ℕ) (i j : Fin n) :
    liftedAngleDistance a k i j = liftedAngleDistance a k j i := abs_sub_comm _ _

theorem liftedAngleDistance_of_lt {n : ℕ} (a : Angles n) (k : ℕ)
    {i j : Fin n} (hij : i < j) :
    liftedAngleDistance a k i j = a.angle ((j : ℤ) + k) - a.angle ((i : ℤ) + k) := by
  unfold liftedAngleDistance
  rw [abs_of_pos (sub_pos.mpr (a.increasing (by exact_mod_cast (show i.val + k < j.val + k by omega))))]

theorem liftedAngleDistance_mem_arc {n : ℕ} (a : Angles n) (k : ℕ)
    {i j : Fin n} (hij : i ≠ j) : liftedAngleDistance a k i j ∈ CirclePotential.arc := by
  have hforward {i j : Fin n} (h : i < j) :
      liftedAngleDistance a k i j ∈ CirclePotential.arc := by
    rw [liftedAngleDistance_of_lt a k h]
    constructor
    · exact sub_pos.mpr (a.increasing (by omega))
    · have hh := a.increasing (show (j : ℤ) + k < ((i : ℤ) + k) + n by omega)
      rw [a.period] at hh
      linarith
  rcases lt_or_gt_of_ne hij with h | h
  · exact hforward h
  · rw [liftedAngleDistance_comm]
    exact hforward h

@[simp] theorem circleForceWeight_self {n : ℕ} (a : Angles n) (i : Fin n) :
    circleForceWeight a i i = 0 := by simp [circleForceWeight]

theorem circleForceWeight_comm {n : ℕ} (a : Angles n) (i j : Fin n) :
    circleForceWeight a i j = circleForceWeight a j i := by
  unfold circleForceWeight
  rw [liftedAngleDistance_comm a 0 i j, liftedAngleDistance_comm a 1 i j]
  simp only [eq_comm]

theorem circleForceWeight_pos {n : ℕ} (a : Angles n) {i j : Fin n} (hij : i ≠ j) :
    0 < circleForceWeight a i j := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  rw [circleForceWeight, if_neg hij]
  exact mul_pos (by positivity) (CotangentSecant.slope_pos
    (liftedAngleDistance_mem_arc a 0 hij) (liftedAngleDistance_mem_arc a 1 hij))

theorem circleForceWeight_nonneg {n : ℕ} (a : Angles n) (i j : Fin n) :
    0 ≤ circleForceWeight a i j := by
  by_cases h : i = j
  · subst j
    simp
  · exact (circleForceWeight_pos a h).le

theorem circleInteraction_eq_first {ι : Type*} (θ : ι → ℝ) (i j : ι) :
    circleInteraction θ i j = CirclePotential.first (θ j - θ i) := by
  rw [CotangentSecant.first_eq_neg_cot]
  unfold circleInteraction
  rw [show (θ i - θ j) / 2 = -((θ j - θ i) / 2) by ring, circleCot_neg]

theorem interaction_next_difference_of_lt {n : ℕ} (a : Angles n)
    {i j : Fin n} (hij : i < j) :
    circleInteraction (shiftedAngleVector a 1) i j - circleInteraction (angleVector a) i j =
      -(n : ℝ) * circleForceWeight a i j * (relativeGaps a i - relativeGaps a j) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt i.isLt)
  rw [circleInteraction_eq_first, circleInteraction_eq_first]
  change CirclePotential.first (a.angle ((j : ℤ) + 1) - a.angle ((i : ℤ) + 1)) -
    CirclePotential.first (a.angle j - a.angle i) = _
  rw [CotangentSecant.first_difference]
  have hdist0 : liftedAngleDistance a 0 i j = a.angle j - a.angle i := by
    simpa only [Nat.cast_zero, add_zero] using liftedAngleDistance_of_lt a 0 hij
  have hdist1 := liftedAngleDistance_of_lt a 1 hij
  simp only [Nat.cast_one] at hdist1
  have hdiff : (a.angle ((j : ℤ) + 1) - a.angle ((i : ℤ) + 1)) -
      (a.angle j - a.angle i) =
      -(2 * Real.pi / n) * (relativeGaps a i - relativeGaps a j) := by
    change (a.angle ((j : ℤ) + 1) - a.angle ((i : ℤ) + 1)) -
      (a.angle j - a.angle i) = -(2 * Real.pi / n) *
        ((a.angle ((i : ℤ) + 1) - a.angle i) / (2 * Real.pi / n) -
         (a.angle ((j : ℤ) + 1) - a.angle j) / (2 * Real.pi / n))
    field_simp [hn0, Real.pi_ne_zero]
    ring
  rw [hdiff, circleForceWeight, if_neg hij.ne, hdist0, hdist1]
  field_simp

theorem interaction_next_difference {n : ℕ} (a : Angles n) (i j : Fin n) :
    circleInteraction (shiftedAngleVector a 1) i j - circleInteraction (angleVector a) i j =
      -(n : ℝ) * circleForceWeight a i j * (relativeGaps a i - relativeGaps a j) := by
  rcases lt_trichotomy i j with h | h | h
  · exact interaction_next_difference_of_lt a h
  · subst j
    simp
  · have he := interaction_next_difference_of_lt a h
    rw [circleInteraction_skew (shiftedAngleVector a 1) i j,
      circleInteraction_skew (angleVector a) i j, circleForceWeight_comm a j i] at he
    nlinarith

def circleForceAt {n : ℕ} (a : Angles n) (i : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, circleCot ((a.angle i - a.angle j) / 2)) / n

theorem circleCot_sub_pi (x : ℝ) : circleCot (x - Real.pi) = circleCot x := by
  have h := circleCot_add_pi (x - Real.pi)
  simpa only [sub_add_cancel] using h.symm

theorem circleForceAt_period {n : ℕ} (a : Angles n) (i : ℕ) :
    circleForceAt a (i + n) = circleForceAt a i := by
  unfold circleForceAt
  apply congrArg (fun x : ℝ => x / n)
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.cast_add, a.period, show (a.angle i + 2 * Real.pi - a.angle j) / 2 =
    (a.angle i - a.angle j) / 2 + Real.pi by ring, circleCot_add_pi]

theorem circleForce_eq_at {n : ℕ} (a : Angles n) (i : Fin n) :
    circleForce (angleVector a) i = circleForceAt a i.val := by
  unfold circleForce circleForceAt
  simp only [Fintype.card_fin, circleInteraction, angleVector]
  rw [← Finset.sum_range (fun j => circleCot ((a.angle i - a.angle j) / 2))]

theorem circleForceAt_next_eq {n : ℕ} (a : Angles n) (i : Fin n) :
    circleForceAt a (i.val + 1) = circleForce (angleVector a) (cyclicAdvance i 1) := by
  rw [circleForce_eq_at]
  change circleForceAt a (i.val + 1) = circleForceAt a ((i.val + 1) % n)
  by_cases h : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt h]
  · have he : i.val + 1 = n := by omega
    rw [he, Nat.mod_self]
    simpa only [zero_add] using circleForceAt_period a 0

theorem circleForceAt_next_difference {n : ℕ} (a : Angles n) (i : Fin n) :
    circleForceAt a (i.val + 1) - circleForceAt a i.val =
      -(∑ j : Fin n, circleForceWeight a i j * (relativeGaps a i - relativeGaps a j)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt i.isLt)
  have hper (j : ℕ) :
      circleCot ((a.angle ((i : ℤ) + 1) - a.angle (j + n : ℕ)) / 2) =
        circleCot ((a.angle ((i : ℤ) + 1) - a.angle j) / 2) + 0 := by
    rw [Nat.cast_add, a.period, show
      (a.angle ((i : ℤ) + 1) - (a.angle j + 2 * Real.pi)) / 2 =
        (a.angle ((i : ℤ) + 1) - a.angle j) / 2 - Real.pi by ring,
      circleCot_sub_pi, add_zero]
  have hshift := sum_shift_of_drift (n := n)
    (fun j => circleCot ((a.angle ((i : ℤ) + 1) - a.angle j) / 2)) 0 hper 1
  simp only [mul_zero, add_zero] at hshift
  have he : circleForceAt a (i.val + 1) - circleForceAt a i.val =
      (∑ j : Fin n, (circleInteraction (shiftedAngleVector a 1) i j -
        circleInteraction (angleVector a) i j)) / n := by
    unfold circleForceAt
    simp only [circleInteraction, shiftedAngleVector, angleVector, Nat.cast_one]
    rw [← sub_div, ← Finset.sum_range (fun j =>
      circleCot ((a.angle ((i : ℤ) + 1) - a.angle ((j : ℤ) + 1)) / 2) -
        circleCot ((a.angle i - a.angle j) / 2))]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [Finset.sum_sub_distrib]
    rw [← hshift]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [he]
  simp_rw [interaction_next_difference]
  rw [show (∑ j : Fin n, -(n : ℝ) * circleForceWeight a i j *
      (relativeGaps a i - relativeGaps a j)) =
        -(n : ℝ) * ∑ j : Fin n,
          circleForceWeight a i j * (relativeGaps a i - relativeGaps a j) by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring]
  field_simp

/-- The actual finite Laplacian identity, equation (2.23). -/
theorem circleForce_next_difference {n : ℕ} (a : Angles n) (i : Fin n) :
    circleForce (angleVector a) (cyclicAdvance i 1) - circleForce (angleVector a) i =
      -(∑ j : Fin n, circleForceWeight a i j * (relativeGaps a i - relativeGaps a j)) := by
  rw [← circleForceAt_next_eq, circleForce_eq_at]
  exact circleForceAt_next_difference a i

/-- Summing the actual consecutive gaps bounds every lifted interval inside a turn. -/
theorem angle_interval_le_of_gap_bound {n : ℕ} (a : Angles n) (hn : 0 < n)
    {b : ℝ} (hb : ∀ i, relativeGaps a i ≤ b) {p q : ℕ}
    (hpq : p ≤ q) (hqn : q ≤ n) :
    a.angle q - a.angle p ≤ (q - p : ℕ) * (2 * Real.pi / n * b) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ = ∑ k ∈ Finset.Ico p q, (a.angle (k + 1 : ℕ) - a.angle k) :=
      (Finset.sum_Ico_sub (fun k : ℕ => a.angle k) hpq).symm
    _ ≤ ∑ _k ∈ Finset.Ico p q, (2 * Real.pi / n * b) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k < n := (Finset.mem_Ico.mp hk).2.trans_le hqn
      have hg := hb ⟨k, hkn⟩
      change (a.angle ((k : ℤ) + 1) - a.angle k) / (2 * Real.pi / n) ≤ b at hg
      have hh := (div_le_iff₀ (by positivity : 0 < 2 * Real.pi / (n : ℝ))).mp hg
      simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hh
    _ = _ := by simp

theorem complement_angle_interval_le_of_gap_bound {n : ℕ} (a : Angles n) (hn : 0 < n)
    {b : ℝ} (hb : ∀ i, relativeGaps a i ≤ b) {p q : ℕ}
    (hpq : p ≤ q) (hqn : q ≤ n) :
    2 * Real.pi - (a.angle q - a.angle p) ≤
      (n - (q - p) : ℕ) * (2 * Real.pi / n * b) := by
  have hp := angle_interval_le_of_gap_bound a hn hb (Nat.zero_le p) (hpq.trans hqn)
  have hq := angle_interval_le_of_gap_bound a hn hb hqn (le_refl n)
  simp only [Nat.sub_zero] at hp
  have hperiod : a.angle (n : ℤ) = a.angle 0 + 2 * Real.pi := by
    simpa only [zero_add] using a.period 0
  calc
    _ = (a.angle p - a.angle 0) + (a.angle n - a.angle q) := by rw [hperiod]; ring
    _ ≤ (p : ℝ) * (2 * Real.pi / n * b) +
        (n - q : ℕ) * (2 * Real.pi / n * b) := add_le_add hp hq
    _ = _ := by
      rw [← add_mul, ← Nat.cast_add]
      congr 2
      omega

theorem circleForceWeight_lower_of_lt {n : ℕ} (a : Angles n)
    {i j : Fin n} (hij : i < j) {b : ℝ} (hb : ∀ k, relativeGaps a k ≤ b) :
    1 / (Real.pi * b ^ 2 * (cyclicDistance i j : ℝ) ^ 2) ≤ circleForceWeight a i j := by
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hb0 : 0 < b := (relativeGaps_pos a hn i).trans_le (hb i)
  have hd0 : (0 : ℝ) < cyclicDistance i j := by exact_mod_cast cyclicDistance_pos hij.ne
  have hdist0 := liftedAngleDistance_of_lt a 0 hij
  simp only [Nat.cast_zero, add_zero] at hdist0
  have hdist1 := liftedAngleDistance_of_lt a 1 hij
  simp only [Nat.cast_one] at hdist1
  have hx := angle_interval_le_of_gap_bound a hn hb
    (show i.val ≤ j.val by exact hij.le) j.isLt.le
  have hy := angle_interval_le_of_gap_bound a hn hb
    (show i.val + 1 ≤ j.val + 1 by omega) (show j.val + 1 ≤ n by omega)
  have hx' := complement_angle_interval_le_of_gap_bound a hn hb
    (show i.val ≤ j.val by exact hij.le) j.isLt.le
  have hy' := complement_angle_interval_le_of_gap_bound a hn hb
    (show i.val + 1 ≤ j.val + 1 by omega) (show j.val + 1 ≤ n by omega)
  have hlength : (j.val + 1) - (i.val + 1) = j.val - i.val := by omega
  rw [hlength] at hy hy'
  simp only [Nat.cast_add, Nat.cast_one] at hy hy'
  rw [← hdist0] at hx hx'
  rw [← hdist1] at hy hy'
  have hs : 2 / ((cyclicDistance i j : ℝ) * (2 * Real.pi / n * b)) ^ 2 ≤
      CotangentSecant.slope (liftedAngleDistance a 0 i j) (liftedAngleDistance a 1 i j) := by
    rw [cyclicDistance_of_le hij.le]
    by_cases hlen : j.val - i.val ≤ n - (j.val - i.val)
    · rw [min_eq_left hlen]
      exact CotangentSecant.slope_lower_of_upper
        (liftedAngleDistance_mem_arc a 0 hij.ne) (liftedAngleDistance_mem_arc a 1 hij.ne) hx hy
    · rw [min_eq_right (by omega : n - (j.val - i.val) ≤ j.val - i.val)]
      exact CotangentSecant.slope_lower_of_complement_upper
        (liftedAngleDistance_mem_arc a 0 hij.ne) (liftedAngleDistance_mem_arc a 1 hij.ne) hx' hy'
  rw [circleForceWeight, if_neg hij.ne]
  calc
    _ = (2 * Real.pi / (n : ℝ) ^ 2) *
        (2 / ((cyclicDistance i j : ℝ) * (2 * Real.pi / n * b)) ^ 2) := by
      field_simp [Real.pi_ne_zero, hn0, hb0.ne', hd0.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

/-- The actual weights satisfy equation (2.24), at the shortest cyclic distance. -/
theorem circleForceWeight_lower {n : ℕ} (a : Angles n)
    {i j : Fin n} (hij : i ≠ j) {b : ℝ} (hb : ∀ k, relativeGaps a k ≤ b) :
    1 / (Real.pi * b ^ 2 * (cyclicDistance i j : ℝ) ^ 2) ≤ circleForceWeight a i j := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact circleForceWeight_lower_of_lt a h hb
  · rw [cyclicDistance_comm i j, circleForceWeight_comm a i j]
    exact circleForceWeight_lower_of_lt a h hb

end
end Erdos1045.EventualExact

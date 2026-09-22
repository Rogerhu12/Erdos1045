import EventualExact.SchurLiftBounds
import EventualExact.LensClosureNonlinear

/-! The actual finite box parameters for the nonlinear lens closure equation. -/

noncomputable section

open scoped BigOperators

namespace Erdos1045.EventualExact.BoxLensLift

open Complex FourierMultiplier FiniteFourierLift SchurLift SchurLiftBounds SchurSpectrum

def angle (n : ℕ) : ℝ := Real.pi / n

def baseWidth (n : ℕ) : ℝ := 2 * Real.cos (angle n)

def radius (n : ℕ) : ℝ := 2 * (1 - Real.cos (angle n))

def coordinate {n : ℕ} (q : Fin n → ℝ) (j : Fin n) : ℝ := q j / FiniteBox.amplitude n

def tangential {n : ℕ} (q : Fin n → ℝ) (j : Fin n) : ℝ :=
  4 * Real.sin (angle n) / n * (firstCoefficient q * frame n j).im

def halfIndex {m : ℕ} (j : Fin m) : Fin (2 * m) := ⟨j.val, by omega⟩

theorem radius_nonneg (n : ℕ) : 0 ≤ radius n := by
  unfold radius
  nlinarith [Real.cos_le_one (angle n)]

theorem radius_le_angle_sq (n : ℕ) : radius n ≤ angle n ^ 2 := by
  unfold radius
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := angle n)]

theorem radius_identity {n : ℕ} (hn : 2 ≤ n) :
    radius n = 2 * Real.sin (angle n) / n * FiniteBox.amplitude n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc : Real.cos (Real.pi / (2 * n)) ≠ 0 := by
    apply (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩).ne'
    · have hp : 0 < Real.pi / (2 * n) := by positivity
      linarith [Real.pi_pos]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * n)).2
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  have ha : angle n = 2 * (Real.pi / (2 * n)) := by unfold angle; ring
  rw [radius, ha, Real.cos_two_mul, Real.sin_two_mul, FiniteBox.amplitude,
    Real.tan_eq_sin_div_cos]
  have htrig := Real.sin_sq_add_cos_sq (Real.pi / (2 * n))
  field_simp
  nlinarith

theorem coordinate_bound {n : ℕ} (hn : 2 ≤ n) (q : Fin n → ℝ)
    (hq : ∀ j, |q j| ≤ FiniteBox.amplitude n) (j : Fin n) : |coordinate q j| ≤ 1 := by
  have hA := FiniteBox.amplitude_pos hn
  rw [coordinate, abs_div, abs_of_pos hA]
  exact (div_le_one hA).2 (hq j)

theorem tangential_sq_le {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ)
    (hq : ∀ j, |q j| ≤ FiniteBox.amplitude n) (j : Fin n) :
    tangential q j ^ 2 ≤ 2 * radius n ^ 2 := by
  have hA := FiniteBox.amplitude_pos (by omega : 2 ≤ n)
  have hmass := meanSquare_le_of_bound (by omega) q hA.le hq
  have hf := firstCoefficient_bound hn q
  have hi : (firstCoefficient q * frame n j).im ^ 2 ≤ normSq (firstCoefficient q) := by
    have he := normSq_mul (firstCoefficient q) (frame n j)
    rw [frame_normSq, mul_one, normSq_apply] at he
    nlinarith [sq_nonneg (firstCoefficient q * frame n j).re]
  have h : 2 * (firstCoefficient q * frame n j).im ^ 2 ≤ FiniteBox.amplitude n ^ 2 := by
    linarith
  rw [radius_identity (by omega)]
  unfold tangential
  calc
    _ = 2 * (2 * Real.sin (angle n) / n) ^ 2 *
        (2 * (firstCoefficient q * frame n j).im ^ 2) := by ring
    _ ≤ 2 * (2 * Real.sin (angle n) / n) ^ 2 * FiniteBox.amplitude n ^ 2 := by
      exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- The sharp first estimate in manuscript (4.12), for actual box coordinates. -/
theorem tangential_abs_le {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ)
    (hq : ∀ j, |q j| ≤ FiniteBox.amplitude n) (j : Fin n) :
    |tangential q j| ≤ Real.sqrt 2 * radius n := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (radius_nonneg n))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact tangential_sq_le hn q hq j

theorem increment_coordinates {n : ℕ} (hn : 2 ≤ n) (q : Fin n → ℝ) (j : Fin n) :
    SchurLift.increment q j = frame n j *
      (((coordinate q j * radius n : ℝ) : ℂ) + (tangential q j : ℂ) * I) := by
  have hA := (FiniteBox.amplitude_pos hn).ne'
  rw [SchurLift.increment, coordinate, tangential, radius_identity hn]
  change frame n j * (((2 * Real.sin (angle n) / n : ℝ) : ℂ) * (q j : ℂ) +
    I * ((4 * Real.sin (angle n) / n : ℝ) : ℂ) *
      ((firstCoefficient q * frame n j).im : ℂ)) = _
  generalize Real.sin (angle n) = sn
  push_cast
  have hAc : (FiniteBox.amplitude n : ℂ) ≠ 0 := by exact_mod_cast hA
  field_simp

theorem frame_halfIndex {m : ℕ} (j : Fin m) :
    frame (2 * m) (halfIndex j) = LensClosure.unit (LensClosure.midpoint m j) := by
  rw [frame, midpointCharacter_eq_exp]
  unfold LensClosure.unit LensClosure.midpoint halfIndex
  congr 2
  push_cast
  ring

theorem height_defect {t : ℝ} (ht : t ^ 2 ≤ 4) : |Lens.height t - 2| ≤ t ^ 2 / 2 := by
  have hs := Lens.height_sq ht
  have hp := Lens.height_nonneg t
  have hle : Lens.height t ≤ 2 := by nlinarith [sq_nonneg t]
  rw [abs_of_nonpos (by linarith)]
  nlinarith [mul_nonneg hp (show 0 ≤ 2 - Lens.height t by linarith)]

theorem initial_increment_error {m : ℕ} (hm : 2 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : ∀ j, |q j| ≤ FiniteBox.amplitude (2 * m)) (j : Fin m)
    (ht : tangential q (halfIndex j) ^ 2 ≤ 4) :
    ‖LensClosure.increment (LensClosure.midpoint m j) (baseWidth (2 * m))
        (coordinate q (halfIndex j)) (tangential q (halfIndex j)) -
      SchurLift.increment q (halfIndex j)‖ ≤ radius (2 * m) ^ 2 := by
  have he : LensClosure.increment (LensClosure.midpoint m j) (baseWidth (2 * m))
        (coordinate q (halfIndex j)) (tangential q (halfIndex j)) -
      SchurLift.increment q (halfIndex j) =
      LensClosure.unit (LensClosure.midpoint m j) *
        ((coordinate q (halfIndex j) * (Lens.height (tangential q (halfIndex j)) - 2) : ℝ) : ℂ) := by
    rw [increment_coordinates (by omega), frame_halfIndex]
    unfold LensClosure.increment Lens.width baseWidth radius
    push_cast
    ring
  rw [he, norm_mul, LensClosure.norm_unit, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ 1 * (tangential q (halfIndex j) ^ 2 / 2) :=
      mul_le_mul (coordinate_bound (by omega) q hq _) (height_defect ht)
        (abs_nonneg _) (by norm_num)
    _ ≤ _ := by have := tangential_sq_le (by omega) q hq (halfIndex j); linarith

theorem half_increment_sum {m : ℕ} (hm : 2 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : FiniteBox.Antiperiodic (by omega) q) :
    (∑ j : Fin m, SchurLift.increment q (halfIndex j)) = 0 := by
  let u := periodize (by omega : 0 < 2 * m) (canonicalLift q)
  have hd (j : Fin m) : SchurLift.increment q (halfIndex j) = u (j.val + 1) - u j := by
    have he := congrFun (canonicalLift_difference (by omega) q) (halfIndex j)
    rw [← he]
    simp only [difference, successor, halfIndex, u, periodize,
      Nat.mod_eq_of_lt (show j.val < 2 * m by omega)]
  have hclose : u m = u 0 := by
    have he := canonicalLift_halfTurn hm q hq ⟨0, by omega⟩
    simpa only [u, periodize, halfTurn, Nat.zero_add, Nat.zero_mod,
      Nat.mod_eq_of_lt (show m < 2 * m by omega)] using he
  simp_rw [hd]
  rw [Fin.sum_univ_eq_sum_range (fun j => u (j + 1) - u j) m,
    Finset.sum_range_sub, hclose, sub_self]

def boxClosure {m : ℕ} (q : Fin (2 * m) → ℝ) : ℂ → ℂ :=
  LensClosure.closure (LensClosure.midpoint m) (fun _ => baseWidth (2 * m))
    (fun j => coordinate q (halfIndex j)) (fun j => tangential q (halfIndex j))

theorem closure_zero_le {m : ℕ} (hm : 2 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega))
    (ht : ∀ j : Fin m, tangential q (halfIndex j) ^ 2 ≤ 4) :
    ‖boxClosure q 0‖ ≤ (m : ℝ) * radius (2 * m) ^ 2 := by
  have he : boxClosure q 0 = ∑ j : Fin m,
      (LensClosure.increment (LensClosure.midpoint m j) (baseWidth (2 * m))
        (coordinate q (halfIndex j)) (tangential q (halfIndex j)) -
      SchurLift.increment q (halfIndex j)) := by
    rw [Finset.sum_sub_distrib, half_increment_sum hm q hq.1, sub_zero]
    simp [boxClosure, LensClosure.closure, LensClosure.heightParameter]
  rw [he]
  calc
    _ ≤ ∑ j : Fin m, ‖LensClosure.increment (LensClosure.midpoint m j) (baseWidth (2 * m))
        (coordinate q (halfIndex j)) (tangential q (halfIndex j)) -
      SchurLift.increment q (halfIndex j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, radius (2 * m) ^ 2 := by
      exact Finset.sum_le_sum fun j _ => initial_increment_error hm q hq.2 j (ht j)
    _ = _ := by simp

theorem radius_le_numeric {n : ℕ} (_hn : 0 < n) : radius n ≤ 16 / (n : ℝ) ^ 2 := by
  calc
    _ ≤ angle n ^ 2 := radius_le_angle_sq n
    _ = Real.pi ^ 2 / (n : ℝ) ^ 2 := by rw [angle, div_pow]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith [Real.pi_lt_four, Real.pi_pos]

theorem tangential_le_numeric {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ)
    (hq : ∀ j, |q j| ≤ FiniteBox.amplitude n) (j : Fin n) :
    |tangential q j| ≤ 32 / (n : ℝ) ^ 2 := by
  calc
    _ ≤ Real.sqrt 2 * radius n := tangential_abs_le hn q hq j
    _ ≤ 2 * radius n := by
      apply mul_le_mul_of_nonneg_right _ (radius_nonneg n)
      exact (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
    _ ≤ 2 * (16 / (n : ℝ) ^ 2) := by
      gcongr
      exact radius_le_numeric (by omega)
    _ = _ := by ring

theorem tangential_small {n : ℕ} (hn : 32 ≤ n) (q : Fin n → ℝ)
    (hq : ∀ j, |q j| ≤ FiniteBox.amplitude n) (j : Fin n) :
    |tangential q j| ≤ 1 / 32 := by
  refine (tangential_le_numeric (by omega) q hq j).trans ?_
  have hnR : (32 : ℝ) ≤ n := by exact_mod_cast hn
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).2
  nlinarith

theorem closure_zero_numeric {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    ‖boxClosure q 0‖ ≤ 128 / ((2 * m : ℕ) : ℝ) ^ 3 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  calc
    _ ≤ (m : ℝ) * radius (2 * m) ^ 2 := closure_zero_le (by omega) q hq (by
      intro j
      have h := tangential_small (by omega) q hq.2 (halfIndex j)
      nlinarith [(abs_le.mp h).1, (abs_le.mp h).2])
    _ ≤ (m : ℝ) * (16 / ((2 * m : ℕ) : ℝ) ^ 2) ^ 2 := by
      gcongr
      · exact radius_nonneg _
      · exact radius_le_numeric (by omega)
    _ = _ := by push_cast; field_simp; ring

def rootRadius (n : ℕ) : ℝ := 1024 / (n : ℝ) ^ 4

theorem rootRadius_nonneg (n : ℕ) : 0 ≤ rootRadius n := by unfold rootRadius; positivity

theorem rootRadius_le {n : ℕ} (hn : 32 ≤ n) : rootRadius n ≤ 1 / 1024 := by
  have hnR : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (1024 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  unfold rootRadius
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 4)).2
  nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 1024)]

theorem box_root_small {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) (j : Fin m) :
    |LensClosure.midpoint m j - LensClosure.midpoint m j| +
      |tangential q (halfIndex j)| + rootRadius (2 * m) ≤ 1 / 4 := by
  have ht := tangential_small (by omega) q hq.2 (halfIndex j)
  have hR := rootRadius_le (by omega : 32 ≤ 2 * m)
  simp only [sub_self, abs_zero, zero_add]
  linarith

theorem box_root_source {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    ‖boxClosure q 0‖ ≤ (m : ℝ) * rootRadius (2 * m) / 4 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  convert closure_zero_numeric hm q hq using 1
  unfold rootRadius
  push_cast
  field_simp
  ring

def repeatHalf {m : ℕ} (hm : 0 < m) (f : Fin m → ℂ) (j : Fin (2 * m)) : ℂ :=
  f ⟨j.val % m, Nat.mod_lt _ hm⟩

theorem repeatHalf_sum {m : ℕ} (hm : 0 < m) (f : Fin m → ℂ) :
    (∑ j, repeatHalf hm f j) = 2 * ∑ j, f j := by
  let u : ℕ → ℂ := fun j => f ⟨j % m, Nat.mod_lt _ hm⟩
  have hu (j : ℕ) : u (m + j) = u j := by simp [u]
  change (∑ j : Fin (2 * m), u j) = _
  rw [Fin.sum_univ_eq_sum_range u (2 * m), show 2 * m = m + m by omega,
    Finset.sum_range_add]
  simp_rw [hu]
  have he : (∑ j ∈ Finset.range m, u j) = ∑ j : Fin m, f j := by
    rw [← Fin.sum_univ_eq_sum_range u m]
    apply Finset.sum_congr rfl
    intro j _
    simp only [u, Nat.mod_eq_of_lt j.isLt]
  rw [he]
  ring

theorem repeatHalf_halfTurn {m : ℕ} (hm : 0 < m) (f : Fin m → ℂ) (j : Fin (2 * m)) :
    repeatHalf hm f (halfTurn hm j) = repeatHalf hm f j := by
  unfold repeatHalf halfTurn
  congr 1
  apply Fin.ext
  simp [Nat.mod_mod_of_dvd _ (by exact ⟨2, by omega⟩ : m ∣ 2 * m), Nat.add_mod]

def correctedHalfIncrement {m : ℕ} (q : Fin (2 * m) → ℝ) (ξ : ℂ) (j : Fin m) : ℂ :=
  LensClosure.increment (LensClosure.midpoint m j) (baseWidth (2 * m))
    (coordinate q (halfIndex j))
    (LensClosure.heightParameter (fun k => tangential q (halfIndex k)) ξ j)

def correctedIncrement {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ) (ξ : ℂ) : Fin (2 * m) → ℂ :=
  repeatHalf hm (correctedHalfIncrement q ξ)

def correctedCenter {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ) (ξ : ℂ) : Fin (2 * m) → ℂ :=
  integral (correctedIncrement hm q ξ)

theorem correctedCenter_mean_zero {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ) (ξ : ℂ) :
    (∑ j, correctedCenter hm q ξ j) = 0 := integral_mean_zero (by omega) _

theorem correctedCenter_difference {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ) (ξ : ℂ)
    (hzero : boxClosure q ξ = 0) :
    difference (by omega) (correctedCenter hm q ξ) = correctedIncrement hm q ξ := by
  apply difference_integral
  rw [correctedIncrement, repeatHalf_sum]
  change (2 : ℂ) * boxClosure q ξ = 0
  rw [hzero, mul_zero]

theorem exists_unique_box_root {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    ∃! ξ : ℂ, ‖ξ‖ ≤ rootRadius (2 * m) ∧ boxClosure q ξ = 0 := by
  exact LensClosure.exists_unique_closure_root (by omega) _ _ _ _ (rootRadius_nonneg _)
    (fun j => coordinate_bound (by omega) q hq.2 (halfIndex j))
    (box_root_small hm q hq) (box_root_source hm q hq)

def boxRoot {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) : ℂ :=
  Classical.choose (exists_unique_box_root hm q hq).exists

theorem boxRoot_spec {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    ‖boxRoot hm q hq‖ ≤ rootRadius (2 * m) ∧ boxClosure q (boxRoot hm q hq) = 0 :=
  Classical.choose_spec (exists_unique_box_root hm q hq).exists

theorem correctedCenter_halfTurn {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ) (ξ : ℂ)
    (hzero : boxClosure q ξ = 0) (j : Fin (2 * m)) :
    correctedCenter hm q ξ (halfTurn hm j) = correctedCenter hm q ξ j := by
  have he : (fun j => correctedCenter hm q ξ (halfTurn hm j)) = correctedCenter hm q ξ := by
    apply integral_unique (by omega)
    · have hs := Equiv.sum_comp
        (Equiv.ofBijective (halfTurn hm) (halfTurn_involutive hm).bijective)
        (correctedCenter hm q ξ)
      exact hs.trans (correctedCenter_mean_zero hm q ξ)
    · funext k
      change correctedCenter hm q ξ (halfTurn hm (successor _ k)) -
        correctedCenter hm q ξ (halfTurn hm k) = correctedIncrement hm q ξ k
      rw [halfTurn_successor]
      change difference (by omega) (correctedCenter hm q ξ) (halfTurn hm k) = _
      rw [correctedCenter_difference hm q ξ hzero]
      exact repeatHalf_halfTurn hm _ k
  exact congrFun he j

theorem repeatHalf_restrict {m : ℕ} (hm : 0 < m) (f : Fin (2 * m) → ℂ)
    (hf : ∀ j, f (halfTurn hm j) = f j) :
    repeatHalf hm (fun j => f (halfIndex j)) = f := by
  funext j
  by_cases hj : j.val < m
  · simp only [repeatHalf, halfIndex, Nat.mod_eq_of_lt hj]
  · have hmj : m ≤ j.val := by omega
    have hjm : j.val - m < m := by omega
    have hmod : j.val % m = j.val - m := by
      rw [Nat.mod_eq_sub_mod hmj, Nat.mod_eq_of_lt hjm]
    have he : halfTurn hm (halfIndex ⟨j.val - m, hjm⟩) = j := by
      apply Fin.ext
      simp only [halfTurn, halfIndex]
      rw [Nat.sub_add_cancel hmj, Nat.mod_eq_of_lt j.isLt]
    simp only [repeatHalf, hmod]
    exact (hf (halfIndex ⟨j.val - m, hjm⟩)).symm.trans (congrArg f he)

theorem correctedHalfIncrement_error {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) (ξ : ℂ) (hξ : ‖ξ‖ ≤ rootRadius (2 * m)) (j : Fin m) :
    ‖correctedHalfIncrement q ξ j - SchurLift.increment q (halfIndex j)‖ ≤
      2048 / ((2 * m : ℕ) : ℝ) ^ 4 := by
  let n := 2 * m
  let d := LensClosure.harmonicFunctional (LensClosure.midpoint m j) ξ
  let t := tangential q (halfIndex j) + d
  have hnR : (32 : ℝ) ≤ n := by dsimp [n]; exact_mod_cast (show 32 ≤ 2 * m by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hd : |d| ≤ 1024 / (n : ℝ) ^ 4 :=
    (LensClosure.harmonicFunctional_le_norm _ _).trans hξ
  have hdn : 1024 / (n : ℝ) ^ 4 ≤ 1 / (n : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 4)
      (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).2
    have hs : 1024 ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (show 0 ≤ (n : ℝ) ^ 2 - 1024 by linarith)]
  have ht : |t| ≤ 33 / (n : ℝ) ^ 2 := by
    have hb := tangential_le_numeric (by omega) q hq.2 (halfIndex j)
    change |tangential q (halfIndex j) + d| ≤ _
    calc
      _ ≤ |tangential q (halfIndex j)| + |d| := abs_add_le _ _
      _ ≤ 32 / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2 := add_le_add hb (hd.trans hdn)
      _ = _ := by ring
  have htsmall : |t| ≤ 1 := by
    refine ht.trans ?_
    apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).2
    nlinarith
  have ht4 : t ^ 2 ≤ 4 := by nlinarith [(abs_le.mp htsmall).1, (abs_le.mp htsmall).2]
  have ht2 : t ^ 2 ≤ (33 / (n : ℝ) ^ 2) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) (by positivity)).2 ht
  have he : correctedHalfIncrement q ξ j - SchurLift.increment q (halfIndex j) =
      LensClosure.unit (LensClosure.midpoint m j) *
        (((coordinate q (halfIndex j) * (Lens.height t - 2) : ℝ) : ℂ) + (d : ℂ) * I) := by
    rw [correctedHalfIncrement, increment_coordinates (by omega), frame_halfIndex]
    unfold LensClosure.increment Lens.width baseWidth radius LensClosure.heightParameter
    change _ = LensClosure.unit (LensClosure.midpoint m j) *
      (((coordinate q (halfIndex j) * (Lens.height (tangential q (halfIndex j) + d) - 2) : ℝ) : ℂ) +
        (d : ℂ) * I)
    push_cast
    ring
  rw [he, norm_mul, LensClosure.norm_unit, one_mul]
  calc
    _ ≤ ‖((coordinate q (halfIndex j) * (Lens.height t - 2) : ℝ) : ℂ)‖ + ‖(d : ℂ) * I‖ :=
      norm_add_le _ _
    _ = |coordinate q (halfIndex j)| * |Lens.height t - 2| + |d| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ t ^ 2 / 2 + |d| := by
      have hh := mul_le_mul (coordinate_bound (by omega) q hq.2 (halfIndex j))
        (height_defect ht4) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      linarith
    _ ≤ (33 / (n : ℝ) ^ 2) ^ 2 / 2 + 1024 / (n : ℝ) ^ 4 := by gcongr
    _ ≤ 2048 / (n : ℝ) ^ 4 := by
      field_simp
      norm_num

theorem correctedIncrement_error {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) (ξ : ℂ) (hξ : ‖ξ‖ ≤ rootRadius (2 * m)) (j : Fin (2 * m)) :
    ‖correctedIncrement (by omega) q ξ j - SchurLift.increment q j‖ ≤
      2048 / ((2 * m : ℕ) : ℝ) ^ 4 := by
  have he := repeatHalf_restrict (by omega) (SchurLift.increment q)
    (increment_halfTurn (by omega) q hq.1)
  rw [← congrFun he j]
  exact correctedHalfIncrement_error hm q hq ξ hξ ⟨j.val % m, Nat.mod_lt _ (by omega)⟩

def liftedCenter {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) : Fin (2 * m) → ℂ :=
  correctedCenter (by omega) q (boxRoot hm q hq)

theorem liftedCenter_mean_zero {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) : (∑ j, liftedCenter hm q hq j) = 0 :=
  correctedCenter_mean_zero _ _ _

theorem liftedCenter_halfTurn {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) (j : Fin (2 * m)) :
    liftedCenter hm q hq (halfTurn (by omega) j) = liftedCenter hm q hq j :=
  correctedCenter_halfTurn _ _ _ (boxRoot_spec hm q hq).2 j

theorem liftedCenter_difference {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    difference (by omega) (liftedCenter hm q hq) =
      correctedIncrement (by omega) q (boxRoot hm q hq) :=
  correctedCenter_difference _ _ _ (boxRoot_spec hm q hq).2

theorem liftedCenter_half_difference {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) (j : Fin m) :
    difference (by omega) (liftedCenter hm q hq) (halfIndex j) =
      correctedHalfIncrement q (boxRoot hm q hq) j := by
  rw [liftedCenter_difference]
  simp only [correctedIncrement, repeatHalf, halfIndex, Nat.mod_eq_of_lt j.isLt]

/-- The actual difference correction in manuscript (4.11), uniformly on the box. -/
theorem liftedCenter_difference_error {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) (j : Fin (2 * m)) :
    ‖difference (by omega) (liftedCenter hm q hq - canonicalLift q) j‖ ≤
      2048 / ((2 * m : ℕ) : ℝ) ^ 4 := by
  have he : difference (by omega) (liftedCenter hm q hq - canonicalLift q) j =
      difference (by omega) (liftedCenter hm q hq) j -
      difference (by omega) (canonicalLift q) j := by
    simp only [difference, Pi.sub_apply]
    ring
  rw [he, liftedCenter_difference, canonicalLift_difference (by omega)]
  exact correctedIncrement_error hm q hq _ (boxRoot_spec hm q hq).1 j

theorem liftedCenter_error {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) (j : Fin (2 * m)) :
    ‖liftedCenter hm q hq j - canonicalLift q j‖ ≤ 4096 / ((2 * m : ℕ) : ℝ) ^ 3 := by
  have hmean : (∑ k, (liftedCenter hm q hq - canonicalLift q) k) = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, liftedCenter_mean_zero,
      canonicalLift_mean_zero (n := 2 * m) (by omega) q, sub_self]
  have he := finite_integral_norm_bound (by omega) _ hmean j
  change ‖liftedCenter hm q hq j - canonicalLift q j‖ ≤ _ at he
  have hn0 : (((2 * m : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (show 2 * m ≠ 0 by omega)
  calc
    _ ≤ 2 * ∑ k, ‖difference (by omega) (liftedCenter hm q hq - canonicalLift q) k‖ := he
    _ ≤ 2 * ∑ _k : Fin (2 * m), 2048 / ((2 * m : ℕ) : ℝ) ^ 4 := by
      gcongr with k
      exact liftedCenter_difference_error hm q hq k
    _ = _ := by simp; field_simp; ring

theorem liftedCenter_sup_error {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    ‖liftedCenter hm q hq - canonicalLift q‖ ≤ 4096 / ((2 * m : ℕ) : ℝ) ^ 3 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  exact liftedCenter_error hm q hq

theorem canonicalIncrement_norm_le {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ)
    (hq : ∀ j, |q j| ≤ FiniteBox.amplitude n) (j : Fin n) :
    ‖SchurLift.increment q j‖ ≤ Real.sqrt 3 * radius n := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (radius_nonneg n))).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), ← Complex.normSq_eq_norm_sq]
  have he := increment_sq_le_of_bound hn q (FiniteBox.amplitude_pos (by omega)).le hq j
  calc
    _ ≤ 12 * Real.sin (Real.pi / n) ^ 2 / (n : ℝ) ^ 2 * FiniteBox.amplitude n ^ 2 := he
    _ = 3 * radius n ^ 2 := by
      rw [radius_identity (by omega)]
      dsimp [angle]
      ring

theorem liftedCenter_increment_norm_le {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) (j : Fin (2 * m)) :
    ‖difference (by omega) (liftedCenter hm q hq) j‖ ≤
      Real.sqrt 3 * radius (2 * m) + 2048 / ((2 * m : ℕ) : ℝ) ^ 4 := by
  have he : difference (by omega) (liftedCenter hm q hq) j =
      SchurLift.increment q j + difference (by omega) (liftedCenter hm q hq - canonicalLift q) j := by
    have hd := congrFun (canonicalLift_difference (by omega) q) j
    simp only [difference, Pi.sub_apply] at hd ⊢
    rw [← hd]
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (canonicalIncrement_norm_le (by omega) q hq.2 j)
    (liftedCenter_difference_error hm q hq j))

theorem radius_lower {n : ℕ} (hn : 2 ≤ n) : 4 / (n : ℝ) ^ 2 ≤ radius n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have ha : |angle n| ≤ Real.pi := by
    rw [abs_of_nonneg (by unfold angle; positivity)]
    exact div_le_self Real.pi_pos.le hnR
  have hc := Real.cos_le_one_sub_mul_cos_sq ha
  have he : 2 / Real.pi ^ 2 * angle n ^ 2 = 2 / (n : ℝ) ^ 2 := by
    unfold angle
    field_simp
  rw [he] at hc
  unfold radius
  rw [show 4 / (n : ℝ) ^ 2 = 2 * (2 / (n : ℝ) ^ 2) by ring]
  linarith

theorem radius_pos {n : ℕ} (hn : 2 ≤ n) : 0 < radius n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact lt_of_lt_of_le (by positivity) (radius_lower hn)

theorem rootRadius_le_quarter_radius {n : ℕ} (hn : 32 ≤ n) : rootRadius n ≤ radius n / 4 := by
  have hnR : (32 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : (1024 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hr := radius_lower (by omega : 2 ≤ n)
  have he : rootRadius n ≤ 1 / (n : ℝ) ^ 2 := by
    unfold rootRadius
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 4)
      (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).2
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (show 0 ≤ (n : ℝ) ^ 2 - 1024 by linarith)]
  rw [show 4 / (n : ℝ) ^ 2 = 4 * (1 / (n : ℝ) ^ 2) by ring] at hr
  linarith

theorem corrected_height_small {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) (ξ : ℂ) (hξ : ‖ξ‖ ≤ rootRadius (2 * m)) (j : Fin m) :
    |LensClosure.heightParameter (fun k => tangential q (halfIndex k)) ξ j| ≤
      2 * radius (2 * m) := by
  have hd := (LensClosure.harmonicFunctional_le_norm (LensClosure.midpoint m j) ξ).trans
    (hξ.trans (rootRadius_le_quarter_radius (by omega)))
  have hb := tangential_abs_le (by omega) q hq.2 (halfIndex j)
  have hs : Real.sqrt 2 ≤ 3 / 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hb' := mul_le_mul_of_nonneg_right hs (radius_nonneg (2 * m))
  unfold LensClosure.heightParameter
  refine (abs_add_le _ _).trans ?_
  nlinarith [radius_nonneg (2 * m)]

theorem corrected_lens_positive {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) (ξ : ℂ) (hξ : ‖ξ‖ ≤ rootRadius (2 * m)) (j : Fin m) :
    let t := LensClosure.heightParameter (fun k => tangential q (halfIndex k)) ξ j
    0 < baseWidth (2 * m) ∧ t ^ 2 ≤ 4 ∧ 0 < Lens.width (baseWidth (2 * m)) t := by
  intro t
  have hR := radius_pos (by omega : 2 ≤ 2 * m)
  have hr : radius (2 * m) ≤ 1 / 64 := by
    refine (radius_le_numeric (by omega)).trans ?_
    have hnR : (32 : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast (show 32 ≤ 2 * m by omega)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((2 * m : ℕ) : ℝ) ^ 2)).2
    nlinarith
  have ht := corrected_height_small hm q hq ξ hξ j
  change |t| ≤ 2 * radius (2 * m) at ht
  have ht2 : t ^ 2 ≤ 4 * radius (2 * m) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg t) (by positivity : 0 ≤ 2 * radius (2 * m))).2 ht
    rw [sq_abs] at h
    nlinarith
  have hL : baseWidth (2 * m) = 2 - radius (2 * m) := by unfold baseWidth radius; ring
  have ht4 : t ^ 2 ≤ 4 := by nlinarith [sq_nonneg (radius (2 * m) - 1 / 64)]
  refine ⟨by rw [hL]; linarith, ht4, ?_⟩
  have hs := Lens.height_sq ht4
  have hp := Lens.height_nonneg t
  rw [Lens.width_pos_iff, hL]
  have hrr : 5 * radius (2 * m) ^ 2 < 4 * radius (2 * m) := by
    nlinarith [mul_nonneg hR.le (show 0 ≤ 1 / 64 - radius (2 * m) by linarith)]
  nlinarith

theorem liftedCenter_cross_constraints {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) (j : Fin m) :
    ‖(baseWidth (2 * m) : ℂ) * LensClosure.unit (LensClosure.midpoint m j) +
      difference (by omega) (liftedCenter hm q hq) (halfIndex j)‖ ≤ 2 ∧
    ‖(baseWidth (2 * m) : ℂ) * LensClosure.unit (LensClosure.midpoint m j) -
      difference (by omega) (liftedCenter hm q hq) (halfIndex j)‖ ≤ 2 := by
  rw [liftedCenter_half_difference, correctedHalfIncrement]
  obtain ⟨hL, ht, hR⟩ := corrected_lens_positive hm q hq _ (boxRoot_spec hm q hq).1 j
  exact (LensClosure.increment_constraints hL.le ht hR).2
    (coordinate_bound (by omega) q hq.2 (halfIndex j))

end Erdos1045.EventualExact.BoxLensLift

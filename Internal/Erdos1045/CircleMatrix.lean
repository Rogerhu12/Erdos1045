import Erdos1045.CyclicAngles
import Erdos1045.MatrixNormalization
import Erdos1045.HullGeometry

open scoped BigOperators

namespace Erdos1045.CircleMatrix

open Configuration CyclicAngles CirclePotential MatrixDefect
noncomputable section

def circlePoint (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

def anglePoints {n : ℕ} (a : Angles n) : Points n := fun i => circlePoint (a.angle i)

def vandermonde {n : ℕ} (z : Points n) : Mat n := fun i j => z i ^ (j : ℕ)

/-- Only generic algebraic and trigonometric identities are exposed here.
The logarithmic-energy identification is proved below, not assumed. -/
structure ClassicalCircleIdentities : Prop where
  vandermonde : ∀ n (z : Points n), detSq (vandermonde z) = discriminant z
  chord : ∀ s t : ℝ, ‖circlePoint t - circlePoint s‖ = |2 * Real.sin ((t - s) / 2)|

theorem circlePoint_periodic (t : ℝ) : circlePoint (t + 2 * Real.pi) = circlePoint t := by
  unfold circlePoint
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem anglePoints_injective (H : ClassicalCircleIdentities) {n : ℕ} (a : Angles n) :
    Function.Injective (anglePoints a) := by
  intro i j hij
  by_contra hne
  wlog hijlt : i < j generalizing i j
  · exact this hij.symm (Ne.symm hne) (lt_of_le_of_ne (le_of_not_gt hijlt) (Ne.symm hne))
  have hlow : 0 < a.angle j - a.angle i := sub_pos.mpr (a.increasing (by exact_mod_cast hijlt))
  have hupp : a.angle j - a.angle i < 2 * Real.pi := by
    have h := a.increasing (show (j : ℤ) < (i : ℤ) + n by omega)
    rw [a.period] at h
    linarith
  have hs : 0 < Real.sin ((a.angle j - a.angle i) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc := H.chord (a.angle i) (a.angle j)
  have heq : circlePoint (a.angle j) = circlePoint (a.angle i) := hij.symm
  rw [heq, sub_self, norm_zero, abs_of_pos (by positivity)] at hc
  linarith

theorem log_discriminant_full_sum {n : ℕ} (z : Points n) (hz : Function.Injective z) :
    Real.log (discriminant z) = ∑ i, ∑ j, Real.log ‖z j - z i‖ := by
  unfold discriminant
  have hne (i j : Fin n) (hj : j ∈ Finset.univ.erase i) : ‖z i - z j‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun h =>
      (Finset.ne_of_mem_erase hj) (hz h).symm))
  rw [Real.log_prod (s := Finset.univ)
    (f := fun i => ∏ j ∈ Finset.univ.erase i, ‖z i - z j‖)
    (fun i _ => Finset.prod_ne_zero_iff.mpr (hne i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.log_prod (fun j hj => norm_ne_zero_iff.mpr (sub_ne_zero.mpr
    (fun h => (Finset.ne_of_mem_erase hj) (hz h).symm)))]
  have hsum := Finset.sum_erase_add (s := Finset.univ)
    (f := fun j => Real.log ‖z i - z j‖) (Finset.mem_univ i)
  simp only [sub_self, norm_zero, Real.log_zero, add_zero] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [norm_sub_rev]

theorem log_discriminant_lag_sum (H : ClassicalCircleIdentities) {n : ℕ} (a : Angles n) :
    Real.log (discriminant (anglePoints a)) =
      ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range n,
        Real.log ‖circlePoint (a.angle ((i : ℤ) + m)) - circlePoint (a.angle i)‖ := by
  rw [log_discriminant_full_sum _ (anglePoints_injective H a)]
  simp only [anglePoints]
  rw [← Finset.sum_range (fun i : ℕ => ∑ j : Fin n,
    Real.log ‖circlePoint (a.angle j) - circlePoint (a.angle i)‖)]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_range (fun j : ℕ =>
    Real.log ‖circlePoint (a.angle j) - circlePoint (a.angle i)‖)]
  have hper (j : ℕ) :
      Real.log ‖circlePoint (a.angle ((j + n : ℕ) : ℤ)) - circlePoint (a.angle i)‖ =
        Real.log ‖circlePoint (a.angle j) - circlePoint (a.angle i)‖ + 0 := by
    rw [Nat.cast_add, a.period, circlePoint_periodic, add_zero]
  have hshift := sum_shift_of_drift (n := n)
    (fun j : ℕ => Real.log ‖circlePoint (a.angle j) - circlePoint (a.angle i)‖) 0 hper i
  simp only [mul_zero, add_zero] at hshift
  rw [← hshift]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.cast_add, add_comm (j : ℤ) (i : ℤ)]

theorem chord_log_window (H : ClassicalCircleIdentities) {n m : ℕ}
    (a : Angles n) (hm0 : 0 < m) (hmn : m < n) (i : ℕ) :
    Real.log ‖circlePoint (a.angle ((i : ℤ) + m)) - circlePoint (a.angle i)‖ =
      Real.log 2 - potential (window a m i) / 2 := by
  have hw := window_mem_arc a hm0 hmn i
  have hs : 0 < Real.sin (window a m i / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by have := hw.1; linarith) (by have := hw.2; linarith)
  rw [H.chord]
  change Real.log |2 * Real.sin (window a m i / 2)| = _
  rw [abs_of_pos (by positivity), Real.log_mul (by norm_num) hs.ne']
  unfold potential
  ring

theorem log_discriminant_potential (H : ClassicalCircleIdentities) {n : ℕ}
    (hn : 0 < n) (a : Angles n) :
    Real.log (discriminant (anglePoints a)) =
      (n : ℝ) * (n - 1) * Real.log 2 -
        (∑ m ∈ Finset.Ico 1 n, ∑ i ∈ Finset.range n, potential (window a m i)) / 2 := by
  rw [log_discriminant_lag_sum H a]
  have hzero : (∑ i ∈ Finset.range n,
      Real.log ‖circlePoint (a.angle ((i : ℤ) + (0 : ℕ))) - circlePoint (a.angle i)‖) = 0 := by simp
  have hsplit := Finset.sum_Ico_eq_sub (f := fun m => ∑ i ∈ Finset.range n,
    Real.log ‖circlePoint (a.angle ((i : ℤ) + m)) - circlePoint (a.angle i)‖) (show 1 ≤ n by omega)
  simp only [Finset.sum_range_one, hzero, sub_zero] at hsplit
  rw [← hsplit]
  have hterm (m : ℕ) (hm : m ∈ Finset.Ico 1 n) :
      (∑ i ∈ Finset.range n,
        Real.log ‖circlePoint (a.angle ((i : ℤ) + m)) - circlePoint (a.angle i)‖) =
      n * Real.log 2 - (∑ i ∈ Finset.range n, potential (window a m i)) / 2 := by
    simp_rw [chord_log_window H a (by have := (Finset.mem_Ico.mp hm).1; omega)
      (Finset.mem_Ico.mp hm).2]
    simp [Finset.sum_sub_distrib, ← Finset.sum_div]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_div]
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  ring

def regularAngles {n : ℕ} (hn : 0 < n) : Angles n where
  angle i := 2 * Real.pi * i / n
  increasing := by
    intro i j hij
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hij' : (i : ℝ) < j := by exact_mod_cast hij
    apply (div_lt_div_iff_of_pos_right hn0).mpr
    nlinarith [Real.pi_pos]
  period := by
    intro i
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp

theorem window_regularAngles {n : ℕ} (hn : 0 < n) (m i : ℕ) :
    window (regularAngles hn) m i = 2 * Real.pi * m / n := by
  simp only [window, regularAngles, Int.cast_add, Int.cast_natCast]
  ring

theorem anglePoints_regular {n : ℕ} (hn : 0 < n) :
    anglePoints (regularAngles hn) = regular n := by
  funext i
  simp only [anglePoints, regularAngles, circlePoint, regular, Int.cast_natCast]

/-- The finite circular energy is exactly the logarithmic Vandermonde deficit.
Both the cyclic reindexing and the cancellation of the reference energy are
proved here from their concrete definitions. -/
theorem energy_eq_log_discriminant (H : ClassicalCircleIdentities)
    (G : HullGeometry.ClassicalHullGeometry) {n : ℕ} (hn : 3 ≤ n) (a : Angles n) :
    energy a = n * Real.log n - Real.log (discriminant (anglePoints a)) := by
  have hn0 : 0 < n := by omega
  have hA := log_discriminant_potential H hn0 a
  have hR := log_discriminant_potential H hn0 (regularAngles hn0)
  rw [anglePoints_regular hn0, G.regular_discriminant n hn, Real.log_pow] at hR
  simp only [window_regularAngles, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hR
  have hE : energy a =
      ((∑ m ∈ Finset.Ico 1 n, ∑ i ∈ Finset.range n, potential (window a m i)) -
        (∑ m ∈ Finset.Ico 1 n, n * potential (2 * Real.pi * m / n))) / 2 := by
    simp only [energy, lagEnergy, Finset.sum_sub_distrib]
  rw [hE]
  linarith

theorem vandermonde_unit_entries {n : ℕ} (a : Angles n) (i j : Fin n) :
    Complex.normSq (vandermonde (anglePoints a) i j) = 1 := by
  simp [vandermonde, anglePoints, Complex.normSq_eq_norm_sq, circlePoint]

theorem vandermonde_det_ne_zero (H : ClassicalCircleIdentities) {n : ℕ} (a : Angles n) :
    (vandermonde (anglePoints a)).det ≠ 0 := by
  apply (detSq_pos_iff _).mp
  rw [H.vandermonde]
  exact discriminant_pos _ (anglePoints_injective H a)

/-- This identifies the gap energy used by the Fourier-kernel theorem with
the matrix defect used by the singular-value stability theorem. -/
theorem energy_eq_matrix_defect (H : ClassicalCircleIdentities)
    (G : HullGeometry.ClassicalHullGeometry) {n : ℕ} (hn : 3 ≤ n) (a : Angles n) :
    energy a = defect (normalize (vandermonde (anglePoints a))) := by
  rw [normalized_energy_eq (by omega) _ (vandermonde_det_ne_zero H a)
    (vandermonde_unit_entries a), H.vandermonde]
  exact energy_eq_log_discriminant H G hn a

end
end Erdos1045.CircleMatrix

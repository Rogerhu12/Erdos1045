import EventualExact.CyclicCosecant
import EventualExact.RegularCircleForce

/-! The force budget for the gaps of an actual ordered circle configuration.
All energy reindexings and the regular reference value are proved explicitly. -/

namespace Erdos1045.EventualExact.CyclicForceBudget

open scoped BigOperators
open CyclicAngles CosecantPotential
noncomputable section

def angleVector {n : ℕ} (a : Angles n) : Fin n → ℝ := fun i => a.angle i

theorem sin_forward_pos {n : ℕ} (a : Angles n) (i j : Fin n) (hij : i < j) :
    0 < Real.sin ((a.angle j - a.angle i) / 2) := by
  have hlow : 0 < a.angle j - a.angle i :=
    sub_pos.mpr (a.increasing (by exact_mod_cast hij))
  have hupp : a.angle j - a.angle i < 2 * Real.pi := by
    have h := a.increasing (show (j : ℤ) < (i : ℤ) + n by omega)
    rw [a.period] at h
    linarith
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

theorem angleVector_separated {n : ℕ} (a : Angles n) (i j : Fin n) (hij : i ≠ j) :
    Real.sin ((angleVector a i - angleVector a j) / 2) ≠ 0 := by
  change Real.sin ((a.angle i - a.angle j) / 2) ≠ 0
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hp := sin_forward_pos a i j hlt
    rw [show (a.angle i - a.angle j) / 2 = -((a.angle j - a.angle i) / 2) by ring,
      Real.sin_neg]
    exact neg_ne_zero.mpr hp.ne'
  · exact (sin_forward_pos a j i hgt).ne'

theorem potential_periodic (t : ℝ) : potential (t + 2 * Real.pi) = potential t := by
  simp only [potential]
  rw [show (t + 2 * Real.pi) / 2 = t / 2 + Real.pi by ring, Real.sin_add_pi, neg_sq]

theorem potential_even (t : ℝ) : potential (-t) = potential t := by
  simp only [potential, neg_div, Real.sin_neg, neg_sq]

theorem potential_zero : potential 0 = 0 := by simp [potential]

theorem energy_full_sum {n : ℕ} (a : Angles n) :
    circleCosecantEnergy (angleVector a) =
      ∑ i : Fin n, ∑ j : Fin n, potential (a.angle j - a.angle i) := by
  classical
  unfold circleCosecantEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    simp [potential_zero]
  · rw [if_neg hij]
    change potential (a.angle i - a.angle j) = potential (a.angle j - a.angle i)
    rw [show a.angle j - a.angle i = -(a.angle i - a.angle j) by ring, potential_even]

theorem energy_lag_range {n : ℕ} (a : Angles n) :
    circleCosecantEnergy (angleVector a) =
      ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range n, potential (window a m i) := by
  rw [energy_full_sum]
  rw [← Finset.sum_range (fun i : ℕ => ∑ j : Fin n,
    potential (a.angle j - a.angle i))]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_range (fun j : ℕ => potential (a.angle j - a.angle i))]
  have hper (j : ℕ) : potential (a.angle ((j + n : ℕ) : ℤ) - a.angle i) =
      potential (a.angle j - a.angle i) + 0 := by
    rw [Nat.cast_add, a.period, show a.angle j + 2 * Real.pi - a.angle i =
      (a.angle j - a.angle i) + 2 * Real.pi by ring, potential_periodic, add_zero]
  have hshift := sum_shift_of_drift (n := n)
    (fun j : ℕ => potential (a.angle j - a.angle i)) 0 hper i
  simp only [mul_zero, add_zero] at hshift
  rw [← hshift]
  apply Finset.sum_congr rfl
  intro j _
  simp only [window, Nat.cast_add, add_comm (j : ℤ) (i : ℤ)]

theorem energy_lag_sum {n : ℕ} (a : Angles n) (hn : 0 < n) :
    circleCosecantEnergy (angleVector a) =
      ∑ m ∈ Finset.Ico 1 n, ∑ i ∈ Finset.range n, potential (window a m i) := by
  rw [energy_lag_range]
  have hzero : (∑ i ∈ Finset.range n, potential (window a 0 i)) = 0 := by
    simp [window, potential_zero]
  have hsplit := Finset.sum_Ico_eq_sub
    (f := fun m => ∑ i ∈ Finset.range n, potential (window a m i)) (show 1 ≤ n by omega)
  simpa only [Finset.sum_range_one, hzero, sub_zero] using hsplit.symm

def regularLift {n : ℕ} (hn : 0 < n) : Angles n where
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

theorem window_regularLift {n : ℕ} (hn : 0 < n) (m i : ℕ) :
    window (regularLift hn) m i = 2 * Real.pi * m / n := by
  simp only [window, regularLift, Int.cast_add, Int.cast_natCast]
  ring

theorem angleVector_regularLift {n : ℕ} (hn : 0 < n) :
    angleVector (regularLift hn) = regularForceAngles n := by
  funext i
  simp [angleVector, regularLift, regularForceAngles]

theorem reference_energy {n : ℕ} (hn : 0 < n) :
    (∑ m ∈ Finset.Ico 1 n, (n : ℝ) * potential (2 * Real.pi * m / n)) =
      (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3 := by
  have h := energy_lag_sum (regularLift hn) hn
  rw [angleVector_regularLift, regularCircleCosecantEnergy hn] at h
  simpa only [window_regularLift, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h.symm

theorem energyDifference_eq_force {n : ℕ} (a : Angles n) (hn : 0 < n) :
    CyclicCosecant.energyDifference a =
      (n : ℝ) ^ 2 * ∑ i, circleForce (angleVector a) i ^ 2 := by
  unfold CyclicCosecant.energyDifference CyclicCosecant.lagEnergy
  rw [Finset.sum_sub_distrib, ← energy_lag_sum a hn, reference_energy hn]
  exact (circleForce_square_identity_fin hn (angleVector a) (angleVector_separated a)).symm

/-- The first inequality in (2.21), with no force-budget assumption. -/
theorem totalGapDefect_le_force {n : ℕ} (a : Angles n) (hn : 3 ≤ n) :
    totalGapDefect (CyclicCosecant.relativeGaps a) ≤
      (3 * Real.pi ^ 2 / 2) * ∑ i, circleForce (angleVector a) i ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h := CyclicCosecant.gapDefect_le_energyDifference a hn
  rw [energyDifference_eq_force a (by omega)] at h
  calc
    _ ≤ (3 * Real.pi ^ 2 / (2 * (n : ℝ) ^ 2)) *
        ((n : ℝ) ^ 2 * ∑ i, circleForce (angleVector a) i ^ 2) := h
    _ = _ := by field_simp

theorem each_gap_le_force {n : ℕ} (a : Angles n) (hn : 3 ≤ n) (i : Fin n) :
    CyclicCosecant.relativeGaps a i ≤
      2 + 3 * Real.pi ^ 2 * ∑ j, circleForce (angleVector a) j ^ 2 :=
  (gap_bounds_of_force_budget (CyclicCosecant.relativeGaps a)
    (CyclicCosecant.relativeGaps_pos a (by omega)) (totalGapDefect_le_force a hn)).1 i

/-- The third inequality in (2.21), for any upper bound `b` on the actual gaps. -/
theorem gapSquareSum_le_force {n : ℕ} (a : Angles n) (hn : 3 ≤ n) {b : ℝ}
    (hb : ∀ i, CyclicCosecant.relativeGaps a i ≤ b) :
    gapSquareSum (CyclicCosecant.relativeGaps a) ≤
      (3 * Real.pi ^ 2 / 4) * b * ∑ i, circleForce (angleVector a) i ^ 2 := by
  have hr := CyclicCosecant.relativeGaps_pos a (by omega)
  have hb0 : 0 ≤ b := (hr ⟨0, by omega⟩).le.trans (hb ⟨0, by omega⟩)
  calc
    _ ≤ b / 2 * totalGapDefect (CyclicCosecant.relativeGaps a) :=
      gapSquareSum_le_total _ hr hb
    _ ≤ b / 2 * ((3 * Real.pi ^ 2 / 2) * ∑ i, circleForce (angleVector a) i ^ 2) :=
      mul_le_mul_of_nonneg_left (totalGapDefect_le_force a hn) (by positivity)
    _ = _ := by ring

/-- A version eliminating the maximum gap from the square-sum upper bound. -/
theorem gapSquareSum_le_force_only {n : ℕ} (a : Angles n) (hn : 3 ≤ n) :
    gapSquareSum (CyclicCosecant.relativeGaps a) ≤
      (3 * Real.pi ^ 2 / 4) *
        (2 + 3 * Real.pi ^ 2 * ∑ i, circleForce (angleVector a) i ^ 2) *
          ∑ i, circleForce (angleVector a) i ^ 2 :=
  gapSquareSum_le_force a hn (each_gap_le_force a hn)

end
end Erdos1045.EventualExact.CyclicForceBudget

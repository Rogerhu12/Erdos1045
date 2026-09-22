import EventualExact.CotangentForce
import Erdos1045.CyclicAngles
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The regular circle has zero force

Periodicity and finite reindexing show that all interaction row sums coincide.
Antisymmetry then makes their common value zero. The force-square identity
therefore evaluates the actual cosecant energy of the regular circle.
-/

namespace Erdos1045.EventualExact

open scoped BigOperators

noncomputable section

def regularForceAngles (n : ℕ) (i : Fin n) : ℝ :=
  2 * Real.pi * (i.val : ℝ) / n

def regularLagCot (n k : ℕ) : ℝ := circleCot (Real.pi * k / n)

theorem circleCot_add_pi (t : ℝ) : circleCot (t + Real.pi) = circleCot t := by
  simp only [circleCot, Real.cos_add_pi, Real.sin_add_pi, neg_div, div_neg, neg_neg]

theorem regularLagCot_period {n : ℕ} (hn : 0 < n) (k : ℕ) :
    regularLagCot n (k + n) = regularLagCot n k := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold regularLagCot
  rw [Nat.cast_add, show Real.pi * ((k : ℝ) + n) / n =
      Real.pi * k / n + Real.pi by field_simp, circleCot_add_pi]

theorem regularForceAngles_half_difference {n : ℕ} (i j : Fin n) :
    (regularForceAngles n i - regularForceAngles n j) / 2 =
      Real.pi * ((i.val : ℝ) - j.val) / n := by
  unfold regularForceAngles
  ring

/-- Distinct regular vertices satisfy the exact trigonometric separation
condition required by the force-square identity. -/
theorem regularForceAngles_separated {n : ℕ} (hn : 0 < n)
    (i j : Fin n) (hij : i ≠ j) :
    Real.sin ((regularForceAngles n i - regularForceAngles n j) / 2) ≠ 0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos (a b : Fin n) (hab : b.val < a.val) :
      0 < Real.sin (Real.pi * ((a.val : ℝ) - b.val) / n) := by
    have habR : (b.val : ℝ) < a.val := by exact_mod_cast hab
    have haR : (a.val : ℝ) < n := by exact_mod_cast a.isLt
    have hbR : (0 : ℝ) ≤ b.val := by positivity
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact div_pos (mul_pos Real.pi_pos (sub_pos.mpr habR)) hnR
    · apply (div_lt_iff₀ hnR).mpr
      nlinarith [Real.pi_pos]
  rw [regularForceAngles_half_difference]
  have hvals : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hvals with hlt | hgt
  · rw [show Real.pi * ((i.val : ℝ) - j.val) / n =
        -(Real.pi * ((j.val : ℝ) - i.val) / n) by ring, Real.sin_neg]
    exact neg_ne_zero.mpr (hpos j i hlt).ne'
  · exact (hpos i j hgt).ne'

/-- A row of the actual interaction is a shifted periodic cotangent row. -/
theorem regularInteraction_eq_lag {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    circleInteraction (regularForceAngles n) i j =
      regularLagCot n (i.val + n - j.val) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsub : j.val ≤ i.val + n := by omega
  unfold circleInteraction regularLagCot
  rw [regularForceAngles_half_difference, Nat.cast_sub hsub, Nat.cast_add]
  rw [show Real.pi * ((i.val : ℝ) + n - j.val) / n =
      Real.pi * ((i.val : ℝ) - j.val) / n + Real.pi by field_simp; ring]
  exact (circleCot_add_pi _).symm

theorem regularInteraction_row_sum {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (∑ j : Fin n, circleInteraction (regularForceAngles n) i j) =
      ∑ k ∈ Finset.range n, regularLagCot n k := by
  simp_rw [regularInteraction_eq_lag hn]
  rw [← Finset.sum_range (fun k => regularLagCot n (i.val + n - k))]
  calc
    (∑ k ∈ Finset.range n, regularLagCot n (i.val + n - k)) =
        ∑ k ∈ Finset.range n, regularLagCot n (i.val + n - (n - 1 - k)) :=
      (Finset.sum_range_reflect (fun k => regularLagCot n (i.val + n - k)) n).symm
    _ = ∑ k ∈ Finset.range n, regularLagCot n (k + (i.val + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk0 := Finset.mem_range.mp hk
      congr 1
      omega
    _ = _ := by
      have h := CyclicAngles.sum_shift_of_drift (regularLagCot n) 0
        (fun k => by simpa using regularLagCot_period hn k) (i.val + 1)
      simpa only [mul_zero, add_zero] using h

/-- All interaction row sums are equal and their total is zero. -/
theorem regularInteraction_row_sum_zero {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (∑ j : Fin n, circleInteraction (regularForceAngles n) i j) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hskew : (∑ i : Fin n, ∑ j : Fin n,
      circleInteraction (regularForceAngles n) i j) =
      -(∑ i : Fin n, ∑ j : Fin n,
        circleInteraction (regularForceAngles n) i j) := by
    calc
      _ = ∑ j : Fin n, ∑ i : Fin n,
          circleInteraction (regularForceAngles n) i j := Finset.sum_comm
      _ = ∑ j : Fin n, ∑ i : Fin n,
          -circleInteraction (regularForceAngles n) j i := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        exact circleInteraction_skew _ j i
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have htotal : (∑ i : Fin n, ∑ j : Fin n,
      circleInteraction (regularForceAngles n) i j) = 0 := by linarith
  simp_rw [regularInteraction_row_sum hn] at htotal
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htotal
  rw [regularInteraction_row_sum hn]
  exact (mul_eq_zero.mp htotal).resolve_left hn0

theorem regularCircleForce_zero {n : ℕ} (hn : 0 < n) (i : Fin n) :
    circleForce (regularForceAngles n) i = 0 := by
  simp only [circleForce, regularInteraction_row_sum_zero hn, zero_div]

/-- The exact regular baseline for the convex cosecant energy comparison. -/
theorem regularCircleCosecantEnergy {n : ℕ} (hn : 0 < n) :
    circleCosecantEnergy (regularForceAngles n) =
      (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3 := by
  have h := circleForce_square_identity_fin hn (regularForceAngles n)
    (regularForceAngles_separated hn)
  simp only [regularCircleForce_zero hn, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_const_zero, mul_zero] at h
  linarith

end

end Erdos1045.EventualExact

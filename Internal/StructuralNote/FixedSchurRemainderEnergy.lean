import StructuralNote.FixedSchurRemainderDifference
import Mathlib.Analysis.Real.Sqrt

/-! Weighted finite-difference bounds for the scalar Schur remainder. -/

namespace StructuralNote.FixedSchurRemainderEnergy

open StructuralNote.FixedSchurRemainderScalar
open StructuralNote.FixedSchurRemainderDifference
open scoped BigOperators Topology

noncomputable section

theorem norm_R_difference_weighted {u v x : ℂ} {U : ℝ}
    (hu : ‖u‖ ≤ U) (hv : ‖v‖ ≤ U) (_hU : 0 ≤ U) (hUquarter : U ≤ 1 / 4)
    (hx : ‖x‖ ≤ 1 / 4) :
    ‖R u x - R v x‖ ≤
      32 * (U * ‖x‖ + U ^ 2 * (‖u‖ + ‖v‖)) * ‖u - v‖ := by
  let M : ℝ := max ‖u‖ ‖v‖
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact (norm_nonneg u).trans (le_max_left _ _)
  have hMu : ‖u‖ ≤ M := by
    exact le_max_left _ _
  have hMv : ‖v‖ ≤ M := by
    exact le_max_right _ _
  have hMU : M ≤ U := by
    exact max_le hu hv
  have hMquarter : M ≤ 1 / 4 := hMU.trans hUquarter
  have hpoint := norm_R_sub_R_u_le (u := u) (v := v) (x := x)
    (U := M) (X := ‖x‖) hMu hMv hM0 hMquarter le_rfl (norm_nonneg x) hx
  have hMsum : M ≤ ‖u‖ + ‖v‖ := by
    dsimp [M]
    exact max_le (le_add_of_nonneg_right (norm_nonneg v))
      (le_add_of_nonneg_left (norm_nonneg u))
  have hM2 : M ^ 2 ≤ U ^ 2 := by
    exact pow_le_pow_left₀ hM0 hMU 2
  have hM3 : M ^ 3 ≤ U ^ 2 * (‖u‖ + ‖v‖) := by
    have hmul := mul_le_mul hM2 hMsum hM0 (sq_nonneg U)
    simpa [pow_succ, mul_assoc] using hmul
  have hMx : M * ‖x‖ ≤ U * ‖x‖ :=
    mul_le_mul_of_nonneg_right hMU (norm_nonneg x)
  have hcoef : M * (‖x‖ + M ^ 2) ≤
      U * ‖x‖ + U ^ 2 * (‖u‖ + ‖v‖) := by
    calc
      M * (‖x‖ + M ^ 2) = M * ‖x‖ + M ^ 3 := by ring
      _ ≤ U * ‖x‖ + U ^ 2 * (‖u‖ + ‖v‖) := add_le_add hMx hM3
  calc
    ‖R u x - R v x‖ ≤ 32 * M * (‖x‖ + M ^ 2) * ‖u - v‖ := hpoint
    _ = (32 * ‖u - v‖) * (M * (‖x‖ + M ^ 2)) := by ring
    _ ≤ (32 * ‖u - v‖) *
        (U * ‖x‖ + U ^ 2 * (‖u‖ + ‖v‖)) := by
      exact mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ = 32 * (U * ‖x‖ + U ^ 2 * (‖u‖ + ‖v‖)) * ‖u - v‖ := by ring

theorem sum_norm_R_difference_le {ι : Type*} [Fintype ι]
    (u v x : ι → ℂ) {U : ℝ}
    (hU : 0 ≤ U) (hUquarter : U ≤ 1 / 4)
    (hu : ∀ i, ‖u i‖ ≤ U) (hv : ∀ i, ‖v i‖ ≤ U)
    (hx : ∀ i, ‖x i‖ ≤ 1 / 4) :
    ∑ i, ‖R (u i) (x i) - R (v i) (x i)‖ ≤
      32 *
        (U * Real.sqrt (∑ i, ‖x i‖ ^ 2) +
          U ^ 2 * (Real.sqrt (∑ i, ‖u i‖ ^ 2) +
            Real.sqrt (∑ i, ‖v i‖ ^ 2))) *
        Real.sqrt (∑ i, ‖u i - v i‖ ^ 2) := by
  let d : ι → ℝ := fun i => ‖u i - v i‖
  let a : ι → ℝ := fun i =>
    U * ‖x i‖ + U ^ 2 * (‖u i‖ + ‖v i‖)
  have hpoint (i : ι) :
      ‖R (u i) (x i) - R (v i) (x i)‖ ≤ 32 * (a i * d i) := by
    simpa [a, d, mul_assoc] using
      (norm_R_difference_weighted (u := u i) (v := v i) (x := x i)
        (U := U) (hu i) (hv i) hU hUquarter (hx i))
  have hsum :
      ∑ i, ‖R (u i) (x i) - R (v i) (x i)‖ ≤ 32 * ∑ i, a i * d i := by
    calc
      ∑ i, ‖R (u i) (x i) - R (v i) (x i)‖ ≤
          ∑ i, 32 * (a i * d i) :=
        Finset.sum_le_sum (fun i _ => hpoint i)
      _ = 32 * ∑ i, a i * d i := by rw [Finset.mul_sum]
  have hcsx := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => ‖x i‖) d
  have hcsu := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => ‖u i‖) d
  have hcsv := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => ‖v i‖) d
  have hcore :
      ∑ i, a i * d i ≤
        U * (Real.sqrt (∑ i, ‖x i‖ ^ 2) * Real.sqrt (∑ i, d i ^ 2)) +
          U ^ 2 *
            (Real.sqrt (∑ i, ‖u i‖ ^ 2) * Real.sqrt (∑ i, d i ^ 2) +
              Real.sqrt (∑ i, ‖v i‖ ^ 2) * Real.sqrt (∑ i, d i ^ 2)) := by
    have hdecomp :
        ∑ i, a i * d i =
          U * (∑ i, ‖x i‖ * d i) +
            U ^ 2 * ((∑ i, ‖u i‖ * d i) + (∑ i, ‖v i‖ * d i)) := by
      simp only [a, add_mul, mul_add, Finset.sum_add_distrib]
      simp only [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hdecomp]
    have hfirst := mul_le_mul_of_nonneg_left hcsx hU
    have hsecond := mul_le_mul_of_nonneg_left (add_le_add hcsu hcsv) (sq_nonneg U)
    exact add_le_add hfirst hsecond
  have hfinal := hsum.trans (mul_le_mul_of_nonneg_left hcore (by norm_num : (0 : ℝ) ≤ 32))
  simpa [d, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hfinal

end
end StructuralNote.FixedSchurRemainderEnergy

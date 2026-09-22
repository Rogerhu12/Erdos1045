import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! A finite polynomial construction removes the apparent pole of the
Bernstein--Walsh pullback at zero. -/

namespace ExteriorReduction

open Complex Metric Set
open scoped BigOperators
noncomputable section

def polynomialDiskPullback (p : Polynomial ℂ) (q : ℂ → ℂ) (A z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    p.coeff k * z ^ (p.natDegree - k) * (A * z + q z) ^ k

theorem polynomialDiskPullback_eq (p : Polynomial ℂ) (q : ℂ → ℂ) (A : ℂ)
    {z : ℂ} (hz : z ≠ 0) :
    polynomialDiskPullback p q A z = z ^ p.natDegree * p.eval (A + q z / z) := by
  rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkdeg : k ≤ p.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have ha : A * z + q z = z * (A + q z / z) := by field_simp
  rw [ha, mul_pow]
  calc
    _ = p.coeff k * (z ^ (p.natDegree - k) * z ^ k) * (A + q z / z) ^ k := by ring
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hkdeg]; ring

theorem polynomialDiskPullback_diffContOnCl (p : Polynomial ℂ) (A : ℂ)
    {q : ℂ → ℂ} (hq : DiffContOnCl ℂ q (ball 0 1)) :
    DiffContOnCl ℂ (polynomialDiskPullback p q A) (ball 0 1) := by
  constructor
  · unfold polynomialDiskPullback
    apply DifferentiableOn.fun_sum
    intro k hk
    exact ((differentiableOn_const (p.coeff k)).mul (differentiableOn_id.pow _)).mul
      (((differentiableOn_const A).mul differentiableOn_id).add hq.differentiableOn |>.pow k)
  · unfold polynomialDiskPullback
    apply continuousOn_finsetSum
    intro k hk
    exact (continuousOn_const.mul (continuousOn_id.pow _)).mul
      ((continuousOn_const.mul continuousOn_id).add hq.continuousOn |>.pow k)

/-- Disk maximum modulus gives the Bernstein--Walsh inequality after the
apparent pole has been removed by an explicit finite polynomial sum. -/
theorem polynomial_bernstein_walsh_disk (p : Polynomial ℂ) (A : ℂ)
    {q : ℂ → ℂ} (hq : DiffContOnCl ℂ q (ball 0 1))
    (hboundary : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval (A + q z / z)‖ ≤ 1)
    {z : ℂ} (hz0 : z ≠ 0) (hz : z ∈ closedBall 0 1) :
    ‖p.eval (A + q z / z)‖ ≤ ‖z‖⁻¹ ^ p.natDegree := by
  have hpull : ‖polynomialDiskPullback p q A z‖ ≤ 1 := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (polynomialDiskPullback_diffContOnCl p A hq) ?_
      (by simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hz)
    intro v hv
    have hvnorm : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp (frontier_ball_subset_sphere hv)
    have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by simp [hvnorm])
    rw [polynomialDiskPullback_eq p q A hv0, norm_mul, norm_pow, hvnorm, one_pow, one_mul]
    exact hboundary v hvnorm
  rw [polynomialDiskPullback_eq p q A hz0, norm_mul, norm_pow] at hpull
  have hn : 0 < ‖z‖ ^ p.natDegree := pow_pos (norm_pos_iff.mpr hz0) _
  rw [inv_pow, ← one_div]
  exact (le_div_iff₀ hn).mpr (by simpa only [mul_comm] using hpull)

/-- A radius h/2 circle inside a region bounded by C yields the exact
2*C/h derivative estimate used in the separation argument. -/
theorem polynomial_cauchy_of_ball_bound (p : Polynomial ℂ) {x : ℂ} {h C : ℝ}
    (hh : 0 < h) (hbound : ∀ y ∈ ball x h, ‖p.eval y‖ ≤ C) :
    ‖p.derivative.eval x‖ ≤ 2 * C / h := by
  have he := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by positivity : (0 : ℝ) < h / 2) p.differentiable.diffContOnCl
    (fun y hy => hbound y (sphere_subset_ball (by linarith : h / 2 < h) hy))
  rw [p.deriv] at he
  convert he using 1
  ring

#print axioms polynomial_bernstein_walsh_disk
#print axioms polynomial_cauchy_of_ball_bound

end
end ExteriorReduction

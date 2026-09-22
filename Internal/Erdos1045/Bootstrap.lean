import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar bootstrap and the sharp trace constant

These are the scalar deductions in sections 4.3 and 5.3 of the candidate proof.
They do not assume that the analytic estimates for an extremal configuration
have been established.  Instead, every needed numerical inequality is an
explicit hypothesis.  In particular no assertion about Faber polynomials or
polygonal extremizers is hidden in these declarations.
-/

noncomputable section

namespace Erdos1045.Bootstrap

/-- The quadratic estimate that upgrades a first-order error to a second-order
deficit.  Its proof does not introduce a square root or divide by the deficit. -/
theorem deficit_bound
    {n δ E A C : ℝ}
    (hn : 0 < n) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (henergy : E ^ 2 ≤ C * δ)
    (hbalance : n * δ ≤ 2 * A * E) :
    n ^ 2 * δ ≤ 4 * A ^ 2 * C := by
  by_cases hzero : δ = 0
  · subst δ
    simp only [mul_zero]
    positivity
  have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hzero)
  have hsquare : (n * δ) ^ 2 ≤ (2 * A * E) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hn.le hδ) hbalance 2
  have hmul := mul_le_mul_of_nonneg_left henergy (show 0 ≤ 4 * A ^ 2 by positivity)
  have hcancel : (n ^ 2 * δ) * δ ≤ (4 * A ^ 2 * C) * δ := by
    nlinarith [hsquare, hmul]
  exact (mul_le_mul_iff_left₀ hδpos).mp (by simpa [mul_comm] using hcancel)

/-- Absorb the term proportional to `n E²` into the capacity deficit.
All constants are independent of the polygon and of the number of vertices. -/
theorem absorb_energy_term
    {n δ E A B C : ℝ}
    (hn : 4 ≤ n) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (henergy : E ^ 2 ≤ C * δ)
    (hlarge : 4 * B * C ≤ n)
    (htrace : 0 ≤ -(n * (n - 1)) * δ + A * n * E + B * n * E ^ 2) :
    n * δ ≤ 2 * A * E := by
  have hnpos : 0 < n := by linarith
  have herror := mul_le_mul_of_nonneg_left henergy
    (show 0 ≤ B * n by positivity)
  have hlargeδ := mul_le_mul_of_nonneg_right hlarge hδ
  have hquadratic : 3 * n / 4 ≤ n - 1 := by linarith
  have hquadraticδ := mul_le_mul_of_nonneg_right hquadratic hδ
  have htrace' : 0 ≤ -(n - 1) * δ + A * E + B * E ^ 2 := by
    have heq : -(n * (n - 1)) * δ + A * n * E + B * n * E ^ 2 =
        n * (-(n - 1) * δ + A * E + B * E ^ 2) := by ring
    rw [heq] at htrace
    exact nonneg_of_mul_nonneg_right htrace hnpos
  have herror' := mul_le_mul_of_nonneg_left henergy hB
  nlinarith

/-- The complete scalar bootstrap used to obtain `δ = O(n⁻²)`.
The estimate is an explicit finite inequality, stronger than an asymptotic
statement with an unspecified constant. -/
theorem quantitative_bootstrap
    {n δ E A B C : ℝ}
    (hn : 4 ≤ n) (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (henergy : E ^ 2 ≤ C * δ)
    (hlarge : 4 * B * C ≤ n)
    (htrace : 0 ≤ -(n * (n - 1)) * δ + A * n * E + B * n * E ^ 2) :
    n ^ 2 * δ ≤ 4 * A ^ 2 * C ∧
      n ^ 2 * E ^ 2 ≤ 4 * A ^ 2 * C ^ 2 := by
  have hb := absorb_energy_term hn hδ hB henergy hlarge htrace
  have hd := deficit_bound (by linarith : 0 < n) hδ hC henergy hb
  refine ⟨hd, ?_⟩
  have he := mul_le_mul_of_nonneg_left henergy (sq_nonneg n)
  have hc := mul_le_mul_of_nonneg_left hd hC
  nlinarith

/-- The conventional inverse-square presentation of the deficit bound. -/
theorem deficit_le_inv_square
    {n δ E A B C : ℝ}
    (hn : 4 ≤ n) (hδ : 0 ≤ δ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (henergy : E ^ 2 ≤ C * δ)
    (hlarge : 4 * B * C ≤ n)
    (htrace : 0 ≤ -(n * (n - 1)) * δ + A * n * E + B * n * E ^ 2) :
    δ ≤ (4 * A ^ 2 * C) / n ^ 2 := by
  have h := (quantitative_bootstrap hn hδ hB hC henergy hlarge htrace).1
  apply (le_div_iff₀ (by positivity : 0 < n ^ 2)).2
  simpa [mul_comm] using h

/-- Completing the square with a positive quadratic coefficient. -/
theorem complete_square (a b x : ℝ) (ha : 0 < a) :
    -a * x ^ 2 + b * x = b ^ 2 / (4 * a) - a * (x - b / (2 * a)) ^ 2 := by
  field_simp
  ring

/-- The sharp upper bound for a concave scalar quadratic. -/
theorem quadratic_upper_bound (a b x : ℝ) (ha : 0 < a) :
    -a * x ^ 2 + b * x ≤ b ^ 2 / (4 * a) := by
  rw [complete_square a b x ha]
  exact sub_le_self _ (mul_nonneg ha.le (sq_nonneg _))

/-- The equality case records the scale selected by the trace argument. -/
theorem quadratic_upper_bound_eq_iff (a b x : ℝ) (ha : 0 < a) :
    -a * x ^ 2 + b * x = b ^ 2 / (4 * a) ↔ x = b / (2 * a) := by
  rw [complete_square a b x ha]
  constructor
  · intro h
    have hm : a * (x - b / (2 * a)) ^ 2 = 0 := by linarith
    have hs : (x - b / (2 * a)) ^ 2 = 0 :=
      (mul_eq_zero.mp hm).resolve_left (ne_of_gt ha)
    nlinarith [sq_nonneg (x - b / (2 * a))]
  · intro h
    rw [h]
    simp

/-- Exact version of the completion of the square in equation (5.12).
Using a square root avoids the manuscript's fractional-power notation. -/
theorem sharp_trace_identity (x : ℝ) :
    -x ^ 2 / (8 * Real.pi) + x * Real.sqrt (Real.pi / 12) =
      Real.pi ^ 2 / 6 -
        (x - 4 * Real.pi * Real.sqrt (Real.pi / 12)) ^ 2 / (8 * Real.pi) := by
  have hp := Real.pi_pos
  have hs := Real.sq_sqrt (show 0 ≤ Real.pi / 12 by positivity)
  field_simp
  linear_combination 96 * Real.pi ^ 2 * hs

/-- The numerical constant that closes the sharp trace upper bound. -/
theorem sharp_trace_upper_bound (x : ℝ) :
    -x ^ 2 / (8 * Real.pi) + x * Real.sqrt (Real.pi / 12) ≤
      Real.pi ^ 2 / 6 := by
  rw [sharp_trace_identity]
  exact sub_le_self _ (by positivity)

/-- A retained square gives a quantitative loss away from the optimal scale. -/
theorem sharp_trace_with_remainder (x ε T : ℝ)
    (hT : T ≤ -x ^ 2 / (8 * Real.pi) + x * Real.sqrt (Real.pi / 12) + ε) :
    T + (x - 4 * Real.pi * Real.sqrt (Real.pi / 12)) ^ 2 / (8 * Real.pi)
      ≤ Real.pi ^ 2 / 6 + ε := by
  rw [sharp_trace_identity] at hT
  linarith

/-- Closing the asymptotic sandwich is an ordinary limit comparison once
the analytic upper and geometric lower bounds have both been proved. -/
theorem squeeze_trace
    {lower trace upper : ℕ → ℝ} {limit : ℝ}
    (hlower : Filter.Tendsto lower Filter.atTop (nhds limit))
    (hupper : Filter.Tendsto upper Filter.atTop (nhds limit))
    (hlo : ∀ᶠ n in Filter.atTop, lower n ≤ trace n)
    (hhi : ∀ᶠ n in Filter.atTop, trace n ≤ upper n) :
    Filter.Tendsto trace Filter.atTop (nhds limit) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper hlo hhi

end Erdos1045.Bootstrap

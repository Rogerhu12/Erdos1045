import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar and finite spectral logarithmic defect

The quantity `χ x = x - 1 - log x` is the scalar ingredient of
`‖A‖²_F - n - log |det A|²`.  This file proves the dimension-free
coercivity estimates needed before any matrix argument is invoked.

The square-root bound avoids a Taylor theorem, a second derivative, and
integration.  All the statements below are proved from mathlib without
project-specific external assumptions; no conformal-mapping input is used here.
-/

namespace Erdos1045.LogDefect

open scoped BigOperators
noncomputable section

/-- The nonnegative scalar defect on the positive real axis. -/
def chi (x : ℝ) : ℝ := x - 1 - Real.log x

@[simp] theorem chi_one : chi 1 = 0 := by
  simp [chi]

theorem chi_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ chi x := by
  have h := Real.log_le_sub_one_of_pos hx
  dsimp [chi]
  linarith

/-- A global coercivity bound with no compactness hypothesis. -/
theorem sqrt_sub_one_sq_le_chi {x : ℝ} (hx : 0 < x) :
    (Real.sqrt x - 1) ^ 2 ≤ chi x := by
  have hs := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hx)
  rw [Real.log_sqrt hx.le] at hs
  have hsq := Real.sq_sqrt hx.le
  dsimp [chi]
  nlinarith

theorem chi_eq_zero_iff {x : ℝ} (hx : 0 < x) :
    chi x = 0 ↔ x = 1 := by
  constructor
  · intro h
    have hs := sqrt_sub_one_sq_le_chi hx
    have hsq := Real.sq_sqrt hx.le
    have hz : Real.sqrt x - 1 = 0 := by nlinarith [sq_nonneg (Real.sqrt x - 1)]
    nlinarith
  · rintro rfl
    exact chi_one

theorem chi_pos_iff {x : ℝ} (hx : 0 < x) :
    0 < chi x ↔ x ≠ 1 := by
  constructor
  · intro h heq
    simp [heq] at h
  · intro h
    exact lt_of_le_of_ne (chi_nonneg hx) fun heq =>
      h ((chi_eq_zero_iff hx).1 heq.symm)

/-- Bounded defect gives a uniform upper spectral bound. -/
theorem self_le_two_mul_chi_add_two {x : ℝ} (hx : 0 < x) :
    x ≤ 2 * chi x + 2 := by
  have hs := sqrt_sub_one_sq_le_chi hx
  have hsq := Real.sq_sqrt hx.le
  nlinarith [sq_nonneg (Real.sqrt x - 2)]

/-- Bounded defect also excludes approach to zero. -/
theorem exp_neg_chi_sub_one_le {x : ℝ} (hx : 0 < x) :
    Real.exp (-chi x - 1) ≤ x := by
  rw [← Real.le_log_iff_exp_le hx]
  dsimp [chi]
  linarith

theorem bounds_of_chi_le {x C : ℝ} (hx : 0 < x) (hC : chi x ≤ C) :
    Real.exp (-C - 1) ≤ x ∧ x ≤ 2 * C + 2 := by
  constructor
  · exact (Real.exp_le_exp.mpr (by linarith)).trans (exp_neg_chi_sub_one_le hx)
  · linarith [self_le_two_mul_chi_add_two hx]

/-- A useful global quadratic bound; its coefficient depends on `x`. -/
theorem sub_one_sq_le_two_mul_self_add_one_mul_chi {x : ℝ} (hx : 0 < x) :
    (x - 1) ^ 2 ≤ 2 * (x + 1) * chi x := by
  have hs := sqrt_sub_one_sq_le_chi hx
  have hsq := Real.sq_sqrt hx.le
  have hfactor : (Real.sqrt x + 1) ^ 2 ≤ 2 * (x + 1) := by
    nlinarith [sq_nonneg (Real.sqrt x - 1)]
  have hprod := mul_le_mul_of_nonneg_left hs (sq_nonneg (Real.sqrt x + 1))
  have hprod' := mul_le_mul_of_nonneg_right hfactor (chi_nonneg hx)
  have hid : (Real.sqrt x + 1) ^ 2 * (Real.sqrt x - 1) ^ 2 = (x - 1) ^ 2 := by
    calc
      _ = ((Real.sqrt x) ^ 2 - 1) ^ 2 := by ring
      _ = (x - 1) ^ 2 := by rw [hsq]
  rw [hid] at hprod
  exact hprod.trans hprod'

/-- On a defect sublevel set, the quadratic coefficient is uniform. -/
theorem sub_one_sq_le_of_chi_le {x C : ℝ} (hx : 0 < x) (hC : chi x ≤ C) :
    (x - 1) ^ 2 ≤ (4 * C + 6) * chi x := by
  have hu := (bounds_of_chi_le hx hC).2
  calc
    (x - 1) ^ 2 ≤ 2 * (x + 1) * chi x :=
      sub_one_sq_le_two_mul_self_add_one_mul_chi hx
    _ ≤ (4 * C + 6) * chi x :=
      mul_le_mul_of_nonneg_right (by linarith) (chi_nonneg hx)

/-- The reverse comparison follows from the tangent inequality for `log (1/x)`. -/
theorem chi_le_sub_one_sq_div {x : ℝ} (hx : 0 < x) :
    chi x ≤ (x - 1) ^ 2 / x := by
  have hl := Real.one_sub_inv_le_log_of_pos hx
  apply (le_div_iff₀ hx).2
  have hi : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
  have hm := mul_le_mul_of_nonneg_left hl hx.le
  dsimp [chi]
  nlinarith

/-- The usual quadratic upper comparison on a positive half-line. -/
theorem chi_le_sub_one_sq_div_lower {x a : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    chi x ≤ (x - 1) ^ 2 / a := by
  have hx : 0 < x := ha.trans_le hax
  exact (chi_le_sub_one_sq_div hx).trans
    (div_le_div_of_nonneg_left (sq_nonneg (x - 1)) ha hax)

/-- A concrete local comparison, convenient after coarse localization. -/
theorem local_quadratic_bounds {x : ℝ} (hl : (1 : ℝ) / 2 ≤ x) (hu : x ≤ 2) :
    (x - 1) ^ 2 / 6 ≤ chi x ∧ chi x ≤ 2 * (x - 1) ^ 2 := by
  have hx : 0 < x := by linarith
  constructor
  · have h := sub_one_sq_le_two_mul_self_add_one_mul_chi hx
    have hm := mul_le_mul_of_nonneg_right (show 2 * (x + 1) ≤ 6 by linarith)
      (chi_nonneg hx)
    linarith
  · have h := chi_le_sub_one_sq_div_lower (show (0 : ℝ) < 1 / 2 by norm_num) hl
    linarith

section FiniteFamily

variable {ι : Type*} (s : Finset ι) (x : ι → ℝ)

/-- Sum of scalar defects, later applied to Gram-matrix eigenvalues. -/
def total : ℝ := ∑ i ∈ s, chi (x i)

/-- Squared distance of a finite spectrum from the constant spectrum one. -/
def deviation : ℝ := ∑ i ∈ s, (x i - 1) ^ 2

theorem total_nonneg (hx : ∀ i ∈ s, 0 < x i) : 0 ≤ total s x := by
  exact Finset.sum_nonneg fun i hi => chi_nonneg (hx i hi)

theorem deviation_nonneg : 0 ≤ deviation s x := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i - 1)

theorem chi_le_total (hx : ∀ i ∈ s, 0 < x i) {j : ι} (hj : j ∈ s) :
    chi (x j) ≤ total s x := by
  exact Finset.single_le_sum (fun i hi => chi_nonneg (hx i hi)) hj

theorem total_eq_zero_iff (hx : ∀ i ∈ s, 0 < x i) :
    total s x = 0 ↔ ∀ i ∈ s, x i = 1 := by
  constructor
  · intro h i hi
    apply (chi_eq_zero_iff (hx i hi)).1
    have hle := chi_le_total s x hx hi
    have hge := chi_nonneg (hx i hi)
    linarith
  · intro h
    apply Finset.sum_eq_zero
    intro i hi
    rw [h i hi, chi_one]

theorem deviation_eq_zero_iff :
    deviation s x = 0 ↔ ∀ i ∈ s, x i = 1 := by
  constructor
  · intro h i hi
    have hle : (x i - 1) ^ 2 ≤ deviation s x :=
      Finset.single_le_sum (fun j _ => sq_nonneg (x j - 1)) hi
    nlinarith [sq_nonneg (x i - 1)]
  · intro h
    apply Finset.sum_eq_zero
    intro i hi
    rw [h i hi]
    norm_num

/-- The spectral interval depends on total defect, not on cardinality. -/
theorem coordinate_bounds_of_total_le (hx : ∀ i ∈ s, 0 < x i)
    {C : ℝ} (hC : total s x ≤ C) {i : ι} (hi : i ∈ s) :
    Real.exp (-C - 1) ≤ x i ∧ x i ≤ 2 * C + 2 := by
  exact bounds_of_chi_le (hx i hi) ((chi_le_total s x hx hi).trans hC)

/-- Dimension-free Hilbert--Schmidt coercivity on a defect sublevel set. -/
theorem deviation_le_mul_total (hx : ∀ i ∈ s, 0 < x i)
    {C : ℝ} (hC : total s x ≤ C) :
    deviation s x ≤ (4 * C + 6) * total s x := by
  unfold deviation total
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact sub_one_sq_le_of_chi_le (hx i hi) ((chi_le_total s x hx hi).trans hC)

/-- In particular, a vanishing total defect forces vanishing quadratic deviation. -/
theorem deviation_le_self_bound (hx : ∀ i ∈ s, 0 < x i) :
    deviation s x ≤ (4 * total s x + 6) * total s x := by
  exact deviation_le_mul_total s x hx le_rfl

/-- A small-defect version with a fixed numerical constant. -/
theorem deviation_le_ten_mul_total (hx : ∀ i ∈ s, 0 < x i)
    (hsmall : total s x ≤ 1) : deviation s x ≤ 10 * total s x := by
  have h := deviation_le_mul_total s x hx hsmall
  norm_num at h
  exact h

theorem coordinate_sq_le_deviation {i : ι} (hi : i ∈ s) :
    (x i - 1) ^ 2 ≤ deviation s x := by
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j - 1)) hi

/-- A usable epsilon bound for individual eigenvalues. -/
theorem coordinate_abs_sub_one_le (hx : ∀ i ∈ s, 0 < x i)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : total s x ≤ 1)
    (hεbound : total s x ≤ ε ^ 2 / 10) {i : ι} (hi : i ∈ s) :
    |x i - 1| ≤ ε := by
  apply abs_le_of_sq_le_sq _ hε
  have hcoordinate := coordinate_sq_le_deviation s x hi
  have hdeviation := deviation_le_ten_mul_total s x hx hsmall
  linarith

/-- Coarse localization needed before applying local quadratic equivalence. -/
theorem half_le_coordinate_le_three_halves (hx : ∀ i ∈ s, 0 < x i)
    (hsmall : total s x ≤ (1 : ℝ) / 40) {i : ι} (hi : i ∈ s) :
    (1 : ℝ) / 2 ≤ x i ∧ x i ≤ (3 : ℝ) / 2 := by
  have h := coordinate_abs_sub_one_le s x hx (ε := 1 / 2) (by norm_num)
    (by linarith) (by norm_num; exact hsmall) hi
  rw [abs_le] at h
  constructor <;> linarith

/-- A positive determinant lower bound follows from bounded defect and trace. -/
theorem log_prod_lower_of_total_le (hx : ∀ i ∈ s, 0 < x i)
    {C : ℝ} (hC : total s x ≤ C) :
    (∑ i ∈ s, x i) - s.card - C ≤ Real.log (∏ i ∈ s, x i) := by
  have hlog := Real.log_prod (fun i hi => (hx i hi).ne')
  have htotal : total s x = (∑ i ∈ s, x i) - s.card -
      Real.log (∏ i ∈ s, x i) := by
    rw [hlog]
    simp [total, chi, Finset.sum_sub_distrib]
  rw [htotal] at hC
  linarith

theorem total_le_deviation_div {a : ℝ} (ha : 0 < a) (hl : ∀ i ∈ s, a ≤ x i) :
    total s x ≤ deviation s x / a := by
  unfold total deviation
  rw [Finset.sum_div]
  exact Finset.sum_le_sum fun i hi => chi_le_sub_one_sq_div_lower ha (hl i hi)

/-- Once eigenvalues lie in `[1/2,2]`, the two defects are equivalent. -/
theorem finite_local_quadratic_bounds
    (hl : ∀ i ∈ s, (1 : ℝ) / 2 ≤ x i) (hu : ∀ i ∈ s, x i ≤ 2) :
    deviation s x / 6 ≤ total s x ∧ total s x ≤ 2 * deviation s x := by
  constructor
  · unfold total deviation
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun i hi => (local_quadratic_bounds (hl i hi) (hu i hi)).1
  · unfold total deviation
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => (local_quadratic_bounds (hl i hi) (hu i hi)).2

/-- Scalar sum form of the trace-minus-log-determinant identity. -/
theorem total_eq_trace_sub_card_sub_log_prod (hx : ∀ i ∈ s, 0 < x i) :
    total s x = (∑ i ∈ s, x i) - s.card - Real.log (∏ i ∈ s, x i) := by
  rw [Real.log_prod (fun i hi => (hx i hi).ne')]
  simp [total, chi, Finset.sum_sub_distrib]

theorem log_prod_le_trace_sub_card (hx : ∀ i ∈ s, 0 < x i) :
    Real.log (∏ i ∈ s, x i) ≤ (∑ i ∈ s, x i) - s.card := by
  have h := total_nonneg s x hx
  rw [total_eq_trace_sub_card_sub_log_prod s x hx] at h
  linarith

/-- The non-normalized determinant bound, with trace defect explicit. -/
theorem prod_le_exp_trace_sub_card (hx : ∀ i ∈ s, 0 < x i) :
    (∏ i ∈ s, x i) ≤ Real.exp ((∑ i ∈ s, x i) - s.card) := by
  have hp : 0 < ∏ i ∈ s, x i := Finset.prod_pos hx
  exact (Real.log_le_iff_le_exp hp).1 (log_prod_le_trace_sub_card s x hx)

/-- A trace-normalized positive spectrum has product at most one. -/
theorem prod_le_one_of_trace_eq (hx : ∀ i ∈ s, 0 < x i)
    (ht : (∑ i ∈ s, x i) = s.card) : (∏ i ∈ s, x i) ≤ 1 := by
  have h := prod_le_exp_trace_sub_card s x hx
  simpa [ht] using h

theorem total_eq_neg_log_prod_of_trace_eq (hx : ∀ i ∈ s, 0 < x i)
    (ht : (∑ i ∈ s, x i) = s.card) :
    total s x = -Real.log (∏ i ∈ s, x i) := by
  rw [total_eq_trace_sub_card_sub_log_prod s x hx, ht]
  ring

/-- The equality case is rigid in every dimension, including an empty spectrum. -/
theorem prod_eq_one_iff_of_trace_eq (hx : ∀ i ∈ s, 0 < x i)
    (ht : (∑ i ∈ s, x i) = s.card) :
    (∏ i ∈ s, x i) = 1 ↔ ∀ i ∈ s, x i = 1 := by
  constructor
  · intro hp
    apply (total_eq_zero_iff s x hx).1
    rw [total_eq_neg_log_prod_of_trace_eq s x hx ht, hp, Real.log_one, neg_zero]
  · intro h
    exact Finset.prod_eq_one h

/-- Quantitative rigidity expressed directly in the determinant deficit. -/
theorem deviation_le_log_product_bound (hx : ∀ i ∈ s, 0 < x i)
    (ht : (∑ i ∈ s, x i) = s.card) :
    deviation s x ≤
      (6 - 4 * Real.log (∏ i ∈ s, x i)) * (-Real.log (∏ i ∈ s, x i)) := by
  have h := deviation_le_self_bound s x hx
  rw [total_eq_neg_log_prod_of_trace_eq s x hx ht] at h
  nlinarith

end FiniteFamily

end

end Erdos1045.LogDefect

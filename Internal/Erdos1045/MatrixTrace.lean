import Erdos1045.MatrixNormalization

namespace Erdos1045.MatrixDefect

open scoped BigOperators ComplexConjugate
noncomputable section

def entryInner {n : ℕ} (U R : Mat n) : ℂ := ∑ i, ∑ j, conj (U i j) * R i j

def cross {n : ℕ} (U R : Mat n) : ℝ := (2 / (n : ℝ)) * (entryInner U R).re

def traceExcess {n : ℕ} (c : ℝ) (F : Mat n) : ℝ :=
  ((n * (n - 1) : ℕ) : ℝ) * Real.log c + frobSq F / n - n

theorem entryInner_add_right {n : ℕ} (U R S : Mat n) :
    entryInner U (R + S) = entryInner U R + entryInner U S := by
  simp [entryInner, mul_add, Finset.sum_add_distrib]

theorem cross_add_right {n : ℕ} (U R S : Mat n) :
    cross U (R + S) = cross U R + cross U S := by
  simp [cross, entryInner_add_right, mul_add]

theorem frobSq_add {n : ℕ} (U R : Mat n) :
    frobSq (U + R) = frobSq U + frobSq R + 2 * (entryInner U R).re := by
  simp only [frobSq, Matrix.add_apply, Complex.normSq_add,
    Finset.sum_add_distrib, ← Finset.mul_sum, entryInner, Complex.re_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re]

theorem entryInner_norm_le {n : ℕ} (U R : Mat n) :
    ‖entryInner U R‖ ≤ Real.sqrt (frobSq U) * Real.sqrt (frobSq R) := by
  have heq : entryInner U R = ∑ p : Fin n × Fin n, conj (U p.1 p.2) * R p.1 p.2 := by
    simp [entryInner, Fintype.sum_prod_type]
  rw [heq]
  calc
    _ ≤ ∑ p : Fin n × Fin n, ‖conj (U p.1 p.2) * R p.1 p.2‖ := norm_sum_le _ _
    _ = ∑ p : Fin n × Fin n, ‖U p.1 p.2‖ * ‖R p.1 p.2‖ := by simp
    _ ≤ Real.sqrt (∑ p : Fin n × Fin n, ‖U p.1 p.2‖ ^ 2) *
        Real.sqrt (∑ p : Fin n × Fin n, ‖R p.1 p.2‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by simp [frobSq, Fintype.sum_prod_type, Complex.sq_norm]

theorem cross_le {n : ℕ} (hn : 0 < n) (U R : Mat n)
    (hU : ∀ i j, Complex.normSq (U i j) = 1) :
    cross U R ≤ 2 * Real.sqrt (frobSq R) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hi := (Complex.re_le_norm (entryInner U R)).trans (entryInner_norm_le U R)
  rw [frobSq_eq_card_sq_of_unit_entries U hU, Real.sqrt_sq (Nat.cast_nonneg n)] at hi
  have hmul := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 / (n : ℝ) by positivity)
  unfold cross
  convert hmul using 1 <;> first | rfl | field_simp

theorem normalized_frobSq_add {n : ℕ} (hn : 0 < n) (U R : Mat n)
    (hU : ∀ i j, Complex.normSq (U i j) = 1) :
    frobSq (U + R) / n - n = cross U R + frobSq R / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [frobSq_add, frobSq_eq_card_sq_of_unit_entries U hU]
  unfold cross
  field_simp
  ring

theorem normalized_frobSq_add_le {n : ℕ} (hn : 0 < n) (U R : Mat n)
    (hU : ∀ i j, Complex.normSq (U i j) = 1) :
    frobSq (U + R) / n - n ≤ 2 * Real.sqrt (frobSq R) + frobSq R / n := by
  rw [normalized_frobSq_add hn U R hU]
  exact add_le_add (cross_le hn U R hU) le_rfl

theorem cross_firstOrder_le {n : ℕ} (hn : 0 < n) (U R R₁ : Mat n)
    (hU : ∀ i j, Complex.normSq (U i j) = 1) :
    cross U R ≤ cross U R₁ + 2 * Real.sqrt (frobSq (R - R₁)) := by
  have heq : R = R₁ + (R - R₁) := by abel
  calc
    cross U R = cross U R₁ + cross U (R - R₁) := by conv_lhs => rw [heq, cross_add_right]
    _ ≤ _ := add_le_add le_rfl (cross_le hn U (R - R₁) hU)

theorem traceExcess_firstOrder_le {n : ℕ} (hn : 0 < n) (c : ℝ) (U R R₁ : Mat n)
    (hU : ∀ i j, Complex.normSq (U i j) = 1) :
    traceExcess c (U + R) ≤ ((n * (n - 1) : ℕ) : ℝ) * Real.log c +
      cross U R₁ + 2 * Real.sqrt (frobSq (R - R₁)) + frobSq R / n := by
  have hex := normalized_frobSq_add hn U R hU
  have hc := cross_firstOrder_le hn U R R₁ hU
  unfold traceExcess
  linarith

/-- The Vandermonde--Faber determinant identity yields the exact scalar defect
decomposition. The exponent is the number of ordered distinct index pairs. -/
theorem defect_trace_identity {n : ℕ} (hn : 0 < n) {c Δ : ℝ} (hc : 0 < c)
    (F : Mat n) (hΔ : 0 < Δ)
    (hdet : Δ = c ^ (n * (n - 1)) * detSq F) :
    defect (normalize F) = traceExcess c F - (Real.log Δ - n * Real.log n) := by
  have hF : F.det ≠ 0 := by
    apply (detSq_pos_iff F).1
    have hp : 0 < c ^ (n * (n - 1)) := pow_pos hc _
    rw [hdet] at hΔ
    exact (mul_pos_iff_of_pos_left hp).1 hΔ
  rw [defect_normalize_log (Nat.ne_of_gt hn) F hF]
  have hlog : Real.log Δ = ((n * (n - 1) : ℕ) : ℝ) * Real.log c + Real.log (detSq F) := by
    rw [hdet, Real.log_mul (pow_ne_zero _ hc.ne') ((detSq_pos_iff F).2 hF).ne', Real.log_pow]
  unfold traceExcess
  linarith

theorem energy_le_traceExcess (classic : ClassicalMatrixFacts)
    {n : ℕ} (hn : 0 < n) {c Δ : ℝ} (hc : 0 < c) (F : Mat n)
    (hΔ : 0 < Δ) (hdet : Δ = c ^ (n * (n - 1)) * detSq F) :
    Real.log Δ - n * Real.log n ≤ traceExcess c F := by
  have hF : detSq F > 0 := by
    rw [hdet] at hΔ
    exact (mul_pos_iff_of_pos_left (pow_pos hc _)).1 hΔ
  have hFn : (normalize F).det ≠ 0 := by
    apply (detSq_pos_iff _).1
    rw [detSq_normalize]
    exact div_pos hF (pow_pos (by exact_mod_cast hn) _)
  have hnonneg := defect_nonneg classic (normalize F) hFn
  rw [defect_trace_identity hn hc F hΔ hdet] at hnonneg
  linarith

theorem traceExcess_nonneg (classic : ClassicalMatrixFacts)
    {n : ℕ} (hn : 0 < n) {c Δ : ℝ} (hc : 0 < c) (F : Mat n)
    (hΔ : (n : ℝ) ^ n ≤ Δ) (hdet : Δ = c ^ (n * (n - 1)) * detSq F) :
    0 ≤ Real.log Δ - n * Real.log n ∧ 0 ≤ traceExcess c F := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp := pow_pos hn' n
  have hd : 0 < Δ := hp.trans_le hΔ
  have hl := Real.log_le_log hp hΔ
  rw [Real.log_pow] at hl
  have ht := energy_le_traceExcess classic hn hc F hd hdet
  constructor <;> linarith

end
end Erdos1045.MatrixDefect

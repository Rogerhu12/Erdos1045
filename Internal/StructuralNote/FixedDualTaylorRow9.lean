import StructuralNote.FixedDualIntervalEvaluation

/-! Actual endpoint signs and midpoint primitive enclosure for Appendix A row a=9.
The rational candidates are checked against proved Taylor and logarithm remainders. -/

namespace StructuralNote.FixedDualTaylorRow9

open Real FixedDualPrimitive FixedDualTaylorBounds FixedDualIntervalEvaluation
open FixedDualTaylorRow79 (Sample piLower piUpper)
noncomputable section

def samples : Fin 3 → Sample := ![
  ⟨9 / 100, 4493927 / 50000000, 1797571 / 20000000, 99595273 / 100000000, 49797637 / 50000000, 26673143 / 100000000, 3334143 / 12500000, 96377089 / 100000000, 9637709 / 10000000, -17161489 / 10000000, -85807439 / 50000000⟩,
  ⟨1 / 10, 9983341 / 100000000, 4991671 / 50000000, 777347 / 781250, 99500417 / 100000000, 1477601 / 5000000, 29552021 / 100000000, 5970853 / 6250000, 95533649 / 100000000, -161110521 / 100000000, -16111051 / 10000000⟩,
  ⟨19 / 200, 2371429 / 25000000, 9485717 / 100000000, 99549089 / 100000000, 9954909 / 10000000, 5623149 / 20000000, 14057873 / 50000000, 19193233 / 20000000, 47983083 / 50000000, -20777949 / 12500000, -166223581 / 100000000⟩]

theorem sample_positive (i : Fin 3) :
    (samples i).x ≤ piLower / 2 ∧ 0 < (samples i).sl ∧ 0 < (samples i).cl := by
  fin_cases i <;> norm_num [samples, piLower]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem sample_trigonometric_bounds (i : Fin 3) :
    ((samples i).sl ≤ sin (samples i).x ∧ sin (samples i).x ≤ (samples i).su) ∧
    ((samples i).cl ≤ cos (samples i).x ∧ cos (samples i).x ≤ (samples i).cu) ∧
    ((samples i).tl ≤ sin (3 * (samples i).x) ∧ sin (3 * (samples i).x) ≤ (samples i).tu) ∧
    ((samples i).dl ≤ cos (3 * (samples i).x) ∧ cos (3 * (samples i).x) ≤ (samples i).du) := by
  fin_cases i <;> refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | apply sine_interval (by norm_num [samples]) 24
    | apply cosine_interval (by norm_num [samples]) 24
  all_goals norm_num [samples, sinePolynomial, cosinePolynomial, sineCoefficient,
    cosineCoefficient, Finset.sum_range_succ, Nat.factorial]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem sample_lower_log (i : Fin 3) :
    (samples i).ll ≤ log (2 * (samples i).sl) ∧ log (2 * (samples i).sl) ≤ (samples i).lu := by
  fin_cases i <;> apply scaled_logarithm_interval (by norm_num [samples]) 2 8
  all_goals norm_num [samples, logPolynomial, logError, logCoordinate, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem sample_upper_log (i : Fin 3) :
    (samples i).ll ≤ log (2 * (samples i).su) ∧ log (2 * (samples i).su) ≤ (samples i).lu := by
  fin_cases i <;> apply scaled_logarithm_interval (by norm_num [samples]) 2 8
  all_goals norm_num [samples, logPolynomial, logError, logCoordinate, Finset.sum_range_succ]

theorem sample_logarithmic_bounds (i : Fin 3) :
    (samples i).ll ≤ log (2 * sin (samples i).x) ∧
      log (2 * sin (samples i).x) ≤ (samples i).lu := by
  have hs := (sample_trigonometric_bounds i).1
  have hpos := (sample_positive i).2.1
  constructor
  · exact (sample_lower_log i).1.trans
      (log_le_log (by positivity) (mul_le_mul_of_nonneg_left hs.1 (by norm_num)))
  · exact (log_le_log (by linarith [hs.1] : 0 < 2 * sin (samples i).x)
      (mul_le_mul_of_nonneg_left hs.2 (by norm_num))).trans (sample_upper_log i).2

theorem sample_evaluation (b : ℝ) (i : Fin 3) :
    (witnessLower b (samples i) ≤ witness b (samples i).x ∧
      witness b (samples i).x ≤ witnessUpper b (samples i)) ∧
    (primitiveLower b (samples i) ≤ primitive b (samples i).x ∧
      primitive b (samples i).x ≤ primitiveUpper b (samples i)) := by
  obtain ⟨hs, hc, ht, hd⟩ := sample_trigonometric_bounds i
  obtain ⟨hx, hs0, hc0⟩ := sample_positive i
  exact evaluate_sample b (samples i) hx hs0.le hc0.le hs hc ht hd (sample_logarithmic_bounds i)

/-- Three genuine function certificates, with no numerical assumptions. -/
theorem row9_complete :
    witness (-1 / 2) (9 / 100) < 0 ∧ 0 < witness (-1 / 2) (10 / 100) ∧
      (1659 : ℝ) / 1000 < primitive (-1 / 2) (19 / 200) ∧
        primitive (-1 / 2) (19 / 200) < 1660 / 1000 := by
  have hl := sample_evaluation (-1 / 2) ⟨0, by omega⟩
  have hr := sample_evaluation (-1 / 2) ⟨1, by omega⟩
  have hm := sample_evaluation (-1 / 2) ⟨2, by omega⟩
  norm_num [samples, witnessLower, witnessUpper, primitiveLower, primitiveUpper,
    piLower, piUpper] at hl hr hm ⊢
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    linarith [hl.1.1, hl.1.2, hr.1.1, hr.1.2, hm.2.1, hm.2.2]

end
end StructuralNote.FixedDualTaylorRow9

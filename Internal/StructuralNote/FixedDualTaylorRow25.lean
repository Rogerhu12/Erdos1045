import StructuralNote.FixedDualIntervalEvaluation

/-! Actual endpoint signs and midpoint primitive enclosure for Appendix A row a=25.
The rational candidates are checked against proved Taylor and logarithm remainders. -/

namespace StructuralNote.FixedDualTaylorRow25

open Real FixedDualPrimitive FixedDualTaylorBounds FixedDualIntervalEvaluation
open FixedDualTaylorRow79 (Sample piLower piUpper)
noncomputable section

def samples : Fin 3 → Sample := ![
  ⟨1 / 4, 4948079 / 20000000, 6185099 / 25000000, 48445621 / 50000000, 96891243 / 100000000, 17040969 / 25000000, 68163877 / 100000000, 36584443 / 50000000, 73168887 / 100000000, -8794821 / 12500000, -70358563 / 100000000⟩,
  ⟨13 / 50, 5141611 / 20000000, 3213507 / 12500000, 96638997 / 100000000, 48319499 / 50000000, 70327941 / 100000000, 35163971 / 50000000, 71091353 / 100000000, 35545677 / 50000000, -8315233 / 12500000, -66521859 / 100000000⟩,
  ⟨51 / 200, 1261227 / 5000000, 25224541 / 100000000, 96766329 / 100000000, 9676633 / 10000000, 69253699 / 100000000, 692537 / 1000000, 14427647 / 20000000, 18034559 / 25000000, -8552571 / 12500000, -68420563 / 100000000⟩]

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
  fin_cases i <;> apply scaled_logarithm_interval (by norm_num [samples]) 1 8
  all_goals norm_num [samples, logPolynomial, logError, logCoordinate, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem sample_upper_log (i : Fin 3) :
    (samples i).ll ≤ log (2 * (samples i).su) ∧ log (2 * (samples i).su) ≤ (samples i).lu := by
  fin_cases i <;> apply scaled_logarithm_interval (by norm_num [samples]) 1 8
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
theorem row25_complete :
    0 < witness (-1) (25 / 100) ∧ witness (-1) (26 / 100) < 0 ∧
      (1824 : ℝ) / 1000 < primitive (-1) (51 / 200) ∧
        primitive (-1) (51 / 200) < 1825 / 1000 := by
  have hl := sample_evaluation (-1) ⟨0, by omega⟩
  have hr := sample_evaluation (-1) ⟨1, by omega⟩
  have hm := sample_evaluation (-1) ⟨2, by omega⟩
  norm_num [samples, witnessLower, witnessUpper, primitiveLower, primitiveUpper,
    piLower, piUpper] at hl hr hm ⊢
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    linarith [hl.1.1, hl.1.2, hr.1.1, hr.1.2, hm.2.1, hm.2.2]

end
end StructuralNote.FixedDualTaylorRow25

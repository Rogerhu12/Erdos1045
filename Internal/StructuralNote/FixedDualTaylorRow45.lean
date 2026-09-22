import StructuralNote.FixedDualIntervalEvaluation

/-! Actual endpoint signs and midpoint primitive enclosure for Appendix A row a=45.
The rational candidates are checked against proved Taylor and logarithm remainders. -/

namespace StructuralNote.FixedDualTaylorRow45

open Real FixedDualPrimitive FixedDualTaylorBounds FixedDualIntervalEvaluation
open FixedDualTaylorRow79 (Sample piLower piUpper)
noncomputable section

def samples : Fin 3 → Sample := ![
  ⟨9 / 20, 43496553 / 100000000, 21748277 / 50000000, 9004471 / 10000000, 90044711 / 100000000, 19514467 / 20000000, 6098271 / 6250000, 5475167 / 25000000, 21900669 / 100000000, -3483533 / 25000000, -870883 / 6250000⟩,
  ⟨23 / 50, 4439481 / 10000000, 44394811 / 100000000, 89605249 / 100000000, 358421 / 400000, 98185353 / 100000000, 49092677 / 50000000, 18964083 / 100000000, 4741021 / 25000000, -2972511 / 25000000, -11890041 / 100000000⟩,
  ⟨91 / 200, 43946231 / 100000000, 5493279 / 12500000, 44913051 / 50000000, 89826103 / 100000000, 1529529 / 1562500, 97889857 / 100000000, 10217337 / 50000000, 817387 / 4000000, -2581123 / 20000000, -12905611 / 100000000⟩]

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
theorem row45_complete :
    0 < witness (-1 / 2) (45 / 100) ∧ witness (-1 / 2) (46 / 100) < 0 ∧
      (1745 : ℝ) / 1000 < primitive (-1 / 2) (91 / 200) ∧
        primitive (-1 / 2) (91 / 200) < 1746 / 1000 := by
  have hl := sample_evaluation (-1 / 2) ⟨0, by omega⟩
  have hr := sample_evaluation (-1 / 2) ⟨1, by omega⟩
  have hm := sample_evaluation (-1 / 2) ⟨2, by omega⟩
  norm_num [samples, witnessLower, witnessUpper, primitiveLower, primitiveUpper,
    piLower, piUpper] at hl hr hm ⊢
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    linarith [hl.1.1, hl.1.2, hr.1.1, hr.1.2, hm.2.1, hm.2.2]

end
end StructuralNote.FixedDualTaylorRow45

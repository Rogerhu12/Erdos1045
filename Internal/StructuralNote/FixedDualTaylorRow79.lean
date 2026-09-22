import StructuralNote.FixedDualTaylorBounds

/-! The complete second row of Appendix A: actual endpoint signs at 79/100,
80/100 and the actual primitive enclosure at 159/200. All tabulated auxiliary
intervals below are proved using finite Taylor sums and rational arithmetic. -/

namespace StructuralNote.FixedDualTaylorRow79

open Real FixedDualPrimitive FixedDualIntervals FixedDualTaylorBounds
noncomputable section

structure Sample where
  x : ℝ
  sl : ℝ
  su : ℝ
  cl : ℝ
  cu : ℝ
  tl : ℝ
  tu : ℝ
  dl : ℝ
  du : ℝ
  ll : ℝ
  lu : ℝ

def samples : Fin 3 → Sample := ![
  ⟨79 / 100, 71035327 / 100000000, 71035328 / 100000000,
    70384531 / 100000000, 70384532 / 100000000,
    69727773 / 100000000, 69727774 / 100000000,
    -71680106 / 100000000, -71680105 / 100000000,
    35115431 / 100000000, 35115433 / 100000000⟩,
  ⟨4 / 5, 71735609 / 100000000, 71735610 / 100000000,
    69670670 / 100000000, 69670671 / 100000000,
    67546318 / 100000000, 67546319 / 100000000,
    -73739372 / 100000000, -73739371 / 100000000,
    36096425 / 100000000, 36096428 / 100000000⟩,
  ⟨159 / 200, 71386360 / 100000000, 71386361 / 100000000,
    70028476 / 100000000, 70028477 / 100000000,
    68644768 / 100000000, 68644769 / 100000000,
    -72717920 / 100000000, -72717919 / 100000000,
    35608380 / 100000000, 35608383 / 100000000⟩]

theorem sample_positive (i : Fin 3) :
    0 < (samples i).x ∧ (samples i).x < 1 ∧ 0 < (samples i).sl ∧
      0 < (samples i).cl ∧ 0 < (samples i).ll := by
  fin_cases i <;> norm_num [samples]

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
  fin_cases i <;> apply logarithm_interval (by norm_num [samples]) 8
  all_goals norm_num [samples, logPolynomial, logError, logCoordinate, Finset.sum_range_succ]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem sample_upper_log (i : Fin 3) :
    (samples i).ll ≤ log (2 * (samples i).su) ∧ log (2 * (samples i).su) ≤ (samples i).lu := by
  fin_cases i <;> apply logarithm_interval (by norm_num [samples]) 8
  all_goals norm_num [samples, logPolynomial, logError, logCoordinate, Finset.sum_range_succ]

theorem sample_logarithmic_bounds (i : Fin 3) :
    (samples i).ll ≤ log (2 * sin (samples i).x) ∧
      log (2 * sin (samples i).x) ≤ (samples i).lu := by
  have hs := (sample_trigonometric_bounds i).1
  have hpos := (sample_positive i).2.2.1
  constructor
  · exact (sample_lower_log i).1.trans
      (log_le_log (by positivity) (mul_le_mul_of_nonneg_left hs.1 (by norm_num)))
  · exact (log_le_log (by linarith [hs.1] : 0 < 2 * sin (samples i).x)
      (mul_le_mul_of_nonneg_left hs.2 (by norm_num))).trans (sample_upper_log i).2

def piLower : ℝ := 31415926535 / 10000000000
def piUpper : ℝ := 31415926536 / 10000000000

theorem pi_bounds : piLower < Real.pi ∧ Real.pi < piUpper := by
  unfold piLower piUpper
  constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]

theorem sample_witness_bounds (i : Fin 3) :
    (samples i).dl + (samples i).tl / 2 + (samples i).cl * (1 + (samples i).ll) -
      (piUpper / 2 - (samples i).x) * (samples i).su ≤ witness (1 / 2) (samples i).x ∧
    witness (1 / 2) (samples i).x ≤
      (samples i).du + (samples i).tu / 2 + (samples i).cu * (1 + (samples i).lu) -
        (piLower / 2 - (samples i).x) * (samples i).sl := by
  obtain ⟨hs, hc, ht, hd⟩ := sample_trigonometric_bounds i
  obtain ⟨hx0, hx1, hs0, hc0, hl0⟩ := sample_positive i
  have hl := sample_logarithmic_bounds i
  have hplus : 1 + (samples i).ll ≤ 1 + log (2 * sin (samples i).x) ∧
      1 + log (2 * sin (samples i).x) ≤ 1 + (samples i).lu := by
    constructor <;> linarith [hl.1, hl.2]
  have hcl := positive_mul_bounds hc hplus hc0.le (by linarith : 0 ≤ 1 + (samples i).ll)
  have hv : piLower / 2 - (samples i).x ≤ Real.pi / 2 - (samples i).x ∧
      Real.pi / 2 - (samples i).x ≤ piUpper / 2 - (samples i).x := by
    constructor <;> linarith [pi_bounds.1, pi_bounds.2]
  have hvs := positive_mul_bounds hv hs
    (by unfold piLower; linarith : 0 ≤ piLower / 2 - (samples i).x) hs0.le
  rw [witness_expand]
  constructor <;> linarith [ht.1, ht.2, hd.1, hd.2, hcl.1, hcl.2, hvs.1, hvs.2]

theorem sample_primitive_bounds (i : Fin 3) :
    (samples i).tl / 3 - (samples i).du / 6 + (samples i).sl * (samples i).ll +
      (piLower / 2 - (samples i).x) * (samples i).cl + (samples i).sl ≤
        primitive (1 / 2) (samples i).x ∧
    primitive (1 / 2) (samples i).x ≤
      (samples i).tu / 3 - (samples i).dl / 6 + (samples i).su * (samples i).lu +
        (piUpper / 2 - (samples i).x) * (samples i).cu + (samples i).su := by
  obtain ⟨hs, hc, ht, hd⟩ := sample_trigonometric_bounds i
  obtain ⟨hx0, hx1, hs0, hc0, hl0⟩ := sample_positive i
  have hl := sample_logarithmic_bounds i
  have hsl := positive_mul_bounds hs hl hs0.le hl0.le
  have hv : piLower / 2 - (samples i).x ≤ Real.pi / 2 - (samples i).x ∧
      Real.pi / 2 - (samples i).x ≤ piUpper / 2 - (samples i).x := by
    constructor <;> linarith [pi_bounds.1, pi_bounds.2]
  have hvc := positive_mul_bounds hv hc
    (by unfold piLower; linarith : 0 ≤ piLower / 2 - (samples i).x) hc0.le
  unfold primitive
  constructor <;> linarith [hs.1, hs.2, ht.1, ht.2, hd.1, hd.2, hsl.1, hsl.2, hvc.1, hvc.2]

/-- The second table row: two genuine endpoint signs and the genuine midpoint enclosure. -/
theorem row79_complete :
    0 < witness (1 / 2) (79 / 100) ∧ witness (1 / 2) (80 / 100) < 0 ∧
      (1861 : ℝ) / 1000 < primitive (1 / 2) (159 / 200) ∧
        primitive (1 / 2) (159 / 200) < 1862 / 1000 := by
  have hl := sample_witness_bounds ⟨0, by omega⟩
  have hr := sample_witness_bounds ⟨1, by omega⟩
  have hm := sample_primitive_bounds ⟨2, by omega⟩
  norm_num [samples, piLower, piUpper] at hl hr hm ⊢
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hl.1, hr.2, hm.1, hm.2]

end
end StructuralNote.FixedDualTaylorRow79

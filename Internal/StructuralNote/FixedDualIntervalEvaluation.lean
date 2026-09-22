import StructuralNote.FixedDualTaylorRow79

/-! Sign-independent interval evaluation and a logarithm scaling rule. -/

namespace StructuralNote.FixedDualIntervalEvaluation

open Real FixedDualPrimitive FixedDualIntervals FixedDualTaylorBounds
open FixedDualTaylorRow79
noncomputable section

theorem scalar_interval {x l u b : ℝ} (hx : l ≤ x ∧ x ≤ u) :
    min (b * l) (b * u) ≤ b * x ∧ b * x ≤ max (b * l) (b * u) := by
  by_cases hb : 0 ≤ b
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hx.1 hb),
      (mul_le_mul_of_nonneg_left hx.2 hb).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hx.2 (le_of_not_ge hb)),
      (mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge hb)).trans (le_max_left _ _)⟩

theorem positive_arbitrary_mul_bounds {x y xl xu yl yu : ℝ}
    (hx : xl ≤ x ∧ x ≤ xu) (hy : yl ≤ y ∧ y ≤ yu) (hxl : 0 ≤ xl) :
    min (xl * yl) (xu * yl) ≤ x * y ∧
      x * y ≤ max (xl * yu) (xu * yu) := by
  have hp : 0 ≤ x := hxl.trans hx.1
  have hl := (scalar_interval (b := yl) hx).1
  have hu := (scalar_interval (b := yu) hx).2
  simp only [mul_comm yl, mul_comm yu] at hl hu
  exact ⟨hl.trans (mul_le_mul_of_nonneg_left hy.1 hp),
    (mul_le_mul_of_nonneg_left hy.2 hp).trans hu⟩

set_option maxRecDepth 8192 in
theorem precise_log_two :
    (693147180 : ℝ) / 1000000000 ≤ log 2 ∧ log 2 ≤ 693147181 / 1000000000 := by
  apply logarithm_interval (by norm_num) 12
  all_goals norm_num [logPolynomial, logError, logCoordinate, Finset.sum_range_succ]

theorem scaled_logarithm_interval {x l u : ℝ} (hx : 0 < x) (k n : ℕ)
    (hl : l ≤ logPolynomial n (2 ^ k * x) - logError n (2 ^ k * x) -
      k * (693147181 / 1000000000 : ℝ))
    (hu : logPolynomial n (2 ^ k * x) + logError n (2 ^ k * x) -
      k * (693147180 / 1000000000 : ℝ) ≤ u) :
    l ≤ log x ∧ log x ≤ u := by
  have h := abs_le.mp (logarithm_taylor_bound (by positivity : 0 < 2 ^ k * x) n)
  have he : log (2 ^ k * x) = k * log 2 + log x := by
    rw [log_mul (by positivity) hx.ne', log_pow]
  rw [he] at h
  have hlo := mul_le_mul_of_nonneg_left precise_log_two.1 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hhi := mul_le_mul_of_nonneg_left precise_log_two.2 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  constructor <;> linarith [h.1, h.2]

def witnessLower (b : ℝ) (r : Sample) : ℝ :=
  r.dl + min (b * r.tl) (b * r.tu) + min (r.cl * (1 + r.ll)) (r.cu * (1 + r.ll)) -
    (piUpper / 2 - r.x) * r.su

def witnessUpper (b : ℝ) (r : Sample) : ℝ :=
  r.du + max (b * r.tl) (b * r.tu) + max (r.cl * (1 + r.lu)) (r.cu * (1 + r.lu)) -
    (piLower / 2 - r.x) * r.sl

def primitiveLower (b : ℝ) (r : Sample) : ℝ :=
  r.tl / 3 - max (b * r.dl) (b * r.du) / 3 + min (r.sl * r.ll) (r.su * r.ll) +
    (piLower / 2 - r.x) * r.cl + r.sl

def primitiveUpper (b : ℝ) (r : Sample) : ℝ :=
  r.tu / 3 - min (b * r.dl) (b * r.du) / 3 + max (r.sl * r.lu) (r.su * r.lu) +
    (piUpper / 2 - r.x) * r.cu + r.su

theorem evaluate_sample (b : ℝ) (r : Sample)
    (hx : r.x ≤ piLower / 2) (hs0 : 0 ≤ r.sl) (hc0 : 0 ≤ r.cl)
    (hs : r.sl ≤ sin r.x ∧ sin r.x ≤ r.su)
    (hc : r.cl ≤ cos r.x ∧ cos r.x ≤ r.cu)
    (ht : r.tl ≤ sin (3 * r.x) ∧ sin (3 * r.x) ≤ r.tu)
    (hd : r.dl ≤ cos (3 * r.x) ∧ cos (3 * r.x) ≤ r.du)
    (hl : r.ll ≤ log (2 * sin r.x) ∧ log (2 * sin r.x) ≤ r.lu) :
    (witnessLower b r ≤ witness b r.x ∧ witness b r.x ≤ witnessUpper b r) ∧
    (primitiveLower b r ≤ primitive b r.x ∧ primitive b r.x ≤ primitiveUpper b r) := by
  have hbt := scalar_interval (b := b) ht
  have hbd := scalar_interval (b := b) hd
  have hplus : 1 + r.ll ≤ 1 + log (2 * sin r.x) ∧
      1 + log (2 * sin r.x) ≤ 1 + r.lu := by
    constructor <;> linarith [hl.1, hl.2]
  have hcl := positive_arbitrary_mul_bounds hc hplus hc0
  have hsl := positive_arbitrary_mul_bounds hs hl hs0
  have hv : piLower / 2 - r.x ≤ Real.pi / 2 - r.x ∧
      Real.pi / 2 - r.x ≤ piUpper / 2 - r.x := by
    constructor <;> linarith [pi_bounds.1, pi_bounds.2]
  have hv0 : 0 ≤ piLower / 2 - r.x := sub_nonneg.mpr hx
  have hvs := positive_mul_bounds hv hs hv0 hs0
  have hvc := positive_mul_bounds hv hc hv0 hc0
  dsimp [witnessLower, witnessUpper, primitiveLower, primitiveUpper]
  rw [witness_expand]
  unfold primitive
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    linarith [hd.1, hd.2, ht.1, ht.2, hs.1, hs.2, hbt.1, hbt.2, hbd.1, hbd.2,
      hcl.1, hcl.2, hsl.1, hsl.2, hvs.1, hvs.2, hvc.1, hvc.2]

end
end StructuralNote.FixedDualIntervalEvaluation

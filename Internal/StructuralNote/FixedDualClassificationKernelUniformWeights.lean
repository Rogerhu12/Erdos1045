import EventualExact.SchurWeightBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Monotonicity of the actual finite Schur weights on the lower half of the spectrum. -/

namespace StructuralNote.FixedDualClassificationKernelUniformWeights

open Real Set Erdos1045.EventualExact
noncomputable section

def slope (x : ℝ) : ℝ := 1 / x - cos x / sin x

theorem slope_hasDerivAt {x : ℝ} (hx : x ∈ Ioo 0 Real.pi) :
    HasDerivAt slope (1 / sin x ^ 2 - 1 / x ^ 2) x := by
  have hs := (sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne'
  have hd := ((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx.1.ne').sub
    ((hasDerivAt_cos x).div (hasDerivAt_sin x) hs)
  convert hd using 1 <;> try rfl
  simp only [id_eq]
  field_simp [hs, hx.1.ne']
  nlinarith [sin_sq_add_cos_sq x]

theorem slope_derivative_nonneg {x : ℝ} (hx : x ∈ Ioo 0 Real.pi) :
    0 ≤ 1 / sin x ^ 2 - 1 / x ^ 2 := by
  have hs := sin_pos_of_pos_of_lt_pi hx.1 hx.2
  exact sub_nonneg.mpr (one_div_le_one_div_of_le (sq_pos_of_pos hs) (sin_sq_le_sq (x := x)))

theorem slope_monotone : MonotoneOn slope (Ioo 0 Real.pi) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => 1 / sin x ^ 2 - 1 / x ^ 2)
    (convex_Ioo 0 Real.pi)
  · intro x hx
    exact (slope_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (slope_hasDerivAt (interior_subset hx)).hasDerivWithinAt
  · intro x hx
    exact slope_derivative_nonneg (interior_subset hx)

def reciprocalSinc (x : ℝ) : ℝ := x / sin x

theorem reciprocalSinc_pos {x : ℝ} (hx : x ∈ Ioo 0 Real.pi) :
    0 < reciprocalSinc x := div_pos hx.1 (sin_pos_of_pos_of_lt_pi hx.1 hx.2)

theorem reciprocalSinc_hasDerivAt {x : ℝ} (hx : x ∈ Ioo 0 Real.pi) :
    HasDerivAt reciprocalSinc (reciprocalSinc x * slope x) x := by
  have hs := (sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne'
  have hd := (hasDerivAt_id x).div (hasDerivAt_sin x) hs
  convert hd using 1 <;> try rfl
  dsimp only [reciprocalSinc, slope, id_eq]
  field_simp [hs, hx.1.ne']

def symmetricCore (L x : ℝ) : ℝ := reciprocalSinc x * reciprocalSinc (L - x)

theorem symmetricCore_hasDerivAt {L x : ℝ}
    (hx : x ∈ Ioo 0 Real.pi) (hy : L - x ∈ Ioo 0 Real.pi) :
    HasDerivAt (symmetricCore L) (symmetricCore L x * (slope x - slope (L - x))) x := by
  have hd := (reciprocalSinc_hasDerivAt hx).mul
    ((reciprocalSinc_hasDerivAt hy).comp x ((hasDerivAt_const x L).sub (hasDerivAt_id x)))
  convert hd using 1 <;> try rfl
  dsimp only [symmetricCore, Function.comp_apply]
  ring

theorem symmetricCore_antitone {L : ℝ} (hL : L ∈ Ioo 0 Real.pi) :
    AntitoneOn (symmetricCore L) (Ioc 0 (L / 2)) := by
  have hi {x : ℝ} (hx : x ∈ Ioc 0 (L / 2)) :
      x ∈ Ioo 0 Real.pi ∧ L - x ∈ Ioo 0 Real.pi ∧ x ≤ L - x := by
    exact ⟨⟨hx.1, by linarith [hx.2, hL.2, pi_pos]⟩,
      ⟨by linarith [hx.2, hL.1], by linarith [hx.1, hL.2]⟩, by linarith [hx.2]⟩
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun x => symmetricCore L x * (slope x - slope (L - x))) (convex_Ioc 0 (L / 2))
  · intro x hx
    exact (symmetricCore_hasDerivAt (hi hx).1 (hi hx).2.1).continuousAt.continuousWithinAt
  · intro x hx
    exact (symmetricCore_hasDerivAt (hi (interior_subset hx)).1
      (hi (interior_subset hx)).2.1).hasDerivWithinAt
  · intro x hx
    obtain ⟨h1, h2, h12⟩ := hi (interior_subset hx)
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact (mul_pos (reciprocalSinc_pos h1) (reciprocalSinc_pos h2)).le
    · exact sub_nonpos.mpr (slope_monotone h1 h2 h12)

theorem weight_eq_symmetricCore {n p : ℕ} (hp : SchurWeights.Active n p) :
    SchurWeights.weight n p =
      (sin (Real.pi / n) ^ 2 / ((n : ℝ) * (Real.pi / n) ^ 2)) *
        symmetricCore (((n : ℝ) - 2) * (Real.pi / n)) (((p : ℝ) - 1) * (Real.pi / n)) := by
  have hnR := (SchurWeights.active_bounds hp).1
  have ha : Real.pi / (n : ℝ) ≠ 0 := div_ne_zero pi_pos.ne' hnR.ne'
  have he : ((n : ℝ) - 2) * (Real.pi / n) - ((p : ℝ) - 1) * (Real.pi / n) =
      Real.pi - ((p : ℝ) + 1) * (Real.pi / n) := by
    field_simp
    ring
  rw [symmetricCore, reciprocalSinc, reciprocalSinc, he, sin_pi_sub]
  rw [show Real.pi - ((p : ℝ) + 1) * (Real.pi / n) =
      ((n : ℝ) - p - 1) * (Real.pi / n) by field_simp; ring]
  rw [SchurWeights.weight, if_pos hp]
  rw [show ((p : ℝ) - 1) * Real.pi / n = ((p : ℝ) - 1) * (Real.pi / n) by ring,
    show ((p : ℝ) + 1) * Real.pi / n = ((p : ℝ) + 1) * (Real.pi / n) by ring]
  field_simp

theorem weight_antitone_lower_half {n p q : ℕ}
    (hp : SchurWeights.Active n p) (hq : SchurWeights.Active n q)
    (hpq : p ≤ q) (hqn : 2 * q ≤ n) : SchurWeights.weight n q ≤ SchurWeights.weight n p := by
  have hnR := (SchurWeights.active_bounds hp).1
  have ha : 0 < Real.pi / (n : ℝ) := div_pos pi_pos hnR
  have hn3 : (3 : ℝ) < n := by have := hp.2.1; have := hp.2.2; exact_mod_cast (show 3 < n by omega)
  have hL : ((n : ℝ) - 2) * (Real.pi / n) ∈ Ioo 0 Real.pi := by
    constructor
    · exact mul_pos (by linarith) ha
    · rw [← mul_div_assoc]
      apply (div_lt_iff₀ hnR).mpr
      nlinarith [pi_pos]
  have hqR : 2 * (q : ℝ) ≤ n := by exact_mod_cast hqn
  have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp.2.1
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq.2.1
  have hx : ((p : ℝ) - 1) * (Real.pi / n) ∈ Ioc 0 (((n : ℝ) - 2) * (Real.pi / n) / 2) := by
    constructor
    · exact mul_pos (by linarith) ha
    · nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 * p by linarith) ha.le]
  have hy : ((q : ℝ) - 1) * (Real.pi / n) ∈ Ioc 0 (((n : ℝ) - 2) * (Real.pi / n) / 2) := by
    constructor
    · exact mul_pos (by linarith) ha
    · nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 * q by linarith) ha.le]
  have h := symmetricCore_antitone hL hx hy
    (mul_le_mul_of_nonneg_right (by linarith : (p : ℝ) - 1 ≤ q - 1) ha.le)
  rw [weight_eq_symmetricCore hp, weight_eq_symmetricCore hq]
  exact mul_le_mul_of_nonneg_left h (by positivity)

end
end StructuralNote.FixedDualClassificationKernelUniformWeights

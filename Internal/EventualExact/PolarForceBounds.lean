import EventualExact.PolarLogPotential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Quantitative bounds for the actual radial and angular polar-force errors. -/

noncomputable section

open scoped BigOperators

namespace Erdos1045.EventualExact

theorem abs_sinh_le_two_mul_abs {y : ℝ} (hy : |y| ≤ 1) :
    |Real.sinh y| ≤ 2 * |y| := by
  have hp := (abs_le.mp (Real.abs_exp_sub_one_le hy))
  have hm := (abs_le.mp (Real.abs_exp_sub_one_le (x := -y) (by simpa using hy)))
  rw [Real.sinh_eq]
  rw [abs_le]
  simp only [abs_neg] at hm
  constructor <;> linarith

theorem cosh_sub_one_le_sq {y : ℝ} (hy : |y| ≤ 1) :
    Real.cosh y - 1 ≤ y ^ 2 := by
  have hp := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hy)).2
  have hm := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := -y) (by simpa using hy))).2
  rw [Real.cosh_eq]
  nlinarith

theorem one_sub_cos_lower_quadratic {x : ℝ} (hx : |x| ≤ Real.pi) :
    2 * x ^ 2 / Real.pi ^ 2 ≤ 1 - Real.cos x := by
  have hc := Real.cos_le_one_sub_mul_cos_sq hx
  have he : 2 / Real.pi ^ 2 * x ^ 2 = 2 * x ^ 2 / Real.pi ^ 2 := by ring
  rw [he] at hc
  linarith

theorem polarDenominator_lower_quadratic (y : ℝ) {x : ℝ} (hx : |x| ≤ Real.pi) :
    2 * x ^ 2 / Real.pi ^ 2 ≤ polarDenominator y x :=
  (one_sub_cos_lower_quadratic hx).trans (polarDenominator_ge y x)

theorem polar_small_radial_argument {ε x y : ℝ} (hε : 0 ≤ ε) (hx : |x| ≤ Real.pi)
    (hy : |y| ≤ ε * |x|) (hsmall : ε * Real.pi ≤ 1) : |y| ≤ 1 :=
  hy.trans ((mul_le_mul_of_nonneg_left hx hε).trans hsmall)

/-- The first pointwise error has the exact admissible constant `pi²`. -/
theorem polarRadialCorrection_bound {ε x y : ℝ} (hε : 0 ≤ ε)
    (hx : |x| ≤ Real.pi) (hx0 : x ≠ 0) (hy : |y| ≤ ε * |x|)
    (hsmall : ε * Real.pi ≤ 1) :
    |polarRadialCorrection y x| ≤ Real.pi ^ 2 * ε / |x| := by
  have ha : 0 < |x| := abs_pos.mpr hx0
  have hq : 0 < 2 * x ^ 2 / Real.pi ^ 2 := by positivity
  have hD := polarDenominator_lower_quadratic y hx
  have hDpos := lt_of_lt_of_le hq hD
  have hsin : |Real.sinh y| ≤ 2 * ε * |x| := by
    have hh := abs_sinh_le_two_mul_abs (polar_small_radial_argument hε hx hy hsmall)
    nlinarith
  rw [polarRadialCorrection, abs_div, abs_of_pos hDpos]
  calc
    _ ≤ (2 * ε * |x|) / (2 * x ^ 2 / Real.pi ^ 2) :=
      div_le_div₀ (by positivity) hsin hq hD
    _ = _ := by rw [← sq_abs x]; field_simp

/-- A slightly relaxed `pi⁴` bound avoids any numerical certificate. -/
theorem polarAngularCorrection_bound {ε x y : ℝ} (hε : 0 ≤ ε)
    (hx : |x| ≤ Real.pi) (hx0 : x ≠ 0) (hy : |y| ≤ ε * |x|)
    (hsmall : ε * Real.pi ≤ 1) :
    |polarAngularCorrection y x| ≤ Real.pi ^ 4 * ε ^ 2 / |x| := by
  have ha : 0 < |x| := abs_pos.mpr hx0
  have hq : 0 < 2 * x ^ 2 / Real.pi ^ 2 := by positivity
  have hc := one_sub_cos_lower_quadratic hx
  have hD := polarDenominator_lower_quadratic y hx
  have hcpos := lt_of_lt_of_le hq hc
  have hDpos := lt_of_lt_of_le hq hD
  have hh0 : 0 ≤ Real.cosh y - 1 := sub_nonneg.mpr (Real.one_le_cosh y)
  have hh : Real.cosh y - 1 ≤ ε ^ 2 * x ^ 2 := by
    have hsq : y ^ 2 ≤ (ε * |x|) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hy) (by positivity : 0 ≤ ε * |x| + |y|), sq_abs y]
    have hsmall' := cosh_sub_one_le_sq (polar_small_radial_argument hε hx hy hsmall)
    nlinarith [sq_abs x]
  have hnum : |Real.sin x| * (Real.cosh y - 1) ≤ ε ^ 2 * |x| * x ^ 2 := by
    have hm := mul_le_mul (Real.abs_sin_le_abs (x := x)) hh hh0 (abs_nonneg x)
    nlinarith
  have hden : (2 * x ^ 2 / Real.pi ^ 2) ^ 2 ≤
      (1 - Real.cos x) * polarDenominator y x := by
    simpa only [pow_two] using mul_le_mul hc hD hq.le hcpos.le
  rw [polarAngularCorrection, abs_div, abs_mul, abs_of_nonneg hh0,
    abs_of_pos (mul_pos hcpos hDpos)]
  calc
    _ ≤ (ε ^ 2 * |x| * x ^ 2) / (2 * x ^ 2 / Real.pi ^ 2) ^ 2 :=
      div_le_div₀ (by positivity) hnum (sq_pos_of_pos hq) hden
    _ = Real.pi ^ 4 * ε ^ 2 / (4 * |x|) := by rw [← sq_abs x]; field_simp; ring
    _ ≤ Real.pi ^ 4 * ε ^ 2 / |x| := by
      apply div_le_div_of_nonneg_left (by positivity) ha
      linarith

section Finite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An explicit reciprocal angular-separation sum; no harmonic estimate is assumed. -/
def polarInverseDistanceSum (x : ι → ℝ) (i : ι) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, 1 / |x j|

theorem polarInverseDistanceSum_nonneg (x : ι → ℝ) (i : ι) :
    0 ≤ polarInverseDistanceSum x i := Finset.sum_nonneg fun _ _ => by positivity

/-- Angle representatives are allowed to differ from the original lifts by full turns. -/
theorem polar_correction_sums_bounds {height θ x : ι → ℝ} (i : ι) {ε : ℝ}
    (hε : 0 ≤ ε) (hsmall : ε * Real.pi ≤ 1)
    (hx : ∀ j, j ≠ i → |x j| ≤ Real.pi)
    (hx0 : ∀ j, j ≠ i → x j ≠ 0)
    (hy : ∀ j, j ≠ i → |height i - height j| ≤ ε * |x j|)
    (hcos : ∀ j, j ≠ i → Real.cos (x j) = Real.cos (θ i - θ j))
    (hsin : ∀ j, j ≠ i → Real.sin (x j) = Real.sin (θ i - θ j)) :
    |polarRadialSum height θ i| ≤ Real.pi ^ 2 * ε * polarInverseDistanceSum x i ∧
    |polarAngularSum height θ i| ≤ Real.pi ^ 4 * ε ^ 2 * polarInverseDistanceSum x i := by
  have hr : ∀ j ∈ Finset.univ.erase i,
      |polarRadialCorrection (height i - height j) (θ i - θ j)| ≤ Real.pi ^ 2 * ε / |x j| := by
    intro j hj
    have hn := (Finset.mem_erase.mp hj).1
    have hb := polarRadialCorrection_bound hε (hx j hn) (hx0 j hn) (hy j hn) hsmall
    simpa only [polarRadialCorrection, polarDenominator, hcos j hn] using hb
  have ha : ∀ j ∈ Finset.univ.erase i,
      |polarAngularCorrection (height i - height j) (θ i - θ j)| ≤ Real.pi ^ 4 * ε ^ 2 / |x j| := by
    intro j hj
    have hn := (Finset.mem_erase.mp hj).1
    have hb := polarAngularCorrection_bound hε (hx j hn) (hx0 j hn) (hy j hn) hsmall
    simpa only [polarAngularCorrection, polarDenominator, hcos j hn, hsin j hn] using hb
  constructor
  · unfold polarRadialSum polarInverseDistanceSum
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, |polarRadialCorrection (height i - height j) (θ i - θ j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.univ.erase i, Real.pi ^ 2 * ε / |x j| := Finset.sum_le_sum hr
      _ = _ := by rw [Finset.mul_sum]; congr 1; funext j; ring
  · unfold polarAngularSum polarInverseDistanceSum
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, |polarAngularCorrection (height i - height j) (θ i - θ j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.univ.erase i, Real.pi ^ 4 * ε ^ 2 / |x j| := Finset.sum_le_sum ha
      _ = _ := by rw [Finset.mul_sum]; congr 1; funext j; ring

/-- The exact stationary force gives a quantitative error, retaining the sampled slope. -/
theorem polar_force_stationarity_bound {height θ x : ι → ℝ} (i : ι) {ε s : ℝ}
    (hε : 0 ≤ ε) (hsmall : ε * Real.pi ≤ 1)
    (hx : ∀ j, j ≠ i → |x j| ≤ Real.pi)
    (hx0 : ∀ j, j ≠ i → x j ≠ 0)
    (hy : ∀ j, j ≠ i → |height i - height j| ≤ ε * |x j|)
    (hcos : ∀ j, j ≠ i → Real.cos (x j) = Real.cos (θ i - θ j))
    (hsin : ∀ j, j ≠ i → Real.sin (x j) = Real.sin (θ i - θ j))
    (hstat : polarForceExpression height θ i s = 0) :
    |polarForce θ i + (1 - 1 / Fintype.card ι) * s| ≤
      (Real.pi ^ 2 * ε * |s| + Real.pi ^ 4 * ε ^ 2) *
        polarInverseDistanceSum x i / Fintype.card ι := by
  have hn : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr (Nonempty.intro i)
  have hb := polar_correction_sums_bounds i hε hsmall hx hx0 hy hcos hsin
  have he : polarForce θ i + (1 - 1 / Fintype.card ι) * s =
      (polarAngularSum height θ i - s * polarRadialSum height θ i) / Fintype.card ι := by
    unfold polarForceExpression at hstat
    apply (eq_div_iff (ne_of_gt hn)).2
    field_simp
    linarith
  rw [he, abs_div, abs_of_pos hn]
  apply div_le_div_of_nonneg_right ?_ hn.le
  calc
    _ ≤ |polarAngularSum height θ i| + |s * polarRadialSum height θ i| := by
      simpa using abs_sub_le (polarAngularSum height θ i) 0 (s * polarRadialSum height θ i)
    _ = |polarAngularSum height θ i| + |s| * |polarRadialSum height θ i| := by rw [abs_mul]
    _ ≤ Real.pi ^ 4 * ε ^ 2 * polarInverseDistanceSum x i +
        |s| * (Real.pi ^ 2 * ε * polarInverseDistanceSum x i) :=
      add_le_add hb.2 (mul_le_mul_of_nonneg_left hb.1 (abs_nonneg s))
    _ = _ := by ring

omit [DecidableEq ι] in
/-- A finite square budget from pointwise slope-sensitive force errors. -/
theorem finite_force_square_budget {f s : ι → ℝ} {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : |c| ≤ 1)
    (herr : ∀ i, |f i + c * s i| ≤ a * |s i| + b) :
    (∑ i, (f i) ^ 2) ≤ 2 * (1 + a) ^ 2 * (∑ i, (s i) ^ 2) +
      2 * Fintype.card ι * b ^ 2 := by
  have hi : ∀ i, (f i) ^ 2 ≤ 2 * (1 + a) ^ 2 * (s i) ^ 2 + 2 * b ^ 2 := by
    intro i
    have hf : |f i| ≤ (1 + a) * |s i| + b := by
      have htri : |f i| ≤ |f i + c * s i| + |c * s i| := by
        simpa using abs_sub_le (f i + c * s i) 0 (c * s i)
      rw [abs_mul] at htri
      have hm := mul_le_mul_of_nonneg_right hc (abs_nonneg (s i))
      nlinarith [herr i]
    have hsq : (f i) ^ 2 ≤ ((1 + a) * |s i| + b) ^ 2 := by
      nlinarith [sq_abs (f i), mul_nonneg (sub_nonneg.mpr hf)
        (by positivity : 0 ≤ (1 + a) * |s i| + b + |f i|)]
    nlinarith [sq_nonneg ((1 + a) * |s i| - b), sq_abs (s i)]
  calc
    _ ≤ ∑ i, (2 * (1 + a) ^ 2 * (s i) ^ 2 + 2 * b ^ 2) := Finset.sum_le_sum fun i _ => hi i
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      ring

end Finite

end Erdos1045.EventualExact

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Polar logarithmic distance and the affine force expression

These are identities and derivative formulas for the actual complex polar curve.
The final slope selection is algebraic and does not assume differentiability at
a corner of a convex boundary.
-/

noncomputable section

open scoped BigOperators

namespace Erdos1045.EventualExact

def polarPoint (h θ : ℝ) : ℂ := (Real.exp h : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

def polarDenominator (y x : ℝ) : ℝ := Real.cosh y - Real.cos x

theorem polarDenominator_ge (y x : ℝ) : 1 - Real.cos x ≤ polarDenominator y x := by
  have := Real.one_le_cosh y
  unfold polarDenominator
  linarith

theorem polarDenominator_pos {y x : ℝ} (hx : Real.cos x < 1) :
    0 < polarDenominator y x :=
  lt_of_lt_of_le (sub_pos.mpr hx) (polarDenominator_ge y x)

theorem polarPoint_distance_sq_cartesian (h k θ φ : ℝ) :
    ‖polarPoint h θ - polarPoint k φ‖ ^ 2 =
      Real.exp h ^ 2 + Real.exp k ^ 2 - 2 * Real.exp h * Real.exp k * Real.cos (θ - φ) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  simp [polarPoint, Complex.normSq_eq_norm_sq, Complex.exp_ofReal_re, Real.cos_sub]
  ring

theorem polar_exp_cosh (h k : ℝ) :
    2 * Real.exp (h + k) * Real.cosh (h - k) = Real.exp h ^ 2 + Real.exp k ^ 2 := by
  have h₁ : Real.exp (h + k) * Real.exp (h - k) = Real.exp h ^ 2 := by
    rw [← Real.exp_add]
    convert Real.exp_add h h using 1 <;> congr 1 <;> ring
  have h₂ : Real.exp (h + k) * Real.exp (-(h - k)) = Real.exp k ^ 2 := by
    rw [← Real.exp_add]
    convert Real.exp_add k k using 1 <;> congr 1 <;> ring
  rw [Real.cosh_eq]
  nlinarith

/-- The exact complex distance formula (2.15). -/
theorem polarPoint_distance_sq (h k θ φ : ℝ) :
    ‖polarPoint h θ - polarPoint k φ‖ ^ 2 =
      2 * Real.exp (h + k) * polarDenominator (h - k) (θ - φ) := by
  rw [polarPoint_distance_sq_cartesian]
  have he := polar_exp_cosh h k
  rw [Real.exp_add] at he ⊢
  unfold polarDenominator
  nlinarith

theorem log_polarPoint_distance_sq {h k θ φ : ℝ}
    (hD : polarDenominator (h - k) (θ - φ) ≠ 0) :
    Real.log (‖polarPoint h θ - polarPoint k φ‖ ^ 2) =
      Real.log 2 + h + k + Real.log (polarDenominator (h - k) (θ - φ)) := by
  rw [polarPoint_distance_sq, Real.log_mul (mul_ne_zero (by norm_num) (Real.exp_ne_zero _)) hD,
    Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem hasDerivAt_polarDenominator {h : ℝ → ℝ} {t s k φ : ℝ}
    (hh : HasDerivAt h s t) :
    HasDerivAt (fun u => polarDenominator (h u - k) (u - φ))
      (s * Real.sinh (h t - k) + Real.sin (t - φ)) t := by
  simpa [polarDenominator, mul_comm] using
    ((hh.sub_const k).cosh).fun_sub (((hasDerivAt_id t).sub_const φ).cos)

/-- The first derivative of the logarithm of actual squared Euclidean distance. -/
theorem hasDerivAt_log_polarPoint_distance_sq {h : ℝ → ℝ} {t s k φ : ℝ}
    (hh : HasDerivAt h s t) (hD : polarDenominator (h t - k) (t - φ) ≠ 0) :
    HasDerivAt (fun u => Real.log (‖polarPoint (h u) u - polarPoint k φ‖ ^ 2))
      (s + (s * Real.sinh (h t - k) + Real.sin (t - φ)) /
        polarDenominator (h t - k) (t - φ)) t := by
  have he := ((hh.add_const k).exp).const_mul 2
  have hd := hasDerivAt_polarDenominator hh (k := k) (φ := φ)
  have hlog := (he.mul hd).log
    (mul_ne_zero (mul_ne_zero (by norm_num) (Real.exp_ne_zero _)) hD)
  dsimp only [Pi.mul_apply] at hlog
  convert hlog using 1
  · funext u
    rw [polarPoint_distance_sq]
  · field_simp

/-- The same denominator calculation works for a one-sided radial derivative. -/
theorem hasDerivWithinAt_polarDenominator {h : ℝ → ℝ} {U : Set ℝ} {t s k φ : ℝ}
    (hh : HasDerivWithinAt h s U t) :
    HasDerivWithinAt (fun u => polarDenominator (h u - k) (u - φ))
      (s * Real.sinh (h t - k) + Real.sin (t - φ)) U t := by
  have hid : HasDerivWithinAt (fun u : ℝ => u) 1 U t := (hasDerivAt_id t).hasDerivWithinAt
  simpa [polarDenominator, mul_comm] using
    ((hh.sub_const k).cosh).fun_sub ((hid.sub_const φ).cos)

/-- A one-sided formula, available even when the two radial slopes differ. -/
theorem hasDerivWithinAt_log_polarPoint_distance_sq {h : ℝ → ℝ} {U : Set ℝ} {t s k φ : ℝ}
    (hh : HasDerivWithinAt h s U t) (hD : polarDenominator (h t - k) (t - φ) ≠ 0) :
    HasDerivWithinAt (fun u => Real.log (‖polarPoint (h u) u - polarPoint k φ‖ ^ 2))
      (s + (s * Real.sinh (h t - k) + Real.sin (t - φ)) /
        polarDenominator (h t - k) (t - φ)) U t := by
  have he := ((hh.add_const k).exp).const_mul 2
  have hd := hasDerivWithinAt_polarDenominator hh (k := k) (φ := φ)
  have hlog := (he.mul hd).log
    (mul_ne_zero (mul_ne_zero (by norm_num) (Real.exp_ne_zero _)) hD)
  dsimp only [Pi.mul_apply] at hlog
  convert hlog using 1
  · funext u
    rw [polarPoint_distance_sq]
  · field_simp

theorem one_sub_cos_eq_two_sin_sq (x : ℝ) :
    1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
  have hc := Real.cos_two_mul (x / 2)
  have hs := Real.sin_sq_add_cos_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hc
  nlinarith

theorem sin_div_one_sub_cos {x : ℝ} (hx : 1 - Real.cos x ≠ 0) :
    Real.sin x / (1 - Real.cos x) = Real.cot (x / 2) := by
  have hhalf : Real.sin (x / 2) ≠ 0 := by
    intro he
    apply hx
    rw [one_sub_cos_eq_two_sin_sq, he]
    norm_num
  have hs := Real.sin_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hs
  rw [one_sub_cos_eq_two_sin_sq, hs, Real.cot_eq_cos_div_sin]
  field_simp

/-- The cotangent separation keeps the entire radial error exactly. -/
theorem polar_sin_quotient_split {y x : ℝ} (hx : 1 - Real.cos x ≠ 0)
    (hD : polarDenominator y x ≠ 0) :
    Real.sin x / polarDenominator y x = Real.cot (x / 2) -
      Real.sin x * (Real.cosh y - 1) / ((1 - Real.cos x) * polarDenominator y x) := by
  rw [← sin_div_one_sub_cos hx]
  unfold polarDenominator at *
  field_simp
  ring

def polarRadialCorrection (y x : ℝ) : ℝ := Real.sinh y / polarDenominator y x

def polarAngularCorrection (y x : ℝ) : ℝ :=
  Real.sin x * (Real.cosh y - 1) / ((1 - Real.cos x) * polarDenominator y x)

theorem polar_log_derivative_split {s y x : ℝ} (hx : 1 - Real.cos x ≠ 0)
    (hD : polarDenominator y x ≠ 0) :
    s + (s * Real.sinh y + Real.sin x) / polarDenominator y x =
      Real.cot (x / 2) + s + s * polarRadialCorrection y x - polarAngularCorrection y x := by
  rw [add_div, polar_sin_quotient_split hx hD]
  unfold polarRadialCorrection polarAngularCorrection
  ring

section Finite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def polarForce (θ : ι → ℝ) (i : ι) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, Real.cot ((θ i - θ j) / 2)) / Fintype.card ι

def polarRadialSum (h θ : ι → ℝ) (i : ι) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, polarRadialCorrection (h i - h j) (θ i - θ j)

def polarAngularSum (h θ : ι → ℝ) (i : ι) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, polarAngularCorrection (h i - h j) (θ i - θ j)

def polarForceExpression (h θ : ι → ℝ) (i : ι) (s : ℝ) : ℝ :=
  Fintype.card ι * polarForce θ i + (Fintype.card ι - 1 : ℝ) * s +
    s * polarRadialSum h θ i - polarAngularSum h θ i

theorem polar_log_derivative_sum {h θ : ι → ℝ} (i : ι) (s : ℝ)
    (hx : ∀ j, j ≠ i → 1 - Real.cos (θ i - θ j) ≠ 0)
    (hD : ∀ j, j ≠ i → polarDenominator (h i - h j) (θ i - θ j) ≠ 0) :
    (∑ j ∈ Finset.univ.erase i,
      (s + (s * Real.sinh (h i - h j) + Real.sin (θ i - θ j)) /
        polarDenominator (h i - h j) (θ i - θ j))) = polarForceExpression h θ i s := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨i⟩))
  have hc : ((Finset.univ.erase i).card : ℝ) = Fintype.card ι - 1 := by
    have hcn : (Finset.univ.erase i).card + 1 = Fintype.card ι := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
      have := Fintype.card_pos_iff.mpr (Nonempty.intro i)
      omega
    have hcr : ((Finset.univ.erase i).card : ℝ) + 1 = Fintype.card ι := by exact_mod_cast hcn
    linarith
  simp_rw [Finset.sum_congr rfl (fun j hj => polar_log_derivative_split
    (hx j (Finset.mem_erase.mp hj).1) (hD j (Finset.mem_erase.mp hj).1))]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, hc, polarForceExpression, polarForce, polarRadialSum, polarAngularSum]
  field_simp

theorem hasDerivAt_polar_log_sum {h : ℝ → ℝ} {height θ : ι → ℝ} (i : ι) {s : ℝ}
    (hh : HasDerivAt h s (θ i)) (hi : h (θ i) = height i)
    (hx : ∀ j, j ≠ i → 1 - Real.cos (θ i - θ j) ≠ 0)
    (hD : ∀ j, j ≠ i → polarDenominator (height i - height j) (θ i - θ j) ≠ 0) :
    HasDerivAt (fun u => ∑ j ∈ Finset.univ.erase i,
      Real.log (‖polarPoint (h u) u - polarPoint (height j) (θ j)‖ ^ 2))
      (polarForceExpression height θ i s) (θ i) := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ.erase i)
    (fun j hj => hasDerivAt_log_polarPoint_distance_sq hh
      (by simpa only [hi] using hD j (Finset.mem_erase.mp hj).1))
  simpa only [hi, polar_log_derivative_sum i s hx hD] using hd

theorem hasDerivWithinAt_polar_log_sum {h : ℝ → ℝ} {U : Set ℝ}
    {height θ : ι → ℝ} (i : ι) {s : ℝ}
    (hh : HasDerivWithinAt h s U (θ i)) (hi : h (θ i) = height i)
    (hx : ∀ j, j ≠ i → 1 - Real.cos (θ i - θ j) ≠ 0)
    (hD : ∀ j, j ≠ i → polarDenominator (height i - height j) (θ i - θ j) ≠ 0) :
    HasDerivWithinAt (fun u => ∑ j ∈ Finset.univ.erase i,
      Real.log (‖polarPoint (h u) u - polarPoint (height j) (θ j)‖ ^ 2))
      (polarForceExpression height θ i s) U (θ i) := by
  have hd := HasDerivWithinAt.fun_sum (u := Finset.univ.erase i)
    (fun j hj => hasDerivWithinAt_log_polarPoint_distance_sq hh
      (by simpa only [hi] using hD j (Finset.mem_erase.mp hj).1))
  simpa only [hi, polar_log_derivative_sum i s hx hD] using hd

end Finite

/-- Endpoint signs of an affine function select a zero between arbitrary endpoints. -/
theorem exists_intermediate_affine_zero {a b l r : ℝ}
    (hl : 0 ≤ a + b * l) (hr : a + b * r ≤ 0) :
    ∃ s ∈ Set.Icc (min l r) (max l r), a + b * s = 0 := by
  by_cases hb : b = 0
  · refine ⟨l, ⟨min_le_left _ _, le_max_left _ _⟩, ?_⟩
    simp only [hb, zero_mul, add_zero] at *
    linarith
  have he : a + b * (-a / b) = 0 := by field_simp; ring
  refine ⟨-a / b, ?_, he⟩
  rcases lt_or_gt_of_ne hb with hbneg | hbpos
  · have hls : l ≤ -a / b := le_of_mul_le_mul_left (by nlinarith) (neg_pos.mpr hbneg)
    have hsr : -a / b ≤ r := le_of_mul_le_mul_left (by nlinarith) (neg_pos.mpr hbneg)
    exact ⟨(min_le_left _ _).trans hls, hsr.trans (le_max_right _ _)⟩
  · have hrs : r ≤ -a / b := le_of_mul_le_mul_left (by nlinarith) hbpos
    have hsl : -a / b ≤ l := le_of_mul_le_mul_left (by nlinarith) hbpos
    exact ⟨(min_le_right _ _).trans hrs, hsl.trans (le_max_left _ _)⟩

theorem exists_intermediate_polar_force_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h θ : ι → ℝ) (i : ι) {l r : ℝ}
    (hl : 0 ≤ polarForceExpression h θ i l)
    (hr : polarForceExpression h θ i r ≤ 0) :
    ∃ s ∈ Set.Icc (min l r) (max l r), polarForceExpression h θ i s = 0 := by
  have he : ∀ s, polarForceExpression h θ i s =
      (Fintype.card ι * polarForce θ i - polarAngularSum h θ i) +
        ((Fintype.card ι - 1 : ℝ) + polarRadialSum h θ i) * s := by
    intro s
    unfold polarForceExpression
    ring
  simp_rw [he] at *
  exact exists_intermediate_affine_zero hl hr

end Erdos1045.EventualExact

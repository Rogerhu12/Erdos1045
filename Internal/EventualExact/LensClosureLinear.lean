import EventualExact.LensAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! The actual lens closure derivative and its two-dimensional linear inverse. -/

namespace Erdos1045.EventualExact.LensClosure

open Complex
open scoped BigOperators
noncomputable section

def unit (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * I)

@[simp] theorem norm_unit (x : ℝ) : ‖unit x‖ = 1 := by simp [unit]

theorem unit_re (x : ℝ) : (unit x).re = Real.cos x := by simp [unit]

theorem unit_im (x : ℝ) : (unit x).im = Real.sin x := by simp [unit]

def midpoint (m : ℕ) (j : Fin m) : ℝ := Real.pi / m * ((j : ℝ) + 1 / 2)

theorem sum_double_midpoint {m : ℕ} (hm : 2 ≤ m) :
    (∑ j : Fin m, Real.cos (2 * midpoint m j)) = 0 ∧
      (∑ j : Fin m, Real.sin (2 * midpoint m j)) = 0 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have ha : 0 < Real.sin ((2 * Real.pi / m) / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [show (2 * Real.pi / m) / 2 = Real.pi / m by ring]
      exact (div_lt_self Real.pi_pos hm1)
  have he : (m : ℝ) * (2 * Real.pi / m) / 2 = Real.pi := by field_simp
  have hc := Real.sin_mul_sum_cos m (2 * Real.pi / m) (Real.pi / m)
  have hs := Real.sin_mul_sum_sin m (2 * Real.pi / m) (Real.pi / m)
  rw [he, Real.sin_pi, zero_mul] at hc hs
  have hc0 := (mul_eq_zero.mp hc).resolve_left ha.ne'
  have hs0 := (mul_eq_zero.mp hs).resolve_left ha.ne'
  have hangle (j : ℕ) : 2 * (Real.pi / m * ((j : ℝ) + 1 / 2)) =
      (2 * Real.pi / m) * j + Real.pi / m := by ring
  constructor
  · simp only [midpoint, hangle]
    rw [← Finset.sum_range (fun j : ℕ => Real.cos ((2 * Real.pi / m) * j + Real.pi / m))]
    exact hc0
  · simp only [midpoint, hangle]
    rw [← Finset.sum_range (fun j : ℕ => Real.sin ((2 * Real.pi / m) * j + Real.pi / m))]
    exact hs0

theorem midpoint_gram {m : ℕ} (hm : 2 ≤ m) :
    (∑ j : Fin m, Real.cos (midpoint m j) ^ 2) = m / 2 ∧
    (∑ j : Fin m, Real.sin (midpoint m j) ^ 2) = m / 2 ∧
    (∑ j : Fin m, Real.cos (midpoint m j) * Real.sin (midpoint m j)) = 0 := by
  obtain ⟨hc, hs⟩ := sum_double_midpoint hm
  have hec : (∑ j : Fin m, Real.cos (2 * midpoint m j)) =
      2 * (∑ j : Fin m, Real.cos (midpoint m j) ^ 2) - m := by
    simp only [Real.cos_two_mul, Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hes : (∑ j : Fin m, Real.sin (2 * midpoint m j)) =
      2 * (∑ j : Fin m, Real.cos (midpoint m j) * Real.sin (midpoint m j)) := by
    simp only [Real.sin_two_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hone : (∑ j : Fin m, Real.cos (midpoint m j) ^ 2) +
      (∑ j : Fin m, Real.sin (midpoint m j) ^ 2) = m := by
    rw [← Finset.sum_add_distrib]
    simp only [Real.cos_sq_add_sin_sq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  constructor
  · linarith
  constructor <;> linarith

def increment (α L s t : ℝ) : ℂ :=
  unit α * (((s * Lens.width L t : ℝ) : ℂ) + (t : ℂ) * I)

def tangent (α s t : ℝ) : ℂ :=
  unit α * (I - ((s * t / Lens.height t : ℝ) : ℂ))

theorem height_hasDerivAt {t : ℝ} (ht : t ^ 2 < 4) :
    HasDerivAt Lens.height (-t / Lens.height t) t := by
  have hd := (((hasDerivAt_id t).pow 2).const_sub 4).sqrt (by dsimp; nlinarith)
  convert hd using 1
  · rfl
  · simp only [Lens.height, id_eq, Pi.pow_apply]
    ring

theorem increment_hasDerivAt (α L s : ℝ) {t : ℝ} (ht : t ^ 2 < 4) :
    HasDerivAt (increment α L s) (tangent α s t) t := by
  have hd := ((((height_hasDerivAt ht).sub_const L).const_mul s).ofReal_comp.fun_add
    ((hasDerivAt_id t).ofReal_comp.mul_const I)).const_mul (unit α)
  convert hd using 1
  · rfl
  · rfl
  · simp only [tangent, ofReal_mul, ofReal_neg, ofReal_div, ofReal_one, one_mul]
    ring

def harmonicFunctional (μ : ℝ) : ℂ →L[ℝ] ℝ :=
  Real.cos μ • Complex.reCLM + Real.sin μ • Complex.imCLM

@[simp] theorem harmonicFunctional_apply (μ : ℝ) (ξ : ℂ) :
    harmonicFunctional μ ξ = Real.cos μ * ξ.re + Real.sin μ * ξ.im := rfl

def heightParameter {m : ℕ} (t : Fin m → ℝ) (ξ : ℂ) (j : Fin m) : ℝ :=
  t j + harmonicFunctional (midpoint m j) ξ

def closure {m : ℕ} (α L s t : Fin m → ℝ) (ξ : ℂ) : ℂ :=
  ∑ j, increment (α j) (L j) (s j) (heightParameter t ξ j)

def closureDerivative {m : ℕ} (α s t : Fin m → ℝ) (ξ : ℂ) : ℂ →L[ℝ] ℂ :=
  ∑ j, (harmonicFunctional (midpoint m j)).smulRight
    (tangent (α j) (s j) (heightParameter t ξ j))

theorem closure_hasFDerivAt {m : ℕ} (α L s t : Fin m → ℝ) (ξ : ℂ)
    (ht : ∀ j, heightParameter t ξ j ^ 2 < 4) :
    HasFDerivAt (closure α L s t) (closureDerivative α s t ξ) ξ := by
  have hd (j : Fin m) : HasFDerivAt
      (fun η => increment (α j) (L j) (s j) (heightParameter t η j))
      ((harmonicFunctional (midpoint m j)).smulRight
        (tangent (α j) (s j) (heightParameter t ξ j))) ξ := by
    have hh : HasFDerivAt (fun η => heightParameter t η j)
        (harmonicFunctional (midpoint m j)) ξ :=
      ((harmonicFunctional (midpoint m j)).hasFDerivAt).const_add (t j)
    convert (increment_hasDerivAt (α j) (L j) (s j) (ht j)).hasFDerivAt.comp ξ hh using 1 <;> rfl
  exact HasFDerivAt.fun_sum (fun j _ => hd j)

def modelDerivative (m : ℕ) : ℂ →L[ℝ] ℂ :=
  ∑ j : Fin m, (harmonicFunctional (midpoint m j)).smulRight (unit (midpoint m j) * I)

theorem harmonicFunctional_le_norm (μ : ℝ) (ξ : ℂ) :
    |harmonicFunctional μ ξ| ≤ ‖ξ‖ := by
  have he : harmonicFunctional μ ξ = ((starRingEnd ℂ) (unit μ) * ξ).re := by
    simp [mul_re, harmonicFunctional_apply, unit_re, unit_im]
  rw [he]
  exact (Complex.abs_re_le_norm _).trans_eq (by simp)

theorem modelDerivative_apply {m : ℕ} (hm : 2 ≤ m) (ξ : ℂ) :
    modelDerivative m ξ = ((m / 2 : ℝ) : ℂ) * I * ξ := by
  obtain ⟨hc, hs, hcs⟩ := midpoint_gram hm
  apply Complex.ext
  · simp only [modelDerivative, sum_apply,
      ContinuousLinearMap.smulRight_apply, Complex.real_smul, Complex.re_sum, mul_re,
      ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one, zero_mul, sub_zero,
      zero_sub, unit_im, harmonicFunctional_apply]
    calc
      _ = -ξ.re * (∑ j : Fin m, Real.cos (midpoint m j) * Real.sin (midpoint m j)) -
          ξ.im * (∑ j : Fin m, Real.sin (midpoint m j) ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hcs, hs]; simp; ring
  · simp only [modelDerivative, sum_apply,
      ContinuousLinearMap.smulRight_apply, Complex.real_smul, Complex.im_sum, mul_im,
      ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one, zero_mul, add_zero,
      unit_re, harmonicFunctional_apply]
    calc
      _ = ξ.re * (∑ j : Fin m, Real.cos (midpoint m j) ^ 2) +
          ξ.im * (∑ j : Fin m, Real.cos (midpoint m j) * Real.sin (midpoint m j)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hc, hcs]; simp; ring

theorem closureDerivative_error {m : ℕ} (α s t : Fin m → ℝ) (ξ v : ℂ)
    {ε : ℝ}
    (herror : ∀ j, ‖tangent (α j) (s j) (heightParameter t ξ j) -
      unit (midpoint m j) * I‖ ≤ ε) :
    ‖closureDerivative α s t ξ v - modelDerivative m v‖ ≤ m * ε * ‖v‖ := by
  have he : closureDerivative α s t ξ v - modelDerivative m v =
      ∑ j, harmonicFunctional (midpoint m j) v •
        (tangent (α j) (s j) (heightParameter t ξ j) - unit (midpoint m j) * I) := by
    simp only [closureDerivative, modelDerivative, sum_apply,
      ContinuousLinearMap.smulRight_apply, ← Finset.sum_sub_distrib, smul_sub]
  rw [he]
  calc
    _ ≤ ∑ j : Fin m, ‖harmonicFunctional (midpoint m j) v •
        (tangent (α j) (s j) (heightParameter t ξ j) - unit (midpoint m j) * I)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, ‖v‖ * ε := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (harmonicFunctional_le_norm _ _) (herror j) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem closureDerivative_lower {m : ℕ} (hm : 2 ≤ m) (α s t : Fin m → ℝ) (ξ v : ℂ)
    (herror : ∀ j, ‖tangent (α j) (s j) (heightParameter t ξ j) -
      unit (midpoint m j) * I‖ ≤ 1 / 4) :
    (m / 4 : ℝ) * ‖v‖ ≤ ‖closureDerivative α s t ξ v‖ := by
  have he := closureDerivative_error α s t ξ v herror
  have hnorm : ‖modelDerivative m v‖ = (m / 2 : ℝ) * ‖v‖ := by
    rw [modelDerivative_apply hm, norm_mul, norm_mul]
    simp
  have ht := norm_sub_le (closureDerivative α s t ξ v)
    (closureDerivative α s t ξ v - modelDerivative m v)
  rw [sub_sub_cancel, hnorm] at ht
  nlinarith

theorem closureDerivative_bijective {m : ℕ} (hm : 2 ≤ m) (α s t : Fin m → ℝ) (ξ : ℂ)
    (herror : ∀ j, ‖tangent (α j) (s j) (heightParameter t ξ j) -
      unit (midpoint m j) * I‖ ≤ 1 / 4) :
    Function.Bijective (closureDerivative α s t ξ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hinj : Function.Injective (closureDerivative α s t ξ) := by
    intro v w hvw
    have h := closureDerivative_lower hm α s t ξ (v - w) herror
    rw [map_sub, hvw, sub_self, norm_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by nlinarith) (norm_nonneg _)))
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

theorem closure_linear_solution {m : ℕ} (hm : 2 ≤ m) (α s t : Fin m → ℝ) (ξ y : ℂ)
    (herror : ∀ j, ‖tangent (α j) (s j) (heightParameter t ξ j) -
      unit (midpoint m j) * I‖ ≤ 1 / 4) :
    ∃! v : ℂ, closureDerivative α s t ξ v = y ∧ ‖v‖ ≤ (4 / m : ℝ) * ‖y‖ := by
  have hbij := closureDerivative_bijective hm α s t ξ herror
  obtain ⟨v, hv⟩ := hbij.surjective y
  refine ⟨v, ⟨hv, ?_⟩, fun w hw => hbij.injective (hw.1.trans hv.symm)⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have h := closureDerivative_lower hm α s t ξ v herror
  rw [hv] at h
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hm0).mpr
  nlinarith

theorem norm_unit_sub_le (α β : ℝ) : ‖unit α - unit β‖ ≤ |α - β| := by
  have he : unit α - unit β = unit β * (Complex.exp (I * ((α - β : ℝ) : ℂ)) - 1) := by
    unfold unit
    rw [mul_sub, ← Complex.exp_add]
    have harg : (β : ℂ) * I + I * ((α - β : ℝ) : ℂ) = (α : ℂ) * I := by
      push_cast
      ring
    rw [harg, mul_one]
  rw [he, norm_mul, norm_unit, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

theorem tangent_error {α μ s t : ℝ} (hs : |s| ≤ 1) (ht : |t| ≤ 1) :
    ‖tangent α s t - unit μ * I‖ ≤ |α - μ| + |t| := by
  have hsq : t ^ 2 ≤ 1 := by nlinarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
  have hJ : 1 ≤ Lens.height t := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 4 - t ^ 2 by linarith)
    simpa [Lens.height] using h
  have hq : |s * t / Lens.height t| ≤ |t| := by
    rw [abs_div, abs_mul, abs_of_pos (by linarith : 0 < Lens.height t)]
    calc
      _ ≤ |t| / Lens.height t := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        nlinarith [mul_nonneg (sub_nonneg.mpr hs) (abs_nonneg t)]
      _ ≤ |t| := div_le_self (abs_nonneg t) hJ
  have he : tangent α s t - unit μ * I =
      (unit α - unit μ) * I - unit α * ((s * t / Lens.height t : ℝ) : ℂ) := by
    unfold tangent
    ring
  rw [he]
  calc
    _ ≤ ‖(unit α - unit μ) * I‖ + ‖unit α * ((s * t / Lens.height t : ℝ) : ℂ)‖ :=
      norm_sub_le _ _
    _ = ‖unit α - unit μ‖ + |s * t / Lens.height t| := by simp [abs_div, abs_mul]
    _ ≤ _ := add_le_add (norm_unit_sub_le α μ) hq

/-- A concrete small angle and height window makes the actual closure derivative invertible. -/
theorem closure_regular {m : ℕ} (hm : 2 ≤ m) (α L s t : Fin m → ℝ) (ξ : ℂ)
    (hs : ∀ j, |s j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |heightParameter t ξ j| ≤ 1 / 4) :
    HasFDerivAt (closure α L s t) (closureDerivative α s t ξ) ξ ∧
      Function.Bijective (closureDerivative α s t ξ) := by
  have ht (j : Fin m) : |heightParameter t ξ j| ≤ 1 := by
    have := hsmall j
    linarith [abs_nonneg (α j - midpoint m j)]
  constructor
  · apply closure_hasFDerivAt
    intro j
    have h := ht j
    nlinarith [(abs_le.mp h).1, (abs_le.mp h).2]
  · apply closureDerivative_bijective hm
    intro j
    exact (tangent_error (hs j) (ht j)).trans (hsmall j)

theorem closure_inverse_bound {m : ℕ} (hm : 2 ≤ m) (α s t : Fin m → ℝ) (ξ y : ℂ)
    (hs : ∀ j, |s j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |heightParameter t ξ j| ≤ 1 / 4) :
    ∃! v : ℂ, closureDerivative α s t ξ v = y ∧ ‖v‖ ≤ (4 / m : ℝ) * ‖y‖ := by
  apply closure_linear_solution hm
  intro j
  have ht : |heightParameter t ξ j| ≤ 1 := by
    have := hsmall j
    linarith [abs_nonneg (α j - midpoint m j)]
  exact (tangent_error (hs j) ht).trans (hsmall j)

theorem increment_constraints {α L s t : ℝ} (hL : 0 ≤ L)
    (ht : t ^ 2 ≤ 4) (hR : 0 < Lens.width L t) :
    (‖(L : ℂ) * unit α + increment α L s t‖ ≤ 2 ∧
      ‖(L : ℂ) * unit α - increment α L s t‖ ≤ 2) ↔ |s| ≤ 1 :=
  Lens.rotated_normalized_constraints_iff (norm_unit α) hL ht hR

/-- Each of the two actual coordinate endpoints activates just its designated cross-edge. -/
theorem increment_endpoint_edges {α L s t : ℝ} (hL : 0 < L)
    (ht : t ^ 2 ≤ 4) (hR : 0 < Lens.width L t) (hs : s = 1 ∨ s = -1) :
    (s = 1 ∧ ‖(L : ℂ) * unit α + increment α L s t‖ = 2 ∧
      ‖(L : ℂ) * unit α - increment α L s t‖ < 2) ∨
    (s = -1 ∧ ‖(L : ℂ) * unit α - increment α L s t‖ = 2 ∧
      ‖(L : ℂ) * unit α + increment α L s t‖ < 2) := by
  have habs : |s| ≤ 1 := by rcases hs with rfl | rfl <;> norm_num
  have hcons := (increment_constraints (α := α) hL.le ht hR).mpr habs
  have hp : ‖(L : ℂ) * unit α + increment α L s t‖ = 2 ↔ s = 1 :=
    Lens.rotated_plus_active_iff (norm_unit α) hL ht hR habs
  have hm : ‖(L : ℂ) * unit α - increment α L s t‖ = 2 ↔ s = -1 :=
    Lens.rotated_minus_active_iff (norm_unit α) hL ht hR habs
  rcases hs with h | h
  · refine Or.inl ⟨h, hp.mpr h, lt_of_le_of_ne hcons.2 ?_⟩
    intro heq
    have := hm.mp heq
    linarith
  · refine Or.inr ⟨h, hm.mpr h, lt_of_le_of_ne hcons.1 ?_⟩
    intro heq
    have := hp.mp heq
    linarith

end
end Erdos1045.EventualExact.LensClosure

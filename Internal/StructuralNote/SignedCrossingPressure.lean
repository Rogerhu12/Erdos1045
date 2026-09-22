import StructuralNote.ActualPressureGap
import EventualExact.PressureSupport
import EventualExact.BoxLensLift

/-! A signed finite expansion of the actual adjacent crossing constraints.
The two angular terms retain their signs; all discarded terms have explicit
nonnegative majorants, ready for the later difference-energy estimates. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.SignedCrossingPressure

open Erdos1045 Erdos1045.EventualExact Complex GapRigidity

def radialSum (a η b₀ b₁ : ℝ) : ℂ :=
  ((1 - b₀ : ℝ) : ℂ) * circle (-(a + η / 2)) +
    ((1 - b₁ : ℝ) : ℂ) * circle (a + η / 2)

def centerStep (η : ℝ) (c₀ c₁ : ℂ) : ℂ :=
  circle (η / 2) * c₁ - circle (-(η / 2)) * c₀

theorem circle_re (t : ℝ) : (circle t).re = Real.cos t := by
  simp [circle, Complex.exp_re]

theorem circle_im (t : ℝ) : (circle t).im = Real.sin t := by
  simp [circle, Complex.exp_im]

theorem radialSum_re (a η b₀ b₁ : ℝ) :
    (radialSum a η b₀ b₁).re = (2 - (b₀ + b₁)) * Real.cos (a + η / 2) := by
  simp only [radialSum, add_re, mul_re, ofReal_re, ofReal_im, zero_mul,
    sub_zero, circle_re, Real.cos_neg]
  ring

theorem radialSum_im (a η b₀ b₁ : ℝ) :
    (radialSum a η b₀ b₁).im = (b₀ - b₁) * Real.sin (a + η / 2) := by
  simp only [radialSum, add_im, mul_im, ofReal_re, ofReal_im, zero_mul,
    add_zero, circle_im, Real.sin_neg]
  ring

theorem centerStep_re (η : ℝ) (c₀ c₁ : ℂ) :
    (centerStep η c₀ c₁).re = Real.cos (η / 2) * (c₁ - c₀).re -
      Real.sin (η / 2) * (c₁ + c₀).im := by
  simp only [centerStep, sub_re, mul_re, circle_re, circle_im,
    Real.cos_neg, Real.sin_neg, add_im]
  ring

theorem circle_mul (s t : ℝ) : circle s * circle t = circle (s + t) :=
  (circle_add s t).symm

/-- The components above are exactly the physical differences in the rotating frame. -/
theorem rotate_actual_center (μ θ₀ θ₁ : ℝ) (c₀ c₁ : ℂ) :
    circle (-(μ + (θ₀ + θ₁) / 2)) * (circle θ₁ * c₁ - circle θ₀ * c₀) =
      centerStep (θ₁ - θ₀) (circle (-μ) * c₀) (circle (-μ) * c₁) := by
  unfold centerStep
  simp only [mul_sub, ← mul_assoc, circle_mul]
  congr 2 <;> congr 1 <;> ring

theorem rotate_actual_radial (μ a θ₀ θ₁ b₀ b₁ : ℝ) :
    circle (-(μ + (θ₀ + θ₁) / 2)) *
      (((1 - b₀ : ℝ) : ℂ) * circle (μ - a + θ₀) +
        ((1 - b₁ : ℝ) : ℂ) * circle (μ + a + θ₁)) =
      radialSum a (θ₁ - θ₀) b₀ b₁ := by
  unfold radialSum
  simp only [mul_add]
  rw [mul_left_comm (circle _) ((1 - b₀ : ℝ) : ℂ),
    mul_left_comm (circle _) ((1 - b₁ : ℝ) : ℂ), circle_mul, circle_mul]
  congr 2 <;> congr 1 <;> ring

theorem cosine_fourth_upper (x : ℝ) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  suffices hp : ∀ t : ℝ, 0 ≤ t → Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 by
    rcases le_total 0 x with hx | hx
    · exact hp x hx
    · simpa only [Real.cos_neg, even_two.neg_pow, Even.neg_pow (by decide : Even 4)] using hp (-x) (by linarith)
  intro t ht
  let f (s : ℝ) := 1 - s ^ 2 / 2 + s ^ 4 / 24 - Real.cos s
  have hd (s : ℝ) : deriv f s = -s + s ^ 3 / 6 + Real.sin s := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro s hs
    rw [hd]
    have hs0 : 0 ≤ s := by
      have hp : 0 < s := by simpa only [interior_Ici, Set.mem_Ioi] using hs
      exact hp.le
    linarith [Real.sin_ge_sub_cube hs0]
  have h := hm (by simp) ht ht
  dsimp [f] at h
  norm_num at h
  linarith

theorem scalar_price_upper {b φ : ℝ} (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 2)
    (hφ : |φ| ≤ 1 / 2) :
    1 ≤ (2 - b) * Real.cos φ ∧
      2 / ((2 - b) * Real.cos φ) - ((2 - b) * Real.cos φ) / 2 ≤
        b + φ ^ 2 + b ^ 2 + φ ^ 4 := by
  have hφ2 : φ ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs φ, (sq_le_sq₀ (abs_nonneg φ) (by norm_num)).2 hφ]
  have hc : (7 / 8 : ℝ) ≤ Real.cos φ := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := φ)]
  let x := (2 - b) * Real.cos φ
  have hx : 1 ≤ x := by
    calc
      1 ≤ (3 / 2 : ℝ) * (7 / 8) := by norm_num
      _ ≤ (2 - b) * Real.cos φ := mul_le_mul (by linarith) hc (by norm_num) (by linarith)
  have hxu : x ≤ 2 := by
    have hm := mul_le_mul_of_nonneg_left (Real.cos_le_one φ) (show 0 ≤ 2 - b by linarith)
    dsimp [x]
    nlinarith
  have he : 2 - x ≤ b + φ ^ 2 := by
    have hm := mul_nonneg hb (sub_nonneg.mpr (Real.cos_le_one φ))
    dsimp [x]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := φ)]
  have he2 : (2 - x) ^ 2 ≤ 2 * (b ^ 2 + φ ^ 4) := by
    have hh := pow_le_pow_left₀ (by linarith : 0 ≤ 2 - x) he 2
    nlinarith [sq_nonneg (b - φ ^ 2)]
  have hdiv : (2 - x) ^ 2 / (2 * x) ≤ b ^ 2 + φ ^ 4 := by
    apply (div_le_iff₀ (show 0 < 2 * x by linarith)).2
    have hm := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2 * (b ^ 2 + φ ^ 4) by positivity)
    nlinarith
  have hid : 2 / x - x / 2 = (2 - x) + (2 - x) ^ 2 / (2 * x) := by
    field_simp
    ring
  refine ⟨hx, ?_⟩
  change 2 / x - x / 2 ≤ _
  rw [hid]
  linarith

theorem radial_price_upper {a η b₀ b₁ : ℝ} (h₀ : 0 ≤ b₀) (h₁ : 0 ≤ b₁)
    (hb : b₀ + b₁ ≤ 1 / 2) (hφ : |a + η / 2| ≤ 1 / 2) (t : ℝ) :
    1 ≤ (radialSum a η b₀ b₁).re ∧
    2 / (radialSum a η b₀ b₁).re - (radialSum a η b₀ b₁).re / 2 +
      (|(radialSum a η b₀ b₁).im| / (radialSum a η b₀ b₁).re) * |t| ≤
      2 * (1 - Real.cos a) + (b₀ + b₁) + a * η + η ^ 2 / 4 +
        (b₀ + b₁) ^ 2 + (a + η / 2) ^ 4 + a ^ 4 / 12 +
        (b₀ + b₁) * |a + η / 2| * |t| := by
  have hp := scalar_price_upper (add_nonneg h₀ h₁) hb hφ
  have hd : |b₀ - b₁| ≤ b₀ + b₁ := abs_le.mpr ⟨by linarith, by linarith⟩
  have hy : |(radialSum a η b₀ b₁).im| ≤ (b₀ + b₁) * |a + η / 2| := by
    rw [radialSum_im, abs_mul]
    exact mul_le_mul hd Real.abs_sin_le_abs (abs_nonneg _) (add_nonneg h₀ h₁)
  have hm : |(radialSum a η b₀ b₁).im| / (radialSum a η b₀ b₁).re ≤
      (b₀ + b₁) * |a + η / 2| := by
    rw [radialSum_re]
    apply (div_le_iff₀ (by linarith : 0 < (2 - (b₀ + b₁)) * Real.cos (a + η / 2))).2
    have hh := mul_le_mul_of_nonneg_left hp.1
      (mul_nonneg (add_nonneg h₀ h₁) (abs_nonneg (a + η / 2)))
    nlinarith
  refine ⟨by simpa only [radialSum_re] using hp.1, ?_⟩
  have ht := mul_le_mul_of_nonneg_right hm (abs_nonneg t)
  rw [radialSum_re]
  rw [radialSum_re] at ht
  nlinarith [cosine_fourth_upper a]

theorem weighted_cross_price {D B : ℂ} (hx : 0 < D.re)
    (hp : ‖D + B‖ ≤ 2) (hm : ‖D - B‖ ≤ 2) (g : ℝ) :
    g * B.re ≤ |g| * (2 / D.re - D.re / 2 + (|D.im| / D.re) * |B.im|) := by
  have h₁ := PressureSupport.actual_cross_price (s := (1 : ℝ)) hx (Or.inl rfl) hp hm
  have h₂ := PressureSupport.actual_cross_price (s := (-1 : ℝ)) hx (Or.inr rfl) hp hm
  have ha : |B.re| ≤ 2 / D.re - D.re / 2 + (|D.im| / D.re) * |B.im| := by
    apply abs_le.mpr
    constructor <;> linarith
  calc
    _ ≤ |g * B.re| := le_abs_self _
    _ = |g| * |B.re| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left ha (abs_nonneg _)

theorem tilted_signed_price {D : ℂ} (η : ℝ) (c₀ c₁ : ℂ) (hx : 0 < D.re)
    (hp : ‖D + centerStep η c₀ c₁‖ ≤ 2) (hm : ‖D - centerStep η c₀ c₁‖ ≤ 2) (g : ℝ) :
    g * (c₁ - c₀).re ≤
      |g| * (2 / D.re - D.re / 2 + (|D.im| / D.re) * |(centerStep η c₀ c₁).im|) +
      η / 2 * (g * (c₁ + c₀).im) +
      η ^ 2 / 8 * |g * (c₁ - c₀).re| + |η| ^ 3 / 48 * |g * (c₁ + c₀).im| := by
  have hw := weighted_cross_price hx hp hm g
  rw [centerStep_re] at hw
  have hc : |1 - Real.cos (η / 2)| ≤ η ^ 2 / 8 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := η / 2)]
  have hs : |Real.sin (η / 2) - η / 2| ≤ |η| ^ 3 / 48 := by
    have h := Real.abs_sub_sin_le (η / 2)
    rw [abs_sub_comm] at h
    norm_num only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_pow] at h
    convert h using 1
    ring
  have h₁ : (1 - Real.cos (η / 2)) * (g * (c₁ - c₀).re) ≤
      η ^ 2 / 8 * |g * (c₁ - c₀).re| := by
    calc
      _ ≤ |(1 - Real.cos (η / 2)) * (g * (c₁ - c₀).re)| := le_abs_self _
      _ = |1 - Real.cos (η / 2)| * |g * (c₁ - c₀).re| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  have h₂ : (Real.sin (η / 2) - η / 2) * (g * (c₁ + c₀).im) ≤
      |η| ^ 3 / 48 * |g * (c₁ + c₀).im| := by
    calc
      _ ≤ |(Real.sin (η / 2) - η / 2) * (g * (c₁ + c₀).im)| := le_abs_self _
      _ = |Real.sin (η / 2) - η / 2| * |g * (c₁ + c₀).im| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
  nlinarith

def remainder (a η b₀ b₁ g : ℝ) (c₀ c₁ : ℂ) : ℝ :=
  |g| * (η ^ 2 / 4 + (b₀ + b₁) ^ 2 + (a + η / 2) ^ 4 + a ^ 4 / 12 +
      (b₀ + b₁) * |a + η / 2| * |(centerStep η c₀ c₁).im|) +
    η ^ 2 / 8 * |g * (c₁ - c₀).re| + |η| ^ 3 / 48 * |g * (c₁ + c₀).im|

theorem remainder_nonneg (a η b₀ b₁ g : ℝ) (c₀ c₁ : ℂ) (hb : 0 ≤ b₀ + b₁) :
    0 ≤ remainder a η b₀ b₁ g c₀ c₁ := by unfold remainder; positivity

/-- A precise signed version of the constraint expansion before energy absorption. -/
theorem pointwise_signed_constraint {a η b₀ b₁ : ℝ} (h₀ : 0 ≤ b₀) (h₁ : 0 ≤ b₁)
    (hb : b₀ + b₁ ≤ 1 / 2) (hφ : |a + η / 2| ≤ 1 / 2)
    (c₀ c₁ : ℂ)
    (hp : ‖radialSum a η b₀ b₁ + centerStep η c₀ c₁‖ ≤ 2)
    (hm : ‖radialSum a η b₀ b₁ - centerStep η c₀ c₁‖ ≤ 2) (g : ℝ) :
    g * (c₁ - c₀).re - 2 * (1 - Real.cos a) * |g| ≤
      |g| * (b₀ + b₁) + a * |g| * η + g * (c₁ + c₀).im * η / 2 +
        remainder a η b₀ b₁ g c₀ c₁ := by
  have hr := radial_price_upper h₀ h₁ hb hφ (centerStep η c₀ c₁).im
  have ht := tilted_signed_price η c₀ c₁ (by linarith : 0 < (radialSum a η b₀ b₁).re) hp hm g
  have hh := mul_le_mul_of_nonneg_left hr.2 (abs_nonneg g)
  unfold remainder
  nlinarith

/-- The finite sum retains both signed angular expressions occurring in (6.17). -/
theorem sum_signed_constraint {ι : Type*} [Fintype ι]
    (a : ℝ) (η b₀ b₁ g : ι → ℝ) (c₀ c₁ : ι → ℂ)
    (h₀ : ∀ j, 0 ≤ b₀ j) (h₁ : ∀ j, 0 ≤ b₁ j)
    (hb : ∀ j, b₀ j + b₁ j ≤ 1 / 2) (hφ : ∀ j, |a + η j / 2| ≤ 1 / 2)
    (hp : ∀ j, ‖radialSum a (η j) (b₀ j) (b₁ j) + centerStep (η j) (c₀ j) (c₁ j)‖ ≤ 2)
    (hm : ∀ j, ‖radialSum a (η j) (b₀ j) (b₁ j) - centerStep (η j) (c₀ j) (c₁ j)‖ ≤ 2) :
    (∑ j, g j * (c₁ j - c₀ j).re) - 2 * (1 - Real.cos a) * (∑ j, |g j|) ≤
      (∑ j, |g j| * (b₀ j + b₁ j)) + a * (∑ j, |g j| * η j) +
      (∑ j, g j * (c₁ j + c₀ j).im * η j) / 2 +
      ∑ j, remainder a (η j) (b₀ j) (b₁ j) (g j) (c₀ j) (c₁ j) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    pointwise_signed_constraint (h₀ j) (h₁ j) (hb j) (hφ j) (c₀ j) (c₁ j) (hp j) (hm j) (g j))
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_div, mul_assoc] using h

/-- The required crossing inequalities follow from actual diameter constraints. -/
theorem diameter_cross_constraints {n : ℕ} (z : Configuration.Points n)
    (hz : Configuration.DiameterAtMost 2 z) (p : Fin n → Fin n)
    (i j : Fin n) :
    ‖(AntipodalDecomposition.oddPart p z i + AntipodalDecomposition.oddPart p z j) +
      (AntipodalDecomposition.evenPart p z j - AntipodalDecomposition.evenPart p z i)‖ ≤ 2 ∧
    ‖(AntipodalDecomposition.oddPart p z i + AntipodalDecomposition.oddPart p z j) -
      (AntipodalDecomposition.evenPart p z j - AntipodalDecomposition.evenPart p z i)‖ ≤ 2 := by
  constructor
  · convert hz j (p i) using 1
    congr 1
    unfold AntipodalDecomposition.oddPart AntipodalDecomposition.evenPart
    ring
  · convert hz i (p j) using 1
    congr 1
    unfold AntipodalDecomposition.oddPart AntipodalDecomposition.evenPart
    ring

theorem pointwise_signed_constraint_of_physical {μ a θ₀ θ₁ b₀ b₁ : ℝ}
    (h₀ : 0 ≤ b₀) (h₁ : 0 ≤ b₁) (hb : b₀ + b₁ ≤ 1 / 2)
    (hφ : |a + (θ₁ - θ₀) / 2| ≤ 1 / 2) (c₀ c₁ : ℂ)
    (hp : ‖(((1 - b₀ : ℝ) : ℂ) * circle (μ - a + θ₀) +
      ((1 - b₁ : ℝ) : ℂ) * circle (μ + a + θ₁)) +
      (circle θ₁ * c₁ - circle θ₀ * c₀)‖ ≤ 2)
    (hm : ‖(((1 - b₀ : ℝ) : ℂ) * circle (μ - a + θ₀) +
      ((1 - b₁ : ℝ) : ℂ) * circle (μ + a + θ₁)) -
      (circle θ₁ * c₁ - circle θ₀ * c₀)‖ ≤ 2) (g : ℝ) :
    g * (circle (-μ) * c₁ - circle (-μ) * c₀).re - 2 * (1 - Real.cos a) * |g| ≤
      |g| * (b₀ + b₁) + a * |g| * (θ₁ - θ₀) +
      g * (circle (-μ) * c₁ + circle (-μ) * c₀).im * (θ₁ - θ₀) / 2 +
      remainder a (θ₁ - θ₀) b₀ b₁ g (circle (-μ) * c₀) (circle (-μ) * c₁) := by
  apply pointwise_signed_constraint h₀ h₁ hb hφ
  · rw [← rotate_actual_radial μ a θ₀ θ₁ b₀ b₁, ← rotate_actual_center μ θ₀ θ₁ c₀ c₁,
      ← mul_add, norm_mul, circle_norm, one_mul]
    exact hp
  · rw [← rotate_actual_radial μ a θ₀ θ₁ b₀ b₁, ← rotate_actual_center μ θ₀ θ₁ c₀ c₁,
      ← mul_sub, norm_mul, circle_norm, one_mul]
    exact hm

theorem radial_sum_le {ι : Type*} [Fintype ι] (p : Equiv.Perm ι)
    (b g : ι → ℝ) (hb : ∀ j, 0 ≤ b j) {G : ℝ} (hg : ∀ j, |g j| ≤ G) :
    (∑ j, |g j| * (b j + b (p j))) ≤ 2 * G * ∑ j, b j := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    mul_le_mul_of_nonneg_right (hg j) (add_nonneg (hb j) (hb (p j))))
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Equiv.sum_comp p b] at h
  nlinarith

def normalComponent (n : ℕ) (a : ℝ) (c₀ c₁ : ℂ) : ℝ :=
  (n : ℝ) / (2 * Real.sin a) * (c₁ - c₀).re

theorem amplitude_identity {n : ℕ} (hn : 2 ≤ n) :
    FiniteBox.amplitude n = (n : ℝ) * (1 - Real.cos (Real.pi / n)) / Real.sin (Real.pi / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sin (Real.pi / n) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    apply (div_lt_iff₀ hnR).2
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  have h := BoxLensLift.radius_identity hn
  unfold BoxLensLift.radius BoxLensLift.angle at h
  apply (eq_div_iff hs.ne').2
  field_simp [hnR.ne'] at h
  nlinarith

/-- The component in the rotating edge frame is the actual normal variable
already used in the physical quadratic form and pressure gap. -/
theorem normalComponent_eq_normal {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ) (j : Fin n) :
    normalComponent n (Real.pi / n)
      ((starRingEnd ℂ) (SchurLift.frame n j) * c j)
      ((starRingEnd ℂ) (SchurLift.frame n j) * c (FiniteFourierLift.successor (by omega) j)) =
        EdgeCoordinates.normal (by omega) c j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sin (Real.pi / n) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    apply (div_lt_iff₀ hnR).2
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  have hf : (starRingEnd ℂ) (SchurLift.frame n j) * SchurLift.frame n j = 1 := by
    rw [mul_comm, Complex.mul_conj, SchurLift.frame_normSq]
    rfl
  have he : (starRingEnd ℂ) (SchurLift.frame n j) *
      (c (FiniteFourierLift.successor (by omega) j) - c j) =
      (2 * Real.sin (Real.pi / n) / n : ℝ) *
        ((EdgeCoordinates.normal (by omega) c j : ℂ) +
          I * (EdgeCoordinates.tangent (by omega) c j : ℂ)) := by
    change (starRingEnd ℂ) (SchurLift.frame n j) * FiniteFourierLift.difference (by omega) c j = _
    rw [EdgeCoordinates.actual_increment hn c, EdgeCoordinates.edgeIncrement]
    calc
      _ = (2 * Real.sin (Real.pi / n) / n : ℝ) *
          ((starRingEnd ℂ) (SchurLift.frame n j) * SchurLift.frame n j) *
          ((EdgeCoordinates.normal (by omega) c j : ℂ) + I * (EdgeCoordinates.tangent (by omega) c j : ℂ)) := by ring
      _ = _ := by rw [hf, mul_one]
  unfold normalComponent
  rw [← mul_sub, he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  field_simp

/-- Formula (6.17) with an explicit, nonnegative summed remainder. In particular,
the radial coefficient is exactly G/(n sin(pi/n)), with no missing factor n. -/
theorem finite_signed_pressure {n : ℕ} (hn : 2 ≤ n) (p : Equiv.Perm (Fin n))
    (η b g : Fin n → ℝ) (c₀ c₁ : Fin n → ℂ)
    (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j, b j + b (p j) ≤ 1 / 2)
    (hφ : ∀ j, |Real.pi / n + η j / 2| ≤ 1 / 2)
    (hp : ∀ j, ‖radialSum (Real.pi / n) (η j) (b j) (b (p j)) +
      centerStep (η j) (c₀ j) (c₁ j)‖ ≤ 2)
    (hm : ∀ j, ‖radialSum (Real.pi / n) (η j) (b j) (b (p j)) -
      centerStep (η j) (c₀ j) (c₁ j)‖ ≤ 2)
    {G : ℝ} (hg : ∀ j, |g j| ≤ G) :
    ((∑ j, normalComponent n (Real.pi / n) (c₀ j) (c₁ j) * g j) -
      FiniteBox.amplitude n * ∑ j, |g j|) / n ≤
      G / (n * Real.sin (Real.pi / n)) * ((n : ℝ) * ∑ j, b j) +
      (Real.pi / n) / (2 * Real.sin (Real.pi / n)) * (∑ j, |g j| * η j) +
      (1 / (4 * Real.sin (Real.pi / n))) * (∑ j, g j * (c₁ j + c₀ j).im * η j) +
      (∑ j, remainder (Real.pi / n) (η j) (b j) (b (p j)) (g j) (c₀ j) (c₁ j)) /
        (2 * Real.sin (Real.pi / n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sin (Real.pi / n) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    apply (div_lt_iff₀ hnR).2
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  have h := sum_signed_constraint (Real.pi / n) η b (fun j => b (p j)) g c₀ c₁
    hb0 (fun j => hb0 (p j)) hb hφ hp hm
  have hr := radial_sum_le p b g hb0 hg
  have he := div_le_div_of_nonneg_right h (show 0 ≤ 2 * Real.sin (Real.pi / n) by positivity)
  have her := div_le_div_of_nonneg_right hr (show 0 ≤ 2 * Real.sin (Real.pi / n) by positivity)
  have hleft : ((∑ j, normalComponent n (Real.pi / n) (c₀ j) (c₁ j) * g j) -
      FiniteBox.amplitude n * ∑ j, |g j|) / n =
      ((∑ j, g j * (c₁ j - c₀ j).re) - 2 * (1 - Real.cos (Real.pi / n)) * ∑ j, |g j|) /
        (2 * Real.sin (Real.pi / n)) := by
    rw [amplitude_identity hn]
    simp only [normalComponent, mul_assoc, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun j _ => mul_comm (c₁ j - c₀ j).re (g j))]
    field_simp
  rw [hleft]
  have hright : (2 * G * ∑ j, b j) / (2 * Real.sin (Real.pi / n)) =
      G / (n * Real.sin (Real.pi / n)) * ((n : ℝ) * ∑ j, b j) := by field_simp
  rw [hright] at her
  simp only [add_div] at he
  have hfinal := he.trans (add_le_add (add_le_add (add_le_add her le_rfl) le_rfl) le_rfl)
  convert hfinal using 1
  · rfl
  · ring

/-- The actual strict pressure gap leaves at least one half of the leading radial
price available for the remaining terms. -/
theorem radial_coefficient_le_half {n : ℕ} (hn : 16 ≤ n) {G : ℝ}
    (hg : G ≤ 31 * Real.pi / 64) :
    G / (n * Real.sin (Real.pi / n)) ≤ 1 / 2 := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hx0 : 0 ≤ Real.pi / n := by positivity
  have hx : Real.pi / n ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ hn0).2
    nlinarith [Real.pi_lt_four]
  have hx2 : (Real.pi / n) ^ 2 ≤ (1 : ℝ) / 16 := by nlinarith
  have hx3 : (Real.pi / n) ^ 3 ≤ (Real.pi / n) / 16 := by
    nlinarith [mul_le_mul_of_nonneg_right hx2 hx0]
  have hs : 31 / 32 * (Real.pi / n) ≤ Real.sin (Real.pi / n) := by
    nlinarith [Real.sin_ge_sub_cube hx0]
  have he : (n : ℝ) * (Real.pi / n) = Real.pi := by field_simp
  have hprod : 31 * Real.pi / 32 ≤ (n : ℝ) * Real.sin (Real.pi / n) := by
    nlinarith [mul_le_mul_of_nonneg_left hs hn0.le]
  have hpos : 0 < (n : ℝ) * Real.sin (Real.pi / n) := by
    nlinarith [Real.pi_pos]
  apply (div_le_iff₀ hpos).2
  linarith

theorem radial_price_le_half {n : ℕ} (hn : 16 ≤ n) {G τ : ℝ}
    (hg : G ≤ 31 * Real.pi / 64) (hτ : 0 ≤ τ) :
    G / (n * Real.sin (Real.pi / n)) * τ ≤ τ / 2 := by
  have h := mul_le_mul_of_nonneg_right (radial_coefficient_le_half hn hg) hτ
  linarith

end StructuralNote.SignedCrossingPressure

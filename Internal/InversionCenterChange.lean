import InvertedConvexDomain
import StarLikePositiveReal

/-!
# Changing the inversion center of one conformal map

The same disk parametrization is used for every point of the convex set.
Changing the center amounts to an explicit Möbius transformation, whose
holomorphic inverse is obtained by swapping the two centers.
-/

namespace ExteriorReduction

open Complex Set Metric Filter
open scoped Topology

noncomputable section

def changeInversionCenter (a b w : ℂ) : ℂ := w / (1 + (a - b) * w)

@[simp] theorem changeInversionCenter_zero (a b : ℂ) :
    changeInversionCenter a b 0 = 0 := by simp [changeInversionCenter]

theorem changeInversionCenter_denominator_ne_zero {K : Set ℂ} {a b w : ℂ}
    (hb : b ∈ K) (hw : w ∈ invertedComplement K a) :
    1 + (a - b) * w ≠ 0 := by
  intro hd
  have hwne : w ≠ 0 := by intro h; simp [h] at hd
  have hvalue : a + w⁻¹ = b := by
    field_simp
    linear_combination hd
  exact (hw.resolve_left hwne) (hvalue ▸ hb)

theorem changeInversionCenter_ne_zero {a b w : ℂ}
    (hw : w ≠ 0) (hd : 1 + (a - b) * w ≠ 0) :
    changeInversionCenter a b w ≠ 0 := div_ne_zero hw hd

theorem changeInversionCenter_point_identity {a b w : ℂ}
    (hw : w ≠ 0) :
    b + (changeInversionCenter a b w)⁻¹ = a + w⁻¹ := by
  simp only [changeInversionCenter, inv_div]
  field_simp
  ring

theorem changeInversionCenter_mapsTo {K : Set ℂ} {a b : ℂ}
    (_hb : b ∈ K) :
    MapsTo (changeInversionCenter a b) (invertedComplement K a)
      (invertedComplement K b) := by
  intro w hw
  by_cases hwne : w = 0
  · simp [hwne]
  · right
    rw [changeInversionCenter_point_identity hwne]
    exact hw.resolve_left hwne

theorem changeInversionCenter_reverse_denominator {a b w : ℂ}
    (hd : 1 + (a - b) * w ≠ 0) :
    1 + (b - a) * changeInversionCenter a b w = (1 + (a - b) * w)⁻¹ := by
  rw [inv_eq_one_div, eq_div_iff hd]
  dsimp [changeInversionCenter]
  rw [add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hd]
  ring

theorem changeInversionCenter_inverse {a b w : ℂ}
    (hd : 1 + (a - b) * w ≠ 0) :
    changeInversionCenter b a (changeInversionCenter a b w) = w := by
  change changeInversionCenter a b w /
    (1 + (b - a) * changeInversionCenter a b w) = w
  rw [changeInversionCenter_reverse_denominator hd, div_inv_eq_mul]
  exact div_mul_cancel₀ _ hd

theorem changeInversionCenter_invOn {K : Set ℂ} {a b : ℂ}
    (ha : a ∈ K) (hb : b ∈ K) :
    InvOn (changeInversionCenter b a) (changeInversionCenter a b)
      (invertedComplement K a) (invertedComplement K b) := by
  constructor
  · intro w hw
    exact changeInversionCenter_inverse (changeInversionCenter_denominator_ne_zero hb hw)
  · intro w hw
    exact changeInversionCenter_inverse (changeInversionCenter_denominator_ne_zero ha hw)

theorem hasDerivAt_changeInversionCenter {a b w : ℂ}
    (hd : 1 + (a - b) * w ≠ 0) :
    HasDerivAt (changeInversionCenter a b) ((1 + (a - b) * w) ^ 2)⁻¹ w := by
  have hh := (hasDerivAt_id w).div
    (((hasDerivAt_id w).const_mul (a - b)).const_add 1) hd
  convert hh using 1 <;> try rfl
  dsimp
  field_simp [hd]
  ring

theorem differentiableOn_changeInversionCenter {K : Set ℂ} {a b : ℂ}
    (hb : b ∈ K) :
    DifferentiableOn ℂ (changeInversionCenter a b) (invertedComplement K a) :=
  fun _ hw => (hasDerivAt_changeInversionCenter
    (changeInversionCenter_denominator_ne_zero hb hw)).differentiableAt.differentiableWithinAt

theorem changeInversionCenter_bijOn {K : Set ℂ} {a b : ℂ}
    (ha : a ∈ K) (hb : b ∈ K) :
    BijOn (changeInversionCenter a b) (invertedComplement K a)
      (invertedComplement K b) := by
  refine ⟨changeInversionCenter_mapsTo hb, (changeInversionCenter_invOn ha hb).1.injOn, ?_⟩
  intro w hw
  exact ⟨changeInversionCenter b a w, changeInversionCenter_mapsTo ha hw,
    (changeInversionCenter_invOn ha hb).2 hw⟩

/-- The logarithmic kernel has nonnegative real part for every point of the
convex set, using a single fixed conformal parametrization at `a`. -/
theorem inversionCenter_kernel_re_nonneg {K : Set ℂ} {a b : ℂ}
    (hK : IsCompact K) (hconv : Convex ℝ K) (ha : a ∈ K) (hb : b ∈ K)
    {g f : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hf : DifferentiableOn ℂ f (invertedComplement K a))
    (hgmap : MapsTo g (ball 0 1) (invertedComplement K a))
    (hfmap : MapsTo f (invertedComplement K a) (ball 0 1))
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, f (g z) = z) (hg0 : g 0 = 0)
    {z : ℂ} (hz : z ∈ ball 0 1) (hz0 : z ≠ 0) :
    0 ≤ (z * deriv g z / (g z * (1 + (a - b) * g z))).re := by
  let gb : ℂ → ℂ := fun w => changeInversionCenter a b (g w)
  let fb : ℂ → ℂ := fun w => f (changeInversionCenter b a w)
  have hgb : DifferentiableOn ℂ gb (ball 0 1) :=
    (differentiableOn_changeInversionCenter hb).comp hg hgmap
  have hfb : DifferentiableOn ℂ fb (invertedComplement K b) :=
    hf.comp (differentiableOn_changeInversionCenter ha) (changeInversionCenter_mapsTo ha)
  have hgbmap : MapsTo gb (ball 0 1) (invertedComplement K b) :=
    (changeInversionCenter_mapsTo hb).comp hgmap
  have hfbmap : MapsTo fb (invertedComplement K b) (ball 0 1) :=
    hfmap.comp (changeInversionCenter_mapsTo ha)
  have hbleft : ∀ w ∈ ball (0 : ℂ) 1, fb (gb w) = w := by
    intro w hw
    dsimp [fb, gb]
    rw [changeInversionCenter_inverse (changeInversionCenter_denominator_ne_zero hb (hgmap hw))]
    exact hleft w hw
  have hgb0 : gb 0 = 0 := by simp [gb, hg0]
  have hpos := StarLike.log_derivative_re_nonneg (invertedComplement_isOpen hK b)
    hgb hfb hgbmap hfbmap hbleft hgb0 (invertedComplement_starConvex hconv hb) hz hz0
  have hd := changeInversionCenter_denominator_ne_zero hb (hgmap hz)
  have hdg := (hasDerivAt_changeInversionCenter hd).comp z
    (hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hder : deriv gb z = ((1 + (a - b) * g z) ^ 2)⁻¹ * deriv g z := hdg.deriv
  have hgne := StarLike.value_ne_zero hleft hg0 hz hz0
  rw [hder] at hpos
  convert hpos using 1
  congr 1
  dsimp [gb, changeInversionCenter]
  field_simp

#print axioms changeInversionCenter_bijOn
#print axioms inversionCenter_kernel_re_nonneg

end
end ExteriorReduction

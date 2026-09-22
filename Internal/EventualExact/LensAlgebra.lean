import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Exact pointwise algebra for the intersection of two radius-two disks.

These lemmas contain no localization, closure, or extremality assumption.  A
positive half-width is required only for normalized coordinates and for the
claim that exactly one constraint is active at an endpoint.
-/

namespace Erdos1045.EventualExact

namespace Lens

noncomputable section

def height (t : ℝ) : ℝ := Real.sqrt (4 - t ^ 2)

def width (L t : ℝ) : ℝ := height t - L

theorem height_nonneg (t : ℝ) : 0 ≤ height t := Real.sqrt_nonneg _

theorem height_sq {t : ℝ} (ht : t ^ 2 ≤ 4) : height t ^ 2 + t ^ 2 = 4 := by
  have h := Real.sq_sqrt (sub_nonneg.mpr ht)
  unfold height
  linarith

theorem add_width (L t : ℝ) : L + width L t = height t := by
  unfold width
  ring

theorem width_nonneg_iff (L t : ℝ) : 0 ≤ width L t ↔ L ≤ height t := by
  exact sub_nonneg

theorem width_pos_iff (L t : ℝ) : 0 < width L t ↔ L < height t := by
  exact sub_pos

theorem two_constraints_iff {L x t : ℝ} (hL : 0 ≤ L) :
    ((L + x) ^ 2 + t ^ 2 ≤ 4 ∧ (L - x) ^ 2 + t ^ 2 ≤ 4) ↔
      (L + |x|) ^ 2 + t ^ 2 ≤ 4 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    constructor
    · exact And.left
    · intro h
      exact ⟨h, by nlinarith [mul_nonneg hL hx]⟩
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx']
    constructor
    · intro h
      nlinarith [h.2]
    · intro h
      constructor <;> nlinarith [mul_nonpos_of_nonneg_of_nonpos hL hx']

theorem two_strict_constraints_iff {L x t : ℝ} (hL : 0 ≤ L) :
    ((L + x) ^ 2 + t ^ 2 < 4 ∧ (L - x) ^ 2 + t ^ 2 < 4) ↔
      (L + |x|) ^ 2 + t ^ 2 < 4 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    constructor
    · exact And.left
    · intro h
      exact ⟨h, by nlinarith [mul_nonneg hL hx]⟩
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx']
    constructor
    · intro h
      nlinarith [h.2]
    · intro h
      constructor <;> nlinarith [mul_nonpos_of_nonneg_of_nonpos hL hx']

theorem two_constraints_iff_abs_le_width {L x t : ℝ} (hL : 0 ≤ L)
    (ht : t ^ 2 ≤ 4) :
    ((L + x) ^ 2 + t ^ 2 ≤ 4 ∧ (L - x) ^ 2 + t ^ 2 ≤ 4) ↔
      |x| ≤ width L t := by
  rw [two_constraints_iff hL]
  have hs := height_sq ht
  have hsum := add_nonneg hL (abs_nonneg x)
  constructor
  · intro h
    have hb : L + |x| ≤ height t :=
      (sq_le_sq₀ hsum (height_nonneg t)).mp (by linarith)
    unfold width
    linarith
  · intro h
    have hb : L + |x| ≤ height t := by
      unfold width at h
      linarith
    have := (sq_le_sq₀ hsum (height_nonneg t)).mpr hb
    linarith

theorem two_strict_constraints_iff_abs_lt_width {L x t : ℝ} (hL : 0 ≤ L)
    (ht : t ^ 2 ≤ 4) :
    ((L + x) ^ 2 + t ^ 2 < 4 ∧ (L - x) ^ 2 + t ^ 2 < 4) ↔
      |x| < width L t := by
  rw [two_strict_constraints_iff hL]
  have hs := height_sq ht
  have hsum := add_nonneg hL (abs_nonneg x)
  constructor
  · intro h
    have hb : L + |x| < height t :=
      (sq_lt_sq₀ hsum (height_nonneg t)).mp (by linarith)
    unfold width
    linarith
  · intro h
    have hb : L + |x| < height t := by
      unfold width at h
      linarith
    have := (sq_lt_sq₀ hsum (height_nonneg t)).mpr hb
    linarith

theorem constraints_imply_height_bound {L x t : ℝ}
    (h : (L + x) ^ 2 + t ^ 2 ≤ 4) : t ^ 2 ≤ 4 := by
  nlinarith [sq_nonneg (L + x)]

theorem normalized_constraints_iff {L t s : ℝ} (hL : 0 ≤ L)
    (ht : t ^ 2 ≤ 4) (hR : 0 < width L t) :
    ((L + s * width L t) ^ 2 + t ^ 2 ≤ 4 ∧
      (L - s * width L t) ^ 2 + t ^ 2 ≤ 4) ↔ |s| ≤ 1 := by
  rw [two_constraints_iff_abs_le_width hL ht, abs_mul, abs_of_pos hR]
  simpa using (mul_le_mul_iff_left₀ hR :
    |s| * width L t ≤ 1 * width L t ↔ |s| ≤ 1)

theorem normalized_strict_constraints_iff {L t s : ℝ} (hL : 0 ≤ L)
    (ht : t ^ 2 ≤ 4) (hR : 0 < width L t) :
    ((L + s * width L t) ^ 2 + t ^ 2 < 4 ∧
      (L - s * width L t) ^ 2 + t ^ 2 < 4) ↔ |s| < 1 := by
  rw [two_strict_constraints_iff_abs_lt_width hL ht, abs_mul, abs_of_pos hR]
  simpa using (mul_lt_mul_iff_left₀ hR :
    |s| * width L t < 1 * width L t ↔ |s| < 1)

theorem exists_normalized_iff {L x t : ℝ} (hL : 0 ≤ L)
    (ht : t ^ 2 ≤ 4) (hR : 0 < width L t) :
    ((L + x) ^ 2 + t ^ 2 ≤ 4 ∧ (L - x) ^ 2 + t ^ 2 ≤ 4) ↔
      ∃ s : ℝ, |s| ≤ 1 ∧ x = s * width L t := by
  constructor
  · intro h
    refine ⟨x / width L t, ?_, ?_⟩
    · rw [abs_div, abs_of_pos hR]
      exact (div_le_one hR).mpr ((two_constraints_iff_abs_le_width hL ht).mp h)
    · exact (div_mul_cancel₀ x (ne_of_gt hR)).symm
  · rintro ⟨s, hs, rfl⟩
    exact (normalized_constraints_iff hL ht hR).mpr hs

theorem normalized_coordinate_unique {L x t s : ℝ} (hR : 0 < width L t)
    (hx : x = s * width L t) : s = x / width L t := by
  apply (eq_div_iff (ne_of_gt hR)).mpr
  exact hx.symm

theorem positive_endpoint_eq {L t : ℝ} (ht : t ^ 2 ≤ 4) :
    (L + width L t) ^ 2 + t ^ 2 = 4 := by
  rw [add_width]
  exact height_sq ht

theorem opposite_endpoint_gap {L t : ℝ} (ht : t ^ 2 ≤ 4) :
    4 - ((L - width L t) ^ 2 + t ^ 2) = 4 * L * width L t := by
  have := positive_endpoint_eq (L := L) ht
  nlinarith

theorem plus_active_iff {L t s : ℝ} (hL : 0 < L)
    (ht : t ^ 2 ≤ 4) (hR : 0 < width L t) (hs : |s| ≤ 1) :
    (L + s * width L t) ^ 2 + t ^ 2 = 4 ↔ s = 1 := by
  have hlow : -(width L t) ≤ s * width L t := by
    have := mul_le_mul_of_nonneg_right (abs_le.mp hs).1 hR.le
    simpa using this
  constructor
  · intro he
    have heq : (L + s * width L t) ^ 2 = (L + width L t) ^ 2 := by
      linarith [positive_endpoint_eq (L := L) ht]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp heq with h | h
    · nlinarith
    · linarith
  · rintro rfl
    simpa using positive_endpoint_eq (L := L) ht

theorem minus_active_iff {L t s : ℝ} (hL : 0 < L)
    (ht : t ^ 2 ≤ 4) (hR : 0 < width L t) (hs : |s| ≤ 1) :
    (L - s * width L t) ^ 2 + t ^ 2 = 4 ↔ s = -1 := by
  have h := plus_active_iff hL ht hR (s := -s) (by simpa using hs)
  convert h using 1 <;> constructor <;> intro he <;> linarith

theorem endpoint_exactly_one {L t : ℝ} (hL : 0 < L)
    (ht : t ^ 2 ≤ 4) (hR : 0 < width L t) :
    (L + width L t) ^ 2 + t ^ 2 = 4 ∧
      (L - width L t) ^ 2 + t ^ 2 < 4 := by
  refine ⟨positive_endpoint_eq ht, ?_⟩
  have hgap := opposite_endpoint_gap (L := L) ht
  have : 0 < 4 * L * width L t := mul_pos (by linarith) hR
  linarith

theorem any_active_iff_endpoint {L t s : ℝ} (hL : 0 < L)
    (ht : t ^ 2 ≤ 4) (hR : 0 < width L t) (hs : |s| ≤ 1) :
    ((L + s * width L t) ^ 2 + t ^ 2 = 4 ∨
      (L - s * width L t) ^ 2 + t ^ 2 = 4) ↔ s = 1 ∨ s = -1 := by
  rw [plus_active_iff hL ht hR hs, minus_active_iff hL ht hR hs]

theorem norm_sq_cartesian (x t : ℝ) :
    ‖(x : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 = x ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply, pow_two]

theorem norm_sq_rotated_plus {u : ℂ} (hu : ‖u‖ = 1) (L x t : ℝ) :
    ‖(L : ℂ) * u + u * ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 =
      (L + x) ^ 2 + t ^ 2 := by
  have he : (L : ℂ) * u + u * ((x : ℂ) + (t : ℂ) * Complex.I) =
      u * (((L + x : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by push_cast; ring
  rw [he, norm_mul, hu, one_mul, norm_sq_cartesian]

theorem norm_sq_rotated_minus {u : ℂ} (hu : ‖u‖ = 1) (L x t : ℝ) :
    ‖(L : ℂ) * u - u * ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 =
      (L - x) ^ 2 + t ^ 2 := by
  have he : (L : ℂ) * u - u * ((x : ℂ) + (t : ℂ) * Complex.I) =
      u * (((L - x : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) := by push_cast; ring
  rw [he, norm_mul, hu, one_mul, norm_sq_cartesian]
  ring

theorem rotated_constraints_iff {u : ℂ} (hu : ‖u‖ = 1)
    {L x t : ℝ} (hL : 0 ≤ L) :
    (‖(L : ℂ) * u + u * ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 ∧
      ‖(L : ℂ) * u - u * ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2) ↔
      (L + |x|) ^ 2 + t ^ 2 ≤ 4 := by
  have hp := sq_le_sq₀ (norm_nonneg ((L : ℂ) * u +
    u * ((x : ℂ) + (t : ℂ) * Complex.I))) (by norm_num : (0 : ℝ) ≤ 2)
  have hm := sq_le_sq₀ (norm_nonneg ((L : ℂ) * u -
    u * ((x : ℂ) + (t : ℂ) * Complex.I))) (by norm_num : (0 : ℝ) ≤ 2)
  rw [norm_sq_rotated_plus hu, show (2 : ℝ) ^ 2 = 4 by norm_num] at hp
  rw [norm_sq_rotated_minus hu, show (2 : ℝ) ^ 2 = 4 by norm_num] at hm
  rw [← hp, ← hm, two_constraints_iff hL]

theorem rotated_normalized_constraints_iff {u : ℂ} (hu : ‖u‖ = 1)
    {L t s : ℝ} (hL : 0 ≤ L) (ht : t ^ 2 ≤ 4) (hR : 0 < width L t) :
    (‖(L : ℂ) * u + u * (((s * width L t : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 ∧
      ‖(L : ℂ) * u - u * (((s * width L t : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2) ↔
      |s| ≤ 1 := by
  rw [rotated_constraints_iff hu hL, ← two_constraints_iff hL,
    normalized_constraints_iff hL ht hR]

theorem rotated_plus_active_iff {u : ℂ} (hu : ‖u‖ = 1)
    {L t s : ℝ} (hL : 0 < L) (ht : t ^ 2 ≤ 4) (hR : 0 < width L t)
    (hs : |s| ≤ 1) :
    ‖(L : ℂ) * u + u * (((s * width L t : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ = 2 ↔
      s = 1 := by
  have hn := norm_sq_rotated_plus hu L (s * width L t) t
  constructor
  · intro h
    apply (plus_active_iff hL ht hR hs).mp
    nlinarith
  · intro h
    have he := (plus_active_iff hL ht hR hs).mpr h
    nlinarith [norm_nonneg ((L : ℂ) * u +
      u * (((s * width L t : ℝ) : ℂ) + (t : ℂ) * Complex.I))]

theorem rotated_minus_active_iff {u : ℂ} (hu : ‖u‖ = 1)
    {L t s : ℝ} (hL : 0 < L) (ht : t ^ 2 ≤ 4) (hR : 0 < width L t)
    (hs : |s| ≤ 1) :
    ‖(L : ℂ) * u - u * (((s * width L t : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ = 2 ↔
      s = -1 := by
  have hn := norm_sq_rotated_minus hu L (s * width L t) t
  constructor
  · intro h
    apply (minus_active_iff hL ht hR hs).mp
    nlinarith
  · intro h
    have he := (minus_active_iff hL ht hR hs).mpr h
    nlinarith [norm_nonneg ((L : ℂ) * u -
      u * (((s * width L t : ℝ) : ℂ) + (t : ℂ) * Complex.I))]

theorem rotated_opposite_endpoint_gap {u : ℂ} (hu : ‖u‖ = 1)
    {L t : ℝ} (ht : t ^ 2 ≤ 4) :
    4 - ‖(L : ℂ) * u - u * ((width L t : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 =
      4 * L * width L t := by
  rw [norm_sq_rotated_minus hu]
  exact opposite_endpoint_gap ht

theorem rotated_endpoint_exactly_one {u : ℂ} (hu : ‖u‖ = 1)
    {L t : ℝ} (hL : 0 < L) (ht : t ^ 2 ≤ 4) (hR : 0 < width L t) :
    ‖(L : ℂ) * u + u * ((width L t : ℂ) + (t : ℂ) * Complex.I)‖ = 2 ∧
      ‖(L : ℂ) * u - u * ((width L t : ℂ) + (t : ℂ) * Complex.I)‖ < 2 := by
  constructor
  · simpa using (rotated_plus_active_iff hu hL ht hR (s := 1) (by norm_num)).mpr rfl
  · have hn := norm_sq_rotated_minus hu L (width L t) t
    have he := (endpoint_exactly_one hL ht hR).2
    nlinarith [norm_nonneg ((L : ℂ) * u -
      u * ((width L t : ℂ) + (t : ℂ) * Complex.I))]

end

end Lens

end Erdos1045.EventualExact

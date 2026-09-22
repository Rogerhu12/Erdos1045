import Erdos1045.CirclePotential
import EventualExact.GapDefect

/-! The actual cosecant-square potential and its quantitative convexity.

The curvature comparison is proved on the whole open arc `(0, 2π)`.
Consequently the tangent-remainder estimate applies on either side of its
base point. No convexity or trigonometric estimate is an external assumption.
-/

namespace Erdos1045.EventualExact.CosecantPotential

open Set
open scoped BigOperators
noncomputable section

abbrev arc : Set ℝ := Erdos1045.CirclePotential.arc

def potential (t : ℝ) : ℝ := 1 / Real.sin (t / 2) ^ 2

def first (t : ℝ) : ℝ := -Real.cos (t / 2) / Real.sin (t / 2) ^ 3

def second (t : ℝ) : ℝ :=
  (3 - 2 * Real.sin (t / 2) ^ 2) / (2 * Real.sin (t / 2) ^ 4)

def corrected (t : ℝ) : ℝ := potential t - 4 / (3 * t ^ 2)

def correctedFirst (t : ℝ) : ℝ := first t + 8 / (3 * t ^ 3)

def correctedSecond (t : ℝ) : ℝ := second t - 8 / t ^ 4

theorem sin_half_pos {t : ℝ} (ht : t ∈ arc) : 0 < Real.sin (t / 2) :=
  Erdos1045.CirclePotential.sin_half_pos ht

theorem potential_hasDerivAt {t : ℝ} (ht : t ∈ arc) :
    HasDerivAt potential (first t) t := by
  have hs := sin_half_pos ht
  have h := (hasDerivAt_const t (1 : ℝ)).div
    ((((hasDerivAt_id t).div_const 2).sin).pow 2) (pow_ne_zero 2 hs.ne')
  apply h.congr_deriv
  dsimp [first]
  field_simp [hs.ne']
  ring

theorem first_hasDerivAt {t : ℝ} (ht : t ∈ arc) :
    HasDerivAt first (second t) t := by
  have hs := sin_half_pos ht
  have hc := (((hasDerivAt_id t).div_const 2).cos).neg
  have hsin := (((hasDerivAt_id t).div_const 2).sin).pow 3
  have h := hc.div hsin (pow_ne_zero 3 hs.ne')
  apply h.congr_deriv
  dsimp [second]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq (t / 2),
    mul_nonneg (sq_nonneg (Real.sin (t / 2))) (sq_nonneg (Real.cos (t / 2)))]

theorem potential_deriv {t : ℝ} (ht : t ∈ arc) : deriv potential t = first t :=
  (potential_hasDerivAt ht).deriv

theorem potential_second_deriv {t : ℝ} (ht : t ∈ arc) :
    deriv (deriv potential) t = second t := by
  have he : deriv potential =ᶠ[nhds t] first := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    exact potential_deriv hx
  exact (first_hasDerivAt ht).congr_of_eventuallyEq he |>.deriv

theorem corrected_hasDerivAt {t : ℝ} (ht : t ∈ arc) :
    HasDerivAt corrected (correctedFirst t) t := by
  have hpower : HasDerivAt (fun x : ℝ => 4 / (3 * x ^ 2)) (-8 / (3 * t ^ 3)) t := by
    have h := (hasDerivAt_const t (4 : ℝ)).div (((hasDerivAt_id t).pow 2).const_mul 3)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 ht.1.ne'))
    apply h.congr_deriv
    dsimp
    field_simp [ht.1.ne']
    ring
  exact ((potential_hasDerivAt ht).sub hpower).congr_deriv (by
    dsimp [correctedFirst]
    ring)

theorem correctedFirst_hasDerivAt {t : ℝ} (ht : t ∈ arc) :
    HasDerivAt correctedFirst (correctedSecond t) t := by
  have hpower : HasDerivAt (fun x : ℝ => 8 / (3 * x ^ 3)) (-8 / t ^ 4) t := by
    have h := (hasDerivAt_const t (8 : ℝ)).div (((hasDerivAt_id t).pow 3).const_mul 3)
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 ht.1.ne'))
    apply h.congr_deriv
    dsimp
    field_simp [ht.1.ne']
    ring
  exact ((first_hasDerivAt ht).add hpower).congr_deriv (by
    dsimp [correctedSecond]
    ring)

theorem second_lower_bound {t : ℝ} (ht : t ∈ arc) : 8 / t ^ 4 ≤ second t := by
  have hs := sin_half_pos ht
  have hsle := Real.sin_le (show 0 ≤ t / 2 by linarith [ht.1])
  have hpow : 16 * Real.sin (t / 2) ^ 4 ≤ t ^ 4 := by
    calc
      _ = (2 * Real.sin (t / 2)) ^ 4 := by ring
      _ ≤ t ^ 4 := by gcongr; linarith
  have hsquare : Real.sin (t / 2) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (t / 2), sq_nonneg (Real.cos (t / 2))]
  calc
    8 / t ^ 4 ≤ 1 / (2 * Real.sin (t / 2) ^ 4) := by
      apply (div_le_div_iff₀ (pow_pos ht.1 4) (by positivity)).mpr
      nlinarith
    _ ≤ second t := by
      unfold second
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith

theorem second_pos {t : ℝ} (ht : t ∈ arc) : 0 < second t :=
  lt_of_lt_of_le (div_pos (by norm_num) (pow_pos ht.1 4)) (second_lower_bound ht)

theorem second_nonneg {t : ℝ} (ht : t ∈ arc) : 0 ≤ second t :=
  (second_pos ht).le

theorem correctedSecond_nonneg {t : ℝ} (ht : t ∈ arc) : 0 ≤ correctedSecond t :=
  sub_nonneg.mpr (second_lower_bound ht)

theorem potential_convex : ConvexOn ℝ arc potential := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := first) (f'' := second)
    (convex_Ioo 0 (2 * Real.pi))
  · exact fun t ht => (potential_hasDerivAt ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (potential_hasDerivAt (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    exact (first_hasDerivAt (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    exact second_nonneg (interior_subset ht)

theorem corrected_convex : ConvexOn ℝ arc corrected := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := correctedFirst) (f'' := correctedSecond)
    (convex_Ioo 0 (2 * Real.pi))
  · exact fun t ht => (corrected_hasDerivAt ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (corrected_hasDerivAt (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    exact (correctedFirst_hasDerivAt (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    exact correctedSecond_nonneg (interior_subset ht)

def remainder (s t : ℝ) : ℝ := potential t - potential s - first s * (t - s)

theorem remainder_nonneg {s t : ℝ} (hs : s ∈ arc) (ht : t ∈ arc) :
    0 ≤ remainder s t := by
  have h := Erdos1045.CirclePotential.supporting_line potential_convex hs ht
    (potential_hasDerivAt hs)
  unfold remainder
  linarith

theorem inverse_square_remainder {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) :
    4 / (3 * t ^ 2) - 4 / (3 * s ^ 2) + 8 / (3 * s ^ 3) * (t - s) =
      4 / (3 * s ^ 2) * Erdos1045.EventualExact.gapDefect (t / s) := by
  unfold Erdos1045.EventualExact.gapDefect
  field_simp
  ring

theorem remainder_ge_gapDefect {s t : ℝ} (hs : s ∈ arc) (ht : t ∈ arc) :
    4 / (3 * s ^ 2) * Erdos1045.EventualExact.gapDefect (t / s) ≤ remainder s t := by
  have h := Erdos1045.CirclePotential.supporting_line corrected_convex hs ht
    (corrected_hasDerivAt hs)
  dsimp [corrected, correctedFirst] at h
  rw [← inverse_square_remainder hs.1.ne' ht.1.ne']
  unfold remainder
  nlinarith

theorem potential_complement (t : ℝ) : potential (2 * Real.pi - t) = potential t := by
  unfold potential
  rw [show (2 * Real.pi - t) / 2 = Real.pi - t / 2 by ring, Real.sin_pi_sub]

theorem sum_remainder_eq {ι : Type*} [Fintype ι] (s : ℝ) (t : ι → ℝ)
    (hmean : ∑ i, t i = Fintype.card ι * s) :
    (∑ i, remainder s (t i)) = (∑ i, potential (t i)) - Fintype.card ι * potential s := by
  simp only [remainder, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hmean]
  ring

end

end Erdos1045.EventualExact.CosecantPotential

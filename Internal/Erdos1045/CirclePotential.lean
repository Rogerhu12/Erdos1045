import Erdos1045.LogDefect
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# The circle logarithmic potential and its quantitative convexity

The irrelevant constant `-2 log 2` is omitted from the potential because all
statements concern energy differences. No external input is used in this file.
In particular, the comparison of its convexity remainder with `2 χ(t/s)` is
proved from the second derivatives rather than postulated.
-/

namespace Erdos1045.CirclePotential

open Set
open scoped BigOperators
noncomputable section

def potential (t : ℝ) : ℝ := -2 * Real.log (Real.sin (t / 2))
def first (t : ℝ) : ℝ := -Real.cos (t / 2) / Real.sin (t / 2)
def second (t : ℝ) : ℝ := 1 / (2 * Real.sin (t / 2) ^ 2)
def corrected (t : ℝ) : ℝ := potential t + 2 * Real.log t
def correctedFirst (t : ℝ) : ℝ := first t + 2 / t
def correctedSecond (t : ℝ) : ℝ := second t - 2 / t ^ 2
def arc : Set ℝ := Ioo 0 (2 * Real.pi)

theorem sin_half_pos {t : ℝ} (ht : t ∈ arc) : 0 < Real.sin (t / 2) :=
  Real.sin_pos_of_pos_of_lt_pi (by rcases ht with ⟨h, _⟩; linarith)
    (by rcases ht with ⟨_, h⟩; linarith)

theorem potential_hasDerivAt {t : ℝ} (ht : t ∈ arc) :
    HasDerivAt potential (first t) t := by
  have hs := sin_half_pos ht
  have h := ((((hasDerivAt_id t).div_const 2).sin).log hs.ne').const_mul (-2)
  apply h.congr_deriv
  dsimp [first]
  ring

theorem first_hasDerivAt {t : ℝ} (ht : t ∈ arc) :
    HasDerivAt first (second t) t := by
  have hs := sin_half_pos ht
  have hc := ((hasDerivAt_id t).div_const 2).cos
  have hsin := ((hasDerivAt_id t).div_const 2).sin
  have h := hc.neg.div hsin hs.ne'
  apply h.congr_deriv
  dsimp [second]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq (t / 2)]

theorem corrected_hasDerivAt {t : ℝ} (ht : t ∈ arc) :
    HasDerivAt corrected (correctedFirst t) t := by
  have h := (potential_hasDerivAt ht).add ((Real.hasDerivAt_log ht.1.ne').const_mul 2)
  apply h.congr_deriv
  simp [correctedFirst, div_eq_mul_inv]

theorem correctedFirst_hasDerivAt {t : ℝ} (ht : t ∈ arc) :
    HasDerivAt correctedFirst (correctedSecond t) t := by
  have h := (first_hasDerivAt ht).add (((hasDerivAt_id t).inv ht.1.ne').const_mul 2)
  apply h.congr_deriv
  simp [correctedSecond]
  ring

theorem second_nonneg {t : ℝ} (_ht : t ∈ arc) : 0 ≤ second t := by
  dsimp [second]
  positivity

theorem correctedSecond_nonneg {t : ℝ} (ht : t ∈ arc) : 0 ≤ correctedSecond t := by
  have hs := sin_half_pos ht
  have ht0 := ht.1
  have hsle := Real.sin_le (show 0 ≤ t / 2 by linarith)
  have hsquare : 4 * Real.sin (t / 2) ^ 2 ≤ t ^ 2 := by nlinarith
  dsimp [correctedSecond, second]
  rw [sub_nonneg]
  apply (div_le_div_iff₀ (sq_pos_of_pos ht0) (by positivity)).mpr
  nlinarith

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

theorem supporting_line {S : Set ℝ} {f : ℝ → ℝ} {s t d : ℝ}
    (hconv : ConvexOn ℝ S f) (hs : s ∈ S) (ht : t ∈ S)
    (hd : HasDerivAt f d s) : d * (t - s) ≤ f t - f s := by
  rcases lt_trichotomy s t with h | h | h
  · have hh := hconv.le_slope_of_hasDerivAt hs ht h hd
    rw [slope_def_field] at hh
    exact (le_div_iff₀ (sub_pos.mpr h)).mp hh
  · subst t; simp
  · have hh := hconv.slope_le_of_hasDerivAt ht hs h hd
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith

def remainder (s t : ℝ) : ℝ := potential t - potential s - first s * (t - s)

theorem remainder_nonneg {s t : ℝ} (hs : s ∈ arc) (ht : t ∈ arc) :
    0 ≤ remainder s t := by
  have h := supporting_line potential_convex hs ht (potential_hasDerivAt hs)
  dsimp [remainder]
  linarith

/-- The scalar comparison used in Lemma 2.3. -/
theorem remainder_ge_logDefect {s t : ℝ} (hs : s ∈ arc) (ht : t ∈ arc) :
    2 * LogDefect.chi (t / s) ≤ remainder s t := by
  have h := supporting_line corrected_convex hs ht (corrected_hasDerivAt hs)
  dsimp [corrected, correctedFirst] at h
  rw [LogDefect.chi, Real.log_div ht.1.ne' hs.1.ne']
  dsimp [remainder]
  have hs0 : s ≠ 0 := hs.1.ne'
  have hid : 2 / s * (t - s) = 2 * (t / s - 1) := by field_simp
  nlinarith

/-- Summing tangent remainders loses the linear term when the mean is fixed. -/
theorem sum_remainder_eq {ι : Type*} [Fintype ι] (s : ℝ) (t : ι → ℝ)
    (hmean : ∑ i, t i = Fintype.card ι * s) :
    (∑ i, remainder s (t i)) = (∑ i, potential (t i)) - Fintype.card ι * potential s := by
  simp only [remainder, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hmean]
  ring

theorem sum_potential_lower {ι : Type*} [Fintype ι] {s : ℝ} (hs : s ∈ arc)
    (t : ι → ℝ) (ht : ∀ i, t i ∈ arc)
    (hmean : ∑ i, t i = Fintype.card ι * s) :
    0 ≤ (∑ i, potential (t i)) - Fintype.card ι * potential s := by
  rw [← sum_remainder_eq s t hmean]
  exact Finset.sum_nonneg fun i _ => remainder_nonneg hs (ht i)

theorem sum_potential_ge_logDefect {ι : Type*} [Fintype ι] {s : ℝ} (hs : s ∈ arc)
    (t : ι → ℝ) (ht : ∀ i, t i ∈ arc)
    (hmean : ∑ i, t i = Fintype.card ι * s) :
    2 * LogDefect.total Finset.univ (fun i => t i / s) ≤
      (∑ i, potential (t i)) - Fintype.card ι * potential s := by
  rw [← sum_remainder_eq s t hmean]
  unfold LogDefect.total
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => remainder_ge_logDefect hs (ht i)

end
end Erdos1045.CirclePotential

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Finite weighted maximum principles

The weights and function in this file are actual finite arrays. The estimates
use only their stated signs, a maximum point, and a quadratic mass budget.
-/

noncomputable section

open scoped BigOperators

namespace Erdos1045.EventualExact

variable {ι : Type*} [Fintype ι]

/-- The weighted graph Laplacian, with the positive sign at a maximum. -/
def weightedLaplacian (w : ι → ι → ℝ) (s : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, w i j * (s i - s j)

/-- The unnormalized quadratic mass of a finite real function. -/
def finiteSquareMass (s : ι → ℝ) : ℝ := ∑ j, (s j) ^ 2

theorem finiteSquareMass_nonneg (s : ι → ℝ) : 0 ≤ finiteSquareMass s :=
  Finset.sum_nonneg fun j _ => sq_nonneg (s j)

theorem weightedLaplacian_nonneg_at_max {w : ι → ι → ℝ} {s : ι → ℝ} {i : ι}
    (hw : ∀ j, 0 ≤ w i j) (hs : ∀ j, s j ≤ s i) :
    0 ≤ weightedLaplacian w s i := by
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sub_nonneg.mpr (hs j))

/-- Diagonal weights are irrelevant: the lower bound is required only off diagonal. -/
theorem weightedLaplacian_ge_uniform {w : ι → ι → ℝ} {s : ι → ℝ}
    {i : ι} {M k : ℝ} (hi : s i = M) (hs : ∀ j, s j ≤ M)
    (hzero : ∑ j, s j = 0) (hw : ∀ j, j ≠ i → k ≤ w i j) :
    k * Fintype.card ι * M ≤ weightedLaplacian w s i := by
  classical
  calc
    _ = ∑ j, k * (M - s j) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp [hzero]
      ring
    _ ≤ ∑ j, w i j * (M - s j) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hji : j = i
      · subst j
        simp [hi]
      · exact mul_le_mul_of_nonneg_right (hw j hji) (sub_nonneg.mpr (hs j))
    _ = weightedLaplacian w s i := by simp [weightedLaplacian, hi]

/-- The maximum at one index is controlled by the total quadratic mass. -/
theorem maximum_sq_le_finiteSquareMass {s : ι → ℝ} {i : ι} {M : ℝ}
    (hi : s i = M) : M ^ 2 ≤ finiteSquareMass s := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (s j))
    (Finset.mem_univ i)
  simpa only [hi, finiteSquareMass] using h

omit [Fintype ι] in
/-- A local quadratic mass budget gives the finite Chebyshev bound. -/
theorem card_above_half_mul_sq_le {s : ι → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (R : Finset ι) :
    ((R.filter fun j => M / 2 < s j).card : ℝ) * M ^ 2 ≤
      4 * ∑ j ∈ R, (s j) ^ 2 := by
  classical
  have hpoint : ∀ j ∈ R.filter (fun j => M / 2 < s j), M ^ 2 ≤ 4 * (s j) ^ 2 := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    nlinarith [sq_nonneg (s j - M / 2)]
  calc
    _ = ∑ j ∈ R.filter (fun j => M / 2 < s j), M ^ 2 := by simp
    _ ≤ ∑ j ∈ R.filter (fun j => M / 2 < s j), 4 * (s j) ^ 2 :=
      Finset.sum_le_sum hpoint
    _ ≤ ∑ j ∈ R, 4 * (s j) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => by positivity)
    _ = _ := by rw [Finset.mul_sum]

theorem card_above_half_le_mass {s : ι → ℝ} {M : ℝ} (hM : 0 < M)
    (R : Finset ι) :
    ((R.filter fun j => M / 2 < s j).card : ℝ) ≤ 4 * finiteSquareMass s / M ^ 2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos hM)).2
  have hR : (∑ j ∈ R, (s j) ^ 2) ≤ finiteSquareMass s :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R)
      (fun j _ _ => sq_nonneg (s j))
  exact (card_above_half_mul_sq_le hM.le R).trans (mul_le_mul_of_nonneg_left hR (by norm_num))

/-- The weights on a selected good set alone give a lower bound. -/
theorem weightedLaplacian_ge_good_card {w : ι → ι → ℝ} {s : ι → ℝ}
    {i : ι} {M k : ℝ} (hi : s i = M) (hM : 0 ≤ M)
    (hs : ∀ j, s j ≤ M) (hw : ∀ j, 0 ≤ w i j) (R : Finset ι)
    (hR : ∀ j ∈ R, k ≤ w i j) :
    ((R.filter fun j => s j ≤ M / 2).card : ℝ) * k * (M / 2) ≤
      weightedLaplacian w s i := by
  classical
  calc
    _ = ∑ j ∈ R.filter (fun j => s j ≤ M / 2), k * (M / 2) := by simp; ring
    _ ≤ ∑ j ∈ R.filter (fun j => s j ≤ M / 2), w i j * (M - s j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hmem := Finset.mem_filter.mp hj
      exact mul_le_mul (hR j hmem.1) (by linarith [hmem.2]) (by positivity) (hw j)
    _ ≤ ∑ j, w i j * (M - s j) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => mul_nonneg (hw j) (sub_nonneg.mpr (hs j)))
    _ = weightedLaplacian w s i := by simp [weightedLaplacian, hi]

omit [Fintype ι] in
theorem good_card_eq_sub_bad_card (s : ι → ℝ) (M : ℝ) (R : Finset ι) :
    ((R.filter fun j => s j ≤ M / 2).card : ℝ) =
      R.card - ((R.filter fun j => M / 2 < s j).card : ℝ) := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := R) (fun j => M / 2 < s j)
  simp only [not_lt] at h
  apply eq_sub_iff_add_eq.mpr
  exact_mod_cast (show (R.filter fun j => s j ≤ M / 2).card +
      (R.filter fun j => M / 2 < s j).card = R.card by omega)

/-- A useful subset bound after replacing the bad-point count by quadratic mass. -/
theorem weightedLaplacian_ge_card_sub_mass {w : ι → ι → ℝ} {s : ι → ℝ}
    {i : ι} {M k : ℝ} (hi : s i = M) (hM : 0 < M) (hk : 0 ≤ k)
    (hs : ∀ j, s j ≤ M) (hw : ∀ j, 0 ≤ w i j) (R : Finset ι)
    (hR : ∀ j ∈ R, k ≤ w i j) :
    (R.card - 4 * finiteSquareMass s / M ^ 2) * k * (M / 2) ≤
      weightedLaplacian w s i := by
  have hcard := card_above_half_le_mass (s := s) hM R
  have hgood := good_card_eq_sub_bad_card s M R
  have hcount : (R.card : ℝ) - 4 * finiteSquareMass s / M ^ 2 ≤
      (R.filter fun j => s j ≤ M / 2).card := by linarith
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcount hk)
    (by positivity)).trans (weightedLaplacian_ge_good_card hi hM.le hs hw R hR)

/-- If at least half of a selected set is good, its contribution is quantitative. -/
theorem weightedLaplacian_ge_half_card {w : ι → ι → ℝ} {s : ι → ℝ}
    {i : ι} {M k : ℝ} (hi : s i = M) (hM : 0 < M) (hk : 0 ≤ k)
    (hs : ∀ j, s j ≤ M) (hw : ∀ j, 0 ≤ w i j) (R : Finset ι)
    (hR : ∀ j ∈ R, k ≤ w i j)
    (hmass : 8 * finiteSquareMass s ≤ R.card * M ^ 2) :
    R.card * k * M / 4 ≤ weightedLaplacian w s i := by
  have hc : 4 * finiteSquareMass s / M ^ 2 ≤ (R.card : ℝ) / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hM)).2
    nlinarith
  have hb := weightedLaplacian_ge_card_sub_mass hi hM hk hs hw R hR
  have hp := mul_nonneg hk hM.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) hp]

/-- The large-radius branch of the finite maximum principle, before inserting pi. -/
theorem cubic_maximum_le_large_radius {w : ι → ι → ℝ} {s : ι → ℝ}
    {i : ι} {M b S : ℝ} (hi : s i = M) (hM : 0 ≤ M) (hb : 0 < b)
    (hs : ∀ j, s j ≤ M) (hzero : ∑ j, s j = 0)
    (hw : ∀ j, j ≠ i → 4 / (b * (Fintype.card ι : ℝ) ^ 2) ≤ w i j)
    (hS : (Fintype.card ι : ℝ) * M ^ 2 / 12 ≤ S) :
    M ^ 3 ≤ 3 * b * S * weightedLaplacian w s i := by
  have hn : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  have hlap := weightedLaplacian_ge_uniform hi hs hzero hw
  have hl : 4 * M / (b * Fintype.card ι) ≤ weightedLaplacian w s i := by
    calc
      _ = (4 / (b * (Fintype.card ι : ℝ) ^ 2)) * Fintype.card ι * M := by field_simp
      _ ≤ _ := hlap
  have hS0 : 0 ≤ S := le_trans (by positivity) hS
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 3 * b * S by positivity)
  have he : 3 * b * S * (4 * M / (b * Fintype.card ι)) =
      12 * S * M / Fintype.card ι := by field_simp; ring
  rw [he] at hm
  apply le_trans ?_ hm
  apply (le_div_iff₀ hn).2
  nlinarith [mul_le_mul_of_nonneg_right hS hM]

/-- For weights at least `4 / (pi * b² * n²)`, the coefficient is `3 pi b²`. -/
theorem cubic_maximum_le_three_pi {w : ι → ι → ℝ} {s : ι → ℝ}
    {i : ι} {M b S : ℝ} (hi : s i = M) (hM : 0 ≤ M) (hb : b ≠ 0)
    (hs : ∀ j, s j ≤ M) (hzero : ∑ j, s j = 0)
    (hw : ∀ j, j ≠ i → 4 / (Real.pi * b ^ 2 * (Fintype.card ι : ℝ) ^ 2) ≤ w i j)
    (hS : (Fintype.card ι : ℝ) * M ^ 2 / 12 ≤ S) :
    M ^ 3 ≤ 3 * Real.pi * b ^ 2 * S * weightedLaplacian w s i := by
  have hpos : 0 < Real.pi * b ^ 2 := mul_pos Real.pi_pos (sq_pos_of_ne_zero hb)
  simpa only [mul_assoc] using cubic_maximum_le_large_radius hi hM hpos hs hzero hw hS

end Erdos1045.EventualExact

import Erdos1045.LocalObjective

/-!
# Removing translation and similarity from an actual small perturbation

Both normalization equations are proved for the explicitly normalized function.
The first Fourier coefficient is controlled by the average of the actual edge
ratios; it is not assumed close to one independently of the geometric input.
-/

namespace Erdos1045.LocalNormalization

open Complex
open scoped BigOperators
noncomputable section

def mean (n : ℕ) (u : ℕ → ℂ) : ℂ := (∑ j ∈ Finset.range n, u j) / (n : ℂ)

def first (n : ℕ) (u : ℕ → ℂ) : ℂ := LocalDFT.coefficient n u 0

def normalized (n : ℕ) (u : ℕ → ℂ) (j : ℕ) : ℂ :=
  (u j - mean n u - first n u * LocalPhase.regularRoot n ^ j) / (1 + first n u)

theorem root_sum_zero {n : ℕ} (hn : 2 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n)) :
    (∑ j ∈ Finset.range n, LocalPhase.regularRoot n ^ j) = 0 := by
  have hd : ¬ n ∣ 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  simpa [hd] using HF.sum_pow 1

theorem first_mul_n {n : ℕ} (hn : 0 < n) (u : ℕ → ℂ) :
    (n : ℂ) * first n u =
      ∑ j ∈ Finset.range n, u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [first, LocalDFT.coefficient, zero_add, mul_one]
  field_simp

theorem mean_mul_n {n : ℕ} (hn : 0 < n) (u : ℕ → ℂ) :
    (n : ℂ) * mean n u = ∑ j ∈ Finset.range n, u j := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold mean
  field_simp

theorem actual_mean {n : ℕ} (hn : 2 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n)) (u : ℕ → ℂ) :
    mean n (LocalObjective.perturbedVertices n u) = mean n u := by
  unfold mean LocalObjective.perturbedVertices LocalObjective.regularVertices
  rw [Finset.sum_add_distrib, root_sum_zero hn HF, zero_add]

theorem actual_first_coefficient {n : ℕ} (hn : 2 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n)) (u : ℕ → ℂ) :
    first n (LocalObjective.perturbedVertices n u) = 1 + first n u := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hp : (∑ j ∈ Finset.range n, LocalPhase.regularRoot n ^ j *
      (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = (n : ℂ) := by
    simpa using HF.sum_mul_conj 1 1
  unfold first LocalDFT.coefficient LocalObjective.perturbedVertices LocalObjective.regularVertices
  simp only [zero_add, mul_one, add_mul, Finset.sum_add_distrib]
  rw [hp]
  field_simp

theorem edge_ratio_sum (HI : LocalDFT.ClassicalDFTInversion) {n : ℕ} (hn : 2 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (u : ℕ → ℂ) (hu : Function.Periodic u n) :
    (∑ j ∈ Finset.range n, LocalDFT.pairRatio n u j 1) = (n : ℂ) * first n u := by
  have hs := LocalFourier.synthesis_sum HF (by omega : 0 < n)
    (fun r => LocalDFT.coefficient n u r *
      LocalFourier.geom (r + 1) (LocalPhase.regularRoot n ^ 1))
  have he (j : ℕ) := LocalDFT.ratioFourier_eq_pairRatio HI (by omega : 0 < n)
    u hu (by omega : 0 < 1) (by omega : 1 < n) j
  simp only [LocalFourier.ratioFourier] at he
  simp only [he] at hs
  simpa [first, LocalFourier.geom] using hs

theorem first_norm_bound (HI : LocalDFT.ClassicalDFTInversion) {n : ℕ} (hn : 4 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (u : ℕ → ℂ) (hu : Function.Periodic u n) {η : ℝ}
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖) :
    ‖first n u‖ ≤ η := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := norm_sum_le (Finset.range n) (fun j => LocalDFT.pairRatio n u j 1)
  rw [edge_ratio_sum HI (by omega) HF u hu, norm_mul, Complex.norm_natCast] at h
  have hb : (∑ j ∈ Finset.range n, ‖LocalDFT.pairRatio n u j 1‖) ≤ (n : ℝ) * η := by
    calc
      _ ≤ ∑ _j ∈ Finset.range n, η := Finset.sum_le_sum fun j _ =>
        LocalMaximum.edge_ratio_bound hn u hstep j
      _ = _ := by simp
  exact (mul_le_mul_iff_right₀ hnR).mp (h.trans hb)

theorem denominator_lower {n : ℕ} {u : ℕ → ℂ} {η : ℝ}
    (hf : ‖first n u‖ ≤ η) : 1 - η ≤ ‖1 + first n u‖ := by
  have h := norm_sub_le (1 + first n u) (first n u)
  norm_num at h
  linarith

theorem denominator_ne_zero {n : ℕ} {u : ℕ → ℂ} {η : ℝ}
    (hf : ‖first n u‖ ≤ η) (hη : η < 1) : 1 + first n u ≠ 0 := by
  exact norm_pos_iff.mp (lt_of_lt_of_le (by linarith) (denominator_lower hf))

theorem normalized_periodic {n : ℕ} (hn : 0 < n) (u : ℕ → ℂ)
    (hu : Function.Periodic u n) : Function.Periodic (normalized n u) n := by
  intro j
  simp only [normalized, hu j, pow_add, LocalDFT.regularRoot_pow hn, mul_one]

theorem normalized_mean_zero {n : ℕ} (hn : 2 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n)) (u : ℕ → ℂ) :
    (∑ j ∈ Finset.range n, normalized n u j) = 0 := by
  simp only [normalized, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [root_sum_zero hn HF, mul_zero]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← mean_mul_n (by omega) u]
  ring

theorem normalized_similarity_zero {n : ℕ} (hn : 2 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n)) (u : ℕ → ℂ) :
    (∑ j ∈ Finset.range n, normalized n u j *
      (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0 := by
  have hc : (∑ j ∈ Finset.range n, (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0 := by
    rw [← map_sum, root_sum_zero hn HF, map_zero]
  have hp : (∑ j ∈ Finset.range n, LocalPhase.regularRoot n ^ j *
      (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = (n : ℂ) := by
    simpa using HF.sum_mul_conj 1 1
  have he (j : ℕ) : normalized n u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j) =
      (u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j) -
        mean n u * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j) -
        first n u * (LocalPhase.regularRoot n ^ j *
          (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j))) / (1 + first n u) := by
    unfold normalized
    ring
  simp_rw [he]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hc, hp, ← first_mul_n (by omega) u]
  ring

theorem normalized_step {n : ℕ} (u : ℕ → ℂ) {η : ℝ}
    (hη : 0 ≤ η) (hη1 : η < 1) (hf : ‖first n u‖ ≤ η)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖) (j : ℕ) :
    ‖normalized n u (j + 1) - normalized n u j‖ ≤
      (2 * η / (1 - η)) * ‖LocalPhase.regularRoot n - 1‖ := by
  have hd : 0 < 1 - η := by linarith
  have he : normalized n u (j + 1) - normalized n u j =
      ((u (j + 1) - u j) - first n u *
        (LocalPhase.regularRoot n ^ (j + 1) - LocalPhase.regularRoot n ^ j)) /
        (1 + first n u) := by unfold normalized; ring
  rw [he, norm_div]
  calc
    _ ≤ (‖u (j + 1) - u j‖ + ‖first n u *
        (LocalPhase.regularRoot n ^ (j + 1) - LocalPhase.regularRoot n ^ j)‖) /
        ‖1 + first n u‖ := div_le_div_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ (2 * η * ‖LocalPhase.regularRoot n - 1‖) / ‖1 + first n u‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      rw [norm_mul, LocalMaximum.edge_denominator_norm]
      have hb := mul_le_mul_of_nonneg_right hf (norm_nonneg (LocalPhase.regularRoot n - 1))
      linarith [hstep j]
    _ ≤ (2 * η * ‖LocalPhase.regularRoot n - 1‖) / (1 - η) :=
      div_le_div_of_nonneg_left (by positivity) hd (denominator_lower hf)
    _ = _ := by ring

theorem normalized_affine {n : ℕ} (u : ℕ → ℂ) (hd : 1 + first n u ≠ 0) (j : ℕ) :
    LocalObjective.perturbedVertices n u j = mean n u + (1 + first n u) *
      LocalObjective.perturbedVertices n (normalized n u) j := by
  unfold LocalObjective.perturbedVertices LocalObjective.regularVertices normalized
  field_simp
  ring

theorem small_normalized_bound {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4000) :
    0 ≤ 2 * η / (1 - η) ∧ 2 * η / (1 - η) ≤ 1 / 1000 := by
  have hd : 0 < 1 - η := by linarith
  constructor
  · positivity
  · rw [div_le_iff₀ hd]
    linarith

end
end Erdos1045.LocalNormalization

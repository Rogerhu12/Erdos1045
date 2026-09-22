import StructuralNote.EdgeCoordinates

/-! Uniform bounds for the actual first Fourier coefficient and its imaginary
    edge coordinate.  These estimates use the literal finite sum defining the
    coefficient; no antiperiodicity assumption is needed. -/

namespace StructuralNote.FixedSchurHarmonicBounds

open scoped BigOperators

open Erdos1045 Erdos1045.EventualExact
open Complex FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open StructuralNote.EdgeCoordinates

noncomputable section

local notation "conj" => (starRingEnd ℂ)

private theorem frame_norm {n : ℕ} (j : Fin n) : ‖frame n j‖ = 1 := by
  have h := frame_normSq n j
  rw [normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (frame n j)]

private theorem firstCoefficient_norm_le_l1_aux {n : ℕ} (q : Fin n → ℝ) :
    ‖∑ j : Fin n, (q j : ℂ) * conj (frame n j)‖ ≤
      ∑ j : Fin n, |q j| := by
  calc
    ‖∑ j : Fin n, (q j : ℂ) * conj (frame n j)‖ ≤
        ∑ j : Fin n, ‖(q j : ℂ) * conj (frame n j)‖ := norm_sum_le _ _
    _ = ∑ j : Fin n, |q j| := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul, norm_real, Real.norm_eq_abs, norm_conj, frame_norm j]
      simp

theorem firstCoefficient_norm_le_l1 {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    ‖firstCoefficient q‖ ≤ (∑ j : Fin n, |q j|) / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold firstCoefficient
  rw [norm_div]
  simp only [norm_natCast]
  exact (div_le_div_of_nonneg_right
    (firstCoefficient_norm_le_l1_aux q) (le_of_lt hnR))

theorem firstCoefficient_norm_le {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    ‖firstCoefficient q‖ ≤ ‖q‖ := by
  have hq (j : Fin n) : |q j| ≤ ‖q‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm q j
  have hs : (∑ j : Fin n, |q j|) ≤ (n : ℝ) * ‖q‖ := by
    calc
      (∑ j : Fin n, |q j|) ≤ ∑ _j : Fin n, ‖q‖ := by
        exact Finset.sum_le_sum (fun j hj => hq j)
      _ = (n : ℝ) * ‖q‖ := by simp
  have hdiv := firstCoefficient_norm_le_l1 hn q
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    ‖firstCoefficient q‖ ≤ (∑ j : Fin n, |q j|) / (n : ℝ) := hdiv
    _ ≤ ((n : ℝ) * ‖q‖) / (n : ℝ) :=
      div_le_div_of_nonneg_right hs (le_of_lt hnR)
    _ = ‖q‖ := by field_simp

theorem firstCoefficient_add {n : ℕ} (q r : Fin n → ℝ) :
    firstCoefficient (q + r) = firstCoefficient q + firstCoefficient r := by
  simp [firstCoefficient, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem firstCoefficient_sub {n : ℕ} (q r : Fin n → ℝ) :
    firstCoefficient (q - r) = firstCoefficient q - firstCoefficient r := by
  simp [firstCoefficient, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sub_div]

theorem firstCoefficient_sub_norm_le {n : ℕ} (hn : 0 < n)
    (q r : Fin n → ℝ) :
    ‖firstCoefficient q - firstCoefficient r‖ ≤ ‖q - r‖ := by
  rw [← firstCoefficient_sub q r]
  exact firstCoefficient_norm_le hn (q - r)

theorem J_add {n : ℕ} (q r : Fin n → ℝ) :
    J (q + r) = J q + J r := by
  funext j
  simp only [J, firstCoefficient_add, Pi.add_apply, add_mul, Complex.add_im]
  ring

theorem J_sub {n : ℕ} (q r : Fin n → ℝ) :
    J (q - r) = J q - J r := by
  funext j
  simp only [J, firstCoefficient_sub, Pi.sub_apply, sub_mul, Complex.sub_im]
  ring

theorem J_norm_le {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    ‖J q‖ ≤ 2 * ‖q‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro j
  have him : |(firstCoefficient q * frame n j).im| ≤
      ‖firstCoefficient q * frame n j‖ := abs_im_le_norm _
  have hprod : ‖firstCoefficient q * frame n j‖ = ‖firstCoefficient q‖ := by
    rw [norm_mul, frame_norm j, mul_one]
  calc
    ‖J q j‖ = |2 * (firstCoefficient q * frame n j).im| := by
      simp [J]
    _ = 2 * |(firstCoefficient q * frame n j).im| := by
      rw [abs_mul]
      norm_num
    _ ≤ 2 * ‖firstCoefficient q * frame n j‖ :=
      mul_le_mul_of_nonneg_left him (by norm_num)
    _ = 2 * ‖firstCoefficient q‖ := by rw [hprod]
    _ ≤ 2 * ‖q‖ := mul_le_mul_of_nonneg_left (firstCoefficient_norm_le hn q) (by norm_num)

theorem J_sub_norm_le {n : ℕ} (hn : 0 < n) (q r : Fin n → ℝ) :
    ‖J q - J r‖ ≤ 2 * ‖q - r‖ := by
  calc
    ‖J q - J r‖ = ‖J (q - r)‖ := by rw [J_sub]
    _ ≤ 2 * ‖q - r‖ := J_norm_le hn (q - r)

theorem J_pointwise_l1 {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (j : Fin n) :
    |J q j| ≤ (2 : ℝ) / (n : ℝ) * ∑ i : Fin n, |q i| := by
  have him : |(firstCoefficient q * frame n j).im| ≤
      ‖firstCoefficient q * frame n j‖ := abs_im_le_norm _
  have hprod : ‖firstCoefficient q * frame n j‖ = ‖firstCoefficient q‖ := by
    rw [norm_mul, frame_norm j, mul_one]
  have hc := firstCoefficient_norm_le_l1 hn q
  calc
    |J q j| = |2 * (firstCoefficient q * frame n j).im| := by simp [J]
    _ = 2 * |(firstCoefficient q * frame n j).im| := by
      rw [abs_mul]
      norm_num
    _ ≤ 2 * ‖firstCoefficient q * frame n j‖ :=
      mul_le_mul_of_nonneg_left him (by norm_num)
    _ = 2 * ‖firstCoefficient q‖ := by rw [hprod]
    _ ≤ 2 * ((∑ i : Fin n, |q i|) / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hc (by norm_num)
    _ = (2 : ℝ) / (n : ℝ) * ∑ i : Fin n, |q i| := by ring

theorem J_antiperiodic {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ) :
    Erdos1045.EventualExact.FiniteBox.Antiperiodic hm (J q) := by
  intro j
  change 2 * (firstCoefficient q * frame (2 * m) (halfTurn hm j)).im =
    -(2 * (firstCoefficient q * frame (2 * m) j).im)
  rw [frame_halfTurn hm j, mul_neg]
  simp
  ring

end

end StructuralNote.FixedSchurHarmonicBounds

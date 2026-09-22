import EventualExact.SchurSpectrum
import Mathlib.Algebra.Order.Chebyshev

/-! Quantitative estimates for the actual mean-zero Schur lift. -/

noncomputable section

open scoped BigOperators

namespace Erdos1045.EventualExact.SchurLiftBounds

open Complex FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum

local notation "conj" => (starRingEnd ℂ)

def meanSquare {n : ℕ} (q : Fin n → ℝ) : ℝ := (∑ j, q j ^ 2) / n

theorem meanSquare_nonneg {n : ℕ} (q : Fin n → ℝ) : 0 ≤ meanSquare q := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

theorem sum_sq_eq {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    (∑ j, q j ^ 2) = (n : ℝ) * meanSquare q := by
  simp [meanSquare, hn.ne', mul_div_cancel₀]

theorem canonicalLift_energyB {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) :
    LocalDFT.energyB n (periodize (by omega) (canonicalLift q)) = meanSquare q / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hi (j : Fin n) : (edgeRatio (by omega) (canonicalLift q) j).im = -q j / n := by
    have h := congrFun (constraint_canonicalLift hn q) j
    rw [constraint_eq_edgeImaginary (by omega)] at h
    apply (eq_div_iff hn0).2
    linarith
  unfold LocalDFT.energyB
  rw [← Fin.sum_univ_eq_sum_range (fun j =>
    (LocalDFT.pairRatio n (periodize (by omega) (canonicalLift q)) j 1).im ^ 2) n]
  change (∑ j : Fin n, (edgeRatio (by omega) (canonicalLift q) j).im ^ 2) = _
  simp_rw [hi, div_pow, neg_sq]
  rw [← Finset.sum_div]
  unfold meanSquare
  ring

/-- The first estimate in (4.6), with an explicit absolute constant. -/
theorem canonicalLift_pairEnergy_le {m : ℕ} (hm : 2 ≤ m)
    (q : Fin (2 * m) → ℝ) (hq : FiniteBox.Antiperiodic (by omega) q) :
    pairEnergy (by omega) (canonicalLift q) ≤ 32 * meanSquare q := by
  have hn0 : ((2 * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2 * m ≠ 0 by omega)
  have hc : HalfPeriodic (by omega) (canonicalLift q) := canonicalLift_halfTurn hm q hq
  have hc0 := centerCoefficient_even_zero (by omega) (canonicalLift q) hc 0 (by decide)
  have hsim : (∑ j ∈ Finset.range (2 * m), periodize (by omega) (canonicalLift q) j *
      conj (LocalPhase.regularRoot (2 * m) ^ j)) = 0 := by
    unfold centerCoefficient LocalDFT.coefficient at hc0
    simp only [Nat.zero_add, Nat.mul_one] at hc0
    simpa only [zero_mul] using (div_eq_iff hn0).mp hc0
  have hmean : (∑ j ∈ Finset.range (2 * m), periodize (by omega) (canonicalLift q) j) = 0 := by
    rw [periodize_sum, canonicalLift_mean_zero (by omega)]
  have he := LocalDFT.normalized_coercivity ClosedFourier.dftInversion
    ClosedFourier.geometricSine (by omega) (ClosedFourier.orthogonality (2 * m) (by omega))
    (periodize (by omega) (canonicalLift q)) (periodize_periodic _ _) hmean hsim
  have hP := pairPotential_eq_quadratic (by omega) (canonicalLift q)
  rw [pairPotential_canonicalLift hm q hq] at hP
  have hV : 0 ≤ normalizedBoxEnergy (operator (2 * m)) q := by
    exact div_nonneg (boxEnergy_nonneg (positiveSemidefinite _) _) (Nat.cast_nonneg _)
  rw [canonicalLift_energyB (by omega)] at he hP
  have hnR : (0 : ℝ) < (2 * m : ℕ) := by exact_mod_cast (show 0 < 2 * m by omega)
  have hcancel : ((2 * m : ℕ) : ℝ) * (meanSquare q / (2 * m : ℕ)) = meanSquare q :=
    mul_div_cancel₀ _ hnR.ne'
  change (pairEnergy (by omega) (canonicalLift q) + _) / 64 ≤ _ at he
  have hB : 0 ≤ meanSquare q / (2 * m : ℕ) := div_nonneg (meanSquare_nonneg q) hnR.le
  rw [hcancel] at he
  nlinarith

theorem imaginary_frame_energy {n : ℕ} (hn : 3 ≤ n) (a : ℂ) :
    (∑ j : Fin n, (a * frame n j).im ^ 2) = (n : ℝ) / 2 * normSq a := by
  have hpoint (j : Fin n) : 2 * (a * frame n j).im ^ 2 =
      normSq a - (a ^ 2 * frame n j ^ 2).re := by
    have h := normSq_mul a (frame n j)
    rw [frame_normSq, mul_one] at h
    have he : (a ^ 2 * frame n j ^ 2) = (a * frame n j) ^ 2 := by ring
    rw [he]
    rw [normSq_apply] at h
    simp only [pow_two, mul_re] at h ⊢
    nlinarith
  have he := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun j _ => hpoint j)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Complex.re_sum] at he
  rw [sum_frame_sq hn, mul_zero, zero_re, sub_zero] at he
  linarith

/-- The real first harmonic uses both conjugate modes; this is the sharp
two-mode Bessel inequality needed again in the geometric box lift. -/
theorem firstCoefficient_bound {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) :
    2 * normSq (firstCoefficient q) ≤ meanSquare q := by
  let a := firstCoefficient q
  have hpoint (j : Fin n) : (q j - 2 * (a * frame n j).re) ^ 2 =
      q j ^ 2 - 4 * ((a * frame n j) * (q j : ℂ)).re +
        2 * normSq a + 2 * (a ^ 2 * frame n j ^ 2).re := by
    have h := normSq_mul a (frame n j)
    rw [frame_normSq, mul_one, normSq_apply] at h
    have he : a ^ 2 * frame n j ^ 2 = (a * frame n j) ^ 2 := by ring
    rw [he]
    simp only [pow_two, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero] at h ⊢
    nlinarith
  have hsum : (∑ j : Fin n, ((a * frame n j) * (q j : ℂ)).re) =
      (n : ℝ) * normSq a := by
    rw [← Complex.re_sum]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, sum_frame_mul (by omega)]
    change (a * ((n : ℂ) * conj a)).re = _
    rw [show a * ((n : ℂ) * conj a) = (n : ℂ) * (a * conj a) by ring,
      mul_conj]
    simp
  have hnonneg : 0 ≤ ∑ j : Fin n, (q j - 2 * (a * frame n j).re) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp_rw [hpoint] at hnonneg
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hnonneg
  rw [hsum, ← Complex.re_sum, ← Finset.mul_sum, sum_frame_sq hn,
    mul_zero, zero_re, mul_zero, add_zero, sum_sq_eq (by omega) q] at hnonneg
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  change 2 * normSq a ≤ meanSquare q
  nlinarith

theorem increment_normSq {n : ℕ} (q : Fin n → ℝ) (j : Fin n) :
    normSq (increment q j) =
      4 * Real.sin (Real.pi / n) ^ 2 / (n : ℝ) ^ 2 * q j ^ 2 +
      16 * Real.sin (Real.pi / n) ^ 2 / (n : ℝ) ^ 2 *
        (firstCoefficient q * frame n j).im ^ 2 := by
  rw [increment, normSq_mul, frame_normSq, one_mul]
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, ofReal_re,
    ofReal_im, I_re, I_im, zero_mul, mul_zero, one_mul, sub_zero, zero_add, add_zero]
  ring

theorem difference_energy_exact {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) :
    (∑ j, normSq (difference (by omega) (canonicalLift q) j)) =
      4 * Real.sin (Real.pi / n) ^ 2 / n *
        (meanSquare q + 2 * normSq (firstCoefficient q)) := by
  rw [canonicalLift_difference hn]
  simp_rw [increment_normSq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_sq_eq (by omega) q, imaginary_frame_energy hn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp
  ring

theorem difference_energy_le {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) :
    (∑ j, normSq (difference (by omega) (canonicalLift q) j)) ≤
      8 * Real.pi ^ 2 / (n : ℝ) ^ 3 * meanSquare q := by
  rw [difference_energy_exact hn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcoef := firstCoefficient_bound hn q
  calc
    _ ≤ 4 * Real.sin (Real.pi / n) ^ 2 / n * (2 * meanSquare q) := by
      gcongr
      linarith
    _ ≤ 4 * (Real.pi / n) ^ 2 / n * (2 * meanSquare q) := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left Real.sin_sq_le_sq (by norm_num)) hnR.le)
        (mul_nonneg (by norm_num) (meanSquare_nonneg q))
    _ = _ := by ring

theorem finite_integral_norm_bound {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ)
    (hmean : ∑ j, c j = 0) (j : Fin n) :
    ‖c j‖ ≤ 2 * ∑ k, ‖difference hn c k‖ := by
  let u := periodize hn c
  let S := ∑ k ∈ Finset.range n, ‖u (k + 1) - u k‖
  have hprefix (k : ℕ) (hk : k ≤ n) : ‖u k - u 0‖ ≤ S := by
    rw [← Finset.sum_range_sub u k]
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
      (fun _ _ _ => norm_nonneg _)
  have hsum : (∑ k ∈ Finset.range n, u k) = 0 := by
    exact (periodize_sum hn c).trans hmean
  have hbase : ‖u 0‖ ≤ S := by
    have he : (∑ k ∈ Finset.range n, (u 0 - u k)) = (n : ℂ) * u 0 := by
      simp [Finset.sum_sub_distrib, hsum]
    have hb : ‖(n : ℂ) * u 0‖ ≤ (n : ℝ) * S := by
      rw [← he]
      refine (norm_sum_le _ _).trans ?_
      calc
        _ ≤ ∑ _k ∈ Finset.range n, S := by
          apply Finset.sum_le_sum
          intro k hk
          rw [norm_sub_rev]
          exact hprefix k (Finset.mem_range.mp hk).le
        _ = _ := by simp
    simp only [norm_mul, Complex.norm_natCast] at hb
    exact le_of_mul_le_mul_left hb (by exact_mod_cast hn : (0 : ℝ) < n)
  have hpoint : ‖u j‖ ≤ 2 * S := by
    calc
      _ = ‖(u j - u 0) + u 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖u j - u 0‖ + ‖u 0‖ := norm_add_le _ _
      _ ≤ S + S := add_le_add (hprefix j j.isLt.le) hbase
      _ = _ := by ring
  have hd (k : Fin n) : u (k.val + 1) - u k = difference hn c k := by
    simp only [u, periodize, difference, successor, Nat.mod_eq_of_lt k.isLt]
  have hS : S = ∑ k, ‖difference hn c k‖ := by
    dsimp [S]
    rw [← Fin.sum_univ_eq_sum_range (fun k => ‖u (k + 1) - u k‖) n]
    simp_rw [hd]
  rw [hS] at hpoint
  simpa only [u, periodize_fin] using hpoint

theorem finite_integral_sq_bound {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ)
    (hmean : ∑ j, c j = 0) (j : Fin n) :
    ‖c j‖ ^ 2 ≤ 4 * (n : ℝ) * ∑ k, normSq (difference hn c k) := by
  have hpoint := finite_integral_norm_bound hn c hmean j
  have hs := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun k : Fin n => ‖difference hn c k‖)
  simp only [Finset.card_univ, Fintype.card_fin, ← Complex.normSq_eq_norm_sq] at hs
  have hnonneg : 0 ≤ ∑ k, ‖difference hn c k‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  nlinarith [norm_nonneg (c j)]

theorem canonicalLift_norm_sq_le {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) (j : Fin n) :
    ‖canonicalLift q j‖ ^ 2 ≤ 32 * Real.pi ^ 2 / (n : ℝ) ^ 2 * meanSquare q := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  calc
    _ ≤ 4 * (n : ℝ) * ∑ k, normSq (difference (by omega) (canonicalLift q) k) :=
      finite_integral_sq_bound (by omega) _ (canonicalLift_mean_zero (by omega) q) j
    _ ≤ 4 * (n : ℝ) * (8 * Real.pi ^ 2 / (n : ℝ) ^ 3 * meanSquare q) := by
      gcongr
      exact difference_energy_le hn q
    _ = _ := by field_simp; ring

theorem canonicalLift_norm_le {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) (j : Fin n) :
    ‖canonicalLift q j‖ ≤ 6 * Real.pi / n * Real.sqrt (meanSquare q) := by
  have hsq := canonicalLift_norm_sq_le hn q j
  have hroot := Real.sq_sqrt (meanSquare_nonneg q)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hright : 0 ≤ 6 * Real.pi / n * Real.sqrt (meanSquare q) := by positivity
  have he : (6 * Real.pi / n * Real.sqrt (meanSquare q)) ^ 2 =
      36 * Real.pi ^ 2 / (n : ℝ) ^ 2 * meanSquare q := by
    rw [mul_pow, hroot]
    ring
  have hnonneg : 0 ≤ Real.pi ^ 2 / (n : ℝ) ^ 2 * meanSquare q := by
    exact mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (meanSquare_nonneg q)
  apply (sq_le_sq₀ (norm_nonneg _) hright).mp
  rw [he]
  calc
    _ ≤ 32 * (Real.pi ^ 2 / (n : ℝ) ^ 2 * meanSquare q) := by
      convert hsq using 1
      ring
    _ ≤ 36 * (Real.pi ^ 2 / (n : ℝ) ^ 2 * meanSquare q) :=
      mul_le_mul_of_nonneg_right (by norm_num) hnonneg
    _ = _ := by ring

theorem canonicalLift_sup_norm_le {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) :
    ‖canonicalLift q‖ ≤ 6 * Real.pi / n * Real.sqrt (meanSquare q) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  exact canonicalLift_norm_le hn q

theorem meanSquare_le_of_bound {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    {A : ℝ} (hA : 0 ≤ A) (hq : ∀ j, |q j| ≤ A) : meanSquare q ≤ A ^ 2 := by
  apply (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).2
  calc
    _ ≤ ∑ _j : Fin n, A ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hA).2 (hq j)
    _ = _ := by simp; ring

/-- Pointwise control before the exact closure correction in (4.10). -/
theorem increment_sq_le_of_bound {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ)
    {A : ℝ} (hA : 0 ≤ A) (hq : ∀ j, |q j| ≤ A) (j : Fin n) :
    normSq (increment q j) ≤ 12 * Real.sin (Real.pi / n) ^ 2 / (n : ℝ) ^ 2 * A ^ 2 := by
  have hm := meanSquare_le_of_bound (by omega) q hA hq
  have hf := firstCoefficient_bound hn q
  have hi : (firstCoefficient q * frame n j).im ^ 2 ≤ normSq (firstCoefficient q) := by
    have he := normSq_mul (firstCoefficient q) (frame n j)
    rw [frame_normSq, mul_one, normSq_apply] at he
    nlinarith [sq_nonneg (firstCoefficient q * frame n j).re]
  have hqj : q j ^ 2 ≤ A ^ 2 := by nlinarith [abs_le.mp (hq j)]
  have hs : 0 ≤ Real.sin (Real.pi / n) ^ 2 / (n : ℝ) ^ 2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [increment_normSq]
  calc
    _ = (Real.sin (Real.pi / n) ^ 2 / (n : ℝ) ^ 2) *
        (4 * q j ^ 2 + 16 * (firstCoefficient q * frame n j).im ^ 2) := by ring
    _ ≤ (Real.sin (Real.pi / n) ^ 2 / (n : ℝ) ^ 2) * (12 * A ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hs
      linarith
    _ = _ := by ring

end Erdos1045.EventualExact.SchurLiftBounds

import Erdos1045.LocalDFT
import Erdos1045.LocalChord
import Erdos1045.LocalNonlinear
import Mathlib.Algebra.BigOperators.Fin

/-!
# Uniform local strict maximality for arbitrary normalized perturbations

The gain is written exactly in pair-distance and perimeter ratios. Ordered
pairs are divided by two. Classical inputs are standard DFT orthogonality and
inversion, the geometric-sine formula, and a universal scalar logarithm bound.
All geometric, Fourier, coefficient, and absorption estimates are proved.
-/

namespace Erdos1045.LocalMaximum

open Complex
open scoped BigOperators
noncomputable section

def gain (n : ℕ) (u : ℕ → ℂ) : ℝ :=
  (∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n,
      2 * Real.log ‖1 + LocalDFT.pairRatio n u j h‖) / 2 -
    (n : ℝ) * ((n : ℝ) - 1) *
      Real.log ((∑ j ∈ Finset.range n, ‖1 + LocalDFT.pairRatio n u j 1‖) / (n : ℝ))

theorem edge_denominator_norm (n j : ℕ) :
    ‖LocalPhase.regularRoot n ^ (j + 1) - LocalPhase.regularRoot n ^ j‖ =
      ‖LocalPhase.regularRoot n - 1‖ := by
  rw [show LocalPhase.regularRoot n ^ (j + 1) - LocalPhase.regularRoot n ^ j =
    LocalPhase.regularRoot n ^ j * (LocalPhase.regularRoot n - 1) by rw [pow_succ]; ring]
  rw [norm_mul, norm_pow, LocalChord.root_norm, one_pow, one_mul]

theorem edge_ratio_bound {n : ℕ} (hn : 4 ≤ n) (u : ℕ → ℂ) {η : ℝ}
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖) (j : ℕ) :
    ‖LocalDFT.pairRatio n u j 1‖ ≤ η := by
  have hroot : LocalPhase.regularRoot n ≠ 1 := by
    simpa using LocalDFT.regularRoot_power_ne_one (by omega : 0 < n)
      (by omega : 0 < 1) (by omega : 1 < n)
  have hpos : 0 < ‖LocalPhase.regularRoot n - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hroot)
  unfold LocalDFT.pairRatio
  rw [norm_div, edge_denominator_norm]
  exact (div_le_iff₀ hpos).2 (hstep j)

theorem pair_ratio_bound (HS : LocalPhase.ClassicalGeometricSine) {n : ℕ}
    (hn : 4 ≤ n) (u : ℕ → ℂ) (hu : Function.Periodic u n) {η : ℝ} (hη : 0 ≤ η)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖)
    {h : ℕ} (hh : h ∈ (Finset.range n).erase 0) (j : ℕ) :
    ‖LocalDFT.pairRatio n u j h‖ ≤ 2 * η := by
  have hm := Finset.mem_erase.mp hh
  have hroot : LocalPhase.regularRoot n ≠ 1 := by
    simpa using LocalDFT.regularRoot_power_ne_one (by omega : 0 < n)
      (by omega : 0 < 1) (by omega : 1 < n)
  exact LocalChord.quotient_bound HS hn (by omega) (Finset.mem_range.mp hm.2) hroot
    (LocalDFT.regularRoot_pow (by omega)) u hu hη hstep j

theorem ratio_linear_sum_zero (HI : LocalDFT.ClassicalDFTInversion) {n h : ℕ}
    (hn : 0 < n) (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (u : ℕ → ℂ) (hu : Function.Periodic u n)
    (hsim : (∑ j ∈ Finset.range n, u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0)
    (hh : 0 < h) (hhn : h < n) :
    (∑ j ∈ Finset.range n, (LocalDFT.pairRatio n u j h).re) = 0 := by
  have hb := LocalDFT.coefficient_zero_of_similarity_normalization u hsim
  have hz := congrArg Complex.re (LocalFourier.ratio_sum_zero HF hn (LocalDFT.coefficient n u) hb h)
  simp only [Complex.re_sum, zero_re] at hz
  have heq : (∑ j ∈ Finset.range n,
      (LocalFourier.ratioFourier n (LocalPhase.regularRoot n) (LocalDFT.coefficient n u) j h).re) =
      ∑ j ∈ Finset.range n, (LocalDFT.pairRatio n u j h).re := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [LocalDFT.ratioFourier_eq_pairRatio HI hn u hu hh hhn]
  rwa [heq] at hz

/-- The nonlinear bound with the ordered-pair normalization correctly retained. -/
theorem gain_upper (HI : LocalDFT.ClassicalDFTInversion)
    (HS : LocalPhase.ClassicalGeometricSine) (HT : LocalNonlinear.ScalarLogTaylor)
    {n : ℕ} (hn : 4 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (u : ℕ → ℂ) (hu : Function.Periodic u n)
    (hsim : (∑ j ∈ Finset.range n, u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖) :
    gain n u ≤ -LocalDFT.positiveQuadratic n u +
      4 * η * (LocalDFT.energyA n u + (n : ℝ) * LocalDFT.energyB n u) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hpair (h : ℕ) (hh : h ∈ (Finset.range n).erase 0) :
      (∑ j ∈ Finset.range n, 2 * Real.log ‖1 + LocalDFT.pairRatio n u j h‖) ≤
        -(∑ j ∈ Finset.range n, (LocalDFT.pairRatio n u j h ^ 2).re) +
          4 * η * ∑ j ∈ Finset.range n, normSq (LocalDFT.pairRatio n u j h) := by
    have hm := Finset.mem_erase.mp hh
    have hl := ratio_linear_sum_zero HI hn0 HF u hu hsim (by omega) (Finset.mem_range.mp hm.2)
    have hp := Finset.sum_le_sum (s := Finset.range n) (fun j _ =>
      LocalNonlinear.pair_log_upper HT hη hsmall (pair_ratio_bound HS hn u hu hη hstep hh j))
    simpa [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hl, Complex.normSq_eq_norm_sq] using hp
  have hpairall := Finset.sum_le_sum (s := (Finset.range n).erase 0) hpair
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at hpairall
  let : NeZero n := ⟨by omega⟩
  have hedgeLinear : (∑ j : Fin n, (LocalDFT.pairRatio n u j.val 1).re) = 0 := by
    calc
      _ = ∑ j ∈ Finset.range n, (LocalDFT.pairRatio n u j 1).re :=
        (Finset.sum_range (fun j => (LocalDFT.pairRatio n u j 1).re)).symm
      _ = 0 := ratio_linear_sum_zero HI hn0 HF u hu hsim (by omega) (by omega)
  have hedge := LocalNonlinear.perimeter_log_lower hη hsmall
    (fun j : Fin n => LocalDFT.pairRatio n u j.val 1)
    (fun j => edge_ratio_bound hn u hstep j.val) hedgeLinear
  simp only [LocalNonlinear.imaginaryEnergy, Fintype.card_fin] at hedge
  have hImagFin : (∑ j : Fin n, (LocalDFT.pairRatio n u j.val 1).im ^ 2) =
      ∑ j ∈ Finset.range n, (LocalDFT.pairRatio n u j 1).im ^ 2 :=
    (Finset.sum_range (fun j => (LocalDFT.pairRatio n u j 1).im ^ 2)).symm
  have hNormFin : (∑ j : Fin n, ‖1 + LocalDFT.pairRatio n u j.val 1‖) =
      ∑ j ∈ Finset.range n, ‖1 + LocalDFT.pairRatio n u j 1‖ :=
    (Finset.sum_range (fun j => ‖1 + LocalDFT.pairRatio n u j 1‖)).symm
  rw [hImagFin, hNormFin] at hedge
  have hmult := mul_le_mul_of_nonneg_left hedge
    (show 0 ≤ (n : ℝ) * ((n : ℝ) - 1) by positivity)
  have hcancel : (n : ℝ) * ((n : ℝ) - 1) *
      ((1 - 2 * η) * LocalDFT.energyB n u / (2 * (n : ℝ))) =
      ((n : ℝ) - 1) / 2 * (1 - 2 * η) * LocalDFT.energyB n u := by field_simp
  change (n : ℝ) * ((n : ℝ) - 1) *
      ((1 - 2 * η) * LocalDFT.energyB n u / (2 * (n : ℝ))) ≤ _ at hmult
  rw [hcancel] at hmult
  have hB : 0 ≤ LocalDFT.energyB n u := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hηB := mul_nonneg hη hB
  have hnηB := mul_nonneg hnR.le hηB
  have hQ : LocalDFT.positiveQuadratic n u =
      (∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n,
        (LocalDFT.pairRatio n u j h ^ 2).re) / 2 +
        ((n : ℝ) - 1) / 2 * LocalDFT.energyB n u := by
    simp [LocalDFT.positiveQuadratic, Complex.div_ofNat_re, Complex.re_sum, pow_two]
  rw [hQ]
  unfold gain LocalDFT.energyA
  simp only [← Finset.mul_sum]
  nlinarith

theorem energyA_nonneg (n : ℕ) (u : ℕ → ℂ) : 0 ≤ LocalDFT.energyA n u := by
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => normSq_nonneg _

theorem energyB_nonneg (n : ℕ) (u : ℕ → ℂ) : 0 ≤ LocalDFT.energyB n u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Uniform local maximum estimate, including the nonlinear terms, for an
arbitrary normalized periodic perturbation of the actual regular polygon. -/
theorem local_maximum_bound (HI : LocalDFT.ClassicalDFTInversion)
    (HS : LocalPhase.ClassicalGeometricSine) (HT : LocalNonlinear.ScalarLogTaylor)
    {n : ℕ} (hn : 4 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (u : ℕ → ℂ) (hu : Function.Periodic u n)
    (hmean : (∑ j ∈ Finset.range n, u j) = 0)
    (hsim : (∑ j ∈ Finset.range n, u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 1000)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖) :
    gain n u ≤ -(LocalDFT.energyA n u + (n : ℝ) * LocalDFT.energyB n u) / 128 := by
  have hc := LocalDFT.normalized_coercivity HI HS hn HF u hu hmean hsim
  have hupp := gain_upper HI HS HT hn HF u hu hsim hη (by linarith) hstep
  exact LocalCoercivity.absorb_upper_remainder (energyA_nonneg n u) (energyB_nonneg n u)
    (Nat.cast_nonneg n) hsmall hc hupp

theorem nonnegative_gain_forces_zero (HI : LocalDFT.ClassicalDFTInversion)
    (HS : LocalPhase.ClassicalGeometricSine) (HT : LocalNonlinear.ScalarLogTaylor)
    {n : ℕ} (hn : 4 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (u : ℕ → ℂ) (hu : Function.Periodic u n)
    (hmean : (∑ j ∈ Finset.range n, u j) = 0)
    (hsim : (∑ j ∈ Finset.range n, u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 1000)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖)
    (hgain : 0 ≤ gain n u) : ∀ j, u j = 0 := by
  have h := local_maximum_bound HI HS HT hn HF u hu hmean hsim hη hsmall hstep
  have hA := energyA_nonneg n u
  have hB := mul_nonneg (Nat.cast_nonneg n) (energyB_nonneg n u)
  have hz : LocalDFT.energyA n u = 0 := by linarith
  exact LocalDFT.zero_energy_forces_zero HI (by omega) HF u hu hmean hz

theorem strict_local_maximum (HI : LocalDFT.ClassicalDFTInversion)
    (HS : LocalPhase.ClassicalGeometricSine) (HT : LocalNonlinear.ScalarLogTaylor)
    {n : ℕ} (hn : 4 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (u : ℕ → ℂ) (hu : Function.Periodic u n)
    (hmean : (∑ j ∈ Finset.range n, u j) = 0)
    (hsim : (∑ j ∈ Finset.range n, u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 1000)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖)
    (hne : ∃ j, u j ≠ 0) : gain n u < 0 := by
  by_contra h
  have hz := nonnegative_gain_forces_zero HI HS HT hn HF u hu hmean hsim hη hsmall hstep
    (not_lt.mp h)
  obtain ⟨j, hj⟩ := hne
  exact hj (hz j)

end

end Erdos1045.LocalMaximum

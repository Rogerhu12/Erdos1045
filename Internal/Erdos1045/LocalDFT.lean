import Erdos1045.LocalHessian

/-!
# Passing from an arbitrary periodic perturbation to its Fourier coefficients

The inversion theorem is a standard universal DFT input with its coefficients
defined by the finite Fourier sum. Normalization and the geometric Hessian
estimate for the given perturbation are conclusions, not assumptions.
-/

namespace Erdos1045.LocalDFT

open Complex
open scoped BigOperators
noncomputable section

def coefficient (n : ℕ) (u : ℕ → ℂ) (r : ℕ) : ℂ :=
  (∑ j ∈ Finset.range n, u j * (starRingEnd ℂ)
    (LocalPhase.regularRoot n ^ (j * (r + 1)))) / (n : ℂ)

/-- Ordinary finite Fourier inversion, merely with indices shifted by one.
This statement is universal in the periodic function being transformed. -/
def ClassicalDFTInversion : Prop :=
  ∀ n : ℕ, 0 < n → ∀ u : ℕ → ℂ, Function.Periodic u n → ∀ j : ℕ,
    u j = LocalFourier.displacement n (LocalPhase.regularRoot n) (coefficient n u) j

theorem regularRoot_pow {n : ℕ} (hn : 0 < n) : LocalPhase.regularRoot n ^ n = 1 := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold LocalPhase.regularRoot
  rw [← Complex.exp_nat_mul]
  have harg : (n : ℂ) * (((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * I) =
      2 * Real.pi * I := by push_cast; field_simp
  rw [harg, Complex.exp_two_pi_mul_I]

theorem regularRoot_power_ne_one {n h : ℕ} (hn : 0 < n) (hh : 0 < h) (hhn : h < n) :
    LocalPhase.regularRoot n ^ h ≠ 1 := by
  have he : LocalPhase.regularRoot n ^ h =
      Complex.exp (2 * Real.pi * I * (h : ℂ) / (n : ℂ)) := by
    unfold LocalPhase.regularRoot
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he]
  exact mt (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff hn.ne').mp
    (Nat.not_dvd_of_pos_of_lt hh hhn)

theorem vertex_difference_ne_zero {n h : ℕ} (hn : 0 < n) (hh : 0 < h)
    (hhn : h < n) (j : ℕ) :
    LocalPhase.regularRoot n ^ (j + h) - LocalPhase.regularRoot n ^ j ≠ 0 := by
  have hw : LocalPhase.regularRoot n ≠ 0 := Complex.exp_ne_zero _
  have hfactor : LocalPhase.regularRoot n ^ (j + h) - LocalPhase.regularRoot n ^ j =
      LocalPhase.regularRoot n ^ j * (LocalPhase.regularRoot n ^ h - 1) := by
    rw [pow_add]
    ring
  rw [hfactor]
  exact mul_ne_zero (pow_ne_zero _ hw) (sub_ne_zero.mpr (regularRoot_power_ne_one hn hh hhn))

theorem coefficient_zero_of_similarity_normalization {n : ℕ} (u : ℕ → ℂ)
    (hu : (∑ j ∈ Finset.range n, u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0) :
    coefficient n u 0 = 0 := by
  simpa [coefficient] using congrArg (fun z : ℂ => z / n) hu

theorem coefficient_last_of_translation_normalization {n : ℕ} (hn : 0 < n)
    (u : ℕ → ℂ) (hu : (∑ j ∈ Finset.range n, u j) = 0) : coefficient n u (n - 1) = 0 := by
  unfold coefficient
  simp only [Nat.sub_add_cancel (show 1 ≤ n by omega)]
  have hp (j : ℕ) : LocalPhase.regularRoot n ^ (j * n) = 1 := by
    rw [Nat.mul_comm, pow_mul, regularRoot_pow hn, one_pow]
  simp only [hp, map_one, mul_one, hu, zero_div]

def pairRatio (n : ℕ) (u : ℕ → ℂ) (j h : ℕ) : ℂ :=
  (u (j + h) - u j) /
    (LocalPhase.regularRoot n ^ (j + h) - LocalPhase.regularRoot n ^ j)

theorem ratioFourier_eq_pairRatio (HI : ClassicalDFTInversion) {n h : ℕ}
    (hn : 0 < n) (u : ℕ → ℂ) (hu : Function.Periodic u n)
    (hh : 0 < h) (hhn : h < n) (j : ℕ) :
    LocalFourier.ratioFourier n (LocalPhase.regularRoot n) (coefficient n u) j h =
      pairRatio n u j h := by
  rw [LocalFourier.ratio_eq_difference_quotient n _ _ j h (vertex_difference_ne_zero hn hh hhn j)]
  rw [← HI n hn u hu (j + h), ← HI n hn u hu j]
  rfl

def energyA (n : ℕ) (u : ℕ → ℂ) : ℝ :=
  (∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n,
    normSq (pairRatio n u j h)) / 2

def energyB (n : ℕ) (u : ℕ → ℂ) : ℝ :=
  ∑ j ∈ Finset.range n, (pairRatio n u j 1).im ^ 2

def positiveQuadratic (n : ℕ) (u : ℕ → ℂ) : ℝ :=
  ((∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n,
      pairRatio n u j h * pairRatio n u j h) / 2 : ℂ).re +
    ((n : ℝ) - 1) / 2 * energyB n u

theorem energyA_eq_fourier (HI : ClassicalDFTInversion) {n : ℕ} (hn : 0 < n)
    (u : ℕ → ℂ) (hu : Function.Periodic u n) :
    energyA n u = LocalHessian.geometricA n (coefficient n u) := by
  unfold energyA LocalHessian.geometricA
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  have hmem := Finset.mem_erase.mp hh
  apply Finset.sum_congr rfl
  intro j hj
  rw [ratioFourier_eq_pairRatio HI hn u hu (by omega) (Finset.mem_range.mp hmem.2)]

theorem energyB_eq_fourier (HI : ClassicalDFTInversion) {n : ℕ} (hn : 2 ≤ n)
    (u : ℕ → ℂ) (hu : Function.Periodic u n) :
    energyB n u = LocalHessian.geometricB n (coefficient n u) := by
  unfold energyB LocalHessian.geometricB
  apply Finset.sum_congr rfl
  intro j hj
  rw [ratioFourier_eq_pairRatio HI (by omega) u hu (by omega) (by omega)]

theorem quadratic_eq_fourier (HI : ClassicalDFTInversion) {n : ℕ} (hn : 2 ≤ n)
    (u : ℕ → ℂ) (hu : Function.Periodic u n) :
    positiveQuadratic n u = LocalHessian.geometricQ n (coefficient n u) := by
  unfold positiveQuadratic LocalHessian.geometricQ
  rw [energyB_eq_fourier HI hn u hu]
  congr 3
  apply Finset.sum_congr rfl
  intro h hh
  have hmem := Finset.mem_erase.mp hh
  apply Finset.sum_congr rfl
  intro j hj
  rw [ratioFourier_eq_pairRatio HI (by omega) u hu (by omega) (Finset.mem_range.mp hmem.2)]

/-- Uniform geometric coercivity for every normalized periodic perturbation. -/
theorem normalized_coercivity (HI : ClassicalDFTInversion)
    (HS : LocalPhase.ClassicalGeometricSine) {n : ℕ} (hn : 4 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (u : ℕ → ℂ) (hu : Function.Periodic u n)
    (hmean : (∑ j ∈ Finset.range n, u j) = 0)
    (hsim : (∑ j ∈ Finset.range n, u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0) :
    (energyA n u + (n : ℝ) * energyB n u) / 64 ≤ positiveQuadratic n u := by
  rw [energyA_eq_fourier HI (by omega) u hu, energyB_eq_fourier HI (by omega) u hu,
    quadratic_eq_fourier HI (by omega) u hu]
  exact LocalHessian.geometric_coercivity HS hn HF (coefficient n u)
    (coefficient_zero_of_similarity_normalization u hsim)
    (coefficient_last_of_translation_normalization (by omega) u hmean)

theorem zero_energy_forces_zero (HI : ClassicalDFTInversion) {n : ℕ} (hn : 0 < n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (u : ℕ → ℂ) (hu : Function.Periodic u n) (hmean : (∑ j ∈ Finset.range n, u j) = 0)
    (hA : energyA n u = 0) : ∀ j, u j = 0 := by
  rw [energyA_eq_fourier HI hn u hu] at hA
  have hz := LocalHessian.geometricA_zero_forces_zero hn HF (coefficient n u)
    (coefficient_last_of_translation_normalization hn u hmean) hA
  intro j
  rw [HI n hn u hu j, hz j]

end

end Erdos1045.LocalDFT

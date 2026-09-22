import Erdos1045.ClosedDFT
import Erdos1045.ClosedGeometricSine

/-! The stronger B-only coercivity needed for the strict pressure gap. -/

namespace Erdos1045.EventualExact.CoercivityRefinement

open Complex
open scoped BigOperators
noncomputable section

theorem paired_B_sum {ι : Type*} [Fintype ι] (n : ℝ) (p : ι → ι)
    (hp : Function.Involutive p) (x : ι → ℂ) :
    LocalPairing.energyB n p x = n / 4 *
      ∑ i, normSq (x i + (starRingEnd ℂ) (x (p i))) := by
  have hi := LocalPairing.sum_involution p hp (fun i => normSq (x i))
  have hc (z : ℂ) : normSq (star z) = normSq z := normSq_conj z
  simp only [normSq_add, starRingEnd_apply, star_star, hc,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hi]
  unfold LocalPairing.energyB
  rw [Complex.re_sum]
  ring

theorem paired_B_coercivity {ι : Type*} [Fintype ι] {n : ℝ} (hn : 0 ≤ n)
    (p : ι → ι) (hp : Function.Involutive p) (r : ι → ℝ) (x : ι → ℂ)
    (hr : ∀ i, 0 ≤ r i) (hupper : ∀ i, r i ≤ (5 / 6 : ℝ) * (n - 1)) :
    (n - 1) / 12 * LocalPairing.energyB n p x ≤ LocalPairing.quadratic n p r x := by
  have hpoint (i : ι) :
      n * (n - 1) / 24 * normSq (x i + (starRingEnd ℂ) (x (p i))) ≤
        LocalCoercivity.blockEnergy n (r i) (x i) ((starRingEnd ℂ) (x (p i))) := by
    have hcoeff := mul_le_mul_of_nonneg_right (hupper i)
      (normSq_nonneg (x i + (starRingEnd ℂ) (x (p i))))
    have hdrop := mul_nonneg (hr i) (normSq_nonneg (x i - (starRingEnd ℂ) (x (p i))))
    have hmul := mul_le_mul_of_nonneg_left (show
        (n - 1) / 6 * normSq (x i + (starRingEnd ℂ) (x (p i))) ≤
        (n - 1 - r i) * normSq (x i + (starRingEnd ℂ) (x (p i))) +
          r i * normSq (x i - (starRingEnd ℂ) (x (p i))) by linarith) (div_nonneg hn (by norm_num : (0 : ℝ) ≤ 4))
    unfold LocalCoercivity.blockEnergy
    convert hmul using 1 <;> first | rfl | ring
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  rw [← Finset.mul_sum] at hs
  rw [paired_B_sum n p hp x, LocalPairing.quadratic_eq_half_sum_blocks n p hp r x]
  nlinarith

theorem full_B_coercivity {n : ℕ} (hn : 4 ≤ n) (b : ℕ → ℂ)
    (hzero : b 0 = 0) (hlast : b (n - 1) = 0) :
    ((n : ℝ) - 1) / 12 * LocalSpectrum.fullB n b ≤ LocalSpectrum.fullQ n b := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hp := paired_B_coercivity (show (0 : ℝ) ≤ n by positivity)
    LocalSpectrum.pairedPartner (LocalSpectrum.pairedPartner_involutive n)
    LocalSpectrum.ratio (LocalSpectrum.amplitude (n := n) b)
    (fun i => (LocalSpectrum.coefficient_bounds hn i).1.le)
    (fun i => (LocalSpectrum.coefficient_bounds hn i).2.1)
  rw [LocalSpectrum.fullB_split hn b hzero hlast, LocalSpectrum.fullQ_split hn b hzero hlast]
  have hnonneg : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) *
      LocalTrigonometry.mode (n : ℝ) 2 ^ 2 * normSq (b 1) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith))
      (sq_nonneg _)) (normSq_nonneg _)
  nlinarith

/-- The manuscript's (3.5), for actual normalized geometric edge quotients. -/
theorem normalized_B_coercivity {n : ℕ} (hn : 4 ≤ n)
    (u : ℕ → ℂ) (hu : Function.Periodic u n)
    (hmean : (∑ j ∈ Finset.range n, u j) = 0)
    (hsim : (∑ j ∈ Finset.range n, u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0) :
    ((n : ℝ) - 1) / 12 * LocalDFT.energyB n u ≤ LocalDFT.positiveQuadratic n u := by
  have hzero := LocalDFT.coefficient_zero_of_similarity_normalization u hsim
  have hlast := LocalDFT.coefficient_last_of_translation_normalization (by omega) u hmean
  rw [LocalDFT.energyB_eq_fourier ClosedFourier.dftInversion (by omega) u hu,
    LocalDFT.quadratic_eq_fourier ClosedFourier.dftInversion (by omega) u hu,
    ← LocalHessian.fullB_eq_geometric ClosedFourier.geometricSine (by omega)
      (ClosedFourier.orthogonality n (by omega)) _ hzero,
    ← LocalHessian.fullQ_eq_geometric ClosedFourier.geometricSine (by omega)
      (ClosedFourier.orthogonality n (by omega)) _ hzero]
  exact full_B_coercivity hn _ hzero hlast

end
end Erdos1045.EventualExact.CoercivityRefinement

import Erdos1045.LocalSpectrum
import Erdos1045.LocalPhase

/-!
# Coercivity of the actual finite geometric ratios

This is the connection between the proved Fourier identities, the actual sine
coefficient bounds, and the local Hessian. In particular, inequality (6.5) is a
conclusion here. It is not an external classical input or a supplied hypothesis.
-/

namespace Erdos1045.LocalHessian

open Complex
open scoped BigOperators
noncomputable section

def geometricA (n : ℕ) (b : ℕ → ℂ) : ℝ :=
  (∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n,
    normSq (LocalFourier.ratioFourier n (LocalPhase.regularRoot n) b j h)) / 2

def geometricB (n : ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ j ∈ Finset.range n,
    (LocalFourier.ratioFourier n (LocalPhase.regularRoot n) b j 1).im ^ 2

def geometricQ (n : ℕ) (b : ℕ → ℂ) : ℝ :=
  ((∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n,
      LocalFourier.ratioFourier n (LocalPhase.regularRoot n) b j h *
        LocalFourier.ratioFourier n (LocalPhase.regularRoot n) b j h) / 2 : ℂ).re +
    ((n : ℝ) - 1) / 2 * geometricB n b

theorem fullA_eq_geometric {n : ℕ} (hn : 0 < n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n)) (b : ℕ → ℂ) :
    LocalSpectrum.fullA n b = geometricA n b := by
  exact (LocalFourier.ratio_energy HF hn b).symm

theorem fullB_eq_geometric (HS : LocalPhase.ClassicalGeometricSine) {n : ℕ}
    (hn : 2 ≤ n) (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (b : ℕ → ℂ) (hzero : b 0 = 0) : LocalSpectrum.fullB n b = geometricB n b := by
  have hnrm (r : ℕ) : normSq (LocalSpectrum.fullAmplitude n b r) =
      LocalTrigonometry.mode (n : ℝ) (r + 1 : ℝ) ^ 2 * normSq (b r) := by
    simp [LocalSpectrum.fullAmplitude, normSq_mul, normSq_ofReal, pow_two]
  have hcross (r : ℕ) :
      (LocalSpectrum.fullAmplitude n b r *
        LocalSpectrum.fullAmplitude n b (LocalFourier.partner n r)).re =
        ((((LocalTrigonometry.mode (n : ℝ) (r + 1 : ℝ) *
          LocalTrigonometry.mode (n : ℝ) (LocalFourier.partner n r + 1 : ℝ) : ℝ) : ℂ) *
          b r * b (LocalFourier.partner n r))).re := by
    simp [LocalSpectrum.fullAmplitude, mul_re, mul_im]
    ring
  have he := LocalPhase.edge_imaginary_energy HS hn HF b hzero
  simpa only [LocalSpectrum.fullB, geometricB, hnrm, hcross, ← Complex.re_sum] using he.symm

theorem fullQ_eq_geometric (HS : LocalPhase.ClassicalGeometricSine) {n : ℕ}
    (hn : 2 ≤ n) (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (b : ℕ → ℂ) (hzero : b 0 = 0) : LocalSpectrum.fullQ n b = geometricQ n b := by
  have he := congrArg Complex.re (LocalFourier.ratio_square_sum HF (by omega) b hzero)
  have hscalar : -(n : ℂ) / 2 = ((-(n : ℝ) / 2 : ℝ) : ℂ) := by push_cast; rfl
  have hterm (r : ℕ) :
      (((r : ℂ) - 1) * ((n : ℂ) - (r + 1)) * b r * b (LocalFourier.partner n r)).re =
        ((r : ℝ) - 1) * ((n : ℝ) - (r + 1)) * (b r * b (LocalFourier.partner n r)).re := by
    simp [mul_re, mul_im]
    ring
  rw [hscalar, Complex.re_ofReal_mul, Complex.re_sum] at he
  simp_rw [hterm] at he
  unfold LocalSpectrum.fullQ geometricQ
  rw [← he, fullB_eq_geometric HS hn HF b hzero]

/-- The manuscript's uniform local coercivity (6.5), for actual pair and edge
ratios of the explicitly defined Fourier perturbation. -/
theorem geometric_coercivity (HS : LocalPhase.ClassicalGeometricSine) {n : ℕ}
    (hn : 4 ≤ n) (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (b : ℕ → ℂ) (hzero : b 0 = 0) (hlast : b (n - 1) = 0) :
    (geometricA n b + (n : ℝ) * geometricB n b) / 64 ≤ geometricQ n b := by
  rw [← fullA_eq_geometric (by omega) HF, ← fullB_eq_geometric HS (by omega) HF b hzero,
    ← fullQ_eq_geometric HS (by omega) HF b hzero]
  exact LocalSpectrum.full_spectral_coercivity hn b hzero hlast

theorem geometricA_nonneg (n : ℕ) (b : ℕ → ℂ) : 0 ≤ geometricA n b := by
  unfold geometricA
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => normSq_nonneg _

theorem geometricB_nonneg (n : ℕ) (b : ℕ → ℂ) : 0 ≤ geometricB n b := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem geometricA_zero_forces_zero {n : ℕ} (hn : 0 < n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (b : ℕ → ℂ) (hlast : b (n - 1) = 0) (hA : geometricA n b = 0) :
    ∀ j, LocalFourier.displacement n (LocalPhase.regularRoot n) b j = 0 := by
  have hsum : (∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n,
      normSq (LocalFourier.ratioFourier n (LocalPhase.regularRoot n) b j h)) = 0 := by
    unfold geometricA at hA
    linarith
  have hb := LocalFourier.zero_pair_energy_forces_coefficients_zero HF hn b hlast hsum
  exact LocalFourier.displacement_zero_of_coefficients_zero _ b hb

end

end Erdos1045.LocalHessian

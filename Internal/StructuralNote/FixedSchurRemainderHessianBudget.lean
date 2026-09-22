import StructuralNote.FixedSchurGeometricRemainderHessian

/-! A uniform scalar budget for the physical remainder Hessian. The inputs
are the base, velocity and acceleration pair energies, keeping their roles
explicit for substitution from the actual chosen-chart bounds. -/

namespace StructuralNote.FixedSchurRemainderHessianBudget

open Complex Erdos1045.EventualExact SchurSpectrum
open GeometricRelativeRemainder SignedPressureAngular FixedSchurGeometricRemainderHessian
open scoped BigOperators

noncomputable section

theorem remainder_energy_budget {n : ℕ} (hn : 0 < n)
    (C D V W A B : Fin n → ℂ) {t K : ℝ}
    (ht : 0 ≤ t) (htsmall : t ≤ 1 / 144) (hK : 0 ≤ K)
    (hu : ∀ p, ‖quotient C (root n) p‖ ≤ 36 * t)
    (hx : ∀ p, ‖quotient D (root n) p‖ ≤ 11 * t)
    (hC : pairEnergy hn C ≤ 1602)
    (hV : pairEnergy hn V ≤ 5120002 * K)
    (hW : pairEnergy hn W ≤ 18 * K)
    (hA : pairEnergy hn A ≤ 32 * K ^ 2)
    (hB : pairEnergy hn B ≤ 500 * K ^ 2) :
    |analyticSecond C D V W A B| ≤ 300000000000 * t * K := by
  have ht1 : t ≤ 1 := by linarith
  have ht2 : t ^ 2 ≤ t := by nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1)]
  have hcoef : 11 * t + (36 * t) ^ 2 ≤ 1307 * t := by nlinarith only [ht2]
  have hU2 : (36 * t) ^ 2 ≤ 1296 * t := by nlinarith only [ht2]
  have hCs : Real.sqrt (pairEnergy hn C) ≤ 41 := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by norm_num, by linarith only [hC]⟩
  have hAs : Real.sqrt (pairEnergy hn A) ≤ 6 * K := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by positivity, by nlinarith only [hA, sq_nonneg K]⟩
  have hBs : Real.sqrt (pairEnergy hn B) ≤ 23 * K := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by positivity, by nlinarith only [hB, sq_nonneg K]⟩
  have hcross : Real.sqrt (pairEnergy hn V) * Real.sqrt (pairEnergy hn W) ≤ 3000000 * K := by
    have hs := sq_nonneg (Real.sqrt (pairEnergy hn V) - Real.sqrt (pairEnergy hn W))
    have hv := Real.sq_sqrt (pairEnergy_nonneg hn V)
    have hw := Real.sq_sqrt (pairEnergy_nonneg hn W)
    nlinarith only [hs, hv, hw, hV, hW, hK]
  have hCA := mul_le_mul hCs hAs (Real.sqrt_nonneg _) (show (0 : ℝ) ≤ 41 by norm_num)
  have hCB := mul_le_mul hCs hBs (Real.sqrt_nonneg _) (show (0 : ℝ) ≤ 41 by norm_num)
  have h1 := mul_le_mul hcoef hV (pairEnergy_nonneg hn V) (by positivity : 0 ≤ 1307 * t)
  have h2 := mul_le_mul_of_nonneg_left hcross (by positivity : 0 ≤ 64 * (36 * t))
  have h3 := mul_le_mul hU2 hW (pairEnergy_nonneg hn W) (by positivity : 0 ≤ 1296 * t)
  have h4 := mul_le_mul hcoef hCA
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity : 0 ≤ 1307 * t)
  have h5 := mul_le_mul_of_nonneg_left hCB (by positivity : 0 ≤ 32 * (36 * t))
  have hb := analyticSecond_abs_le hn C D V W A B
    (by positivity : 0 ≤ 36 * t) (by linarith : 36 * t ≤ 1 / 4)
    (by positivity : 0 ≤ 11 * t) (by linarith : 11 * t ≤ 1 / 4) hu hx
  have hprod := mul_nonneg ht hK
  ring_nf at hb h1 h2 h3 h4 h5 hprod ⊢
  linarith only [hb, h1, h2, h3, h4, h5, hprod]

end
end StructuralNote.FixedSchurRemainderHessianBudget

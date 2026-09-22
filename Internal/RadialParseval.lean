import FaberKernelGenerating
import RadialEnergy
import Erdos1045.DirectFourierParseval

/-! Parseval on actual interior circles of an analytic function. -/

namespace ExteriorReduction

open Complex Metric MeasureTheory
open FaberKernel
open scoped ComplexConjugate
noncomputable section

private theorem conj_circle_pow (r t : ℝ) (n : ℕ) :
    conj (circleMap 0 r t) ^ n =
      (r : ℂ) ^ n * Erdos1045.FaberFourier.character n t := by
  rw [conj_circleMap_zero, circleMap_zero, mul_pow]
  congr 1
  unfold Erdos1045.FaberFourier.character
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem circle_taylor_fourier_conj {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (t : ℝ) :
    Erdos1045.FaberFourier.series
      (fun n => conj (taylorCoefficients q n) * (r : ℂ) ^ n) t =
      conj (q (circleMap 0 r t)) := by
  have hz : circleMap 0 r t ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_nonneg hr0]
    exact hr1
  have hs := Complex.hasSum_conj'.mpr (canonical_taylor_hasSum hq hz)
  have he (n : ℕ) : conj (taylorCoefficients q n * circleMap 0 r t ^ n) =
      (conj (taylorCoefficients q n) * (r : ℂ) ^ n) * Erdos1045.FaberFourier.character n t := by
    rw [map_mul, map_pow, conj_circle_pow]
    ring
  simpa only [he, Erdos1045.FaberFourier.series] using hs.tsum_eq

theorem circle_taylor_norm_summable {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => ‖conj (taylorCoefficients q n) * (r : ℂ) ^ n‖) := by
  have hz : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa [mem_ball_zero_iff, abs_of_nonneg hr0] using hr1
  simpa only [norm_mul, norm_conj] using canonical_taylor_norm_summable hq hz

/-- Finite-circle Parseval, derived from the actual Taylor series and the
already proved Fourier Parseval theorem. No coefficient square sum is assumed. -/
theorem analytic_circle_parseval {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => ‖taylorCoefficients q n‖ ^ 2 * r ^ (2 * n)) ∧
      Real.circleAverage (fun z => ‖q z‖ ^ 2) 0 r =
        ∑' n, ‖taylorCoefficients q n‖ ^ 2 * r ^ (2 * n) := by
  have hd := circle_taylor_norm_summable hq.differentiableOn hr0 hr1
  obtain ⟨hsq, _, he⟩ := Erdos1045.DirectFourier.parseval _ hd
  have hecoeff (n : ℕ) :
      ‖conj (taylorCoefficients q n) * (r : ℂ) ^ n‖ ^ 2 =
        ‖taylorCoefficients q n‖ ^ 2 * r ^ (2 * n) := by
    simp only [norm_mul, norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0, mul_pow, ← pow_mul, Nat.mul_comm]
  simp only [hecoeff] at hsq he
  refine ⟨hsq, ?_⟩
  have heint : Erdos1045.FaberFourier.energy
      (Erdos1045.FaberFourier.series
        (fun n => conj (taylorCoefficients q n) * (r : ℂ) ^ n)) =
      ∫ t in 0..2 * Real.pi, ‖q (circleMap 0 r t)‖ ^ 2 := by
    unfold Erdos1045.FaberFourier.energy Erdos1045.FaberFourier.circleMeasure
    rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    simp_rw [circle_taylor_fourier_conj hq.differentiableOn hr0 hr1, norm_conj]
  rw [heint] at he
  rw [Real.circleAverage_def, smul_eq_mul, he]
  field_simp

#print axioms analytic_circle_parseval

end
end ExteriorReduction

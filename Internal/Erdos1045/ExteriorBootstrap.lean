import Erdos1045.ExteriorMatrix
import Erdos1045.Bootstrap

namespace Erdos1045.ExteriorClassical

open Configuration MatrixDefect ExteriorBoundary
noncomputable section

/-- The actual matrix estimate and the classical perimeter identities imply
the inverse-square capacity and energy bounds. No asymptotic error is a premise. -/
theorem ExteriorData.bootstrap_bound {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HC : CircleMatrix.ClassicalCircleIdentities) (HM : ClassicalMatrixFacts)
    (hn : 4 ≤ n) (hΔ : (n : ℝ) ^ n ≤ discriminant z)
    {K : ℝ} (hK : 0 ≤ K)
    (hR : frobSq d.errorMatrix ≤ K * (n : ℝ) ^ 2 * d.energySquared)
    (hlarge : 4 * K * (18 * Real.pi) ≤ n) :
    (n : ℝ) ^ 2 * (1 - d.capacity) ≤ 16 * K * (18 * Real.pi) ∧
      (n : ℝ) ^ 2 * d.energySquared ≤ 16 * K * (18 * Real.pi) ^ 2 := by
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have he0 := d.toBoundaryData.energySquared_nonneg
  have hesq := Real.sq_sqrt he0
  have hroot : Real.sqrt (frobSq d.errorMatrix) ≤
      Real.sqrt K * (n : ℝ) * Real.sqrt d.energySquared := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    simpa only [mul_pow, Real.sq_sqrt hK, Real.sq_sqrt he0] using hR
  have hquad : frobSq d.errorMatrix / n ≤ K * n * d.energySquared := by
    apply (div_le_iff₀ hn').2
    convert hR using 1 <;> first | rfl | ring
  have ht0 := (d.trace_nonneg HC HM hn0 hΔ).2
  have ht := d.trace_coarse_bound hn0
  have htrace : 0 ≤ -((n : ℝ) * (n - 1)) * (1 - d.capacity) +
      (2 * Real.sqrt K) * n * Real.sqrt d.energySquared +
      K * n * (Real.sqrt d.energySquared) ^ 2 := by
    rw [hesq]
    nlinarith
  have hb := Bootstrap.quantitative_bootstrap (by exact_mod_cast hn)
    (sub_nonneg.mpr d.toBoundaryData.capacity_le_one) hK
    (show 0 ≤ 18 * Real.pi by positivity)
    (show (Real.sqrt d.energySquared) ^ 2 ≤ 18 * Real.pi * (1 - d.capacity) by
      rw [hesq]; exact d.toBoundaryData.coarse_energy)
    hlarge htrace
  simp only [mul_pow, Real.sq_sqrt hK, Real.sq_sqrt he0] at hb
  constructor
  · nlinarith [hb.1]
  · nlinarith [hb.2]

end
end Erdos1045.ExteriorClassical

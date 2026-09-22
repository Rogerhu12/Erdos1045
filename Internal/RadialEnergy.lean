import LogMeanEnergy
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# Energy on actual interior circles of a zero-free analytic function

The integrability and both mean identities are derived from analyticity,
nonvanishing and the normalization at zero. No boundary root, boundary
logarithm, or separately assumed mean identity is used.
-/

namespace ExteriorReduction

open Complex Metric Set Filter
open scoped Topology

noncomputable section

def radialMeanNorm (F : ℂ → ℂ) (r : ℝ) : ℝ :=
  Real.circleAverage (fun z => ‖F z‖) 0 r

def radialMeanEnergy (F : ℂ → ℂ) (r : ℝ) : ℝ :=
  Real.circleAverage (fun z => ‖F z - 1‖ ^ 2) 0 r

theorem analytic_real_mean_one {F : ℂ → ℂ} {r : ℝ}
    (hF : AnalyticOnNhd ℂ F (closedBall 0 |r|)) (hzero : F 0 = 1) :
    Real.circleAverage (fun z => (F z).re) 0 r = 1 := by
  have hh : InnerProductSpace.HarmonicOnNhd (fun z => (F z).re)
      (closedBall 0 |r|) := fun z hz => (hF z hz).harmonicAt_re
  rw [hh.circleAverage_eq, hzero]
  simp

theorem analytic_mean_norm_ge_one {F : ℂ → ℂ} {r : ℝ}
    (hF : AnalyticOnNhd ℂ F (closedBall 0 |r|)) (hzero : F 0 = 1) :
    1 ≤ radialMeanNorm F r := by
  have hc := hF.continuousOn.mono sphere_subset_closedBall
  have hre : ContinuousOn (fun z => (F z).re) (sphere 0 |r|) :=
    Complex.continuous_re.comp_continuousOn hc
  have hi := Real.circleAverage_mono hre.circleIntegrable' hc.norm.circleIntegrable'
    (fun z _ => Complex.re_le_norm (F z))
  rw [analytic_real_mean_one hF hzero] at hi
  exact hi

/-- The norm-square deviation identity, with its mean supplied by analyticity. -/
theorem analytic_circle_variance {F : ℂ → ℂ} {r : ℝ}
    (hF : AnalyticOnNhd ℂ F (closedBall 0 |r|)) (hzero : F 0 = 1) :
    radialMeanEnergy F r = Real.circleAverage (fun z => ‖F z‖ ^ 2) 0 r - 1 := by
  have hc := hF.continuousOn.mono sphere_subset_closedBall
  have hsq := (hc.norm.pow 2).circleIntegrable'
  have hre := (Complex.continuous_re.comp_continuousOn hc).circleIntegrable'
  have hs (z : ℂ) : ‖z - 1‖ ^ 2 = ‖z‖ ^ 2 - 2 * z.re + 1 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  unfold radialMeanEnergy
  simp_rw [hs]
  rw [Real.circleAverage_fun_add (f₁ := fun z => ‖F z‖ ^ 2 - 2 * (F z).re)
      (f₂ := fun _ => (1 : ℝ)) (hsq.sub (hre.const_smul (a := (2 : ℝ))))
      (circleIntegrable_const 1 0 r),
    Real.circleAverage_fun_sub (f₁ := fun z => ‖F z‖ ^ 2)
      (f₂ := fun z => 2 * (F z).re) hsq (hre.const_smul (a := (2 : ℝ))),
    show (fun z => 2 * (F z).re) = (fun z => (2 : ℝ) • (F z).re) from rfl,
    Real.circleAverage_fun_smul, analytic_real_mean_one hF hzero,
    Real.circleAverage_const]
  simp
  ring

/-- Finite-radius energy from ordinary analytic hypotheses alone. -/
theorem analytic_circle_energy_bound {F : ℂ → ℂ} {r B : ℝ}
    (hF : AnalyticOnNhd ℂ F (closedBall 0 |r|))
    (hne : ∀ z ∈ closedBall 0 |r|, F z ≠ 0) (hzero : F 0 = 1)
    (hB : 1 ≤ B) (hbound : ∀ z ∈ sphere 0 |r|, ‖F z‖ ≤ B) :
    radialMeanEnergy F r ≤ 2 * (B + 1) * (radialMeanNorm F r - 1) := by
  have hc := hF.continuousOn.mono sphere_subset_closedBall
  have hnorm := hc.norm.circleIntegrable'
  have hsq := (hc.norm.pow 2).circleIntegrable'
  have hlog : CircleIntegrable (fun z => Real.log ‖F z‖) 0 r :=
    (hc.norm.log (fun z hz => norm_ne_zero_iff.mpr
      (hne z (sphere_subset_closedBall hz)))).circleIntegrable'
  have hone := circleIntegrable_const (1 : ℝ) 0 r
  have hlog2 := hlog.const_smul (a := (2 : ℝ))
  have hi := Real.circleAverage_mono
    ((hsq.sub hone).sub hlog2)
    (((hnorm.sub hone).sub hlog).const_smul (a := 2 * (B + 1)))
    (fun z hz => scalar_log_moment_bound
      (norm_pos_iff.mpr (hne z (sphere_subset_closedBall hz))) hB (hbound z hz))
  change Real.circleAverage (fun z => ‖F z‖ ^ 2 - 1 - 2 * Real.log ‖F z‖) 0 r ≤
    Real.circleAverage (fun z => (2 * (B + 1)) • (‖F z‖ - 1 - Real.log ‖F z‖)) 0 r at hi
  rw [Real.circleAverage_fun_sub (f₁ := fun z => ‖F z‖ ^ 2 - 1)
      (f₂ := fun z => 2 * Real.log ‖F z‖) (hsq.sub hone) hlog2,
    Real.circleAverage_fun_sub (f₁ := fun z => ‖F z‖ ^ 2)
      (f₂ := fun _ => (1 : ℝ)) hsq hone,
    show (fun z => 2 * Real.log ‖F z‖) = (fun z => (2 : ℝ) • Real.log ‖F z‖) from rfl,
    Real.circleAverage_fun_smul, Real.circleAverage_fun_smul,
    Real.circleAverage_fun_sub (f₁ := fun z => ‖F z‖ - 1)
      (f₂ := fun z => Real.log ‖F z‖) (hnorm.sub hone) hlog,
    Real.circleAverage_fun_sub (f₁ := fun z => ‖F z‖)
      (f₂ := fun _ => (1 : ℝ)) hnorm hone,
    analytic_log_mean_zero hF hne hzero, Real.circleAverage_const] at hi
  rw [analytic_circle_variance hF hzero]
  simpa [radialMeanNorm] using hi

/-- Every closed subdisk lies in the unit disk; no boundary regularity is needed. -/
theorem analytic_disk_energy_bound {F : ℂ → ℂ} {r B : ℝ}
    (hF : AnalyticOnNhd ℂ F (ball 0 1))
    (hne : ∀ z ∈ ball 0 1, F z ≠ 0) (hzero : F 0 = 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hB : 1 ≤ B)
    (hbound : ∀ z ∈ sphere 0 r, ‖F z‖ ≤ B) :
    radialMeanEnergy F r ≤ 2 * (B + 1) * (radialMeanNorm F r - 1) := by
  have hsub : closedBall (0 : ℂ) |r| ⊆ ball 0 1 := by
    rw [abs_of_nonneg hr0]
    exact closedBall_subset_ball hr1
  exact analytic_circle_energy_bound (hF.mono hsub)
    (fun z hz => hne z (hsub hz)) hzero hB
    (by simpa [abs_of_nonneg hr0] using hbound)

theorem analytic_disk_scaled_energy_bound {F : ℂ → ℂ} {r B c : ℝ}
    (hF : AnalyticOnNhd ℂ F (ball 0 1))
    (hne : ∀ z ∈ ball 0 1, F z ≠ 0) (hzero : F 0 = 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hB : 1 ≤ B)
    (hbound : ∀ z ∈ sphere 0 r, ‖F z‖ ≤ B) :
    2 * Real.pi * c ^ 2 * radialMeanEnergy F r ≤
      4 * Real.pi * c * (B + 1) * (c * radialMeanNorm F r - c) := by
  have h := mul_le_mul_of_nonneg_left
    (analytic_disk_energy_bound hF hne hzero hr0 hr1 hB hbound)
    (show 0 ≤ 2 * Real.pi * c ^ 2 by positivity)
  calc
    _ ≤ 2 * Real.pi * c ^ 2 * (2 * (B + 1) * (radialMeanNorm F r - 1)) := h
    _ = _ := by ring

#print axioms analytic_circle_energy_bound
#print axioms analytic_disk_scaled_energy_bound

end
end ExteriorReduction

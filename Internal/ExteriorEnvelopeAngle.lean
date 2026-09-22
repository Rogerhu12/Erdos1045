import ExteriorEnvelopeLevels
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! A holomorphic logarithm of the actual nonvanishing disk derivative, and
the resulting continuous lift of the normal angle on an exterior circle. -/

namespace ExteriorReduction.ExteriorEnvelope

open Complex Metric Set Filter
open scoped Topology

noncomputable section

theorem exists_analytic_log_on_disk {D : ℂ → ℂ}
    (hD : AnalyticOnNhd ℂ D (ball 0 1)) (hne : ∀ z ∈ ball (0 : ℂ) 1, D z ≠ 0) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L (ball 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, Complex.exp (L z) = D z) ∧
      (∀ z ∈ ball (0 : ℂ) 1, HasDerivAt L (deriv D z / D z) z) := by
  have hsc : IsSimplyConnected (ball (0 : ℂ) 1) := by
    let := ((convex_ball (0 : ℂ) 1).starConvex
      (show (0 : ℂ) ∈ ball 0 1 by simp)).contractibleSpace
      (show (ball (0 : ℂ) 1).Nonempty from ⟨0, by simp⟩)
    exact SimplyConnectedSpace.ofContractible _
  have hzero : (0 : ℂ) ∉ D '' ball 0 1 := by
    rintro ⟨z, hz, hDz⟩
    exact hne z hz hDz
  obtain ⟨L, hLc, hexp⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc isOpen_ball
    hD.continuousOn hzero
  have hderiv (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : HasDerivAt L (deriv D z / D z) z := by
    have he : Complex.exp ∘ L =ᶠ[𝓝 z] D := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact hexp hw
    have hd := HasDerivAt.of_comp_left (hLc.continuousAt (isOpen_ball.mem_nhds hz))
      (Complex.hasDerivAt_exp (L z)) (hD z hz).differentiableAt.hasDerivAt
      (Complex.exp_ne_zero (L z)) he
    have hexpz : Complex.exp (L z) = D z := hexp hz
    simpa only [hexpz] using hd
  refine ⟨L, (analyticOnNhd_iff_differentiableOn isOpen_ball).mpr ?_, hexp, hderiv⟩
  exact fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt

def inverseCircle (ρ : ℝ) (t : ℂ) : ℂ := (ρ : ℂ) * Complex.exp (-(t * I))

theorem inverseCircle_mem_disk {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (t : ℝ) :
    inverseCircle ρ (t : ℂ) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, inverseCircle, norm_mul]
  simpa [Complex.norm_exp, Complex.mul_re, abs_of_nonneg hρ] using hρ1

theorem inverseCircle_hasDerivAt (ρ : ℝ) (t : ℂ) :
    HasDerivAt (inverseCircle ρ) (-I * inverseCircle ρ t) t := by
  have hd := ((((hasDerivAt_id t).mul_const I).neg).cexp).const_mul (ρ : ℂ)
  convert hd using 1 <;> try rfl
  simp only [inverseCircle, Pi.neg_apply, id_eq]
  ring

def normalAngle (L : ℂ → ℂ) (ρ t : ℝ) : ℝ := t + (L (inverseCircle ρ (t : ℂ))).im

theorem normalAngle_hasDerivAt {D L : ℂ → ℂ}
    (hL : ∀ z ∈ ball (0 : ℂ) 1, HasDerivAt L (deriv D z / D z) z)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (t : ℝ) :
    HasDerivAt (normalAngle L ρ)
      (derivativeCriterion D (inverseCircle ρ (t : ℂ))).re t := by
  have hd := ((hL _ (inverseCircle_mem_disk hρ hρ1 t)).comp (t : ℂ)
    (inverseCircle_hasDerivAt ρ (t : ℂ))).comp_ofReal
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd
  have hh := (hasDerivAt_id t).add hi
  change HasDerivAt (normalAngle L ρ)
    (1 + (deriv D (inverseCircle ρ (t : ℂ)) / D (inverseCircle ρ (t : ℂ)) *
      (-I * inverseCircle ρ (t : ℂ))).im) t at hh
  convert hh using 1
  have he (z : ℂ) : deriv D z / D z * (-I * z) = -(z * deriv D z / D z) * I := by ring
  simp only [he, derivativeCriterion, Complex.sub_re, Complex.one_re,
    Complex.mul_I_im, Complex.neg_re]
  ring

#print axioms exists_analytic_log_on_disk
#print axioms normalAngle_hasDerivAt

end
end ExteriorReduction.ExteriorEnvelope

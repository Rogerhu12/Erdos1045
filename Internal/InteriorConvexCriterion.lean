import ConvexCriterionPilot
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Components of the independent interior convexity criterion. -/

namespace ExteriorReduction.InteriorConvexCriterion

open Complex Metric Set Filter
open scoped Topology ComplexConjugate

noncomputable section

/-- The second-order necessary condition at a real local maximum. -/
theorem second_deriv_nonpos_of_local_max {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hmax : IsLocalMax f 0) :
    deriv (deriv f) 0 ≤ 0 := by
  have hfirst : deriv f 0 = 0 := hmax.deriv_eq_zero
  have htaylor (t : ℝ) : taylorWithinEval f 2 univ 0 t =
      f 0 + (deriv (deriv f) 0 / 2) * t ^ 2 := by
    simp [show 2 = 1 + 1 from rfl, taylorWithinEval_succ,
      iteratedDerivWithin_univ, iteratedDeriv_succ, hfirst]
    ring
  have hlim : Tendsto (fun t : ℝ =>
      (f t - (f 0 + (deriv (deriv f) 0 / 2) * t ^ 2)) / t ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
    have h := Real.taylor_tendsto (f := f) (n := 2) convex_univ
      (mem_univ 0) hf.contDiffOn
    simp only [nhdsWithin_univ, htaylor, sub_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hevent : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      (f t - (f 0 + (deriv (deriv f) 0 / 2) * t ^ 2)) / t ^ 2 ≤
        -(deriv (deriv f) 0 / 2) := by
    filter_upwards [hmax.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht htne
    have htpos : 0 < t ^ 2 := sq_pos_of_ne_zero (by simpa using htne)
    rw [div_le_iff₀ htpos]
    linarith
  have h := le_of_tendsto hlim hevent
  linarith

/-- A stationary complex path at a local maximum of its squared norm. -/
theorem re_second_deriv_mul_conj_nonpos {H : ℝ → ℂ}
    (hH : ContDiff ℝ 2 H) (hfirst : deriv H 0 = 0)
    (hmax : IsLocalMax (fun t => ‖H t‖ ^ 2) 0) :
    (deriv (deriv H) 0 * conj (H 0)).re ≤ 0 := by
  have hF := second_deriv_nonpos_of_local_max (hH.norm_sq ℝ) hmax
  have hderiv : deriv (fun t => ‖H t‖ ^ 2) =
      fun t => 2 * inner ℝ (H t) (deriv H t) := by
    funext t
    exact ((hH.differentiable (by norm_num) t).hasDerivAt.norm_sq).deriv
  rw [hderiv] at hF
  have hsecond := (((hH.differentiable (by norm_num) 0).hasDerivAt).inner ℝ
    ((hH.differentiable_deriv_two 0).hasDerivAt)).const_mul 2
  rw [hsecond.deriv] at hF
  have hi : inner ℝ (H 0) (deriv (deriv H) 0) ≤ 0 := by
    simp only [hfirst, inner_zero_right] at hF
    linarith
  simpa [Complex.inner, mul_comm] using hi

/-- The preceding necessary condition applied to a function holomorphic near
every point of the real axis. -/
theorem analytic_real_axis_max_second_deriv {A : ℂ → ℂ}
    (hA : ∀ t : ℝ, AnalyticAt ℂ A (t : ℂ)) (hfirst : deriv A 0 = 0)
    (hbound : ∀ t : ℝ, ‖A (t : ℂ)‖ ≤ ‖A 0‖) :
    (deriv (deriv A) 0 * conj (A 0)).re ≤ 0 := by
  let H : ℝ → ℂ := fun t => A (t : ℂ)
  have hH : ContDiff ℝ 2 H := contDiff_iff_contDiffAt.mpr fun t =>
    ((hA t).contDiffAt.restrict_scalars ℝ).comp t
      Complex.ofRealCLM.contDiff.contDiffAt
  have hHd : deriv H = fun t : ℝ => deriv A (t : ℂ) := by
    funext t
    exact (hA t).differentiableAt.hasDerivAt.comp_ofReal.deriv
  have hHd0 : deriv H 0 = 0 := by simpa [hHd] using hfirst
  have hHdd : deriv (deriv H) 0 = deriv (deriv A) 0 := by
    rw [hHd]
    exact (hA 0).deriv.differentiableAt.hasDerivAt.comp_ofReal.deriv
  have hmax : IsLocalMax (fun t => ‖H t‖ ^ 2) 0 :=
    Filter.Eventually.of_forall fun t => by
      have ht := hbound t
      change ‖A (t : ℂ)‖ ^ 2 ≤ ‖A (0 : ℂ)‖ ^ 2
      nlinarith [norm_nonneg (A (t : ℂ)), norm_nonneg (A 0)]
  simpa [hHdd, H] using re_second_deriv_mul_conj_nonpos hH hHd0 hmax

def rotation (k z t : ℂ) : ℂ := Complex.exp (k * t) * z

theorem rotation_analyticAt (k z t : ℂ) : AnalyticAt ℂ (rotation k z) t := by
  unfold rotation
  fun_prop

theorem rotation_deriv_zero (k z : ℂ) : deriv (rotation k z) 0 = k * z := by
  have h : HasDerivAt (rotation k z) (k * z) 0 := by
    convert! ((((hasDerivAt_id (0 : ℂ)).const_mul k).cexp).mul_const z) using 1
    simp
  exact h.deriv

theorem rotation_second_deriv_zero (k z : ℂ) :
    deriv (deriv (rotation k z)) 0 = k ^ 2 * z := by
  have h : iteratedDeriv 2 (rotation k z) 0 = k ^ 2 * z := by
    change iteratedDeriv 2 (fun t : ℂ => Complex.exp (k * t) * z) 0 = k ^ 2 * z
    rw [iteratedDeriv_mul_const_field, iteratedDeriv_cexp_const_mul]
    simp
  simpa [show 2 = 1 + 1 from rfl, iteratedDeriv_succ] using h

theorem rotated_value_second_deriv {g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) (k : ℂ) :
    deriv (deriv (g ∘ rotation k z)) 0 =
      deriv (deriv g) z * (k * z) ^ 2 + deriv g z * (k ^ 2 * z) := by
  have h := iteratedDeriv_comp_two
    (show ContDiffAt ℂ 2 g (rotation k z 0) by simpa [rotation] using hg.contDiffAt)
    (rotation_analyticAt k z 0).contDiffAt
  simpa [show 2 = 1 + 1 from rfl, iteratedDeriv_succ,
    rotation_deriv_zero, rotation_second_deriv_zero, rotation] using h

end
end ExteriorReduction.InteriorConvexCriterion

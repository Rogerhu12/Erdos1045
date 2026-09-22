import StructuralNote.ThirdSchwarzCoefficient
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! The first and third jets of the tangent map, with the sharp disk bound. -/

namespace StructuralNote.ThirdSchwarzJet

open Complex Set Metric Filter FormalMultilinearSeries
open ThirdSchwarzCoefficient
open scoped Topology
noncomputable section

theorem dslope_jet {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    deriv ((Function.swap dslope 0)^[k] g) 0 =
      iteratedDeriv (k + 1) g 0 / (k + 1).factorial := by
  have h := hg.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope k
  have hd := h.deriv
  change deriv ((Function.swap dslope 0)^[k] g) 0 =
    ((fslope^[k]) (ofScalars ℂ (fun n => iteratedDeriv n g 0 / n.factorial))).coeff 1 at hd
  rw [coeff_iterate_fslope, coeff_ofScalars, Nat.add_comm 1] at hd
  exact hd

theorem disk_third_coefficient_bound {g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ g (ball 0 1))
    (hb : ∀ z ∈ ball 0 1, ‖g z‖ ≤ 1) (hzero : g 0 = 0)
    (hsecond : iteratedDeriv 2 g 0 = 0) :
    ‖iteratedDeriv 3 g 0 / 6‖ ≤ 1 - ‖deriv g 0‖ ^ 2 := by
  have hn : ball (0 : ℂ) 1 ∈ 𝓝 0 := ball_mem_nhds _ (by norm_num)
  have ha := hd.analyticOnNhd isOpen_ball 0 (by simp)
  have hdq := (Complex.differentiableOn_dslope hn).mpr hd
  have hmap : MapsTo g (ball 0 1) (closedBall (g 0) 1) := by
    intro z hz
    simpa only [mem_closedBall, hzero, dist_zero_right] using hb z hz
  have hbq (z : ℂ) (hz : z ∈ ball 0 1) : ‖dslope g 0 z‖ ≤ 1 := by
    simpa only [div_one] using Complex.norm_dslope_le_div_of_mapsTo_ball hd hmap hz
  have hq1 : deriv (dslope g 0) 0 = 0 := by
    have h := dslope_jet ha 1
    simpa only [Function.iterate_one, Function.swap, hsecond, zero_div] using h
  have hbound := second_coefficient_bound hdq hbq hq1
  have h3 := dslope_jet ha 2
  norm_num only [Function.iterate_succ_apply, Function.iterate_zero_apply,
    Function.swap, Nat.reduceAdd, Nat.factorial] at h3
  rw [h3, dslope_same] at hbound
  simpa using hbound

theorem tangent_second {z : ℂ} (hz : Complex.cos z ≠ 0) :
    iteratedDeriv 2 Complex.tan z = 2 * Complex.sin z / Complex.cos z ^ 3 := by
  have he : deriv Complex.tan = fun z => 1 / Complex.cos z ^ 2 := funext Complex.deriv_tan
  have hd := ((hasDerivAt_const z (1 : ℂ)).div ((Complex.hasDerivAt_cos z).pow 2)
    (pow_ne_zero 2 hz)).deriv
  rw [show iteratedDeriv 2 Complex.tan = deriv (deriv Complex.tan) by
    simp only [show 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_zero], he]
  simp only [Pi.div_def, Pi.pow_def] at hd
  rw [hd]
  field_simp
  ring

theorem tangent_third_zero : iteratedDeriv 3 Complex.tan 0 = 2 := by
  have hcos : ∀ᶠ z : ℂ in 𝓝 0, Complex.cos z ≠ 0 :=
    Complex.continuous_cos.continuousAt.eventually_ne (by simp)
  have he : iteratedDeriv 2 Complex.tan =ᶠ[𝓝 0]
      fun z => 2 * Complex.sin z / Complex.cos z ^ 3 := hcos.mono (fun _ hz => tangent_second hz)
  rw [show 3 = 2 + 1 by omega, iteratedDeriv_succ, he.deriv_eq]
  have hd := ((Complex.hasDerivAt_sin (0 : ℂ)).const_mul 2).div
    ((Complex.hasDerivAt_cos (0 : ℂ)).pow 3) (by simp)
  convert hd.deriv using 1 <;> norm_num

theorem tangent_composition_jets {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hzero : F 0 = 0) :
    deriv (Complex.tan ∘ F) 0 = deriv F 0 ∧
    iteratedDeriv 2 (Complex.tan ∘ F) 0 = iteratedDeriv 2 F 0 ∧
    iteratedDeriv 3 (Complex.tan ∘ F) 0 = iteratedDeriv 3 F 0 + 2 * deriv F 0 ^ 3 := by
  have hc : Complex.cos (F 0) ≠ 0 := by simp [hzero]
  have h1 := ((Complex.hasDerivAt_tan hc).comp 0 hF.differentiableAt.hasDerivAt).deriv
  have h2 := iteratedDeriv_comp_two (Complex.contDiffAt_tan.mpr hc) hF.contDiffAt
  have h3 := iteratedDeriv_comp_three (Complex.contDiffAt_tan.mpr hc) hF.contDiffAt
  have ht2 : iteratedDeriv 2 Complex.tan 0 = 0 := by simpa using tangent_second (z := 0) (by simp)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hzero, Complex.cos_zero, one_pow, div_one, one_mul] using h1
  · simpa only [hzero, ht2, Complex.deriv_tan, Complex.cos_zero, one_pow, div_one,
      zero_mul, one_mul, zero_add] using h2
  · simpa only [hzero, tangent_third_zero, ht2, Complex.deriv_tan, Complex.cos_zero,
      one_pow, div_one, mul_zero, zero_mul, one_mul, add_zero, zero_add, add_comm] using h3

theorem tangent_third_coefficient_bound {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (hzero : F 0 = 0)
    (hsecond : iteratedDeriv 2 F 0 = 0)
    (hd : DifferentiableOn ℂ (Complex.tan ∘ F) (ball 0 1))
    (hb : ∀ z ∈ ball 0 1, ‖Complex.tan (F z)‖ ≤ 1) :
    ‖iteratedDeriv 3 F 0 / 6 + deriv F 0 ^ 3 / 3‖ ≤ 1 - ‖deriv F 0‖ ^ 2 := by
  have hj := tangent_composition_jets hF hzero
  have h := disk_third_coefficient_bound hd hb (by simp [hzero]) (hj.2.1.trans hsecond)
  rw [hj.1, hj.2.2, show (iteratedDeriv 3 F 0 + 2 * deriv F 0 ^ 3) / 6 =
    iteratedDeriv 3 F 0 / 6 + deriv F 0 ^ 3 / 3 by ring] at h
  exact h

end
end StructuralNote.ThirdSchwarzJet

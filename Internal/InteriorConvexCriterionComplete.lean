import InteriorConvexCriterion

/-!
The analytic convexity criterion for a conformal map of the disk onto a convex
domain.  The proof uses symmetric rotations and Schwarz's lemma; it does not
use Schwarz--Christoffel or any boundary extension theorem.
-/

namespace ExteriorReduction.InteriorConvexCriterion

open Complex Metric Set Filter
open scoped Topology ComplexConjugate

noncomputable section

def rotationMean (g : ℂ → ℂ) (z t : ℂ) : ℂ :=
  (g (rotation I z t) + g (rotation (-I) z t)) / 2

theorem rotation_real_mem_ball {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1)
    (t : ℝ) : rotation I z t ∈ ball (0 : ℂ) 1 ∧
      rotation (-I) z t ∈ ball (0 : ℂ) 1 := by
  have hnorm : ‖Complex.exp (I * (t : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have hnorm' : ‖Complex.exp (-I * (t : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  constructor <;> simpa only [rotation, mem_ball_zero_iff, norm_mul, hnorm,
    hnorm', one_mul] using hz

theorem rotationMean_zero (g : ℂ → ℂ) (z : ℂ) : rotationMean g z 0 = g z := by
  simp only [rotationMean, rotation, mul_zero, Complex.exp_zero, one_mul]
  ring

theorem rotationMean_analyticAt_zero {g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) : AnalyticAt ℂ (rotationMean g z) 0 := by
  have hp : AnalyticAt ℂ (g ∘ rotation I z) 0 :=
    (show AnalyticAt ℂ g (rotation I z 0) by simpa [rotation] using hg).comp
      (rotation_analyticAt I z 0)
  have hm : AnalyticAt ℂ (g ∘ rotation (-I) z) 0 :=
    (show AnalyticAt ℂ g (rotation (-I) z 0) by simpa [rotation] using hg).comp
      (rotation_analyticAt (-I) z 0)
  exact (hp.add hm).div_const

theorem rotationMean_deriv_zero {g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) : deriv (rotationMean g z) 0 = 0 := by
  have hp : HasDerivAt (g ∘ rotation I z) (deriv g z * (I * z)) 0 := by
    have hgp : AnalyticAt ℂ g (rotation I z 0) := by simpa [rotation] using hg
    have hd := hgp.differentiableAt.hasDerivAt.comp 0
      (rotation_analyticAt I z 0).differentiableAt.hasDerivAt
    simpa [rotation_deriv_zero, rotation] using hd
  have hm : HasDerivAt (g ∘ rotation (-I) z) (deriv g z * (-I * z)) 0 := by
    have hgm : AnalyticAt ℂ g (rotation (-I) z 0) := by simpa [rotation] using hg
    have hd := hgm.differentiableAt.hasDerivAt.comp 0
      (rotation_analyticAt (-I) z 0).differentiableAt.hasDerivAt
    simpa [rotation_deriv_zero, rotation] using hd
  have hd : HasDerivAt (rotationMean g z)
      ((deriv g z * (I * z) + deriv g z * (-I * z)) / 2) 0 :=
    (hp.add hm).div_const 2
  rw [hd.deriv]
  ring

theorem rotationMean_second_deriv_zero {g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) :
    deriv (deriv (rotationMean g z)) 0 =
      -(deriv (deriv g) z * z ^ 2 + deriv g z * z) := by
  have hp : AnalyticAt ℂ (g ∘ rotation I z) 0 :=
    (show AnalyticAt ℂ g (rotation I z 0) by simpa [rotation] using hg).comp
      (rotation_analyticAt I z 0)
  have hm : AnalyticAt ℂ (g ∘ rotation (-I) z) 0 :=
    (show AnalyticAt ℂ g (rotation (-I) z 0) by simpa [rotation] using hg).comp
      (rotation_analyticAt (-I) z 0)
  have hsum := iteratedDeriv_add (n := 2) hp.contDiffAt hm.contDiffAt
  have hid (f : ℂ → ℂ) : iteratedDeriv 2 f 0 = deriv (deriv f) 0 := by
    simp [show 2 = 1 + 1 from rfl, iteratedDeriv_succ]
  rw [hid, hid, hid] at hsum
  have hdiv := iteratedDeriv_div_const (n := 2)
    ((g ∘ rotation I z) + (g ∘ rotation (-I) z)) (2 : ℂ) (x := 0)
  rw [hid, hid, hsum, rotated_value_second_deriv hg,
    rotated_value_second_deriv hg] at hdiv
  change deriv (deriv (rotationMean g z)) 0 = _ at hdiv
  rw [hdiv]
  simp only [neg_mul, neg_sq, mul_pow, Complex.I_sq]
  ring

theorem inverse_deriv_mul_deriv {g G : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 1))
    (hG : AnalyticOnNhd ℂ G (g '' ball 0 1))
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, G (g z) = z)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    deriv G (g z) * deriv g z = 1 := by
  have heq : G ∘ g =ᶠ[𝓝 z] id := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact hleft w hw
  have hd := (hG (g z) ⟨z, hz, rfl⟩).differentiableAt.hasDerivAt.comp z
    (hg z hz).differentiableAt.hasDerivAt
  rw [← hd.deriv, heq.deriv_eq]
  exact deriv_id z

/-- Necessity of the analytic convexity criterion, proved solely from the
holomorphic inverse and convexity of the image. -/
theorem convex_image_criterion_nonneg {g G : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 1))
    (hG : AnalyticOnNhd ℂ G (g '' ball 0 1))
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, G (g z) = z)
    (hconv : Convex ℝ (g '' ball 0 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    0 ≤ (1 + z * deriv (deriv g) z / deriv g z).re := by
  by_cases hz0 : z = 0
  · simp [hz0]
  let V : ℂ → ℂ := rotationMean g z
  let A : ℂ → ℂ := G ∘ V
  have hVmem (t : ℝ) : V (t : ℂ) ∈ g '' ball 0 1 := by
    have hrot := rotation_real_mem_ball hz t
    have hmid := hconv ⟨_, hrot.1, rfl⟩ ⟨_, hrot.2, rfl⟩
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    convert hmid using 1
    simp only [V, rotationMean, Complex.real_smul]
    push_cast
    ring
  have hV (t : ℝ) : AnalyticAt ℂ V (t : ℂ) := by
    have hrot := rotation_real_mem_ball hz t
    exact (((hg _ hrot.1).comp (rotation_analyticAt I z t)).add
      ((hg _ hrot.2).comp (rotation_analyticAt (-I) z t))).div_const
  have hA (t : ℝ) : AnalyticAt ℂ A (t : ℂ) :=
    (hG _ (hVmem t)).comp (hV t)
  have hV0 : V 0 = g z := rotationMean_zero g z
  have hA0 : A 0 = z := by simpa [A, hV0] using hleft z hz
  have hVfirst : deriv V 0 = 0 := rotationMean_deriv_zero (hg z hz)
  have hAfirst : deriv A 0 = 0 := by
    have hd := (hG _ (hVmem 0)).differentiableAt.hasDerivAt.comp 0
      (hV 0).differentiableAt.hasDerivAt
    simpa [A, hVfirst] using hd.deriv
  have hAbound (t : ℝ) : ‖A (t : ℂ)‖ ≤ ‖A 0‖ := by
    rw [hA0]
    exact ConvexCriterion.inverse_midpoint_rotation_norm_le
      hg.differentiableOn hG.differentiableOn hleft hconv
      (by simp [Complex.norm_exp, Complex.mul_re])
      (by simp [Complex.norm_exp, Complex.mul_re]) hz
  have hsecond := analytic_real_axis_max_second_deriv hA hAfirst hAbound
  have hAdd : deriv (deriv A) 0 = deriv G (g z) *
      -(deriv (deriv g) z * z ^ 2 + deriv g z * z) := by
    have hd := iteratedDeriv_comp_two (hG _ (hVmem 0)).contDiffAt (hV 0).contDiffAt
    simpa [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, A, hVfirst, hV0,
      V, rotationMean_second_deriv_zero (hg z hz)] using hd
  have hinv := inverse_deriv_mul_deriv hg hG hleft hz
  have hdne : deriv g z ≠ 0 := by
    intro h
    simp [h] at hinv
  have hinv' : deriv G (g z) = (deriv g z)⁻¹ := by
    apply (mul_right_cancel₀ hdne)
    simpa [hdne] using hinv
  have halgebra : (deriv G (g z) *
      -(deriv (deriv g) z * z ^ 2 + deriv g z * z) * conj z).re =
      -(‖z‖ ^ 2) * (1 + z * deriv (deriv g) z / deriv g z).re := by
    rw [hinv']
    have heq : (deriv g z)⁻¹ *
        -(deriv (deriv g) z * z ^ 2 + deriv g z * z) * conj z =
        -((‖z‖ ^ 2 : ℝ) : ℂ) *
          (1 + z * deriv (deriv g) z / deriv g z) := by
      push_cast
      rw [← Complex.mul_conj']
      field_simp
      ring
    rw [heq, Complex.mul_re]
    simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  rw [hAdd, hA0, halgebra] at hsecond
  have hpos : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz0)
  nlinarith

/-- The derivative cannot vanish when a holomorphic left inverse exists. -/
theorem deriv_ne_zero_of_analytic_left_inverse {g G : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 1))
    (hG : AnalyticOnNhd ℂ G (g '' ball 0 1))
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, G (g z) = z)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : deriv g z ≠ 0 := by
  have h := inverse_deriv_mul_deriv hg hG hleft hz
  intro hzero
  simp [hzero] at h

/-- The criterion is strictly positive throughout the disk. -/
theorem convex_image_criterion_pos {g G : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 1))
    (hG : AnalyticOnNhd ℂ G (g '' ball 0 1))
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, G (g z) = z)
    (hconv : Convex ℝ (g '' ball 0 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    0 < (1 + z * deriv (deriv g) z / deriv g z).re := by
  have hP : AnalyticOnNhd ℂ
      (fun w => 1 + w * deriv (deriv g) w / deriv g w) (ball 0 1) := by
    intro w hw
    exact analyticAt_const.add ((analyticAt_id.mul (hg w hw).deriv.deriv).div
      (hg w hw).deriv (deriv_ne_zero_of_analytic_left_inverse hg hG hleft hw))
  exact ConvexCriterion.realPart_pos_of_nonneg hP.differentiableOn
    (by simp) (fun w hw => convex_image_criterion_nonneg hg hG hleft hconv hw) z hz

/-- The same result using ordinary holomorphic-on-domain hypotheses.  The
image's openness is only used to obtain the inverse's local analyticity. -/
theorem convex_image_criterion_pos_of_differentiableOn {g G : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1))
    (hG : DifferentiableOn ℂ G (g '' ball 0 1))
    (hopen : IsOpen (g '' ball 0 1))
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, G (g z) = z)
    (hconv : Convex ℝ (g '' ball 0 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    0 < (1 + z * deriv (deriv g) z / deriv g z).re := by
  exact convex_image_criterion_pos
    ((analyticOnNhd_iff_differentiableOn isOpen_ball).mpr hg)
    ((analyticOnNhd_iff_differentiableOn hopen).mpr hG) hleft hconv hz

#print axioms convex_image_criterion_nonneg
#print axioms convex_image_criterion_pos
#print axioms convex_image_criterion_pos_of_differentiableOn

end
end ExteriorReduction.InteriorConvexCriterion

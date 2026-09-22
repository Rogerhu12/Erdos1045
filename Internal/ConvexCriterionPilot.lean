import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Schwarz

/-! A small verified component of the proposed convexity-criterion proof.

This file proves Study's subdisk convexity and the exact Schwarz inequality
for the rotated-average proof, as well as the final strict-positivity step.
It does not yet prove the geometric necessity of the exterior criterion.
-/

namespace ExteriorReduction.ConvexCriterion

open Set Metric

theorem realPart_pos_of_nonneg {P : ℂ → ℂ}
    (hP : DifferentiableOn ℂ P (ball 0 1))
    (hzero : 0 < (P 0).re)
    (hnonneg : ∀ z ∈ ball 0 1, 0 ≤ (P z).re) :
    ∀ z ∈ ball 0 1, 0 < (P z).re := by
  intro z hz
  by_contra hbad
  have hzeq : (P z).re = 0 := le_antisymm (le_of_not_gt hbad) (hnonneg z hz)
  let G : ℂ → ℂ := fun w => Complex.exp (-P w)
  have hG : DifferentiableOn ℂ G (ball 0 1) :=
    Complex.differentiable_exp.comp_differentiableOn hP.neg
  have hm : IsMaxOn (norm ∘ G) (ball 0 1) z := by
    intro w hw
    change ‖Complex.exp (-P w)‖ ≤ ‖Complex.exp (-P z)‖
    simp only [Complex.norm_exp, Complex.neg_re, hzeq, neg_zero, Real.exp_zero]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hnonneg w hw))
  have heq := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn
    (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected isOpen_ball hG hz hm
    (by simp : (0 : ℂ) ∈ ball 0 1)
  change ‖Complex.exp (-P 0)‖ = ‖Complex.exp (-P z)‖ at heq
  simp only [Complex.norm_exp, Complex.neg_re, hzeq, neg_zero, Real.exp_zero] at heq
  have hlt : Real.exp (-(P 0).re) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hzero)
  linarith

theorem realPart_pos_of_boundary_nonneg {P : ℂ → ℂ}
    (hP : DiffContOnCl ℂ P (ball 0 1)) (hzero : 0 < (P 0).re)
    (hboundary : ∀ z ∈ frontier (ball (0 : ℂ) 1), 0 ≤ (P z).re) :
    ∀ z ∈ ball 0 1, 0 < (P z).re := by
  apply realPart_pos_of_nonneg hP.differentiableOn hzero
  intro z hz
  have hG : DiffContOnCl ℂ (fun w => Complex.exp (-P w)) (ball 0 1) :=
    ⟨Complex.differentiable_exp.comp_differentiableOn hP.differentiableOn.neg,
      Complex.continuous_exp.comp_continuousOn hP.continuousOn.neg⟩
  have hnorm : ‖Complex.exp (-P z)‖ ≤ 1 :=
    Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hG
      (fun w hw => by
        simp only [Complex.norm_exp, Complex.neg_re]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hboundary w hw)))
      (subset_closure hz)
  simp only [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff] at hnorm
  linarith

/-- Study's subdisk convexity, derived directly from Schwarz's lemma.  The
inverse is only required to be holomorphic on the image of the unit disk. -/
theorem convex_image_closedBall_of_convex_image_ball
    {g G : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hG : DifferentiableOn ℂ G (g '' ball 0 1))
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, G (g z) = z)
    (hconv : Convex ℝ (g '' ball 0 1))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Convex ℝ (g '' closedBall (0 : ℂ) r) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hscale {x : ℂ} (hx : x ∈ closedBall 0 r) :
      MapsTo (fun w : ℂ => w * (x / (r : ℂ))) (ball 0 1) (ball 0 1) := by
    intro w hw
    rw [mem_ball_zero_iff] at hw ⊢
    have hx' : ‖x‖ ≤ r := mem_closedBall_zero_iff.mp hx
    have hxr : ‖x / (r : ℂ)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact (div_le_one hr).mpr hx'
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg w) hxr).trans_lt hw
  have hinverse {v : ℂ} (hv : v ∈ g '' ball 0 1) :
      G v ∈ ball 0 1 ∧ g (G v) = v := by
    rcases hv with ⟨z, hz, rfl⟩
    rw [hleft z hz]
    exact ⟨hz, rfl⟩
  intro u hu v hv a b ha hb hab
  rcases hu with ⟨x, hx, rfl⟩
  rcases hv with ⟨y, hy, rfl⟩
  let V : ℂ → ℂ := fun w => a • g (w * (x / (r : ℂ))) +
    b • g (w * (y / (r : ℂ)))
  have hVmap : MapsTo V (ball 0 1) (g '' ball 0 1) := by
    intro w hw
    exact hconv ⟨_, hscale hx hw, rfl⟩ ⟨_, hscale hy hw, rfl⟩ ha hb hab
  have hV : DifferentiableOn ℂ V (ball 0 1) := by
    exact ((hg.comp (differentiable_id.mul_const _).differentiableOn
      (hscale hx)).const_smul a).add
      ((hg.comp (differentiable_id.mul_const _).differentiableOn
        (hscale hy)).const_smul b)
  have hHG : DifferentiableOn ℂ (G ∘ V) (ball 0 1) := hG.comp hV hVmap
  have hHGmap : MapsTo (G ∘ V) (ball 0 1) (closedBall 0 1) := by
    intro w hw
    exact ball_subset_closedBall (hinverse (hVmap hw)).1
  have hHGzero : (G ∘ V) 0 = 0 := by
    simp only [Function.comp_apply, V, zero_mul]
    rw [← add_smul, hab, one_smul]
    exact hleft 0 (by simp)
  have hrnorm : ‖(r : ℂ)‖ < 1 := by simpa [abs_of_pos hr] using hr1
  have hSchwarz := Complex.norm_le_norm_of_mapsTo_ball hHG hHGmap hHGzero hrnorm
  have hVr : V (r : ℂ) = a • g x + b • g y := by
    simp [V, mul_div_cancel₀, hrC]
  refine ⟨G (V (r : ℂ)), ?_, ?_⟩
  · apply mem_closedBall_zero_iff.mpr
    simpa [Function.comp_apply, abs_of_pos hr] using hSchwarz
  · exact (hinverse (hVmap (mem_ball_zero_iff.mpr hrnorm))).2.trans hVr

/-- The precise Schwarz estimate for the symmetric-average proof of the
analytic convexity criterion.  Taking `u = exp (I*t)` and `v = exp (-I*t)`
gives the required estimate for every real parameter `t`. -/
theorem inverse_midpoint_rotation_norm_le
    {g G : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hG : DifferentiableOn ℂ G (g '' ball 0 1))
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, G (g z) = z)
    (hconv : Convex ℝ (g '' ball 0 1))
    {u v z : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hz : z ∈ ball (0 : ℂ) 1) :
    ‖G ((g (u * z) + g (v * z)) / 2)‖ ≤ ‖z‖ := by
  have hmul {c : ℂ} (hc : ‖c‖ ≤ 1) :
      MapsTo (fun w : ℂ => c * w) (ball 0 1) (ball 0 1) := by
    intro w hw
    rw [mem_ball_zero_iff, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg w) hc).trans_lt
      (mem_ball_zero_iff.mp hw)
  let V : ℂ → ℂ := fun w => (g (u * w) + g (v * w)) / 2
  have hVmap : MapsTo V (ball 0 1) (g '' ball 0 1) := by
    intro w hw
    have hmid := hconv ⟨_, hmul hu hw, rfl⟩ ⟨_, hmul hv hw, rfl⟩
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    convert hmid using 1
    simp only [V, Complex.real_smul]
    push_cast
    ring
  have hV : DifferentiableOn ℂ V (ball 0 1) :=
    ((hg.comp (differentiable_id.const_mul _).differentiableOn
      (hmul hu)).add
      (hg.comp (differentiable_id.const_mul _).differentiableOn
        (hmul hv))).div_const 2
  have hHmap : MapsTo (G ∘ V) (ball 0 1) (closedBall 0 1) := by
    intro w hw
    rcases hVmap hw with ⟨s, hs, heq⟩
    change G (V w) ∈ closedBall 0 1
    rw [← heq, hleft s hs]
    exact ball_subset_closedBall hs
  have hH0 : (G ∘ V) 0 = 0 := by
    change G ((g (u * 0) + g (v * 0)) / 2) = 0
    simp only [mul_zero]
    have havg : (g 0 + g 0) / 2 = g 0 := by ring
    rw [havg]
    exact hleft 0 (by simp)
  exact Complex.norm_le_norm_of_mapsTo_ball (hG.comp hV hVmap) hHmap hH0
    (mem_ball_zero_iff.mp hz)

end ExteriorReduction.ConvexCriterion

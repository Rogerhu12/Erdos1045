import StructuralNote.FixedSchurRemainderHessianSum
import StructuralNote.FixedSchurRemainderGeometry

/-! The scalar analytic remainder Hessian in physical center/diameter
coordinates, with all acceleration terms and its pair-energy bound. -/

namespace StructuralNote.FixedSchurGeometricRemainderHessian

open Complex Filter Erdos1045.EventualExact SchurSpectrum
open GeometricRelativeRemainder SignedPressureAngular AngularFirstEnergy
open FixedSchurRemainderScalar FixedSchurRemainderSecond FixedSchurRemainderPath
open FixedSchurRemainderHessianSum
open scoped BigOperators Topology

noncomputable section

def analyticRemainder {n : ℕ} (C D : Fin n → ℂ) : ℝ :=
  (∑ p : Fin n × Fin n, R (quotient C (root n) p) (quotient D (root n) p)).re / 2

def analyticVelocity {n : ℕ} (C D V W : Fin n → ℂ) : ℝ :=
  (∑ p : Fin n × Fin n,
    (Ru (quotient C (root n) p) (quotient D (root n) p) * quotient V (root n) p +
      Rx (quotient C (root n) p) (quotient D (root n) p) * quotient W (root n) p)).re / 2

def analyticSecond {n : ℕ} (C D V W A B : Fin n → ℂ) : ℝ :=
  (∑ p : Fin n × Fin n,
    (Ruu (quotient C (root n) p) (quotient D (root n) p) * quotient V (root n) p ^ 2 +
      2 * Rux (quotient C (root n) p) (quotient D (root n) p) *
        quotient V (root n) p * quotient W (root n) p +
      Rxx (quotient C (root n) p) (quotient D (root n) p) * quotient W (root n) p ^ 2 +
      Ru (quotient C (root n) p) (quotient D (root n) p) * quotient A (root n) p +
      Rx (quotient C (root n) p) (quotient D (root n) p) * quotient B (root n) p)).re / 2

theorem quotient_hasDerivAt {n : ℕ} {C : ℝ → Fin n → ℂ} {V : Fin n → ℂ} {t : ℝ}
    (hC : ∀ j, HasDerivAt (fun r => C r j) (V j) t) (p : Fin n × Fin n) :
    HasDerivAt (fun r => quotient (C r) (root n) p) (quotient V (root n) p) t :=
  ((hC p.1).sub (hC p.2)).div_const (root n p.1 - root n p.2)

theorem analyticRemainder_hasDerivAt {n : ℕ} {C D : ℝ → Fin n → ℂ}
    {V W : Fin n → ℂ} {t : ℝ}
    (hC : ∀ j, HasDerivAt (fun r => C r j) (V j) t)
    (hD : ∀ j, HasDerivAt (fun r => D r j) (W j) t)
    (hU : ∀ p, ‖quotient (C t) (root n) p‖ ≤ 1 / 4)
    (hX : ∀ p, ‖quotient (D t) (root n) p‖ ≤ 1 / 4) :
    HasDerivAt (fun r => analyticRemainder (C r) (D r))
      (analyticVelocity (C t) (D t) V W) t := by
  have hd := hasDerivAt_sum_R_path (quotient_hasDerivAt hC) (quotient_hasDerivAt hD) hU hX
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd).div_const 2

theorem analyticVelocity_hasDerivAt {n : ℕ} {C D V W : ℝ → Fin n → ℂ}
    {A B : Fin n → ℂ} {t : ℝ}
    (hC : ∀ j, HasDerivAt (fun r => C r j) (V t j) t)
    (hD : ∀ j, HasDerivAt (fun r => D r j) (W t j) t)
    (hV : ∀ j, HasDerivAt (fun r => V r j) (A j) t)
    (hW : ∀ j, HasDerivAt (fun r => W r j) (B j) t)
    (hU : ∀ p, ‖quotient (C t) (root n) p‖ ≤ 1 / 4)
    (hX : ∀ p, ‖quotient (D t) (root n) p‖ ≤ 1 / 4) :
    HasDerivAt (fun r => analyticVelocity (C r) (D r) (V r) (W r))
      (analyticSecond (C t) (D t) (V t) (W t) A B) t := by
  have hd := hasDerivAt_sum_R_velocity (quotient_hasDerivAt hC) (quotient_hasDerivAt hD)
    (quotient_hasDerivAt hV) (quotient_hasDerivAt hW) hU hX
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd).div_const 2

theorem analytic_second_derivative {n : ℕ} {C D V W : ℝ → Fin n → ℂ}
    {A B : Fin n → ℂ} {t : ℝ}
    (hfirst : ∀ᶠ z in 𝓝 t,
      (∀ j, HasDerivAt (fun r => C r j) (V z j) z) ∧
      (∀ j, HasDerivAt (fun r => D r j) (W z j) z) ∧
      (∀ p, ‖quotient (C z) (root n) p‖ ≤ 1 / 4) ∧
      (∀ p, ‖quotient (D z) (root n) p‖ ≤ 1 / 4))
    (hV : ∀ j, HasDerivAt (fun r => V r j) (A j) t)
    (hW : ∀ j, HasDerivAt (fun r => W r j) (B j) t) :
    HasDerivAt (deriv (fun r => analyticRemainder (C r) (D r)))
      (analyticSecond (C t) (D t) (V t) (W t) A B) t := by
  have h0 := hfirst.self_of_nhds
  have hd := analyticVelocity_hasDerivAt h0.1 h0.2.1 hV hW h0.2.2.1 h0.2.2.2
  apply hd.congr_of_eventuallyEq
  filter_upwards [hfirst] with r hr
  exact (analyticRemainder_hasDerivAt hr.1 hr.2.1 hr.2.2.1 hr.2.2.2).deriv

theorem quotient_l2Norm {n : ℕ} (hn : 0 < n) (C : Fin n → ℂ) :
    l2Norm (quotient C (root n)) = Real.sqrt 2 * Real.sqrt (pairEnergy hn C) := by
  have hs : (∑ p, ‖quotient C (root n) p‖ ^ 2) = 2 * pairEnergy hn C := by
    rw [pairEnergy_eq_quotient_sum]
    ring
  rw [l2Norm, hs, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

theorem analyticSecond_abs_le {n : ℕ} (hn : 0 < n) (C D V W A B : Fin n → ℂ)
    {U X : ℝ} (hU : 0 ≤ U) (hUq : U ≤ 1 / 4) (hX : 0 ≤ X) (hXq : X ≤ 1 / 4)
    (hu : ∀ p, ‖quotient C (root n) p‖ ≤ U)
    (hx : ∀ p, ‖quotient D (root n) p‖ ≤ X) :
    |analyticSecond C D V W A B| ≤
      32 * (X + U ^ 2) * pairEnergy hn V +
        64 * U * Real.sqrt (pairEnergy hn V) * Real.sqrt (pairEnergy hn W) +
        128 * U ^ 2 * pairEnergy hn W +
        32 * (X + U ^ 2) * Real.sqrt (pairEnergy hn C) * Real.sqrt (pairEnergy hn A) +
        32 * U * Real.sqrt (pairEnergy hn C) * Real.sqrt (pairEnergy hn B) := by
  have hs := sum_norm_R_hessian_le (quotient C (root n)) (quotient D (root n))
    (quotient V (root n)) (quotient W (root n)) (quotient A (root n)) (quotient B (root n))
    hU hUq hX hXq hu hx
  have hre := (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans hs)
  have hdiv := div_le_div_of_nonneg_right hre (show (0 : ℝ) ≤ 2 by norm_num)
  change |(_ : ℂ).re| / 2 ≤ _ at hdiv
  rw [analyticSecond, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  apply hdiv.trans_eq
  simp only [quotient_l2Norm hn, mul_pow, Real.sq_sqrt (pairEnergy_nonneg hn _),
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

end
end StructuralNote.FixedSchurGeometricRemainderHessian

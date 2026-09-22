import StructuralNote.CommonFiberNonlocalSizes
import StructuralNote.AngularFirstEnergy

/-! The actual common-domain configuration is a uniformly small relative chord
perturbation of the regular polygon. No chord hypothesis is supplied externally. -/

namespace StructuralNote.CommonFiberHessianGeometryChord

open Erdos1045 Erdos1045.EventualExact Complex
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure CommonDomainRadius
open CommonFiberGeometry CommonFiberBounds CommonFiberSmallCoefficients
open SignedPressureAngular GeometricRelativeRemainder
open scoped BigOperators
noncomputable section

theorem logOrder_one_le {n : ℕ} (hn : 2 ≤ n) : (1 : ℝ) ≤ logOrder n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hc : Real.log n / Real.log 2 ≤ (logOrder n : ℝ) := Nat.le_ceil _
  exact (one_le_div hlog2).mpr hlog |>.trans hc

theorem sqrt_log_le {n : ℕ} (hn : 2 ≤ n) : Real.sqrt (Real.log n) ≤ n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  nlinarith [Real.sq_sqrt hl, Real.sqrt_nonneg (Real.log n),
    Real.log_le_sub_one_of_pos (show (0 : ℝ) < n by linarith),
    mul_nonneg (show (0 : ℝ) ≤ n by positivity) (show (0 : ℝ) ≤ n - 1 by linarith)]

theorem domain_theta_coarse {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v) (j : Fin (2 * m)) :
    |θ j| ≤ 4 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  apply (domain_theta_bound hm θ v hdom j).trans
  have hs := sqrt_log_le (show 2 ≤ 2 * m by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
  calc
    _ ≤ 4 * (logOrder (2 * m) : ℝ) * (2 * m) / (2 * m : ℝ) ^ 2 := by gcongr
    _ = _ := by field_simp

theorem unit_sub_one (t : ℝ) : ‖unit t - 1‖ ≤ |t| := by
  simpa only [unit, Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_zero] using norm_unit_sub_le t 0

theorem root_character (n : ℕ) (j : Fin n) : root n j = character n 1 j := by
  simp only [root, character, mul_one]

theorem root_step_bound {n : ℕ} (hn : 0 < n) (j : Fin n) :
    ‖difference hn (root n) j‖ ≤ 8 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : root n = fun j : Fin n => character n 1 j := funext (root_character n)
  have hf : ‖frame n j‖ = 1 := by
    have hh := frame_normSq n j
    rw [normSq_eq_norm_sq] at hh
    nlinarith [norm_nonneg (frame n j)]
  rw [he, reference_difference, norm_mul, norm_mul, norm_real, Real.norm_eq_abs, norm_I,
    hf, mul_one, mul_one, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hs := Real.abs_sin_le_abs (x := Real.pi / n)
  rw [abs_of_pos (by positivity : 0 < Real.pi / n)] at hs
  have hp := div_le_div_of_nonneg_right Real.pi_lt_four.le hnR.le
  calc
    _ ≤ 2 * (4 / (n : ℝ)) := mul_le_mul_of_nonneg_left (hs.trans hp) (by norm_num)
    _ = _ := by ring

def angularError {n : ℕ} (θ : Fin n → ℝ) : Fin n → ℂ := fun j => diameterVector θ j - root n j

theorem angularError_point {n : ℕ} (θ : Fin n → ℝ) (j : Fin n) : ‖angularError θ j‖ ≤ |θ j| := by
  have he : angularError θ j = root n j * (unit (θ j) - 1) := by
    simp only [angularError, diameterVector, root_character]
    ring
  rw [he, norm_mul, root_norm, one_mul]
  exact unit_sub_one _

theorem angularError_step {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (j : Fin n) :
    ‖difference hn (angularError θ) j‖ ≤ 8 / (n : ℝ) * |θ (successor hn j)| + |angleDifference hn θ j| := by
  have he : difference hn (angularError θ) j =
      difference hn (root n) j * (unit (θ (successor hn j)) - 1) +
      root n j * (unit (θ (successor hn j)) - unit (θ j)) := by
    simp only [difference, angularError, diameterVector, root_character]
    ring
  rw [he]
  have hs := norm_add_le (difference hn (root n) j * (unit (θ (successor hn j)) - 1))
    (root n j * (unit (θ (successor hn j)) - unit (θ j)))
  simp only [norm_mul, root_norm, one_mul] at hs
  have hp := mul_le_mul (root_step_bound hn j) (unit_sub_one (θ (successor hn j)))
    (norm_nonneg _) (by positivity : 0 ≤ 8 / (n : ℝ))
  exact hs.trans (add_le_add hp (norm_unit_sub_le _ _))

theorem domain_angularError_step {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v) (j : Fin (2 * m)) :
    ‖difference (by omega) (angularError θ) j‖ ≤ 42 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by
  have hs := angularError_step (by omega) θ j
  have hp := mul_le_mul_of_nonneg_left (domain_theta_coarse hm θ v hdom (successor (by omega) j))
    (by positivity : 0 ≤ 8 / (2 * m : ℝ))
  have hd := domain_angle_difference hm θ v hdom j
  have he : 8 / (2 * m : ℝ) * (4 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ)) +
      10 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 = 42 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by ring
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
  exact hs.trans ((add_le_add hp hd).trans_eq he)

def perturbation {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) : Fin (2 * m) → ℂ :=
  fun j => configuration hm θ v σ ξ j - root (2 * m) j

theorem domain_perturbation_step {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hdom : InDomain (by omega) θ v) (hσ : ∀ j, |σ j| ≤ 1)
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hz : closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j)) σ (coordinates (by omega) v) ξ = 0)
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m) (j : Fin (2 * m)) :
    ‖difference (by omega) (perturbation (by omega) θ v σ ξ) j‖ ≤
      1200 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by
  have hc : ‖difference (by omega) (center (by omega) θ v σ ξ) j‖ ≤
      (10 * (logOrder (2 * m) : ℝ) + 1049) / (2 * m : ℝ) ^ 2 := by
    apply CommonFiberNonlocalFrames.center_step_bound (by omega) θ v σ ξ hz
    intro k
    have hb := domain_bodyNorm_bound hm θ v σ hdom hξ hσ horder
    have hp := norm_le_pi_norm (fun k => LensIncrementDerivatives.body
      (2 * Real.cos (halfAngle (by omega) θ k)) (σ k) (heightParameter (coordinates (by omega) v) ξ k)) k
    have he : ‖fiberIncrement (by omega) θ v σ ξ k‖ = ‖LensIncrementDerivatives.body
      (2 * Real.cos (halfAngle (by omega) θ k)) (σ k) (heightParameter (coordinates (by omega) v) ξ k)‖ := by
      simp only [fiberIncrement, LensClosure.increment, LensIncrementDerivatives.body, norm_mul, norm_unit, one_mul]
    rw [he]
    exact hp.trans hb
  have he : difference (by omega) (perturbation (by omega) θ v σ ξ) j =
      difference (by omega) (angularError θ) j + difference (by omega) (center (by omega) θ v σ ξ) j := by
    simp only [difference, perturbation, CommonFiberGeometry.configuration, angularError]
    ring
  rw [he]
  have hb := (norm_add_le _ _).trans (add_le_add (domain_angularError_step (by omega) θ v hdom j) hc)
  apply hb.trans
  have hL := logOrder_one_le (show 2 ≤ 2 * m by omega)
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  linarith

theorem pairRatio_of_step {n : ℕ} (hn : 0 < n) (u : ℕ → ℂ) (hu : Function.Periodic u n)
    {B : ℝ} (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ B) {h : ℕ} (hh : 0 < h) (hhn : h < n) (j : ℕ) :
    ‖LocalDFT.pairRatio n u j h‖ ≤ (n : ℝ) / 4 * B := by
  have hs (k : ℕ) (hk : 0 < k) (hkn : 2 * k ≤ n) (j : ℕ) :
      ‖LocalDFT.pairRatio n u j k‖ ≤ (n : ℝ) / 4 * B := by
    apply (QuarticWindowBound.short_pairRatio_bound hn hk hkn u j).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (n : ℝ) / 4)
    rw [QuarticWindowBound.average_eq]
    have hsum := Finset.sum_le_sum (s := Finset.range k) (fun r _ => hstep (j + r))
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    apply (div_le_iff₀ (by exact_mod_cast hk : (0 : ℝ) < k)).mpr
    simpa only [QuarticWindowBound.incrementNorm, mul_comm] using hsum
  by_cases hshort : 2 * h ≤ n
  · exact hs h hh hshort j
  · rw [← QuarticWindowBound.pairRatio_reverse hn hhn.le u hu j]
    exact hs (n - h) (by omega) (by omega) (j + h)

theorem quotient_of_step {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hstep : ∀ j, ‖difference hn c j‖ ≤ B) (i j : Fin n) :
    ‖quotient c (root n) (i, j)‖ ≤ (n : ℝ) / 4 * B := by
  have hp (k h : ℕ) (hh : 0 < h) (hhn : h < n) := pairRatio_of_step hn (periodize hn c)
    (periodize_periodic hn c) (NonlocalFeasibility.periodize_step_bound hn c hstep) hh hhn k
  have hlt (i j : Fin n) (hij : j.val < i.val) : ‖quotient c (root n) (i, j)‖ ≤ (n : ℝ) / 4 * B := by
    have hh := hp j.val (i.val - j.val) (by omega) (by omega)
    simpa only [LocalDFT.pairRatio, Nat.add_sub_of_le (Nat.le_of_lt hij), periodize_fin, quotient, root] using hh
  rcases lt_trichotomy j.val i.val with h | h | h
  · exact hlt i j h
  · have he : j = i := Fin.ext h
    subst j
    simpa only [quotient, sub_self, zero_div, norm_zero] using (mul_nonneg (by positivity : 0 ≤ (n : ℝ) / 4) hB)
  · have he : quotient c (root n) (i, j) = quotient c (root n) (j, i) := by
      unfold quotient
      rw [← neg_div_neg_eq]
      congr 1 <;> ring
    rw [he]
    exact hlt j i h

theorem domain_relative_chord {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hdom : InDomain (by omega) θ v) (hσ : ∀ j, |σ j| ≤ 1)
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hz : closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j)) σ (coordinates (by omega) v) ξ = 0)
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m) (i j : Fin (2 * m)) :
    ‖quotient (perturbation (by omega) θ v σ ξ) (root (2 * m)) (i, j)‖ ≤
      300 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hh := quotient_of_step (by omega) (perturbation (by omega) θ v σ ξ) (by positivity)
    (domain_perturbation_step hm θ v σ ξ hdom hσ hξ hz horder) i j
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hh
  exact hh.trans_eq (by field_simp; ring)

end
end StructuralNote.CommonFiberHessianGeometryChord

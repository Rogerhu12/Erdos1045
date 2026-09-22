import StructuralNote.MatchingActivityRadialSource

/-! The leading closure correction is tangential to the reference polygon.
Only its small rotated normal component contributes to the pressure work. -/

namespace StructuralNote.MatchingActivityRadialProjection

open Erdos1045 Erdos1045.EventualExact Complex
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonTangentialParameters BoxLensLift
open MatchingActivityRadialClosure MatchingActivityRadialVelocity MatchingActivityRadialSource
open LensIncrementDerivatives LensClosurePathDerivatives ClosedSourceIntegration
open scoped BigOperators
noncomputable section

def normal (μ : ℝ) (z : ℂ) : ℝ := ((starRingEnd ℂ) (unit μ) * z).re

theorem normal_le_norm (μ : ℝ) (z : ℂ) : |normal μ z| ≤ ‖z‖ := by
  simpa only [normal, norm_mul, norm_conj, norm_unit, one_mul] using abs_re_le_norm ((starRingEnd ℂ) (unit μ) * z)

theorem normal_tangent (μ : ℝ) : normal μ (unit μ * I) = 0 := by
  have hu : (starRingEnd ℂ) (unit μ) * unit μ = 1 := by
    rw [mul_comm, Complex.mul_conj, normSq_eq_norm_sq, norm_unit]
    norm_num
  rw [normal, ← mul_assoc, hu, one_mul, I_re]

theorem normal_tangent_bound {α μ σ t : ℝ} (hσ : |σ| ≤ 1) (ht : |t| ≤ 1) :
    |normal μ (tangent α σ t)| ≤ |α - μ| + |t| := by
  have he : normal μ (tangent α σ t) = normal μ (tangent α σ t - unit μ * I) := by
    have ht0 := normal_tangent μ
    dsimp only [normal] at ht0
    simp only [normal, mul_sub, sub_re, ht0, sub_zero]
  rw [he]
  exact (normal_le_norm _ _).trans (tangent_error hσ ht)

theorem corrected_normal_bound {m : ℕ} (α σ ν : Fin m → ℝ) (v : ℂ) (source : Fin m → ℂ)
    (hσ : ∀ j, |σ j| ≤ 1) (hν : ∀ j, |ν j| ≤ 1) (j : Fin m) :
    |normal (midpoint m j) (corrected α σ ν 0 v source j)| ≤
      ‖source j‖ + ‖v‖ * (|α j - midpoint m j| + |ν j|) := by
  have he : normal (midpoint m j) (corrected α σ ν 0 v source j) =
      normal (midpoint m j) (source j) + harmonicFunctional (midpoint m j) v * normal (midpoint m j) (tangent (α j) (σ j) (ν j)) := by
    simp only [normal, corrected, heightParameter, map_zero, add_zero, mul_add, add_re]
    rw [show (starRingEnd ℂ) (unit (midpoint m j)) * ((harmonicFunctional (midpoint m j) v : ℂ) * tangent (α j) (σ j) (ν j)) =
      (harmonicFunctional (midpoint m j) v : ℂ) * ((starRingEnd ℂ) (unit (midpoint m j)) * tangent (α j) (σ j) (ν j)) by ring]
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add (normal_le_norm _ _)
  rw [abs_mul]
  exact mul_le_mul (harmonicFunctional_le_norm _ _) (normal_tangent_bound (hσ j) (hν j))
    (abs_nonneg _) (norm_nonneg _)

theorem corrected_normal_sum {m : ℕ} (α σ ν : Fin m → ℝ) (v : ℂ) (source : Fin m → ℂ)
    {ε : ℝ} (hσ : ∀ j, |σ j| ≤ 1) (hν : ∀ j, |ν j| ≤ 1)
    (he : ∀ j, |α j - midpoint m j| + |ν j| ≤ ε) :
    (∑ j, |normal (midpoint m j) (corrected α σ ν 0 v source j)|) ≤
      (∑ j, ‖source j‖) + (m : ℝ) * ‖v‖ * ε := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (corrected_normal_bound α σ ν v source hσ hν j).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left (he j) (norm_nonneg v))))
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc] using hs

theorem real_half_sum {m : ℕ} (hm : 0 < m) (f : Fin (2 * m) → ℝ)
    (hf : ∀ j, f (halfTurn hm j) = f j) :
    (∑ j, f j) = 2 * ∑ j : Fin m, f (CommonClosureEnergy.halfIndex j) := by
  have he := repeatHalf_restrict hm (fun j => (f j : ℂ)) (fun j => congrArg Complex.ofReal (hf j))
  have hs := congrArg (fun d : Fin (2 * m) → ℂ => (∑ j, d j).re) he
  rw [repeatHalf_sum] at hs
  norm_num only [mul_re, Complex.re_sum, ofReal_re, ofReal_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hs
  exact hs.symm

theorem pressure_work_bound {m : ℕ} (hm : 0 < m) (U : Fin (2 * m) → ℂ)
    (hU : HalfPeriodic hm U) (g : Fin (2 * m) → ℝ) {G H : ℝ}
    (hg : ∀ j, |g j| ≤ G)
    (hH : (∑ j : Fin m, |normal (midpoint m j) (difference (by omega) U (CommonClosureEnergy.halfIndex j))|) ≤ H)
    (hs : 0 < Real.sin (Real.pi / (2 * m : ℝ))) :
    |finitePairing g (constraint (by omega) U) / (2 * m : ℝ)| ≤ G * H / Real.sin (Real.pi / (2 * m : ℝ)) := by
  have hn : (0 : ℝ) < 2 * m := by positivity
  have hG : 0 ≤ G := (abs_nonneg (g ⟨0, by omega⟩)).trans (hg _)
  let f : Fin (2 * m) → ℝ := fun j => |((starRingEnd ℂ) (frame (2 * m) j) * difference (by omega) U j).re|
  have hf : ∀ j, f (halfTurn hm j) = f j := by
    intro j
    have hd := CommonTangentialParameters.difference_halfPeriodic hm U hU j
    simp only [f, frame_halfTurn, hd, map_neg, neg_mul, neg_re, abs_neg]
  have hfs : (∑ j, f j) ≤ 2 * H := by
    rw [real_half_sum hm f hf]
    have he (j : Fin m) : f (CommonClosureEnergy.halfIndex j) = |normal (midpoint m j)
        (difference (by omega) U (CommonClosureEnergy.halfIndex j))| := by
      simp only [f, normal]
      congr 3
      exact congrArg (starRingEnd ℂ) (BoxLensLift.frame_halfIndex j)
    simp_rw [he]
    linarith
  have he : finitePairing g (constraint (by omega) U) / (2 * m : ℝ) =
      (∑ j, g j * ((starRingEnd ℂ) (frame (2 * m) j) * difference (by omega) U j).re) /
        (2 * Real.sin (Real.pi / (2 * m : ℝ))) := by
    unfold finitePairing constraint
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [show (∑ j, g j * ((2 * m : ℝ) / (2 * Real.sin (Real.pi / (2 * m : ℝ))) *
      ((starRingEnd ℂ) (frame (2 * m) j) * difference (by omega) U j).re)) =
      (2 * m : ℝ) / (2 * Real.sin (Real.pi / (2 * m : ℝ))) *
        ∑ j, g j * ((starRingEnd ℂ) (frame (2 * m) j) * difference (by omega) U j).re by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring]
    field_simp
  rw [he, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sin (Real.pi / (2 * m : ℝ)))]
  have hpoint (j : Fin (2 * m)) : |g j * ((starRingEnd ℂ) (frame (2 * m) j) * difference (by omega) U j).re| ≤ G * f j := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hg j) (abs_nonneg _)
  have hp : |∑ j, g j * ((starRingEnd ℂ) (frame (2 * m) j) * difference (by omega) U j).re| ≤ ∑ j, G * f j :=
    (Finset.abs_sum_le_sum_abs (fun j => g j * ((starRingEnd ℂ) (frame (2 * m) j) * difference (by omega) U j).re) Finset.univ).trans
      (Finset.sum_le_sum (fun j _ => hpoint j))
  rw [← Finset.mul_sum] at hp
  have hh := hp.trans (mul_le_mul_of_nonneg_left hfs hG)
  calc
    _ ≤ (G * (2 * H)) / (2 * Real.sin (Real.pi / (2 * m : ℝ))) := div_le_div_of_nonneg_right hh (by positivity)
    _ = _ := by ring

end
end StructuralNote.MatchingActivityRadialProjection

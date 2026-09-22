import StructuralNote.LensClosurePathDerivatives
import StructuralNote.CommonFiberGeometry

/-! Discrete integration of a genuinely closed source, including the correction
from the two closure equations. These estimates apply to both fiber derivatives. -/

namespace StructuralNote.ClosedSourceIntegration

open Erdos1045.EventualExact Complex LensClosure LensClosurePathDerivatives
open FiniteFourierLift FourierMultiplier SchurSpectrum BoxLensLift
open scoped BigOperators
noncomputable section

theorem integral_hasDerivAt {n : ℕ} {d : ℝ → Fin n → ℂ} {d' : Fin n → ℂ} {x : ℝ}
    (hd : ∀ j, HasDerivAt (fun s => d s j) (d' j) x) (j : Fin n) :
    HasDerivAt (fun s => integral (d s) j) (integral d' j) x := by
  have hc (p : Fin n) : HasDerivAt (fun s => coefficient (d s) p) (coefficient d' p) x :=
    (HasDerivAt.fun_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) =>
      (hd k).mul_const ((starRingEnd ℂ) (character n p k)))).div_const (n : ℂ)
  have hi (p : Fin n) : HasDerivAt (fun s => integralCoefficients (d s) p)
      (integralCoefficients d' p) x := by
    by_cases hp : p.val = 0
    · simp only [integralCoefficients, if_pos hp]
      exact hasDerivAt_const x 0
    · simpa only [integralCoefficients, if_neg hp] using (hc p).div_const (differenceSymbol n p)
  exact HasDerivAt.fun_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin n))) =>
    (hi p).mul_const (character n p j))

theorem repeatHalf_hasDerivAt {m : ℕ} (hm : 0 < m) {d : ℝ → Fin m → ℂ}
    {d' : Fin m → ℂ} {x : ℝ} (hd : ∀ j, HasDerivAt (fun s => d s j) (d' j) x)
    (j : Fin (2 * m)) :
    HasDerivAt (fun s => repeatHalf hm (d s) j) (repeatHalf hm d' j) x :=
  hd ⟨j.val % m, Nat.mod_lt _ hm⟩

theorem repeatHalf_map_sum {m : ℕ} (hm : 0 < m) (d : Fin m → ℂ) (f : ℂ → ℝ) :
    (∑ j, f (repeatHalf hm d j)) = 2 * ∑ j, f (d j) := by
  have hh := congrArg Complex.re (repeatHalf_sum hm (fun j => ((f (d j) : ℝ) : ℂ)))
  simpa [repeatHalf, mul_re] using hh

def corrected {m : ℕ} (α σ ν : Fin m → ℝ) (ξ v : ℂ) (source : Fin m → ℂ) (j : Fin m) : ℂ :=
  source j + (harmonicFunctional (midpoint m j) v : ℂ) *
    tangent (α j) (σ j) (heightParameter ν ξ j)

theorem corrected_sum {m : ℕ} (α σ ν : Fin m → ℝ) (ξ v : ℂ) (source : Fin m → ℂ)
    (heq : closureDerivative α σ ν ξ v = -∑ j, source j) :
    (∑ j, corrected α σ ν ξ v source j) = 0 := by
  simp only [corrected, Finset.sum_add_distrib, ← closureDerivative_apply_sum, heq, add_neg_cancel]

def integrateCorrected {m : ℕ} (hm : 0 < m) (α σ ν : Fin m → ℝ) (ξ v : ℂ)
    (source : Fin m → ℂ) : Fin (2 * m) → ℂ :=
  integral (repeatHalf hm (corrected α σ ν ξ v source))

theorem integrateCorrected_difference {m : ℕ} (hm : 0 < m) (α σ ν : Fin m → ℝ)
    (ξ v : ℂ) (source : Fin m → ℂ)
    (heq : closureDerivative α σ ν ξ v = -∑ j, source j) :
    difference (by omega) (integrateCorrected hm α σ ν ξ v source) =
      repeatHalf hm (corrected α σ ν ξ v source) := by
  apply difference_integral
  rw [repeatHalf_sum, corrected_sum α σ ν ξ v source heq, mul_zero]

theorem integrateCorrected_l1 {m : ℕ} (hm : 2 ≤ m) (α σ ν : Fin m → ℝ) (ξ v : ℂ)
    (source : Fin m → ℂ) (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |heightParameter ν ξ j| ≤ 1 / 4)
    (heq : closureDerivative α σ ν ξ v = -∑ j, source j) :
    (∑ j, ‖integrateCorrected (by omega) α σ ν ξ v source j‖) ≤
      36 * (2 * m : ℝ) * ∑ j, ‖source j‖ := by
  have hd := integrateCorrected_difference (by omega) α σ ν ξ v source heq
  have hs := corrected_source_l1 hm α σ ν ξ v source hσ hsmall heq
  change (∑ j, ‖corrected α σ ν ξ v source j‖) ≤ _ at hs
  have hj (j : Fin (2 * m)) :
      ‖integrateCorrected (by omega) α σ ν ξ v source j‖ ≤ 36 * ∑ k, ‖source k‖ := by
    have hb := SchurLiftBounds.finite_integral_norm_bound (by omega)
      (integrateCorrected (by omega) α σ ν ξ v source)
      (integral_mean_zero (by omega) _) j
    rw [hd, repeatHalf_map_sum (by omega)] at hb
    linarith
  have ha := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (2 * m)))) => hj j)
  calc
    _ ≤ ((2 * m : ℕ) : ℝ) * (36 * ∑ k, ‖source k‖) := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using ha
    _ = _ := by push_cast; ring

theorem integrateCorrected_energy {m : ℕ} (hm : 2 ≤ m) (α σ ν : Fin m → ℝ) (ξ v : ℂ)
    (source : Fin m → ℂ) (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |α j - midpoint m j| + |heightParameter ν ξ j| ≤ 1 / 4)
    (heq : closureDerivative α σ ν ξ v = -∑ j, source j) :
    pairEnergy (by omega) (integrateCorrected (by omega) α σ ν ξ v source) ≤
      65 / 8 * (2 * m : ℝ) ^ 3 * ∑ j, ‖source j‖ ^ 2 := by
  have hd := integrateCorrected_difference (by omega) α σ ν ξ v source heq
  have hs := corrected_source_l2 hm α σ ν ξ v source hσ hsmall heq
  change (∑ j, ‖corrected α σ ν ξ v source j‖ ^ 2) ≤ _ at hs
  have he := DiscreteEnergy.pairEnergy_le_difference (by omega)
    (integrateCorrected (by omega) α σ ν ξ v source)
  rw [hd] at he
  simp only [normSq_eq_norm_sq, Nat.cast_mul, Nat.cast_ofNat] at he
  rw [repeatHalf_map_sum (by omega) _ (fun z => ‖z‖ ^ 2)] at he
  calc
    _ ≤ (2 * m : ℝ) ^ 3 / 32 * (2 * ∑ j, ‖corrected α σ ν ξ v source j‖ ^ 2) := he
    _ ≤ (2 * m : ℝ) ^ 3 / 32 * (2 * (130 * ∑ j, ‖source j‖ ^ 2)) := by gcongr
    _ = _ := by ring

end
end StructuralNote.ClosedSourceIntegration

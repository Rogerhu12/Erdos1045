import StructuralNote.CommonFiberFirstBounds
import EventualExact.DiscretePoincare

/-! Energy estimates for the actual small first-derivative source. The three
coefficients are the increment size, the small sine, and the tangent error. -/

namespace StructuralNote.CommonFiberDerivativeEnergy

open Erdos1045.EventualExact Complex LensClosure LensIncrementDerivatives
open CommonClosureEnergy CommonTangentialParameters CommonFiberFirstDerivative
open CommonFiberFirstBounds FiniteFourierLift SchurSpectrum DiscreteEnergy
open scoped BigOperators
noncomputable section

theorem sum_comp_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) (g : κ → ℝ) (hg : ∀ k, 0 ≤ g k) :
    (∑ i, g (f i)) ≤ ∑ k, g k := by
  classical
  calc
    _ = ∑ k ∈ Finset.univ.image f, g k := (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => hg k)

theorem half_sum_le {m : ℕ} (f : Fin (2 * m) → ℝ) (hf : ∀ j, 0 ≤ f j) :
    (∑ j : Fin m, f (CommonClosureEnergy.halfIndex j)) ≤ ∑ j, f j := by
  apply sum_comp_le _ _ f hf
  intro i j hij
  exact Fin.ext (congrArg (fun k : Fin (2 * m) => k.val) hij)

theorem successor_square_sum {n : ℕ} (hn : 2 ≤ n) (η : Fin n → ℝ) :
    (∑ j, η (successor (by omega) j) ^ 2) = ∑ j, η j ^ 2 := by
  have he (j : Fin n) : finRotate n j = successor (by omega) j := by
    let : NeZero n := ⟨by omega⟩
    rw [finRotate_apply]
    apply Fin.ext
    change (j.val + 1 % n) % n = (j.val + 1) % n
    rw [Nat.mod_eq_of_lt (show 1 < n by omega)]
  simpa only [he] using Equiv.sum_comp (finRotate n) (fun j => η j ^ 2)

theorem average_square_sum {n : ℕ} (hn : 2 ≤ n) (η : Fin n → ℝ) :
    (∑ j, angleAverage (by omega) η j ^ 2) ≤ ∑ j, η j ^ 2 := by
  have hj (j : Fin n) : angleAverage (by omega) η j ^ 2 ≤
      (η j ^ 2 + η (successor (by omega) j) ^ 2) / 2 := by
    dsimp [angleAverage]
    nlinarith [sq_nonneg (η j - η (successor (by omega) j))]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hj j)
  rw [← Finset.sum_div, Finset.sum_add_distrib, successor_square_sum hn η] at hs
  linarith

theorem average_energy {m : ℕ} (hm : 0 < m) (η : Fin (2 * m) → ℝ)
    (hmean : ∑ j, (η j : ℂ) = 0) :
    (2 * m : ℝ) * (∑ j : Fin m, angleAverage (by omega) η (CommonClosureEnergy.halfIndex j) ^ 2) ≤
      4 * pairEnergy (by omega) (fun j => (η j : ℂ)) := by
  have hs := (half_sum_le (fun j => angleAverage (by omega) η j ^ 2) (fun j => sq_nonneg _)).trans
    (average_square_sum (by omega) η)
  have hp := mean_zero_poincare (by omega : 2 ≤ 2 * m) (fun j => (η j : ℂ)) hmean
  simp only [normSq_ofReal, ← pow_two, Nat.cast_mul, Nat.cast_ofNat] at hp
  have hn : (2 : ℝ) ≤ 2 * m := by exact_mod_cast (show 2 ≤ 2 * m by omega)
  have hs0 : 0 ≤ ∑ j : Fin (2 * m), η j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * m)
  nlinarith

theorem half_difference_energy {m : ℕ} (hm : 0 < m) (η : Fin (2 * m) → ℝ) :
    (2 * m : ℝ) ^ 2 * (∑ j : Fin m, angleDifference (by omega) η (CommonClosureEnergy.halfIndex j) ^ 2) ≤
      8 * Real.pi ^ 2 * pairEnergy (by omega) (fun j => (η j : ℂ)) := by
  have hs := half_sum_le (fun j => angleDifference (by omega) η j ^ 2) (fun j => sq_nonneg _)
  have he := difference_energy_le (by omega : 0 < 2 * m) (fun j => (η j : ℂ))
  have hc (j : Fin (2 * m)) : normSq (difference (by omega) (fun j => (η j : ℂ)) j) =
      angleDifference (by omega) η j ^ 2 := by
    simp only [difference, ← ofReal_sub, normSq_ofReal, angleDifference, pow_two]
  simp only [hc, Nat.cast_mul, Nat.cast_ofNat] at he
  exact (mul_le_mul_of_nonneg_left hs (sq_nonneg _)).trans he

theorem coordinate_energy {m : ℕ} (hm : 0 < m) (h : Fin (2 * m) → ℂ) :
    (2 * m : ℝ) ^ 2 * (∑ j, coordinates hm h j ^ 2) ≤
      8 * Real.pi ^ 2 * pairEnergy (by omega) h := by
  have hs : (∑ j, coordinates hm h j ^ 2) ≤
      ∑ j : Fin m, ‖difference (by omega) h (CommonClosureEnergy.halfIndex j)‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    simpa only [sq_abs, BoxLensLift.halfIndex, CommonClosureEnergy.halfIndex] using
      pow_le_pow_left₀ (abs_nonneg _) (coordinates_abs_le hm h j) 2
  have ht := half_sum_le (fun j => ‖difference (by omega) h j‖ ^ 2) (fun j => sq_nonneg _)
  have he := difference_energy_le (by omega : 0 < 2 * m) h
  simp only [normSq_eq_norm_sq, Nat.cast_mul, Nat.cast_ofNat] at he
  exact (mul_le_mul_of_nonneg_left (hs.trans ht) (sq_nonneg _)).trans he

theorem residual_square_bound {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ) (j : Fin m)
    {B S T : ℝ}
    (hσ : |σ j| ≤ 1) (ht : |heightParameter (coordinates hm v) ξ j| ≤ 1)
    (hb : ‖body (2 * Real.cos (halfAngle hm θ j)) (σ j) (heightParameter (coordinates hm v) ξ j)‖ ≤ B)
    (hs : |Real.sin (halfAngle hm θ j)| ≤ S)
    (he : |phase hm θ j - LensClosure.midpoint m j| + |heightParameter (coordinates hm v) ξ j| ≤ T) :
    ‖residual hm θ v σ ξ η h j‖ ^ 2 ≤
      3 * (B ^ 2 * angleAverage (by omega) η (CommonClosureEnergy.halfIndex j) ^ 2 +
        S ^ 2 * angleDifference (by omega) η (CommonClosureEnergy.halfIndex j) ^ 2 +
        T ^ 2 * coordinates hm h j ^ 2) := by
  have hr := residual_bound hm θ v σ ξ η h j hσ ht
  have hb' := mul_le_mul_of_nonneg_left hb (abs_nonneg (angleAverage (by omega) η (CommonClosureEnergy.halfIndex j)))
  have hs' := mul_le_mul_of_nonneg_right hs (abs_nonneg (angleDifference (by omega) η (CommonClosureEnergy.halfIndex j)))
  have he' := mul_le_mul_of_nonneg_left he (abs_nonneg (coordinates hm h j))
  have hnorm : ‖residual hm θ v σ ξ η h j‖ ≤
      |angleAverage (by omega) η (CommonClosureEnergy.halfIndex j)| * B +
      S * |angleDifference (by omega) η (CommonClosureEnergy.halfIndex j)| +
      |coordinates hm h j| * T := by linarith
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hc := sq_nonneg (|angleAverage (by omega) η (CommonClosureEnergy.halfIndex j)| * B -
    S * |angleDifference (by omega) η (CommonClosureEnergy.halfIndex j)|)
  have hd := sq_nonneg (|angleAverage (by omega) η (CommonClosureEnergy.halfIndex j)| * B -
    |coordinates hm h j| * T)
  have hf := sq_nonneg (S * |angleDifference (by omega) η (CommonClosureEnergy.halfIndex j)| -
    |coordinates hm h j| * T)
  nlinarith [sq_abs (angleAverage (by omega) η (CommonClosureEnergy.halfIndex j)),
    sq_abs (angleDifference (by omega) η (CommonClosureEnergy.halfIndex j)), sq_abs (coordinates hm h j)]

theorem residual_sum_energy {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ)
    {B S T : ℝ} (hmean : ∑ j, (η j : ℂ) = 0) (hσ : ∀ j, |σ j| ≤ 1)
    (ht : ∀ j, |heightParameter (coordinates hm v) ξ j| ≤ 1)
    (hb : ∀ j, ‖body (2 * Real.cos (halfAngle hm θ j)) (σ j) (heightParameter (coordinates hm v) ξ j)‖ ≤ B)
    (hs : ∀ j, |Real.sin (halfAngle hm θ j)| ≤ S)
    (he : ∀ j, |phase hm θ j - LensClosure.midpoint m j| + |heightParameter (coordinates hm v) ξ j| ≤ T) :
    (2 * m : ℝ) ^ 2 * (∑ j, ‖residual hm θ v σ ξ η h j‖ ^ 2) ≤
      (12 * B ^ 2 * (2 * m : ℝ) + 24 * Real.pi ^ 2 * S ^ 2) *
        pairEnergy (by omega) (fun j => (η j : ℂ)) +
      24 * Real.pi ^ 2 * T ^ 2 * pairEnergy (by omega) h := by
  have hr := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
    residual_square_bound hm θ v σ ξ η h j (hσ j) (ht j) (hb j) (hs j) (he j))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hr
  have hA := mul_le_mul_of_nonneg_left (average_energy hm η hmean)
    (show 0 ≤ B ^ 2 * (2 * m : ℝ) by positivity)
  have hD := mul_le_mul_of_nonneg_left (half_difference_energy hm η) (sq_nonneg S)
  have hT := mul_le_mul_of_nonneg_left (coordinate_energy hm h) (sq_nonneg T)
  have hR := mul_le_mul_of_nonneg_left hr (sq_nonneg (2 * m : ℝ))
  nlinarith only [hA, hD, hT, hR]

theorem first_center_energy {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (ξ' : ℂ) {B S T : ℝ}
    (hmean : ∑ j, (η j : ℂ) = 0) (hh : ParameterSpace (by omega) h)
    (hz : (∑ j, velocity (by omega) θ v σ ξ η h ξ' j) = 0) (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |phase (by omega) θ j - LensClosure.midpoint m j| +
      |heightParameter (coordinates (by omega) v) ξ j| ≤ 1 / 4)
    (hb : ∀ j, ‖body (2 * Real.cos (halfAngle (by omega) θ j)) (σ j)
      (heightParameter (coordinates (by omega) v) ξ j)‖ ≤ B)
    (hs : ∀ j, |Real.sin (halfAngle (by omega) θ j)| ≤ S)
    (he : ∀ j, |phase (by omega) θ j - LensClosure.midpoint m j| +
      |heightParameter (coordinates (by omega) v) ξ j| ≤ T) :
    pairEnergy (by omega) (centerVelocity (by omega) θ v σ ξ η h ξ' - h) ≤
      (195 / 2 * (2 * m : ℝ) ^ 2 * B ^ 2 + 195 * Real.pi ^ 2 * (2 * m : ℝ) * S ^ 2) *
        pairEnergy (by omega) (fun j => (η j : ℂ)) +
      195 * Real.pi ^ 2 * (2 * m : ℝ) * T ^ 2 * pairEnergy (by omega) h := by
  have ht (j : Fin m) : |heightParameter (coordinates (by omega) v) ξ j| ≤ 1 := by
    have hj := hsmall j
    linarith [abs_nonneg (phase (by omega) θ j - LensClosure.midpoint m j)]
  have hR := residual_sum_energy (by omega) θ v σ ξ η h hmean hσ ht hb hs he
  calc
    _ ≤ 65 / 8 * (2 * m : ℝ) ^ 3 * ∑ j, ‖residual (by omega) θ v σ ξ η h j‖ ^ 2 :=
      centerVelocity_error_energy hm θ v σ ξ η h ξ' hh hz hσ hsmall
    _ = (65 / 8 * (2 * m : ℝ)) *
        ((2 * m : ℝ) ^ 2 * ∑ j, ‖residual (by omega) θ v σ ξ η h j‖ ^ 2) := by ring
    _ ≤ (65 / 8 * (2 * m : ℝ)) *
        ((12 * B ^ 2 * (2 * m : ℝ) + 24 * Real.pi ^ 2 * S ^ 2) *
          pairEnergy (by omega) (fun j => (η j : ℂ)) +
        24 * Real.pi ^ 2 * T ^ 2 * pairEnergy (by omega) h) :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    _ = _ := by ring

def bodyNorm {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin m → ℝ) (ξ : ℂ) : ℝ :=
  ‖fun j => body (2 * Real.cos (halfAngle hm θ j)) (σ j) (heightParameter (coordinates hm v) ξ j)‖

def sineNorm {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) : ℝ :=
  ‖fun j => Real.sin (halfAngle hm θ j)‖

def tangentErrorNorm {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (ξ : ℂ) : ℝ :=
  ‖fun j => |phase hm θ j - LensClosure.midpoint m j| + |heightParameter (coordinates hm v) ξ j|‖

/-- All three error coefficients below are computed from the actual geometry;
there are no extra source estimates in the hypotheses. -/
theorem first_center_energy_actual_coefficients {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (ξ' : ℂ)
    (hmean : ∑ j, (η j : ℂ) = 0) (hh : ParameterSpace (by omega) h)
    (hz : (∑ j, velocity (by omega) θ v σ ξ η h ξ' j) = 0) (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |phase (by omega) θ j - LensClosure.midpoint m j| +
      |heightParameter (coordinates (by omega) v) ξ j| ≤ 1 / 4) :
    pairEnergy (by omega) (centerVelocity (by omega) θ v σ ξ η h ξ' - h) ≤
      (195 / 2 * (2 * m : ℝ) ^ 2 * bodyNorm (by omega) θ v σ ξ ^ 2 +
        195 * Real.pi ^ 2 * (2 * m : ℝ) * sineNorm (by omega) θ ^ 2) *
        pairEnergy (by omega) (fun j => (η j : ℂ)) +
      195 * Real.pi ^ 2 * (2 * m : ℝ) * tangentErrorNorm (by omega) θ v ξ ^ 2 *
        pairEnergy (by omega) h := by
  apply first_center_energy hm θ v σ ξ η h ξ' hmean hh hz hσ hsmall
  · intro j
    unfold bodyNorm
    exact norm_le_pi_norm (fun k : Fin m => body (2 * Real.cos (halfAngle (by omega) θ k))
      (σ k) (heightParameter (coordinates (by omega) v) ξ k)) j
  · intro j
    unfold sineNorm
    exact (Real.norm_eq_abs _).symm.le.trans
      (norm_le_pi_norm (fun k : Fin m => Real.sin (halfAngle (by omega) θ k)) j)
  · intro j
    unfold tangentErrorNorm
    have hnonneg : 0 ≤ |phase (by omega) θ j - LensClosure.midpoint m j| +
        |heightParameter (coordinates (by omega) v) ξ j| := by positivity
    exact (Real.norm_of_nonneg hnonneg).symm.le.trans
      (norm_le_pi_norm (fun k : Fin m => |phase (by omega) θ k - LensClosure.midpoint m k| +
        |heightParameter (coordinates (by omega) v) ξ k|) j)

end
end StructuralNote.CommonFiberDerivativeEnergy

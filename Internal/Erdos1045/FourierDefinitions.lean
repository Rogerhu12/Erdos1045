import Erdos1045.FaberSampling
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Circle functions and actual sampled tail coefficients

Definitions and elementary series identities used by the direct Parseval,
finite-polynomial approximation, and separated-interval sampling proofs.
-/

namespace Erdos1045.FaberFourier

open MeasureTheory
open scoped BigOperators
noncomputable section

def circleMeasure : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * Real.pi))

def energy (f : ℝ → ℂ) : ℝ := ∫ t, ‖f t‖ ^ 2 ∂circleMeasure

def character (m : ℕ) (t : ℝ) : ℂ := Complex.exp (-(m : ℂ) * Complex.I * t)

def series (a : ℕ → ℂ) (t : ℝ) : ℂ := ∑' m, a m * character m t

/-- A periodic Sobolev function with its continuous representative and an
actual weak derivative; the integral identity fixes the derivative semantics. -/
structure CircleH1 where
  value : ℝ → ℂ
  weakDerivative : ℝ → ℂ
  continuous_value : Continuous value
  periodic_value : Function.Periodic value (2 * Real.pi)
  derivative_locally_integrable : LocallyIntegrable weakDerivative
  fundamental_identity : ∀ s t : ℝ,
    value t - value s = ∫ x in s..t, weakDerivative x
  square_integrable_value : Integrable (fun t => ‖value t‖ ^ 2) circleMeasure
  square_integrable_derivative : Integrable (fun t => ‖weakDerivative t‖ ^ 2) circleMeasure

def H1Sampling {n : ℕ} (θ : Fin n → ℝ) (C : ℝ) : Prop :=
  ∀ f : CircleH1, (∑ j, ‖f.value (θ j)‖ ^ 2) ≤
    C * ((n : ℝ) * energy f.value + energy f.weakDerivative / n)

def Separated {n : ℕ} (θ : Fin n → ℝ) (γ : ℝ) : Prop :=
  (∀ j, 0 ≤ θ j ∧ θ j < 2 * Real.pi) ∧
  ∀ i j, i ≠ j → γ / n ≤ min |θ i - θ j| (2 * Real.pi - |θ i - θ j|)

theorem norm_character (m : ℕ) (t : ℝ) : ‖character m t‖ = 1 := by
  simp [character, Complex.norm_exp]

def tailCoefficients (a : ℕ → ℂ) (k : ℕ) (m : ℕ) : ℂ := a (m + k)

/-- The shifted version of `c⁻¹ ∑_{m≥k} a_m w_j^(k-1-m)` with
`w_j = exp (I θ_j)`. The phase factor has modulus one. -/
def coefficient {n : ℕ} (c : ℝ) (a : ℕ → ℂ) (θ : Fin n → ℝ)
    (j : Fin n) (k : ℕ) : ℂ :=
  (c : ℂ)⁻¹ * character 1 (θ j) * series (tailCoefficients a k) (θ j)

theorem norm_coefficient_sq {n : ℕ} {c : ℝ} (hc : 0 < c)
    (a : ℕ → ℂ) (θ : Fin n → ℝ) (j : Fin n) (k : ℕ) :
    ‖coefficient c a θ j k‖ ^ 2 = ‖series (tailCoefficients a k) (θ j)‖ ^ 2 / c ^ 2 := by
  simp [coefficient, norm_inv, norm_character, Complex.norm_real,
    abs_of_pos hc, div_eq_mul_inv, mul_pow, mul_comm]

theorem tail_summable {a : ℕ → ℂ}
    (ha : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖a m‖ ^ 2)) (k : ℕ) :
    Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖tailCoefficients a k m‖ ^ 2) := by
  have hs := ha.comp_injective (show Function.Injective (fun m : ℕ => m + k) from
    fun _ _ h => Nat.add_right_cancel h)
  apply Summable.of_nonneg_of_le (fun m => by positivity) _ hs
  intro m
  have hm : (m : ℝ) ≤ ((m + k : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right m k
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg m) hm 2
  exact mul_le_mul_of_nonneg_right (add_le_add le_rfl hp) (sq_nonneg _)

theorem coefficient_energies_summable {a : ℕ → ℂ}
    (ha : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖a m‖ ^ 2)) :
    Summable (fun m => ‖a m‖ ^ 2) ∧
      Summable (fun m : ℕ => (m : ℝ) ^ 2 * ‖a m‖ ^ 2) := by
  constructor
  · apply Summable.of_nonneg_of_le (fun m => sq_nonneg _) _ ha
    intro m
    nlinarith [mul_nonneg (sq_nonneg (m : ℝ)) (sq_nonneg ‖a m‖)]
  · apply Summable.of_nonneg_of_le (fun m => by positivity) _ ha
    intro m
    nlinarith [sq_nonneg ‖a m‖]

theorem samplingKernel_summable (n k : ℕ) {a : ℕ → ℂ}
    (ha : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖a m‖ ^ 2)) :
    Summable (fun m => Erdos1045.FaberSampling.samplingKernel n k m * ‖a m‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun m => by
    unfold Erdos1045.FaberSampling.samplingKernel
    split_ifs <;> positivity) _ (ha.mul_left ((n : ℝ) + 1 / n))
  intro m
  unfold Erdos1045.FaberSampling.samplingKernel
  split_ifs with hkm
  · have hd : ((m - (k + 1) : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m (k + 1)
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg (m - (k + 1))) hd 2
    have hq := div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)
    have hf : (n : ℝ) + ((m - (k + 1) : ℕ) : ℝ) ^ 2 / n ≤
        ((n : ℝ) + 1 / n) * (1 + (m : ℝ) ^ 2) := by
      simp only [div_eq_mul_inv, one_mul] at hq ⊢
      nlinarith [mul_nonneg (Nat.cast_nonneg n) (sq_nonneg (m : ℝ)),
        inv_nonneg.mpr (show (0 : ℝ) ≤ n by positivity)]
    exact (mul_le_mul_of_nonneg_right hf (sq_nonneg ‖a m‖)).trans_eq (by ring)
  · simp only [zero_mul]
    positivity

theorem samplingKernel_tsum_eq_tail (n k : ℕ) {a : ℕ → ℂ}
    (ha : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖a m‖ ^ 2)) :
    (∑' m, Erdos1045.FaberSampling.samplingKernel n k m * ‖a m‖ ^ 2) =
      (∑' m : ℕ, ((n : ℝ) + (m : ℝ) ^ 2 / n) * ‖a (m + (k + 1))‖ ^ 2) := by
  have hs := (samplingKernel_summable n k ha).sum_add_tsum_nat_add (k + 1)
  have hz : (∑ m ∈ Finset.range (k + 1),
      Erdos1045.FaberSampling.samplingKernel n k m * ‖a m‖ ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    simp [Erdos1045.FaberSampling.samplingKernel,
      show ¬k + 1 ≤ m from Nat.not_le.mpr (Finset.mem_range.mp hm)]
  rw [hz, zero_add] at hs
  rw [← hs]
  apply tsum_congr
  intro m
  simp [Erdos1045.FaberSampling.samplingKernel]

theorem tail_energy_eq (n k : ℕ) {a : ℕ → ℂ}
    (ha : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖a m‖ ^ 2)) :
    (n : ℝ) * (∑' m, ‖a (m + k)‖ ^ 2) +
      (∑' m : ℕ, (m : ℝ) ^ 2 * ‖a (m + k)‖ ^ 2) / n =
    ∑' m : ℕ, ((n : ℝ) + (m : ℝ) ^ 2 / n) * ‖a (m + k)‖ ^ 2 := by
  have hc := coefficient_energies_summable (tail_summable ha k)
  dsimp [tailCoefficients] at hc
  rw [← tsum_mul_left, ← tsum_div_const]
  rw [← (hc.1.mul_left (n : ℝ)).tsum_add (hc.2.div_const (n : ℝ))]
  apply tsum_congr
  intro m
  ring

end

end Erdos1045.FaberFourier

import StructuralNote.FixedDualClassificationCircleShift

/-! Actual convolution of the periodic step profile, with exact signed
frequency phases. No rotation of the finite grid is introduced. -/

namespace StructuralNote.FixedDualClassificationStepPotential

open Real Set MeasureTheory FixedDualClassificationStep FixedDualClassificationFunctional
open FixedDualClassificationPeriodicStep FixedDualClassificationCircleShift
open FixedDualClassificationOddSpectrum FixedDualClassificationKernelTail
open Erdos1045.EventualExact Erdos1045.EventualExact.FiniteBox
open scoped BigOperators ComplexConjugate
noncomputable section

def continuousPotential {n : ℕ} (q : Fin n → ℝ) (scale θ : ℝ) : ℝ :=
  kernelPotential (reflected (circleProfile q scale) θ)

def stepTerm {n : ℕ} (q : Fin n → ℝ) (scale θ : ℝ) (k : ℤ) : ℂ :=
  (2 * kernelCoefficient k * (scale * sinc ((2 * k + 1) * Real.pi / n)) : ℝ) *
    oscillation (-(2 * k + 1)) θ * conj (signedMidpointCoefficient q (2 * k + 1))

theorem reflected_step_coefficient {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (hq : Antiperiodic hm q) (scale θ : ℝ) (k : ℤ) :
    oddCoefficient (reflected (circleProfile q scale) θ) k =
      (scale * sinc ((2 * k + 1) * Real.pi / (2 * m : ℕ)) : ℝ) *
        oscillation (-(2 * k + 1)) θ * conj (signedMidpointCoefficient q (2 * k + 1)) := by
  have hbound := circleProfile_bound q scale (∑ j, |q j|)
    (Finset.sum_nonneg (fun j _ => abs_nonneg (q j)))
    (fun j => Finset.single_le_sum (fun i _ => abs_nonneg (q i)) (Finset.mem_univ j))
  rw [reflected_oddCoefficient (circleProfile_measurable q scale) hbound
    (circleProfile_antiperiodic hm q hq scale), circleProfile_fourierCoeff (by omega)]
  simp only [map_mul, Complex.conj_ofReal, Int.cast_add, Int.cast_mul,
    Int.cast_ofNat, Int.cast_one]
  ring

theorem continuousPotential_hasSum {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (hq : Antiperiodic hm q) (scale θ : ℝ) :
    HasSum (stepTerm q scale θ) (continuousPotential q scale θ : ℂ) := by
  have hmF := reflected_measurable (circleProfile_measurable q scale) θ
  have hbound := circleProfile_bound q scale (∑ j, |q j|)
    (Finset.sum_nonneg (fun j _ => abs_nonneg (q j)))
    (fun j => Finset.single_le_sum (fun i _ => abs_nonneg (q i)) (Finset.mem_univ j))
  have h := kernel_potential_hasSum (box_memLp hmF (fun u _ => reflected_bound hbound θ u))
  simp_rw [reflected_step_coefficient hm q hq scale θ] at h
  convert h using 1
  · funext k
    unfold stepTerm
    push_cast
    ring
  · rfl

theorem continuousPotential_truncation {A scale ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ s : Finset ℤ, ∀ m : ℕ, ∀ hm : 0 < m, ∀ q : Fin (2 * m) → ℝ,
      Antiperiodic hm q → (∀ j, |q j| ≤ A) → ∀ θ : ℝ,
      ‖(continuousPotential q scale θ : ℂ) - ∑ k ∈ s, stepTerm q scale θ k‖ < ε := by
  obtain ⟨s, hs⟩ := uniform_potential_truncation (mul_nonneg (abs_nonneg scale) hA) hε
  refine ⟨s, fun m hm q hq hb θ => ?_⟩
  have h := hs (reflected (circleProfile q scale) θ)
    (reflected_measurable (circleProfile_measurable q scale) θ)
    (fun u _ => reflected_bound (circleProfile_bound q scale A hA hb) θ u)
  change ‖(continuousPotential q scale θ : ℂ) -
    ∑ k ∈ s, (2 * kernelCoefficient k : ℂ) * oddCoefficient (reflected (circleProfile q scale) θ) k‖ < ε at h
  simp_rw [reflected_step_coefficient hm q hq scale θ] at h
  convert h using 1
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  unfold stepTerm
  push_cast
  ring

end
end StructuralNote.FixedDualClassificationStepPotential

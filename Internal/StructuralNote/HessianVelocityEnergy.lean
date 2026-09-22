import StructuralNote.HessianAngularReference
import StructuralNote.RadialInterpolationEnergy
import StructuralNote.SignedPressureAngular

/-! Uniform energy of the reference angular velocity. The mean-zero condition
removes the constant angular direction without a logarithmic loss. -/

namespace StructuralNote.HessianVelocityEnergy

open Erdos1045 Erdos1045.EventualExact Complex SchurSpectrum DiscreteEnergy
open AngularObjectiveCurvature HessianReferencePotential
open scoped BigOperators
noncomputable section

theorem root_mul_energy {n : ℕ} (hn : 0 < n) (g : Fin n → ℂ) :
    pairEnergy hn (fun j => root n j * g j) ≤
      2 * pairEnergy hn g + n * ∑ j, normSq (g j) := by
  have hp (i j : Fin n) :
      normSq (root n i * g i - root n j * g j) / normSq (root n i - root n j) ≤
        2 * (normSq (g i - g j) / normSq (root n i - root n j)) + 2 * normSq (g j) := by
    have he : root n i * g i - root n j * g j =
        root n i * (g i - g j) + (root n i - root n j) * g j := by ring
    have hs := SignedPressureAngular.normSq_add_le (root n i * (g i - g j))
      ((root n i - root n j) * g j)
    have hr : normSq (root n i) = 1 := by
      simp only [normSq_eq_norm_sq, root, norm_pow, ClosedFourier.root_norm, one_pow]
    rw [normSq_mul, normSq_mul, hr, one_mul] at hs
    rw [← he] at hs
    by_cases hz : normSq (root n i - root n j) = 0
    · simp only [hz, div_zero, mul_zero, zero_add]
      exact mul_nonneg (by norm_num) (normSq_nonneg _)
    · have hh := div_le_div_of_nonneg_right hs (normSq_nonneg (root n i - root n j))
      simpa only [add_div, mul_div_assoc, mul_div_cancel_left₀ _ hz] using hh
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hp i j))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  simp only [pairEnergy_eq_chord_sum]
  simp only [root] at hs ⊢
  linarith only [hs]

theorem mean_zero_mass {n : ℕ} (hn : 2 ≤ n) (g : Fin n → ℂ) (hg : ∑ j, g j = 0) :
    (n : ℝ) * (∑ j, normSq (g j)) ≤ 4 * pairEnergy (by omega) g := by
  have hp := mean_zero_poincare hn g hg
  have hmass : 0 ≤ ∑ j, normSq (g j) := Finset.sum_nonneg (fun _ _ => normSq_nonneg _)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith only [hp, mul_nonneg (sub_nonneg.mpr hnR) hmass]

theorem angular_energy {n : ℕ} (hn : 2 ≤ n) (η : Fin n → ℝ)
    (hη : ∑ j, (η j : ℂ) = 0) :
    pairEnergy (by omega) (fun j => I * root n j * (η j : ℂ)) ≤
      6 * pairEnergy (by omega) (fun j => (η j : ℂ)) := by
  have he : (fun j => I * root n j * (η j : ℂ)) =
      (fun j => I * (root n j * (η j : ℂ))) := by funext j; ring
  rw [he, RadialInterpolationEnergy.pairEnergy_scale, norm_I, one_pow, one_mul]
  have hp := root_mul_energy (by omega) (fun j => (η j : ℂ))
  have hm := mean_zero_mass hn (fun j => (η j : ℂ)) hη
  linarith

theorem reference_velocity_energy {n : ℕ} (hn : 2 ≤ n) (η : Fin n → ℝ)
    (h : Fin n → ℂ) (hη : ∑ j, (η j : ℂ) = 0) :
    pairEnergy (by omega) (fun j => I * root n j * (η j : ℂ) + h j) ≤
      12 * (pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) := by
  have hs := QuadraticStability.pairEnergy_add_le (by omega : 0 < n)
    (fun j => I * root n j * (η j : ℂ)) h
  have ha := angular_energy hn η hη
  have hh := pairEnergy_nonneg (by omega : 0 < n) h
  change pairEnergy (by omega) (fun j => I * root n j * (η j : ℂ) + h j) ≤ _ at hs
  linarith

end
end StructuralNote.HessianVelocityEnergy

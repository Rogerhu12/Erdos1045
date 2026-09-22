import StructuralNote.HessianVelocityEnergy
import StructuralNote.CommonFiberHessianGeometryChord

/-! The shared angular displacement has energy at most six times the actual
angular parameter energy, without a logarithmic loss. -/

namespace StructuralNote.AngularDisplacementEnergy

open Erdos1045 Erdos1045.EventualExact Complex SchurSpectrum LensClosure
open AngularObjectiveCurvature CommonFiberGeometry HessianVelocityEnergy HessianReferencePotential
open CommonFiberHessianGeometryChord
open scoped BigOperators
noncomputable section

theorem unit_energy {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) :
    pairEnergy hn (fun j => unit (θ j) - 1) ≤ pairEnergy hn (fun j => (θ j : ℂ)) := by
  have hp (i j : Fin n) :
      normSq ((unit (θ i) - 1) - (unit (θ j) - 1)) ≤ normSq ((θ i : ℂ) - (θ j : ℂ)) := by
    rw [sub_sub_sub_cancel_right, ← ofReal_sub, normSq_ofReal, ← pow_two, normSq_eq_norm_sq]
    simpa only [sq_abs] using pow_le_pow_left₀ (norm_nonneg _) (norm_unit_sub_le (θ i) (θ j)) 2
  rw [pairEnergy_eq_chord_sum, pairEnergy_eq_chord_sum]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  exact Finset.sum_le_sum (fun j _ => div_le_div_of_nonneg_right (hp i j) (normSq_nonneg _))

theorem unit_mass {n : ℕ} (θ : Fin n → ℝ) :
    (∑ j, normSq (unit (θ j) - 1)) ≤ ∑ j, normSq (θ j : ℂ) := by
  apply Finset.sum_le_sum
  intro j _
  rw [normSq_eq_norm_sq, normSq_ofReal, ← pow_two]
  simpa only [sq_abs] using pow_le_pow_left₀ (norm_nonneg _) (unit_sub_one (θ j)) 2

theorem displacement_energy {n : ℕ} (hn : 2 ≤ n) (θ : Fin n → ℝ)
    (hmean : ∑ j, (θ j : ℂ) = 0) :
    pairEnergy (by omega) (fun j => diameterVector θ j - root n j) ≤
      6 * pairEnergy (by omega) (fun j => (θ j : ℂ)) := by
  have he : (fun j => diameterVector θ j - root n j) =
      (fun j => root n j * (unit (θ j) - 1)) := by
    funext j
    simp only [diameterVector, root, FourierMultiplier.character, Nat.mul_one]
    ring
  rw [he]
  have hp := root_mul_energy (by omega : 0 < n) (fun j => unit (θ j) - 1)
  have hu := unit_energy (by omega : 0 < n) θ
  have hm := mul_le_mul_of_nonneg_left (unit_mass θ) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hs := mean_zero_mass hn (fun j => (θ j : ℂ)) hmean
  linarith only [hp, hu, hm, hs]

end
end StructuralNote.AngularDisplacementEnergy

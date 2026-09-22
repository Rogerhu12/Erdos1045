import StructuralNote.LogDiscriminantHessian
import EventualExact.QuadraticStability
import StructuralNote.CommonTangentialParameters

/-! Identifying the regular-configuration Hessian with the already proved
Schur quadratic, including its coercivity on the actual free parameter space. -/

namespace StructuralNote.HessianReferencePotential

open Erdos1045 Erdos1045.EventualExact Complex SchurSpectrum
open LogDiscriminantHessian CommonTangentialParameters
open scoped BigOperators
noncomputable section

def root (n : ℕ) (j : Fin n) : ℂ := LocalPhase.regularRoot n ^ (j : ℕ)

theorem quadratic_eq_potential {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    quadratic (root n) c = 2 * pairPotential hn c := by
  let f : ℕ → ℕ → ℝ := fun i j =>
    (((periodize hn c i - periodize hn c j) /
      (LocalPhase.regularRoot n ^ i - LocalPhase.regularRoot n ^ j)) ^ 2).re
  have hp (i j : ℕ) : f (i + n) j = f i j := by
    simp only [f, periodize_periodic hn c i, pow_add, LocalDFT.regularRoot_pow hn, mul_one]
  have hshift (j : ℕ) : (∑ h ∈ Finset.range n, f (j + h) j) = ∑ i ∈ Finset.range n, f i j := by
    have hh := CyclicAngles.sum_shift_of_drift (fun i => f i j) 0
      (fun i => by rw [hp]; ring) j
    simpa only [mul_zero, add_zero, Nat.add_comm] using hh
  have hs : (∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n, f (j + h) j) =
      ∑ i : Fin n, ∑ j : Fin n, (((c i - c j) / (root n i - root n j)) ^ 2).re := by
    rw [Finset.sum_erase _ (by simp [f]), Finset.sum_comm]
    simp_rw [hshift]
    rw [Finset.sum_comm, Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro j _
    simp only [f, periodize, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt, root]
  rw [AntipodalLog.pairPotential_eq_real_sum]
  change quadratic (root n) c = 2 * (-(∑ h ∈ (Finset.range n).erase 0,
    ∑ j ∈ Finset.range n, f (j + h) j) / 2)
  rw [hs]
  unfold quadratic
  ring

theorem quadratic_velocity_error {n : ℕ} (hn : 0 < n) (c d : Fin n → ℂ) :
    |quadratic (root n) (c + d) - quadratic (root n) c| ≤
      4 * Real.sqrt (pairEnergy hn c) * Real.sqrt (pairEnergy hn d) + 2 * pairEnergy hn d := by
  rw [quadratic_eq_potential hn, quadratic_eq_potential hn, ← mul_sub,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := mul_le_mul_of_nonneg_left (QuadraticStability.potential_difference_le hn c d)
    (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith only [hh]

theorem kernel_negative {m : ℕ} (hm : 2 ≤ m) (h : Fin (2 * m) → ℂ)
    (hh : ParameterSpace (by omega) h) :
    quadratic (root (2 * m)) h ≤ -pairEnergy (by omega) h / 32 := by
  rw [quadratic_eq_potential (by omega)]
  have hc := kernel_coercivity hm h hh.1 hh.2.1 hh.2.2
  linarith

end
end StructuralNote.HessianReferencePotential

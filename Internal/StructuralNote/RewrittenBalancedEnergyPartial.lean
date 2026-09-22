import StructuralNote.RewrittenBalancedCoefficientLimit
import EventualExact.WholeBoxObjective

/-! Fixed partial energy limits and a uniform tail estimate for the actual
balanced finite vertices. -/

namespace StructuralNote.RewrittenBalancedEnergyPartial

open Real Complex Filter Erdos1045.EventualExact FourierMultiplier
open FiniteBox SolThreeBlockWord RewrittenBalancedCoefficientLimit
open FixedDualClassificationStep FixedDualClassificationStepEnergy
open FixedDualClassificationMultiplierLimit FixedDualClassificationFiniteTail
open FixedDualClassificationOddSpectrum SchurLiftBounds
open scoped BigOperators Topology
noncomputable section

def finiteEnergy (m : ℕ) : ℝ :=
  normalizedBoxEnergy (operator (2 * m)) (balancedVertex m)

def finiteTerm (m k : ℕ) : ℝ :=
  SchurWeights.weight (2 * m) (2 * k + 1) *
    ‖signedMidpointCoefficient (balancedVertex m) (2 * k + 1)‖ ^ 2

def limitTerm (k : ℕ) : ℝ :=
  positiveWeight k *
    ((3 - 6 * Real.cos (Real.pi * (2 * k + 1 : ℕ) / 3)) /
      ((2 * k + 1 : ℕ) : ℝ) ^ 2)

def finitePartial (m P : ℕ) : ℝ := ∑ k ∈ Finset.range P, finiteTerm m k
def limitPartial (P : ℕ) : ℝ := ∑ k ∈ Finset.range P, limitTerm k

theorem finiteTerm_nonneg (m k : ℕ) : 0 ≤ finiteTerm m k :=
  mul_nonneg (SchurWeights.weight_nonneg _ _) (sq_nonneg _)

theorem finiteTerm_tendsto (k : ℕ) :
    Tendsto (fun m => finiteTerm m k) atTop (𝓝 (limitTerm k)) := by
  by_cases hk : k = 0
  · subst k
    have hw (n : ℕ) : SchurWeights.weight n 1 = 0 :=
      SchurWeights.weight_eq_zero (by simp [SchurWeights.Active])
    simp [finiteTerm, limitTerm, positiveWeight, kernelCoefficient,
      naturalKernelCoefficient, hw]
  · have hw := (positive_multiplier_tendsto k).comp
      (tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id)
    have hc := coefficientFormula_tendsto (by omega : 2 * k + 1 ≠ 0)
    apply (hw.mul hc).congr'
    filter_upwards [eventually_ge_atTop (2 * k + 4)] with m hm
    have hp : SchurWeights.Active (2 * m) (2 * k + 1) :=
      ⟨⟨k, by omega⟩, by omega, by omega⟩
    have he : ‖signedMidpointCoefficient (balancedVertex m) (2 * (k : ℤ) + 1)‖ ^ 2 =
        coefficientFormula m (2 * k + 1) := by
      simpa only [Fin.val_mk, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        using actual_coefficient_formula (by omega : 3 ≤ m)
          ⟨2 * k + 1, by omega⟩ hp
    dsimp only [finiteTerm]
    rw [he]
    rfl

theorem limitTerm_nonneg (k : ℕ) : 0 ≤ limitTerm k :=
  ge_of_tendsto (finiteTerm_tendsto k)
    (Filter.Eventually.of_forall (fun m => finiteTerm_nonneg m k))

theorem finitePartial_tendsto (P : ℕ) :
    Tendsto (fun m => finitePartial m P) atTop (𝓝 (limitPartial P)) := by
  exact tendsto_finsetSum _ (fun k _ => finiteTerm_tendsto k)

theorem balanced_meanSquare_le {m : ℕ} (hm : 3 ≤ m) :
    meanSquare (balancedVertex m) ≤ 16 := by
  apply le_trans (SchurLiftBounds.meanSquare_le_of_bound
    (by omega : 0 < 2 * m) (balancedVertex m) (by norm_num : (0 : ℝ) ≤ 4) ?_)
    (by norm_num)
  intro j
  rw [balancedVertex, dif_pos hm]
  exact (vertex_abs (amplitude_pos (by omega)).le _ j).le.trans
    (WholeBoxObjective.amplitude_le_four (by omega))

theorem finitePartial_tail {m P : ℕ} (hm : 3 ≤ m) (hP : 4 * P < 2 * m) :
    0 ≤ finiteEnergy m - finitePartial m P ∧
      finiteEnergy m - finitePartial m P ≤ 16 / (2 * (P : ℝ) + 1) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  have ht := energy_lowFrequency_error (P := 2 * P) (by omega : 0 < 2 * m)
    (show Even (2 * m) from ⟨m, by omega⟩) (balancedVertex m)
  rw [finite_positive_energy hP (show Even (2 * m) from ⟨m, by omega⟩)] at ht
  refine ⟨ht.1, ht.2.trans ?_⟩
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  exact div_le_div_of_nonneg_right (balanced_meanSquare_le hm) (by positivity)

theorem finiteEnergy_le {m : ℕ} (hm : 3 ≤ m) : finiteEnergy m ≤ 16 := by
  have h := (finitePartial_tail (P := 0) hm (by omega)).2
  simpa [finitePartial] using h

theorem limitPartial_le (P : ℕ) : limitPartial P ≤ 16 := by
  apply le_of_tendsto (finitePartial_tendsto P)
  filter_upwards [eventually_ge_atTop (2 * P + 3)] with m hm
  have ht := (finitePartial_tail (P := P) (by omega : 3 ≤ m) (by omega)).1
  have he := finiteEnergy_le (by omega : 3 ≤ m)
  linarith

end
end StructuralNote.RewrittenBalancedEnergyPartial

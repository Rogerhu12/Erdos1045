import StructuralNote.StrongPointwiseNormal

/-! Sharp pointwise center increments from the canonical lift and residual budget. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.StrongPointwiseSteps

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter GapRigidity
open SchurSpectrum SchurLift SchurLiftBounds DiscreteEnergy FiniteFourierLift FourierMultiplier
open ExtremalPolarCenter NormalizedPolarRepresentation SignedPressureRemainder StrongObjectiveEstimate
open SinglePressureEstimate StrongBudgetConsequences StrongPointwiseNormal ActualCrossingGeometry

theorem complex_difference_of_budget {n : ℕ} (hn : 0 < n) (v : Points n)
    (hE : pairEnergy hn v ≤ budgetConstant / (n : ℝ) ^ 2) (j : Fin n) :
    ‖difference hn v j‖ ≤ angleConstant / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he := DiscreteEnergy.difference_energy_le hn v
  have hs := Finset.single_le_sum (s := Finset.univ) (f := fun j => normSq (difference hn v j))
    (fun i _ => normSq_nonneg _) (Finset.mem_univ j)
  have hs' := mul_le_mul_of_nonneg_left hs (sq_nonneg (n : ℝ))
  have hδ : normSq (difference hn v j) ≤ 8 * Real.pi ^ 2 * pairEnergy hn v / (n : ℝ) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hn0)).2
    nlinarith only [he, hs']
  have hC : angleConstant ^ 2 = 8 * Real.pi ^ 2 * budgetConstant :=
    Real.sq_sqrt (by have := budgetConstant_nonneg; positivity)
  have hδ' : ‖difference hn v j‖ ^ 2 ≤ (angleConstant / (n : ℝ) ^ 2) ^ 2 := by
    rw [← normSq_eq_norm_sq]
    calc
      _ ≤ 8 * Real.pi ^ 2 * pairEnergy hn v / (n : ℝ) ^ 2 := hδ
      _ ≤ 8 * Real.pi ^ 2 * (budgetConstant / (n : ℝ) ^ 2) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by positivity)) (sq_nonneg _)
      _ = _ := by rw [div_pow, hC]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (by unfold angleConstant; positivity)).1 hδ'

theorem canonical_increment_bound {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ)
    (hq : ∀ j, |q j| ≤ 5) (j : Fin n) :
    ‖difference (by omega) (canonicalLift q) j‖ ≤ 20 * Real.pi / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hi := increment_sq_le_of_bound hn q (by norm_num : (0 : ℝ) ≤ 5) hq j
  have hh : normSq (increment q j) ≤ 300 * Real.pi ^ 2 / (n : ℝ) ^ 4 := by
    calc
      _ ≤ 12 * Real.sin (Real.pi / n) ^ 2 / (n : ℝ) ^ 2 * (5 : ℝ) ^ 2 := hi
      _ ≤ 12 * (Real.pi / n) ^ 2 / (n : ℝ) ^ 2 * (5 : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left Real.sin_sq_le_sq (by norm_num))
            (sq_nonneg _)) (by norm_num)
      _ = _ := by ring
  rw [canonicalLift_difference hn]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 20 * Real.pi / (n : ℝ) ^ 2)).1
  rw [← normSq_eq_norm_sq]
  calc
    _ ≤ 300 * Real.pi ^ 2 / (n : ℝ) ^ 4 := hh
    _ ≤ 400 * Real.pi ^ 2 / (n : ℝ) ^ 4 := by gcongr; norm_num
    _ = _ := by ring

def centerStepConstant : ℝ := 20 * Real.pi + angleConstant

def physicalStepConstant : ℝ := centerStepConstant + angleConstant * centerConstant

theorem center_difference_bound {n : ℕ} (hn : 3 ≤ n) (c : Points n) (q : Fin n → ℝ)
    (hq : ∀ j, |q j| ≤ 5)
    (hD : pairEnergy (by omega) (c - canonicalLift q) ≤ budgetConstant / (n : ℝ) ^ 2) (j : Fin n) :
    ‖difference (by omega) c j‖ ≤ centerStepConstant / (n : ℝ) ^ 2 := by
  have he : difference (by omega) c j = difference (by omega) (canonicalLift q) j +
      difference (by omega) (c - canonicalLift q) j := by simp only [difference, Pi.sub_apply]; ring
  rw [he]
  calc
    _ ≤ ‖difference (by omega) (canonicalLift q) j‖ +
        ‖difference (by omega) (c - canonicalLift q) j‖ := norm_add_le _ _
    _ ≤ 20 * Real.pi / (n : ℝ) ^ 2 + angleConstant / (n : ℝ) ^ 2 :=
      add_le_add (canonical_increment_bound hn q hq j) (complex_difference_of_budget (by omega) _ hD j)
    _ = _ := by unfold centerStepConstant; ring

theorem derotation_difference_bound {n : ℕ} (hn : 0 < n) (c : Points n) (θ : Fin n → ℝ)
    (hc : ‖c‖ ≤ centerConstant / n)
    (hd : ∀ j, ‖difference hn c j‖ ≤ centerStepConstant / (n : ℝ) ^ 2)
    (hθ : ∀ j, |θ (successor hn j) - θ j| ≤ angleConstant / (n : ℝ) ^ 2) (j : Fin n) :
    ‖difference hn (fun j => circle (θ j) * c j) j‖ ≤ physicalStepConstant / (n : ℝ) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hC : 0 ≤ centerConstant := Real.sqrt_nonneg _
  have hT : 0 ≤ angleConstant := Real.sqrt_nonneg _
  have he : difference hn (fun j => circle (θ j) * c j) j =
      circle (θ (successor hn j)) * difference hn c j +
        (circle (θ (successor hn j)) - circle (θ j)) * c j := by unfold difference; ring
  have hprod : angleConstant / (n : ℝ) ^ 2 * (centerConstant / n) ≤
      angleConstant * centerConstant / (n : ℝ) ^ 2 := by
    have hc' : centerConstant / (n : ℝ) ≤ centerConstant :=
      div_le_self hC hn1
    have hm := mul_le_mul_of_nonneg_left hc' (div_nonneg hT (sq_nonneg (n : ℝ)))
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hm
  rw [he]
  calc
    _ ≤ ‖circle (θ (successor hn j)) * difference hn c j‖ +
        ‖(circle (θ (successor hn j)) - circle (θ j)) * c j‖ := norm_add_le _ _
    _ = ‖difference hn c j‖ + ‖circle (θ (successor hn j)) - circle (θ j)‖ * ‖c j‖ := by
      rw [norm_mul, circle_norm, one_mul, norm_mul]
    _ ≤ centerStepConstant / (n : ℝ) ^ 2 +
        angleConstant / (n : ℝ) ^ 2 * (centerConstant / n) := by
      exact add_le_add (hd j) (mul_le_mul ((circle_lipschitz _ _).trans (hθ j))
        ((norm_le_pi_norm c j).trans hc) (norm_nonneg _) (by positivity))
    _ ≤ centerStepConstant / (n : ℝ) ^ 2 + angleConstant * centerConstant / (n : ℝ) ^ 2 :=
      add_le_add le_rfl hprod
    _ = _ := by unfold physicalStepConstant; ring

end StructuralNote.StrongPointwiseSteps

import Erdos1045.MatrixDirectTransfer

/-! The coarse and fine asymptotic uses of direct Gram perturbation.
The matrix size may vary along the sequence. -/

namespace Erdos1045.MatrixDefect

open Filter
open scoped Topology
open MatrixStability
noncomputable section

variable {N : ℕ → ℕ} (A V : (j : ℕ) → Mat (N j))

theorem direct_eventually_transfer
    (hA : ∀ᶠ j in atTop, (A j).det ≠ 0)
    {C : ℝ} (hC : ∀ᶠ j in atTop, defect (A j) ≤ C)
    (hE : Tendsto (fun j => frobSq (A j - V j)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, (V j).det ≠ 0 ∧ 0 ≤ defect (V j) ∧
      defect (V j) ≤ directStabilityConstant C * (defect (A j) + frobSq (A j - V j)) := by
  have hs := (tendsto_order.1 hE).2 (lowerScale C) (lowerScale_pos C)
  have ho := (tendsto_order.1 hE).2 1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hA, hC, hs, ho] with j hjA hjC hjs hjo
  exact direct_transfer (A j) (V j) hjA hjC hjs.le hjo.le

theorem direct_eventually_bounded_defect
    (hA : ∀ᶠ j in atTop, (A j).det ≠ 0)
    {C : ℝ} (hCnonneg : 0 ≤ C) (hC : ∀ᶠ j in atTop, defect (A j) ≤ C)
    (hE : Tendsto (fun j => frobSq (A j - V j)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, (V j).det ≠ 0 ∧
      0 ≤ defect (V j) ∧ defect (V j) ≤ directStabilityConstant C * (C + 1) := by
  have ht := direct_eventually_transfer A V hA hC hE
  have ho := (tendsto_order.1 hE).2 1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [ht, hC, ho] with j hj hjC hjo
  refine ⟨hj.1, hj.2.1, hj.2.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (add_le_add hjC hjo.le)
    (directStabilityConstant_nonneg hCnonneg)

theorem direct_tendsto_defect_and_eventually_nonsingular
    (hA : ∀ᶠ j in atTop, (A j).det ≠ 0)
    (hD : Tendsto (fun j => defect (A j)) atTop (𝓝 0))
    (hE : Tendsto (fun j => frobSq (A j - V j)) atTop (𝓝 0)) :
    (∀ᶠ j in atTop, (V j).det ≠ 0) ∧
      Tendsto (fun j => defect (V j)) atTop (𝓝 0) := by
  have hC : ∀ᶠ j in atTop, defect (A j) ≤ 1 :=
    ((tendsto_order.1 hD).2 1 (by norm_num)).mono fun _ hj => hj.le
  have ht := direct_eventually_transfer A V hA hC hE
  have hbound : Tendsto
      (fun j => directStabilityConstant 1 * (defect (A j) + frobSq (A j - V j)))
      atTop (𝓝 0) := by
    convert (hD.add hE).const_mul (directStabilityConstant 1) using 1
    simp
  exact ⟨ht.mono (fun _ hj => hj.1),
    squeeze_zero' (ht.mono fun _ hj => hj.2.1) (ht.mono fun _ hj => hj.2.2) hbound⟩

theorem direct_tendsto_normalized_energy
    (hA : ∀ᶠ j in atTop, (A j).det ≠ 0)
    (hD : Tendsto (fun j => defect (A j)) atTop (𝓝 0))
    (hE : Tendsto (fun j => frobSq (A j - V j)) atTop (𝓝 0))
    (htrace : ∀ᶠ j in atTop, frobSq (V j) = N j) :
    Tendsto (fun j => -Real.log (detSq (V j))) atTop (𝓝 0) := by
  have hd := (direct_tendsto_defect_and_eventually_nonsingular A V hA hD hE).2
  apply hd.congr'
  filter_upwards [htrace] with j hj
  exact defect_eq_neg_log_detSq (V j) hj

end
end Erdos1045.MatrixDefect

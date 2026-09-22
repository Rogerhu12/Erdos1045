import StructuralNote.FixedDualClassificationKernelUniformBounds
import StructuralNote.FixedDualClassificationKernelUniformSeries
import Mathlib.Analysis.PSeries

/-! Divergence at the first grid spacing, the qualitative endpoint needed for one-pass compression. -/

namespace StructuralNote.FixedDualClassificationKernelUniformDivergence

open Real Finset Filter Erdos1045.EventualExact
open FixedDualClassificationKernel FixedDualClassificationKernelUniformBounds
open FixedDualClassificationKernelUniformSeries FixedDualClassificationMultiplierLimit
open FixedDualClassificationOddSpectrum
open scoped Topology BigOperators
noncomputable section

def firstGridHead (m P : ℕ) : ℝ :=
  ∑ k ∈ range P, SchurWeights.weight (2 * m) (2 * k + 1) *
    cos ((2 * k + 1 : ℕ) * (Real.pi / m))

def coefficientMass (P : ℕ) : ℝ := ∑ k ∈ range P, 2 * kernelCoefficient (k : ℤ)

theorem firstGridHead_le {m P : ℕ} (hm : 4 ≤ m) (hP : P ≤ m / 4) :
    firstGridHead m P - 2 ≤ finiteKernel (2 * m) (Real.pi / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsum : firstGridHead m P ≤ firstGridHead m (m / 4) := by
    apply sum_le_sum_of_subset_of_nonneg (range_mono hP)
    intro k hk _
    apply mul_nonneg (SchurWeights.weight_nonneg _ _)
    apply cos_nonneg_of_mem_Icc
    constructor
    · linarith [show 0 ≤ ((2 * k + 1 : ℕ) : ℝ) * (Real.pi / m) by positivity, pi_pos]
    · have hkR : (2 * k + 1 : ℕ) ≤ m / 2 := by have := mem_range.mp hk; omega
      have hkr : 2 * ((2 * k + 1 : ℕ) : ℝ) ≤ m := by
        exact_mod_cast (show 2 * (2 * k + 1) ≤ m by omega)
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      have ht : ((2 * k + 1 : ℕ) : ℝ) * (Real.pi / m) * 2 ≤ Real.pi := by
        rw [show ((2 * k + 1 : ℕ) : ℝ) * (Real.pi / m) * 2 =
          (2 * ((2 * k + 1 : ℕ) : ℝ) * Real.pi) / m by ring]
        apply (div_le_iff₀ hm0).mpr
        nlinarith [mul_le_mul_of_nonneg_right hkr pi_pos.le]
      exact ht
  have h := (abs_le.mp (first_grid_tail_bound hm)).1
  change -(2 : ℝ) ≤ finiteKernel (2 * m) (Real.pi / m) - firstGridHead m (m / 4) at h
  linarith

theorem firstGridHead_tendsto (P : ℕ) :
    Tendsto (fun m => firstGridHead m P) atTop (𝓝 (coefficientMass P)) := by
  have hm : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    exact eventually_atTop.mpr ⟨N, fun m hm => by omega⟩
  have ht := tendsto_const_div_atTop_nhds_zero_nat Real.pi
  apply tendsto_finsetSum
  intro k _
  have hc := continuous_cos.continuousAt.tendsto.comp (ht.const_mul ((2 * k + 1 : ℕ) : ℝ))
  simpa only [Function.comp_def, mul_zero, cos_zero, mul_one] using
    ((positive_multiplier_tendsto k).comp hm).mul hc

theorem coefficientMass_eq {P : ℕ} (hP : 0 < P) :
    coefficientMass P = (1 / 2 : ℝ) * (∑ k ∈ range P, 1 / ((k : ℝ) + 1)) - 1 / 2 := by
  have hterm (k : ℕ) : 2 * kernelCoefficient (k : ℤ) =
      (1 / 2 : ℝ) * (1 / ((k : ℝ) + 1)) - if k = 0 then 1 / 2 else 0 := by
    by_cases hk : k = 0
    · subst k
      norm_num [kernelCoefficient, naturalKernelCoefficient]
    · rw [coefficient_pos_formula (Nat.pos_of_ne_zero hk), if_neg hk, sub_zero]
      field_simp
  unfold coefficientMass
  simp_rw [hterm]
  rw [sum_sub_distrib, ← mul_sum]
  simp only [sum_ite_eq', mem_range, hP, if_true]

theorem coefficientMass_unbounded (M : ℝ) : ∃ P : ℕ, M < coefficientMass P := by
  obtain ⟨P, hP, hsum⟩ := ((eventually_gt_atTop 0).and
    (tendsto_sum_range_one_div_nat_succ_atTop.eventually (eventually_gt_atTop (2 * M + 1)))).exists
  refine ⟨P, ?_⟩
  rw [coefficientMass_eq hP]
  linarith

theorem first_grid_tendsto_atTop :
    Tendsto (fun m : ℕ => finiteKernel (2 * m) (Real.pi / m)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  obtain ⟨P, hP⟩ := coefficientMass_unbounded (M + 3)
  have hh := (firstGridHead_tendsto P).eventually (lt_mem_nhds hP)
  filter_upwards [hh, eventually_ge_atTop (max 4 (4 * P))] with m hm hlarge
  have h := firstGridHead_le (m := m) (P := P) (by omega) (by omega)
  linarith

end
end StructuralNote.FixedDualClassificationKernelUniformDivergence

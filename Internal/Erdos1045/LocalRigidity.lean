import Erdos1045.LocalNormalization
import Erdos1045.Configuration

/-!
# Local rigidity without preassigned Fourier normalization

An actual edge perturbation of relative size at most 1/4000 is normalized
explicitly. The geometric objective is invariant under this normalization.
Consequently every nonregular configuration in that neighborhood has strictly
smaller objective than the regular polygon. No vanishing-mode assumption is
part of this final theorem.
-/

namespace Erdos1045.LocalRigidity

open Complex
open scoped BigOperators
noncomputable section

theorem perimeter_affine (n : ℕ) (z : ℕ → ℂ) (a b : ℂ) :
    LocalObjective.perimeter n (fun j => a + b * z j) =
      ‖b‖ * LocalObjective.perimeter n z := by
  unfold LocalObjective.perimeter
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show a + b * z (j + 1) - (a + b * z j) = b * (z (j + 1) - z j) by ring,
    norm_mul]

theorem logDistanceProduct_affine {n : ℕ} (hn : 0 < n) (z : ℕ → ℂ) (a b : ℂ)
    (hb : b ≠ 0)
    (hz : ∀ h ∈ (Finset.range n).erase 0, ∀ j, z (j + h) - z j ≠ 0) :
    LocalObjective.logDistanceProduct n (fun j => a + b * z j) =
      (n : ℝ) * ((n : ℝ) - 1) * Real.log ‖b‖ + LocalObjective.logDistanceProduct n z := by
  have ht (h : ℕ) (hh : h ∈ (Finset.range n).erase 0) (j : ℕ) :
      Real.log ‖a + b * z (j + h) - (a + b * z j)‖ =
        Real.log ‖b‖ + Real.log ‖z (j + h) - z j‖ := by
    rw [show a + b * z (j + h) - (a + b * z j) = b * (z (j + h) - z j) by ring,
      norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hb) (norm_ne_zero_iff.mpr (hz h hh j))]
  unfold LocalObjective.logDistanceProduct
  have he : (∑ h ∈ (Finset.range n).erase 0,
      ∑ j ∈ Finset.range n, Real.log ‖a + b * z (j + h) - (a + b * z j)‖) =
      ∑ h ∈ (Finset.range n).erase 0,
        ∑ j ∈ Finset.range n, (Real.log ‖b‖ + Real.log ‖z (j + h) - z j‖) := by
    apply Finset.sum_congr rfl
    intro h hh
    exact Finset.sum_congr rfl (fun j _ => ht h hh j)
  rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hn), Finset.card_range]
  have hn1 : 1 ≤ n := by omega
  push_cast [Nat.cast_sub hn1]
  ring

theorem objective_affine {n : ℕ} (hn : 0 < n) (z : ℕ → ℂ) (a b : ℂ) (hb : b ≠ 0)
    (hz : ∀ h ∈ (Finset.range n).erase 0, ∀ j, z (j + h) - z j ≠ 0)
    (hL : 0 < LocalObjective.perimeter n z) :
    LocalObjective.objective n (fun j => a + b * z j) = LocalObjective.objective n z := by
  unfold LocalObjective.objective
  rw [logDistanceProduct_affine hn z a b hb hz, perimeter_affine,
    Real.log_mul (norm_ne_zero_iff.mpr hb) hL.ne']
  ring

theorem small_perturbation_distinct (HS : LocalPhase.ClassicalGeometricSine)
    {n : ℕ} (hn : 4 ≤ n) (u : ℕ → ℂ) (hu : Function.Periodic u n) {η : ℝ}
    (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖)
    (h : ℕ) (hh : h ∈ (Finset.range n).erase 0) (j : ℕ) :
    LocalObjective.perturbedVertices n u (j + h) - LocalObjective.perturbedVertices n u j ≠ 0 := by
  have hm := Finset.mem_erase.mp hh
  have hd := LocalDFT.vertex_difference_ne_zero (by omega : 0 < n)
    (by omega : 0 < h) (Finset.mem_range.mp hm.2) j
  have hr := LocalMaximum.pair_ratio_bound HS hn u hu hη hstep hh j
  have hp := LocalObjective.norm_one_add_pos_of_half
    (by linarith : ‖LocalDFT.pairRatio n u j h‖ ≤ 1 / 2)
  rw [LocalObjective.difference_factor (by omega) (by omega) (Finset.mem_range.mp hm.2)]
  exact mul_ne_zero hd (norm_pos_iff.mp hp)

theorem small_perturbation_perimeter_pos {n : ℕ} (hn : 4 ≤ n) (u : ℕ → ℂ) {η : ℝ}
    (hsmall : η ≤ 1 / 4)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖) :
    0 < LocalObjective.perimeter n (LocalObjective.perturbedVertices n u) := by
  have hp := LocalNonlinear.norm_one_add_pos hsmall (LocalMaximum.edge_ratio_bound hn u hstep 0)
  have hd := LocalDFT.vertex_difference_ne_zero (by omega : 0 < n)
    (by omega : 0 < 1) (by omega : 1 < n) 0
  have ht : 0 < ‖LocalObjective.perturbedVertices n u (0 + 1) -
      LocalObjective.perturbedVertices n u 0‖ := by
    rw [LocalObjective.difference_factor (by omega) (by omega) (by omega), norm_mul]
    exact mul_pos (norm_pos_iff.mpr hd) hp
  exact ht.trans_le (Finset.single_le_sum (fun j _ => norm_nonneg
    (LocalObjective.perturbedVertices n u (j + 1) - LocalObjective.perturbedVertices n u j))
    (Finset.mem_range.mpr (show 0 < n by omega)))

theorem root_power_eq_regular (n : ℕ) (j : Fin n) :
    LocalPhase.regularRoot n ^ (j : ℕ) = Configuration.regular n j := by
  unfold LocalPhase.regularRoot Configuration.regular
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem normalized_zero_implies_regular {n : ℕ} (u : ℕ → ℂ)
    (hd : 1 + LocalNormalization.first n u ≠ 0)
    (hz : ∀ j, LocalNormalization.normalized n u j = 0) :
    Configuration.IsRegular (fun j : Fin n => LocalObjective.perturbedVertices n u j) := by
  refine ⟨LocalNormalization.mean n u, 1 + LocalNormalization.first n u, hd, Equiv.refl _, ?_⟩
  intro j
  dsimp only
  rw [LocalNormalization.normalized_affine u hd]
  simp only [LocalObjective.perturbedVertices, hz, add_zero, LocalObjective.regularVertices,
    root_power_eq_regular, Equiv.refl_apply]

/-- The actual geometric local theorem, with normalization constructed internally.
The nonregularity condition is the permutation-invariant predicate used by the
global configuration development. -/
theorem strict_local_rigidity (HI : LocalDFT.ClassicalDFTInversion)
    (HS : LocalPhase.ClassicalGeometricSine) (HT : LocalNonlinear.ScalarLogTaylor)
    {n : ℕ} (hn : 4 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (u : ℕ → ℂ) (hu : Function.Periodic u n) {η : ℝ}
    (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4000)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖)
    (hnonreg : ¬ Configuration.IsRegular
      (fun j : Fin n => LocalObjective.perturbedVertices n u j)) :
    LocalObjective.objective n (LocalObjective.perturbedVertices n u) <
      LocalObjective.objective n (LocalObjective.regularVertices n) := by
  let v := LocalNormalization.normalized n u
  have hf := LocalNormalization.first_norm_bound HI hn HF u hu hstep
  have hd := LocalNormalization.denominator_ne_zero hf (by linarith : η < 1)
  have hvper : Function.Periodic v n := LocalNormalization.normalized_periodic (by omega) u hu
  obtain ⟨hε, hεsmall⟩ := LocalNormalization.small_normalized_bound hη hsmall
  have hvstep := LocalNormalization.normalized_step u hη (by linarith : η < 1) hf hstep
  have hvne : ∃ j, v j ≠ 0 := by
    by_contra! hz
    exact hnonreg (normalized_zero_implies_regular u hd hz)
  have hvmax := LocalObjective.strict_local_objective_maximum HI HS HT hn HF v hvper
    (LocalNormalization.normalized_mean_zero (by omega) HF u)
    (LocalNormalization.normalized_similarity_zero (by omega) HF u)
    hε hεsmall hvstep hvne
  have hz := small_perturbation_distinct HS hn v hvper hε (by linarith) hvstep
  have hL := small_perturbation_perimeter_pos hn v (by linarith) hvstep
  have ha := objective_affine (by omega : 0 < n) (LocalObjective.perturbedVertices n v)
    (LocalNormalization.mean n u) (1 + LocalNormalization.first n u) hd hz hL
  have he : (fun j => LocalNormalization.mean n u + (1 + LocalNormalization.first n u) *
      LocalObjective.perturbedVertices n v j) = LocalObjective.perturbedVertices n u := by
    funext j
    exact (LocalNormalization.normalized_affine u hd j).symm
  rw [he] at ha
  exact ha.trans_lt hvmax

end
end Erdos1045.LocalRigidity

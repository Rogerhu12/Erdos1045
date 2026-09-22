import Erdos1045.LocalRigidity
import Erdos1045.CircleGapQuantitative

/-! The finite configuration and periodic-offset definitions of the objective
agree. This is a reindexing proof, not an additional analytic hypothesis. -/

namespace Erdos1045.LocalConfiguration

open Complex
open scoped BigOperators
noncomputable section

theorem logDistanceProduct_eq_sum {n : ℕ} (z : ℕ → ℂ) (hz : Function.Periodic z n) :
    LocalObjective.logDistanceProduct n z =
      ∑ i : Fin n, ∑ j : Fin n, Real.log ‖z i - z j‖ := by
  unfold LocalObjective.logDistanceProduct
  rw [Finset.sum_erase _ (by simp)]
  rw [Finset.sum_comm]
  have hshift (j : ℕ) :
      (∑ h ∈ Finset.range n, Real.log ‖z (j + h) - z j‖) =
      ∑ i ∈ Finset.range n, Real.log ‖z i - z j‖ := by
    have hs := CyclicAngles.sum_shift_of_drift (n := n)
      (fun i => Real.log ‖z i - z j‖) 0 (fun i => by rw [hz i]; simp) j
    simpa [Nat.add_comm] using hs
  simp_rw [hshift]
  rw [Finset.sum_comm]
  have hf (f : ℕ → ℝ) : (∑ i ∈ Finset.range n, f i) = ∑ i : Fin n, f i :=
    Finset.sum_range f
  rw [hf]
  apply Finset.sum_congr rfl
  intro i hi
  exact hf _

theorem logDiscriminant_eq_sum {n : ℕ} (z : Configuration.Points n)
    (hz : Function.Injective z) :
    Real.log (Configuration.discriminant z) = ∑ i, ∑ j, Real.log ‖z i - z j‖ := by
  have hn (i j : Fin n) (hj : j ∈ Finset.univ.erase i) : ‖z i - z j‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    exact sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hj) (hz h).symm)
  unfold Configuration.discriminant
  rw [Real.log_prod (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j hj => hn i j hj))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.log_prod (fun j hj => hn i j hj), Finset.sum_erase _ (by simp)]

theorem perimeter_eq_boundaryLength {n : ℕ} (hn : 2 ≤ n) (z : ℕ → ℂ)
    (hz : Function.Periodic z n) :
    LocalObjective.perimeter n z = Configuration.boundaryLength (fun j : Fin n => z j) := by
  let : NeZero n := ⟨by omega⟩
  unfold LocalObjective.perimeter Configuration.boundaryLength
  rw [Finset.sum_range (fun j => ‖z (j + 1) - z j‖)]
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  dsimp only
  rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]
  exact CyclicAngles.periodic_mod z hz (i.val + 1)

theorem objective_eq {n : ℕ} (hn : 2 ≤ n) (z : ℕ → ℂ) (hz : Function.Periodic z n)
    (hinj : Function.Injective (fun j : Fin n => z j)) :
    LocalObjective.objective n z = Configuration.objective (fun j : Fin n => z j) := by
  unfold LocalObjective.objective Configuration.objective
  rw [logDistanceProduct_eq_sum z hz, logDiscriminant_eq_sum _ hinj,
    perimeter_eq_boundaryLength hn z hz]
  simp only [Configuration.exponent, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]

theorem periodic_of_perturbed {n : ℕ} (hn : 0 < n) (u : ℕ → ℂ)
    (hu : Function.Periodic u n) :
    Function.Periodic (LocalObjective.perturbedVertices n u) n := by
  intro j
  simp [LocalObjective.perturbedVertices, LocalObjective.regularVertices,
    pow_add, LocalDFT.regularRoot_pow hn, hu j]

theorem small_perturbation_injective (HS : LocalPhase.ClassicalGeometricSine)
    {n : ℕ} (hn : 4 ≤ n) (u : ℕ → ℂ) (hu : Function.Periodic u n) {η : ℝ}
    (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖) :
    Function.Injective (fun j : Fin n => LocalObjective.perturbedVertices n u j) := by
  have hlt (i j : Fin n) (hij : i.val < j.val) :
      LocalObjective.perturbedVertices n u i ≠ LocalObjective.perturbedVertices n u j := by
    have hh : j.val - i.val ∈ (Finset.range n).erase 0 := by
      simp only [Finset.mem_erase, Finset.mem_range]
      omega
    have h := LocalRigidity.small_perturbation_distinct HS hn u hu hη hsmall hstep
      (j.val - i.val) hh i.val
    rw [Nat.add_sub_of_le (Nat.le_of_lt hij)] at h
    exact (sub_ne_zero.mp h).symm
  intro i j hij
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact False.elim (hlt i j h hij)
  · exact Fin.ext h
  · exact False.elim (hlt j i h hij.symm)

theorem regular_injective {n : ℕ} (hn : 4 ≤ n)
    (HS : LocalPhase.ClassicalGeometricSine) :
    Function.Injective (Configuration.regular n) := by
  have h := small_perturbation_injective HS hn (fun _ => 0) (fun _ => by simp)
    (η := 0) (by norm_num) (by norm_num) (fun _ => by simp)
  simpa [LocalObjective.perturbedVertices, LocalObjective.regularVertices,
    LocalRigidity.root_power_eq_regular] using h

theorem strict_local_rigidity (HI : LocalDFT.ClassicalDFTInversion)
    (HS : LocalPhase.ClassicalGeometricSine) (HT : LocalNonlinear.ScalarLogTaylor)
    {n : ℕ} (hn : 4 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (u : ℕ → ℂ) (hu : Function.Periodic u n) {η : ℝ}
    (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4000)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖)
    (hnonreg : ¬ Configuration.IsRegular
      (fun j : Fin n => LocalObjective.perturbedVertices n u j)) :
    Configuration.objective (fun j : Fin n => LocalObjective.perturbedVertices n u j) <
      Configuration.objective (Configuration.regular n) := by
  have h := LocalRigidity.strict_local_rigidity HI HS HT hn HF u hu hη hsmall hstep hnonreg
  rw [objective_eq (by omega) _ (periodic_of_perturbed (by omega) u hu)
    (small_perturbation_injective HS hn u hu hη (by linarith) hstep)] at h
  have hp : Function.Periodic (LocalObjective.regularVertices n) n := by
    intro j
    simp [LocalObjective.regularVertices, pow_add, LocalDFT.regularRoot_pow (by omega : 0 < n)]
  have he : (fun j : Fin n => LocalObjective.regularVertices n j) = Configuration.regular n := by
    funext j
    exact LocalRigidity.root_power_eq_regular n j
  rw [objective_eq (by omega) _ hp (by rw [he]; exact regular_injective hn HS), he] at h
  exact h

end
end Erdos1045.LocalConfiguration

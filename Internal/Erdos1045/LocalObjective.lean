import Erdos1045.LocalMaximum

/-!
# The local theorem for the geometric logarithmic objective

The objective uses actual vertex distances and the actual perimeter. Ordered
pair logarithms equal the logarithm of the squared unordered distance product.
The equality with the ratio gain is proved, so the local maximum theorem below
does not concern an unrelated auxiliary functional.
-/

namespace Erdos1045.LocalObjective

open Complex
open scoped BigOperators
noncomputable section

def regularVertices (n : ℕ) (j : ℕ) : ℂ := LocalPhase.regularRoot n ^ j

def perturbedVertices (n : ℕ) (u : ℕ → ℂ) (j : ℕ) : ℂ := regularVertices n j + u j

def perimeter (n : ℕ) (z : ℕ → ℂ) : ℝ :=
  ∑ j ∈ Finset.range n, ‖z (j + 1) - z j‖

def logDistanceProduct (n : ℕ) (z : ℕ → ℂ) : ℝ :=
  ∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n, Real.log ‖z (j + h) - z j‖

def objective (n : ℕ) (z : ℕ → ℂ) : ℝ :=
  logDistanceProduct n z - (n : ℝ) * ((n : ℝ) - 1) * Real.log (perimeter n z)

theorem difference_factor {n h : ℕ} (hn : 0 < n) (hh : 0 < h) (hhn : h < n)
    (u : ℕ → ℂ) (j : ℕ) :
    perturbedVertices n u (j + h) - perturbedVertices n u j =
      (regularVertices n (j + h) - regularVertices n j) * (1 + LocalDFT.pairRatio n u j h) := by
  have hden := LocalDFT.vertex_difference_ne_zero hn hh hhn j
  unfold perturbedVertices regularVertices LocalDFT.pairRatio
  field_simp
  ring

theorem norm_one_add_pos_of_half {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : 0 < ‖1 + z‖ := by
  have h := norm_sub_le (1 + z) z
  norm_num at h
  linarith

theorem perimeter_regular (n : ℕ) :
    perimeter n (regularVertices n) = (n : ℝ) * ‖LocalPhase.regularRoot n - 1‖ := by
  simp [perimeter, regularVertices, LocalMaximum.edge_denominator_norm]

theorem perimeter_perturbed {n : ℕ} (hn : 4 ≤ n) (u : ℕ → ℂ) :
    perimeter n (perturbedVertices n u) =
      ‖LocalPhase.regularRoot n - 1‖ *
        ∑ j ∈ Finset.range n, ‖1 + LocalDFT.pairRatio n u j 1‖ := by
  unfold perimeter
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [difference_factor (by omega) (by omega) (by omega), norm_mul]
  rw [show ‖regularVertices n (j + 1) - regularVertices n j‖ =
      ‖LocalPhase.regularRoot n - 1‖ from LocalMaximum.edge_denominator_norm n j]

theorem perimeter_log_difference {n : ℕ} (hn : 4 ≤ n) (u : ℕ → ℂ) {η : ℝ}
    (hsmall : η ≤ 1 / 4)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖) :
    Real.log (perimeter n (perturbedVertices n u)) - Real.log (perimeter n (regularVertices n)) =
      Real.log ((∑ j ∈ Finset.range n, ‖1 + LocalDFT.pairRatio n u j 1‖) / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hroot : LocalPhase.regularRoot n ≠ 1 := by
    simpa using LocalDFT.regularRoot_power_ne_one (by omega : 0 < n)
      (by omega : 0 < 1) (by omega : 1 < n)
  have hd : 0 < ‖LocalPhase.regularRoot n - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hroot)
  have hzero : 0 < ‖1 + LocalDFT.pairRatio n u 0 1‖ :=
    LocalNonlinear.norm_one_add_pos hsmall (LocalMaximum.edge_ratio_bound hn u hstep 0)
  have hsingle : ‖1 + LocalDFT.pairRatio n u 0 1‖ ≤
      ∑ j ∈ Finset.range n, ‖1 + LocalDFT.pairRatio n u j 1‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg (1 + LocalDFT.pairRatio n u j 1))
      (Finset.mem_range.mpr (show 0 < n by omega))
  have hS : 0 < ∑ j ∈ Finset.range n, ‖1 + LocalDFT.pairRatio n u j 1‖ := hzero.trans_le hsingle
  rw [perimeter_perturbed hn u, perimeter_regular, Real.log_mul hd.ne' hS.ne',
    Real.log_mul hnR.ne' hd.ne', Real.log_div hS.ne' hnR.ne']
  ring

theorem pair_log_difference (HS : LocalPhase.ClassicalGeometricSine) {n : ℕ}
    (hn : 4 ≤ n) (u : ℕ → ℂ) (hu : Function.Periodic u n) {η : ℝ}
    (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖) :
    logDistanceProduct n (perturbedVertices n u) - logDistanceProduct n (regularVertices n) =
      (∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n,
        2 * Real.log ‖1 + LocalDFT.pairRatio n u j h‖) / 2 := by
  have hterm (h : ℕ) (hh : h ∈ (Finset.range n).erase 0) (j : ℕ) :
      Real.log ‖perturbedVertices n u (j + h) - perturbedVertices n u j‖ =
        Real.log ‖regularVertices n (j + h) - regularVertices n j‖ +
          Real.log ‖1 + LocalDFT.pairRatio n u j h‖ := by
    have hm := Finset.mem_erase.mp hh
    have hden := LocalDFT.vertex_difference_ne_zero (by omega : 0 < n)
      (by omega : 0 < h) (Finset.mem_range.mp hm.2) j
    have hp := LocalMaximum.pair_ratio_bound HS hn u hu hη hstep hh j
    have hpos := norm_one_add_pos_of_half (by linarith : ‖LocalDFT.pairRatio n u j h‖ ≤ 1 / 2)
    rw [difference_factor (by omega) (by omega) (Finset.mem_range.mp hm.2), norm_mul]
    exact Real.log_mul (norm_ne_zero_iff.mpr hden) hpos.ne'
  have hs : logDistanceProduct n (perturbedVertices n u) =
      logDistanceProduct n (regularVertices n) +
        ∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n,
          Real.log ‖1 + LocalDFT.pairRatio n u j h‖ := by
    unfold logDistanceProduct
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h hh
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact hterm h hh j
  rw [hs]
  simp only [← Finset.mul_sum]
  ring

theorem objective_difference_eq_gain (HS : LocalPhase.ClassicalGeometricSine) {n : ℕ}
    (hn : 4 ≤ n) (u : ℕ → ℂ) (hu : Function.Periodic u n) {η : ℝ}
    (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖) :
    objective n (perturbedVertices n u) - objective n (regularVertices n) =
      LocalMaximum.gain n u := by
  have hp := pair_log_difference HS hn u hu hη hsmall hstep
  have hl := perimeter_log_difference hn u hsmall hstep
  unfold objective LocalMaximum.gain
  linear_combination hp - (n : ℝ) * ((n : ℝ) - 1) * hl

/-- The quantitative geometric local maximum theorem. Only universally stated
classical Fourier and scalar analytic facts appear as external inputs. -/
theorem local_objective_bound (HI : LocalDFT.ClassicalDFTInversion)
    (HS : LocalPhase.ClassicalGeometricSine) (HT : LocalNonlinear.ScalarLogTaylor)
    {n : ℕ} (hn : 4 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (u : ℕ → ℂ) (hu : Function.Periodic u n)
    (hmean : (∑ j ∈ Finset.range n, u j) = 0)
    (hsim : (∑ j ∈ Finset.range n, u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 1000)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖) :
    objective n (perturbedVertices n u) - objective n (regularVertices n) ≤
      -(LocalDFT.energyA n u + (n : ℝ) * LocalDFT.energyB n u) / 128 := by
  rw [objective_difference_eq_gain HS hn u hu hη (by linarith) hstep]
  exact LocalMaximum.local_maximum_bound HI HS HT hn HF u hu hmean hsim hη hsmall hstep

theorem strict_local_objective_maximum (HI : LocalDFT.ClassicalDFTInversion)
    (HS : LocalPhase.ClassicalGeometricSine) (HT : LocalNonlinear.ScalarLogTaylor)
    {n : ℕ} (hn : 4 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (u : ℕ → ℂ) (hu : Function.Periodic u n)
    (hmean : (∑ j ∈ Finset.range n, u j) = 0)
    (hsim : (∑ j ∈ Finset.range n, u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 1000)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖)
    (hne : ∃ j, u j ≠ 0) :
    objective n (perturbedVertices n u) < objective n (regularVertices n) := by
  have hg := LocalMaximum.strict_local_maximum HI HS HT hn HF u hu hmean hsim hη hsmall hstep hne
  rw [← objective_difference_eq_gain HS hn u hu hη (by linarith) hstep] at hg
  linarith

end

end Erdos1045.LocalObjective

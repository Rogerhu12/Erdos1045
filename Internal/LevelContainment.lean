import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Level-set containment from distance to the frontier

This is the topological step needed before applying a Cauchy estimate.
It uses no Jordan curve theorem or boundary parametrization. Once an
exterior level set's frontier has been identified, a distance estimate
puts the required disk inside that set.
-/

namespace ExteriorReduction

open Set Metric

theorem ball_subset_of_frontier_distance {K : Set ℂ} {x : ℂ} {r : ℝ}
    (hx : x ∈ K) (hfrontier : ∀ z ∈ frontier K, r ≤ dist x z) :
    ball x r ⊆ K := by
  by_cases hK : K = univ
  · simp [hK]
  obtain ⟨z, hz, heq⟩ := exists_mem_frontier_infDist_compl_eq_dist hx hK
  intro y hy
  by_contra hyK
  have hdist : dist x y < r := by simpa only [mem_ball, dist_comm] using hy
  have hinf := infDist_le_dist_of_mem (x := x) (show y ∈ Kᶜ from hyK)
  rw [heq] at hinf
  exact (hdist.trans_le (hfrontier z hz)).not_ge hinf

theorem disks_subset_of_frontier_separation {K L : Set ℂ} {r : ℝ}
    (hKL : K ⊆ L) (hsep : ∀ x ∈ K, ∀ z ∈ frontier L, r ≤ ‖z - x‖) :
    ∀ x ∈ K, ball x r ⊆ L := by
  intro x hx
  apply ball_subset_of_frontier_distance (hKL hx)
  intro z hz
  simpa only [dist_eq_norm, norm_sub_rev] using hsep x hx z hz

#print axioms ball_subset_of_frontier_distance

end ExteriorReduction

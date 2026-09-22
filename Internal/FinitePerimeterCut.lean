import FinitePerimeterNormalCones
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! A nontrivial finite configuration has a support-transition direction.
Rotating that direction to the argument cut makes every strict angular cell
an interval. The cut is constructed using connectedness of the unit circle. -/

namespace ExteriorReduction.Reinhardt

open Complex Set Metric
open Erdos1045.Configuration Erdos1045.HullGeometry
open scoped ComplexConjugate

noncomputable section

theorem other_point_of_nontrivial {n : ℕ} (z : Points n)
    (hne : ∃ i j, z i ≠ z j) (k : Fin n) : ∃ j, z j ≠ z k := by
  obtain ⟨i, j, hij⟩ := hne
  by_contra! hall
  exact hij ((hall i).trans (hall j).symm)

theorem strictNormalCone_eq_of_point_eq {n : ℕ} (z : Points n) {i j : Fin n}
    (hij : z i = z j) : strictNormalCone z i = strictNormalCone z j := by
  simp only [strictNormalCone, hij]

/-- The unit circle cannot be partitioned into disjoint open strict normal
cones: a transition direction necessarily exists. -/
theorem exists_normal_cut {n : ℕ} (z : Points n) (hne : ∃ i j, z i ≠ z j) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ i, u ∉ strictNormalCone z i := by
  by_contra! hcover
  obtain ⟨i, hi⟩ := hcover 1 (by simp)
  let V : Set ℂ := ⋃ j : Fin n, ⋃ (_h : z j ≠ z i), strictNormalCone z j
  have hV : IsOpen V := isOpen_iUnion fun j => isOpen_iUnion fun _ => strictNormalCone_isOpen z j
  have hdis : Disjoint (strictNormalCone z i) V := by
    rw [Set.disjoint_left]
    intro u hu hv
    obtain ⟨j, hv⟩ := mem_iUnion.mp hv
    obtain ⟨hj, hv⟩ := mem_iUnion.mp hv
    exact Set.disjoint_left.mp (strictNormalCone_disjoint z hj.symm) hu hv
  have hsub : sphere (0 : ℂ) 1 ⊆ strictNormalCone z i ∪ V := by
    intro u hu
    obtain ⟨j, hj⟩ := hcover u (mem_sphere_zero_iff_norm.mp hu)
    by_cases he : z j = z i
    · left
      rwa [strictNormalCone_eq_of_point_eq z he] at hj
    · right
      exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨he, hj⟩⟩
  have hone : (sphere (0 : ℂ) 1 ∩ strictNormalCone z i).Nonempty := ⟨1, by simp, hi⟩
  have hall : sphere (0 : ℂ) 1 ⊆ strictNormalCone z i :=
    IsPreconnected.subset_left_of_subset_union (strictNormalCone_isOpen z i) hV hdis hsub hone
      (isPreconnected_sphere (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num) 0 1)
  have hneg := hall (show (-1 : ℂ) ∈ sphere 0 1 by simp)
  obtain ⟨j, hj⟩ := other_point_of_nontrivial z hne i
  have hp := hi j hj
  have hn := hneg j hj
  simp only [map_one, mul_one, map_neg, mul_neg, Complex.neg_re] at hp hn
  linarith

theorem strictNormalCone_rotate {n : ℕ} (z : Points n) (i : Fin n)
    {a : ℂ} (ha : a ≠ 0) (u : ℂ) :
    u ∈ strictNormalCone (fun j => a * z j) i ↔ conj a * u ∈ strictNormalCone z i := by
  have hne (j : Fin n) : a * z j ≠ a * z i ↔ z j ≠ z i := by
    exact not_congr (mul_right_inj' ha)
  have he (j : Fin n) :
      ((a * z i - a * z j) * conj u).re = ((z i - z j) * conj (conj a * u)).re := by
    simp only [map_mul, conj_conj]
    congr 1
    ring
  simp only [strictNormalCone, mem_ofPred_eq, hne, he]

/-- A unit rotation places an actual support transition on the negative real
ray. This is a change of coordinates, not a new geometric hypothesis. -/
theorem exists_rotation_normal_cut {n : ℕ} (z : Points n) (hne : ∃ i j, z i ≠ z j) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ i, (-1 : ℂ) ∉ strictNormalCone (fun j => a * z j) i := by
  obtain ⟨u, hu, hcut⟩ := exists_normal_cut z hne
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  refine ⟨-conj u, by simp [hu], ?_⟩
  intro i hi
  rw [strictNormalCone_rotate z i (neg_ne_zero.mpr ((map_ne_zero (starRingEnd ℂ)).2 hu0))] at hi
  exact hcut i (by simpa using hi)

#print axioms exists_normal_cut
#print axioms exists_rotation_normal_cut

end
end ExteriorReduction.Reinhardt

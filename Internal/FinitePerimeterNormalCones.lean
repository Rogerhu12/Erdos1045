import ReinhardtPartition
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.IntermediateValue

/-!
# Connected angular cells of a finite support function

Strict normal cones are open and convex. If the cut ray belongs to no strict
normal cone, the principal argument is continuous on each cone, and its image
is an interval. This is the geometric source of the linear bound on the number
of normal sectors; it does not postulate a perimeter inequality.
-/

namespace ExteriorReduction.Reinhardt

open Complex Set Metric
open Erdos1045.Configuration Erdos1045.HullGeometry
open scoped ComplexConjugate

noncomputable section

def strictNormalCone {n : ℕ} (z : Points n) (i : Fin n) : Set ℂ :=
  {u | ∀ j, z j ≠ z i → 0 < ((z i - z j) * conj u).re}

theorem strictNormalCone_convex {n : ℕ} (z : Points n) (i : Fin n) :
    Convex ℝ (strictNormalCone z i) := by
  intro u hu v hv a b ha hb hab j hj
  have hp := hu j hj
  have hq := hv j hj
  have he : ((z i - z j) * conj (a • u + b • v)).re =
      a * ((z i - z j) * conj u).re + b * ((z i - z j) * conj v).re := by
    simp [Complex.real_smul, mul_add, mul_comm, mul_left_comm]
  rw [he]
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb1 : b = 1 := by linarith
    simpa only [← ha0, hb1, zero_mul, zero_add, one_mul] using hq
  · exact add_pos_of_pos_of_nonneg (mul_pos ha0 hp) (mul_nonneg hb hq.le)

theorem strictNormalCone_isOpen {n : ℕ} (z : Points n) (i : Fin n) :
    IsOpen (strictNormalCone z i) := by
  have he : strictNormalCone z i = ⋂ j : Fin n,
      {u : ℂ | z j ≠ z i → 0 < ((z i - z j) * conj u).re} := by ext; simp [strictNormalCone]
  rw [he]
  apply isOpen_iInter_of_finite
  intro j
  by_cases hj : z j ≠ z i
  · have heq : {u : ℂ | z j ≠ z i → 0 < ((z i - z j) * conj u).re} =
        {u : ℂ | 0 < ((z i - z j) * conj u).re} := by
      ext u
      exact ⟨fun h => h hj, fun h _ => h⟩
    rw [heq]
    exact isOpen_lt continuous_const (by fun_prop)
  · simp [hj]

theorem strictNormalCone_smul_iff {n : ℕ} (z : Points n) (i : Fin n)
    {r : ℝ} (hr : 0 < r) (u : ℂ) :
    r • u ∈ strictNormalCone z i ↔ u ∈ strictNormalCone z i := by
  have he (j : Fin n) : ((z i - z j) * conj (r • u)).re =
      r * ((z i - z j) * conj u).re := by
    simp [Complex.real_smul, mul_comm, mul_left_comm]
  simp only [strictNormalCone, mem_ofPred_eq, he, mul_pos_iff_of_pos_left hr]

theorem zero_not_mem_strictNormalCone {n : ℕ} (z : Points n) (i : Fin n)
    (hne : ∃ j, z j ≠ z i) : (0 : ℂ) ∉ strictNormalCone z i := by
  intro h
  obtain ⟨j, hj⟩ := hne
  simpa using h j hj

theorem strictNormalCone_disjoint {n : ℕ} (z : Points n) {i j : Fin n}
    (hij : z i ≠ z j) : Disjoint (strictNormalCone z i) (strictNormalCone z j) := by
  rw [Set.disjoint_left]
  intro u hi hj
  have hp := hi j hij.symm
  have hq := hj i hij
  have he : ((z j - z i) * conj u).re = -((z i - z j) * conj u).re := by
    rw [← neg_sub (z i) (z j), neg_mul, Complex.neg_re]
  rw [he] at hq
  linarith

/-- A cut direction on a support transition ensures that every strict cone
avoids the negative real ray, so ordinary `arg` has no discontinuity there. -/
theorem strictNormalCone_subset_slitPlane {n : ℕ} (z : Points n) (i : Fin n)
    (hne : ∃ j, z j ≠ z i) (hcut : (-1 : ℂ) ∉ strictNormalCone z i) :
    strictNormalCone z i ⊆ Complex.slitPlane := by
  intro u hu
  by_contra hbad
  have hu0 : u ≠ 0 := by
    intro he
    exact zero_not_mem_strictNormalCone z i hne (he ▸ hu)
  have hparts : u.re ≤ 0 ∧ u.im = 0 := by
    simpa only [Complex.slitPlane, Set.mem_ofPred_eq, not_or, not_lt, not_not] using hbad
  have hre : u.re < 0 := by
    refine lt_of_le_of_ne hparts.1 ?_
    intro he
    exact hu0 (Complex.ext he hparts.2)
  have heq : (-u.re) • (-1 : ℂ) = u := by
    apply Complex.ext <;> simp [Complex.real_smul, hparts.2]
  apply hcut
  apply (strictNormalCone_smul_iff z i (neg_pos.mpr hre) (-1)).mp
  rwa [heq]

def strictNormalAngles {n : ℕ} (z : Points n) (i : Fin n) : Set ℝ :=
  Complex.arg '' strictNormalCone z i

/-- Each vertex has one connected angular cell after cutting at a support
transition. In particular it cannot disappear and reappear in the normal fan. -/
theorem strictNormalAngles_ordConnected {n : ℕ} (z : Points n) (i : Fin n)
    (hne : ∃ j, z j ≠ z i) (hcut : (-1 : ℂ) ∉ strictNormalCone z i) :
    OrdConnected (strictNormalAngles z i) := by
  apply IsPreconnected.ordConnected
  exact (strictNormalCone_convex z i).isPreconnected.image _
    (Complex.continuousOn_arg.mono (strictNormalCone_subset_slitPlane z i hne hcut))

theorem strictNormalAngles_subset {n : ℕ} (z : Points n) (i : Fin n)
    (hne : ∃ j, z j ≠ z i) (hcut : (-1 : ℂ) ∉ strictNormalCone z i) :
    strictNormalAngles z i ⊆ Ioo (-Real.pi) Real.pi := by
  rintro t ⟨u, hu, rfl⟩
  have hs := strictNormalCone_subset_slitPlane z i hne hcut hu
  exact ⟨Complex.neg_pi_lt_arg u,
    lt_of_le_of_ne (Complex.arg_le_pi u) (Complex.slitPlane_arg_ne_pi hs)⟩

#print axioms strictNormalAngles_ordConnected

end
end ExteriorReduction.Reinhardt

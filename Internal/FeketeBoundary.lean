import Erdos1045.ClosedInterpolation
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Every point of a nontrivial Fekete configuration lies on the boundary of
its convex hull. This uses the actual bounded Lagrange polynomial. -/

namespace ExteriorReduction

open Complex Metric Set Filter
open Erdos1045.Configuration Erdos1045.ExteriorClassical
open scoped Topology
noncomputable section

theorem fekete_points_mem_frontier {n : ℕ} (hn : 2 ≤ n) {z : Points n}
    (hz : Function.Injective z) (hf : Fekete z) (i : Fin n) :
    z i ∈ frontier (hull z) := by
  have hzi : z i ∈ hull z := subset_convexHull ℝ (range z) (mem_range_self i)
  rw [frontier, Set.mem_sdiff]
  refine ⟨subset_closure hzi, ?_⟩
  intro hi
  obtain ⟨p, _, hp, hb⟩ := fekete_interpolation_proved n hn z hz hf
  have hself : (p i).eval (z i) = 1 := by simpa using hp i i
  have hm : IsLocalMax (norm ∘ (p i).eval) (z i) := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hi] with x hx
    simpa [Function.comp_apply, hself] using hb i x hx
  have he := Complex.eventually_eq_of_isLocalMax_norm
    (Filter.Eventually.of_forall (fun x => (p i).differentiableAt (x := x))) hm
  have hpoly : p i = Polynomial.C 1 := (p i).eq_of_infinite_eval_eq (Polynomial.C 1) (by
    apply infinite_of_mem_nhds (z i)
    filter_upwards [he] with x hx
    simpa [hself] using hx)
  obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    exact exists_ne i
  have hjval := hp i j
  rw [hpoly, Polynomial.eval_C, if_neg (Ne.symm hj)] at hjval
  exact one_ne_zero hjval

#print axioms fekete_points_mem_frontier

end
end ExteriorReduction

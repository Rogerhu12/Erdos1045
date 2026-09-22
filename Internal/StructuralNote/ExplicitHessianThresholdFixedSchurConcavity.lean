import StructuralNote.ExplicitHessianThresholdFixedSchurGeometry
import StructuralNote.ExplicitFixedSchurHessianEstimate
import StructuralNote.ExplicitCanonicalEntryObjectivePaths
import StructuralNote.FixedSchurStrictConcavity

/-! Explicit strict concavity and the complete fixed-Schur fiber package. -/

namespace StructuralNote.ExplicitHessianThresholdFixedSchurConcavity

open Filter Set Complex
open Erdos1045 Erdos1045.EventualExact SchurSpectrum
open CommonDomainClosure CommonFiberCanonicalDirections CommonFiberCanonicalPaths
open CommonDomainSegments CommonDomainConvexity
open FixedSchurChosenLinearization FixedSchurChosenSecondBounds
open FixedSchurConfigurationDerivatives FixedSchurObjectivePaths
open FixedSchurEquationSmooth FixedSchurChart FixedSchurChartSmooth
open LogDiscriminantSecondDerivative
open ExplicitHessianThreshold ExplicitHessianThresholdFixedSchur
open ExplicitHessianThresholdFixedSchurGeometry
open ExplicitHessianThresholdDownstream
open ExplicitCanonicalEntryObjectivePaths ExplicitFixedSchurHessianEstimate
open scoped BigOperators Topology ContDiff

noncomputable section

theorem affine_strict_curvature {m : ℕ}
    (hN : orderThreshold ≤ 2 * m) (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega)) (x d : SchurParameters m) (t : ℝ)
    (hx : affinePath x d t ∈ FixedSchurChartSmooth.domain (by omega))
    (hd : Admissible (by omega) d) (hne : d ≠ 0) :
    deriv (deriv (fun r => objective (by omega) s (affinePath x d r))) t < 0 := by
  rw [ExplicitCanonicalEntryObjectivePaths.affine_deriv2_eq hN hm s x d t hx hd]
  have hb := (ExplicitFixedSchurHessianEstimate.actual_hessian_estimate hN hm s
    (affinePath x d t).1 d.1 (affinePath x d t).2 d.2 hx hd).2
  have hsplit : d.1 ≠ 0 ∨ d.2 ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hne (Prod.ext hh.1 hh.2)
  have hp := HessianEnergyPositive.total_energy_pos (show 2 ≤ 2 * m by omega)
    d.1 d.2 hd.2.1 hd.2.2.2.1 hsplit
  exact hb.trans_lt (by linarith only [hp])

theorem objective_contDiffWithinAt {m : ℕ}
    (hN : orderThreshold ≤ 2 * m) (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega)) (x : SchurParameters m)
    (hx : x ∈ FixedSchurChartSmooth.domain (by omega)) :
    ContDiffWithinAt ℝ ∞ (objective (by omega) s)
      (FixedSchurChartSmooth.domain (by omega)) x := by
  exact ExplicitHessianThresholdFixedSchur.objective_contDiffWithinAt_of_geometry
    hN hm s x hx (geometric_properties hN hm s x.1 x.2 hx)

theorem strictConcaveOn {m : ℕ}
    (hN : orderThreshold ≤ 2 * m) (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (m := m) (by omega)) :
    StrictConcaveOn ℝ (FixedSchurChartSmooth.domain (by omega))
      (objective (by omega) s) := by
  have hcont : ContinuousOn (objective (by omega) s)
      (FixedSchurChartSmooth.domain (by omega)) := by
    intro x hx
    exact (objective_contDiffWithinAt hN hm s x hx).continuousWithinAt
  refine ⟨domain_convex (by omega), ?_⟩
  intro x hx y hy hxy a b ha hb hab
  let f : ℝ → ℝ := fun t => objective (by omega) s (affinePath x (y - x) t)
  have hmap : Set.MapsTo (affinePath x (y - x)) (Set.Icc 0 1)
      (FixedSchurChartSmooth.domain (by omega)) :=
    fun t ht => affine_between_mem (by omega) x y hx hy ht
  have hf : ContinuousOn f (Set.Icc 0 1) :=
    hcont.comp (affinePath_contDiff x (y - x)).continuous.continuousOn hmap
  have hd := difference_direction (show 0 < m by omega) x y hx hy
  have hne : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hstrict : StrictConcaveOn ℝ (Set.Icc 0 1) f := by
    apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) hf
    intro t ht
    rw [interior_Icc] at ht
    have hh := affine_strict_curvature hN hm s x (y - x) t
      (affine_between_mem (by omega) x y hx hy ⟨ht.1.le, ht.2.le⟩) hd hne
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply, f] using hh
  have hh := hstrict.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    (by norm_num : (0 : ℝ) ≠ 1) ha hb hab
  have hz : affinePath x (y - x) 0 = x := by simp only [affinePath, zero_smul, add_zero]
  have ho : affinePath x (y - x) 1 = y := by simp only [affinePath, one_smul, add_sub_cancel]
  have hc : affinePath x (y - x) b = a • x + b • y := by
    rw [affine_between, show 1 - b = a by linarith]
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, f, hz, ho, hc] using hh

/-- The complete pointwise fixed-Schur fiber package at the explicit order. -/
theorem fiberData {m : ℕ} (hN : orderThreshold ≤ 2 * m) (hm : 3 ≤ m) :
    FixedSchurFiberData hm := by
  apply fiberData_of_strictConcavity hN hm
  intro s
  exact strictConcaveOn hN (by omega) s

end
end StructuralNote.ExplicitHessianThresholdFixedSchurConcavity

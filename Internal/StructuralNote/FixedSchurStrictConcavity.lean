import StructuralNote.FixedSchurStrictCurvature
import StructuralNote.CommonDomainSegments
import Mathlib.Analysis.Convex.Deriv

/-! Strict concavity on the literal fixed-Schur common domain. -/

namespace StructuralNote.FixedSchurStrictConcavity

open Filter Erdos1045.EventualExact
open FixedSchurEquationSmooth FixedSchurObjectivePaths FixedSchurStrictCurvature
open CommonFiberCanonicalPaths CommonDomainSegments CommonDomainConvexity
open scoped Topology

noncomputable section

theorem eventual_strictConcaveOn : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega)),
      StrictConcaveOn ℝ (FixedSchurChartSmooth.domain (by omega)) (objective (by omega) s) := by
  filter_upwards [eventual_affine_strict_curvature, eventual_objective_contDiffWithinAt]
    with m hcurv hsmooth
  intro hm s
  have hcont : ContinuousOn (objective (by omega) s) (FixedSchurChartSmooth.domain (by omega)) := by
    intro x hx
    exact (hsmooth hm s x hx).continuousWithinAt
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
    have hh := hcurv hm s x (y - x) t (affine_between_mem (by omega) x y hx hy ⟨ht.1.le, ht.2.le⟩)
      hd hne
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply, f] using hh
  have hh := hstrict.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num) (by norm_num : (0 : ℝ) ≠ 1) ha hb hab
  have hz : affinePath x (y - x) 0 = x := by simp only [affinePath, zero_smul, add_zero]
  have ho : affinePath x (y - x) 1 = y := by simp only [affinePath, one_smul, add_sub_cancel]
  have hc : affinePath x (y - x) b = a • x + b • y := by
    rw [affine_between, show 1 - b = a by linarith]
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, f, hz, ho, hc] using hh

theorem eventual_maximizer_unique : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega)),
      ∀ x ∈ FixedSchurChartSmooth.domain (by omega), ∀ y ∈ FixedSchurChartSmooth.domain (by omega),
      IsMaxOn (objective (by omega) s) (FixedSchurChartSmooth.domain (by omega)) x →
      IsMaxOn (objective (by omega) s) (FixedSchurChartSmooth.domain (by omega)) y → x = y := by
  filter_upwards [eventual_strictConcaveOn] with m hc
  intro hm s x hx y hy hxmax hymax
  exact (hc hm s).eq_of_isMaxOn hxmax hymax hx hy

end
end StructuralNote.FixedSchurStrictConcavity

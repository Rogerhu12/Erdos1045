import StructuralNote.FixedSchurStrictConcavity
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Stationary points of each actual fixed-Schur fiber are its unique maximizers. -/

namespace StructuralNote.FixedSchurStationaryUniqueness

open Filter Erdos1045.EventualExact
open FixedSchurEquationSmooth FixedSchurObjectivePaths FixedSchurStrictConcavity
open CommonFiberCanonicalPaths CommonFiberCanonicalDirections CommonDomainSegments
open scoped Topology ContDiff

noncomputable section

def Stationary {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (x : SchurParameters m) : Prop :=
  ∀ d : SchurParameters m, Admissible hm d →
    deriv (fun t => objective hm s (affinePath x d t)) 0 = 0

theorem global_max_stationary {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (x : SchurParameters m) (hx : x ∈ FixedSchurChartSmooth.domain hm)
    (hmax : IsMaxOn (objective hm s) (FixedSchurChartSmooth.domain hm) x) :
    Stationary hm s x := by
  intro d hd
  have hlocal : IsLocalMax (fun t => objective hm s (affinePath x d t)) 0 := by
    change ∀ᶠ t in 𝓝 (0 : ℝ), objective hm s (affinePath x d t) ≤ objective hm s (affinePath x d 0)
    filter_upwards [affine_domain_near_zero hm x d hx hd] with t ht
    have hb : objective hm s (affinePath x d t) ≤ objective hm s x := hmax ht
    simpa only [affinePath, zero_smul, add_zero] using hb
  exact hlocal.deriv_eq_zero

theorem concave_affine_between {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (hc : ConcaveOn ℝ (FixedSchurChartSmooth.domain hm) (objective hm s))
    (x y : SchurParameters m) (hx : x ∈ FixedSchurChartSmooth.domain hm)
    (hy : y ∈ FixedSchurChartSmooth.domain hm) :
    ConcaveOn ℝ (Set.Icc 0 1) (fun t => objective hm s (affinePath x (y - x) t)) := by
  have he : (fun t : ℝ => AffineMap.lineMap x y t) = affinePath x (y - x) := by
    funext t
    rw [AffineMap.lineMap_apply, affine_between]
    simp only [vsub_eq_sub, vadd_eq_add]
    module
  have hmap : Set.Icc (0 : ℝ) 1 ⊆ (AffineMap.lineMap x y) ⁻¹' FixedSchurChartSmooth.domain hm := by
    intro t ht
    change AffineMap.lineMap x y t ∈ FixedSchurChartSmooth.domain hm
    rw [congrFun he t]
    exact affine_between_mem hm x y hx hy ht
  have hb := (hc.comp_affineMap (AffineMap.lineMap x y)).subset hmap (convex_Icc 0 1)
  simpa only [Function.comp_def, he] using hb

theorem eventual_stationary_global_max : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega)) (x : SchurParameters m),
      x ∈ FixedSchurChartSmooth.domain (by omega) → Stationary (by omega) s x →
      IsMaxOn (objective (by omega) s) (FixedSchurChartSmooth.domain (by omega)) x := by
  filter_upwards [eventual_strictConcaveOn, eventual_objective_direction_contDiffAt] with m hc hsmooth
  intro hm s x hx hstat y hy
  have hd : Admissible (by omega) (y - x) := difference_direction (by omega) x y hx hy
  have hdiff := (hsmooth hm s x (y - x) hx hd).differentiableAt (by simp)
  have hz : HasDerivAt (fun t => objective (by omega) s (affinePath x (y - x) t)) 0 0 := by
    simpa only [hstat (y - x) hd] using hdiff.hasDerivAt
  have hconc := concave_affine_between (by omega) s (hc hm s).concaveOn x y hx hy
  have hbound := hconc.slope_le_of_hasDerivAt
    (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num) (by norm_num : (0 : ℝ) < 1) hz
  have he0 : affinePath x (y - x) 0 = x := by simp only [affinePath, zero_smul, add_zero]
  have he1 : affinePath x (y - x) 1 = y := by simp only [affinePath, one_smul, add_sub_cancel]
  simp only [slope_def_field, sub_zero, div_one, he0, he1, sub_nonpos] at hbound
  exact hbound

theorem eventual_stationary_unique : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega)),
      ∀ x ∈ FixedSchurChartSmooth.domain (by omega), ∀ y ∈ FixedSchurChartSmooth.domain (by omega),
      Stationary (by omega) s x → Stationary (by omega) s y → x = y := by
  filter_upwards [eventual_stationary_global_max, eventual_maximizer_unique] with m hmax huniq
  intro hm s x hx y hy hxs hys
  exact huniq hm s x hx y hy (hmax hm s x hx hxs) (hmax hm s y hy hys)

theorem eventual_stationary_iff_global_max : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega)) (x : SchurParameters m),
      x ∈ FixedSchurChartSmooth.domain (by omega) →
      (Stationary (by omega) s x ↔
        IsMaxOn (objective (by omega) s) (FixedSchurChartSmooth.domain (by omega)) x) := by
  filter_upwards [eventual_stationary_global_max] with m hmax
  intro hm s x hx
  exact ⟨hmax hm s x hx, global_max_stationary (by omega) s x hx⟩

end
end StructuralNote.FixedSchurStationaryUniqueness

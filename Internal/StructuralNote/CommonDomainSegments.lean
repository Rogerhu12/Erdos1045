import StructuralNote.CommonDomainConvexity
import StructuralNote.CommonFiberCanonicalPaths

/-! Affine segments and their admissible directions in the actual common domain. -/

namespace StructuralNote.CommonDomainSegments

open Erdos1045.EventualExact Complex Filter FourierMultiplier SchurSpectrum
open CommonTangentialParameters CommonFiberSmooth CommonFiberCanonical CommonFiberCanonicalPaths
open CommonDomainConvexity
open scoped BigOperators Topology
noncomputable section

theorem affine_between {m : ℕ} (x y : FreeParameters m) (t : ℝ) :
    affinePath x (y - x) t = (1 - t) • x + t • y := by
  unfold affinePath
  module

theorem affine_between_mem {m : ℕ} (hm : 0 < m) (x y : FreeParameters m)
    (hx : x ∈ domain hm) (hy : y ∈ domain hm) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    affinePath x (y - x) t ∈ domain hm := by
  rw [affine_between]
  exact domain_convex hm hx hy (by linarith [ht.2]) ht.1 (by ring)

theorem affine_between_near {m : ℕ} (hm : 0 < m) (x y : FreeParameters m)
    (hx : x ∈ domain hm) (hy : y ∈ domain hm) {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    ∀ᶠ s in 𝓝 t, affinePath x (y - x) s ∈ domain hm := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact affine_between_mem hm x y hx hy ⟨hs.1.le, hs.2.le⟩

theorem difference_direction {m : ℕ} (hm : 0 < m) (x y : FreeParameters m)
    (hx : x ∈ domain hm) (hy : y ∈ domain hm) :
    HalfPeriodic hm (fun j => ((y - x).1 j : ℂ)) ∧
      (∑ j, ((y - x).1 j : ℂ)) = 0 ∧ ParameterSpace hm (y - x).2 := by
  have hθ : (fun j => ((y - x).1 j : ℂ)) =
      (fun j => (y.1 j : ℂ) - (x.1 j : ℂ)) := by
    funext j
    simp only [Prod.fst_sub, Pi.sub_apply, ofReal_sub]
  refine ⟨?_, ?_, ?_⟩
  · rw [hθ]
    intro j
    dsimp only
    have hxj : (x.1 (halfTurn hm j) : ℂ) = x.1 j := hx.1 j
    have hyj : (y.1 (halfTurn hm j) : ℂ) = y.1 j := hy.1 j
    rw [hyj, hxj]
  · rw [hθ, Finset.sum_sub_distrib, hy.2.1, hx.2.1, sub_self]
  · have hh := parameterSpace_linear hm y.2 x.2 hy.2.2.1 hx.2.2.1 1 (-1)
    have he : (fun j => ((1 : ℝ) : ℂ) * y.2 j + ((-1 : ℝ) : ℂ) * x.2 j) = (y - x).2 := by
      funext j
      change ((1 : ℝ) : ℂ) * y.2 j + ((-1 : ℝ) : ℂ) * x.2 j = y.2 j - x.2 j
      simp only [ofReal_one, ofReal_neg, one_mul, neg_one_mul, sub_eq_add_neg]
    rwa [he] at hh

end
end StructuralNote.CommonDomainSegments

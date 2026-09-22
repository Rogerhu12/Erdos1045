import StructuralNote.CommonFiberCanonical
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! The canonical root is smooth along actual domain paths; for affine paths
the smoothness and both ordinary derivatives require no root regularity assumption. -/

namespace StructuralNote.CommonFiberCanonicalPaths

open Erdos1045.EventualExact Complex Filter
open LensClosure CommonClosureEnergy CommonDomainRadius CommonDomainClosure
open CommonTangentialParameters CommonFiberGeometry CommonFiberSmooth CommonFiberCanonical
open scoped BigOperators Topology ContDiff
noncomputable section

theorem path_contDiffAt {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ)
    (hr : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ)) (hσ : ∀ j, |σ j| ≤ 1)
    (p : ℝ → FreeParameters m) (t : ℝ) (hp : ContDiffAt ℝ ∞ p t)
    (hdom : ∀ᶠ s in 𝓝 t, p s ∈ domain (by omega)) :
    ContDiffAt ℝ ∞ (fun s => root (by omega) σ (p s)) t ∧
      ContDiffAt ℝ ∞ (fun s => fiber (by omega) σ (p s)) t := by
  obtain ⟨g, _, hg, hcfg, hagree⟩ :=
    exists_local_model hm σ (p t) hr hσ hdom.self_of_nhds
  have he : ∀ᶠ s in 𝓝 t, root (by omega) σ (p s) = g (p s) := by
    filter_upwards [hp.continuousAt.eventually hagree, hdom] with s hs hd
    exact (hs.2 hd).symm
  constructor
  · exact (hg.comp t hp).congr_of_eventuallyEq he
  · apply (hcfg.comp t hp).congr_of_eventuallyEq
    filter_upwards [he] with s hs
    simp only [Function.comp_def, fiber, hs]

theorem path_closure {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ)
    (hr : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ)) (hσ : ∀ j, |σ j| ≤ 1)
    (p : ℝ → FreeParameters m) (t : ℝ)
    (hdom : ∀ᶠ s in 𝓝 t, p s ∈ domain (by omega)) :
    ∀ᶠ s in 𝓝 t, closureFamily (data (by omega) σ (p s)) (root (by omega) σ (p s)) = 0 := by
  filter_upwards [hdom] with s hs
  exact (root_spec hm σ (p s) hr hσ hs).2

def affinePath {m : ℕ} (x d : FreeParameters m) (s : ℝ) : FreeParameters m := x + s • d

theorem affinePath_contDiff {m : ℕ} (x d : FreeParameters m) : ContDiff ℝ ∞ (affinePath x d) := by
  unfold affinePath
  fun_prop

theorem affine_contDiffAt {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ)
    (hr : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ)) (hσ : ∀ j, |σ j| ≤ 1)
    (x d : FreeParameters m) (t : ℝ)
    (hdom : ∀ᶠ s in 𝓝 t, affinePath x d s ∈ domain (by omega)) :
    ContDiffAt ℝ ∞ (fun s => root (by omega) σ (affinePath x d s)) t ∧
      ContDiffAt ℝ ∞ (fun s => fiber (by omega) σ (affinePath x d s)) t :=
  path_contDiffAt hm σ hr hσ _ t (affinePath_contDiff x d).contDiffAt hdom

theorem affine_contDiffWithinAt {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ)
    (hr : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ)) (hσ : ∀ j, |σ j| ≤ 1)
    (x d : FreeParameters m) (S : Set ℝ) (t : ℝ) (ht : t ∈ S)
    (hdom : ∀ s ∈ S, affinePath x d s ∈ domain (by omega)) :
    ContDiffWithinAt ℝ ∞ (fun s => root (by omega) σ (affinePath x d s)) S t ∧
      ContDiffWithinAt ℝ ∞ (fun s => fiber (by omega) σ (affinePath x d s)) S t := by
  have hp := (affinePath_contDiff x d).contDiffAt.contDiffWithinAt (s := S) (x := t)
  exact ⟨(root_contDiffWithinAt hm σ _ hr hσ (hdom t ht)).comp t hp hdom,
    (fiber_contDiffWithinAt hm σ _ hr hσ (hdom t ht)).comp t hp hdom⟩

theorem affine_root_derivatives {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ)
    (hr : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ)) (hσ : ∀ j, |σ j| ≤ 1)
    (x d : FreeParameters m) (t : ℝ)
    (hdom : ∀ᶠ s in 𝓝 t, affinePath x d s ∈ domain (by omega)) :
    (∀ᶠ s in 𝓝 t, HasDerivAt (fun r => root (by omega) σ (affinePath x d r))
      (deriv (fun r => root (by omega) σ (affinePath x d r)) s) s) ∧
    HasDerivAt (deriv (fun r => root (by omega) σ (affinePath x d r)))
      (deriv (deriv (fun r => root (by omega) σ (affinePath x d r))) t) t := by
  have hs := (affine_contDiffAt hm σ hr hσ x d t hdom).1
  have hs2 : ContDiffAt ℝ 2 (fun r => root (by omega) σ (affinePath x d r)) t :=
    hs.of_le (WithTop.coe_le_coe.mpr le_top)
  constructor
  · filter_upwards [hs2.eventually (by norm_num)] with s hs
    exact (hs.differentiableAt (by norm_num)).hasDerivAt
  · have hd : ContDiffAt ℝ 1 (deriv (fun r => root (by omega) σ (affinePath x d r))) t :=
      hs2.derivWithin (by norm_num)
    exact (hd.differentiableAt (by norm_num)).hasDerivAt

end
end StructuralNote.CommonFiberCanonicalPaths

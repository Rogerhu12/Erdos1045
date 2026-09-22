import StructuralNote.CommonFiberCanonicalCurvature

/-! Smoothness of the actual logarithmic distance product on the canonical domain. -/

namespace StructuralNote.CommonFiberCanonicalObjective

open Erdos1045 Erdos1045.EventualExact Complex Filter
open CommonDomainRadius CommonFiberSmooth CommonFiberCanonical
open CommonFiberDifferentialEstimate HessianErrorLimits CommonFiberHessianGeometryDomain
open scoped BigOperators Topology ContDiff
noncomputable section

def logProduct {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (x : FreeParameters m) : ℝ :=
  Real.log (Configuration.discriminant (fiber hm σ x))

theorem log_discriminant_contDiffWithinAt {m n : ℕ} (f : FreeParameters m → Fin n → ℂ)
    (S : Set (FreeParameters m)) (x : FreeParameters m)
    (hf : ContDiffWithinAt ℝ ∞ f S x) (hi : Function.Injective (f x)) :
    ContDiffWithinAt ℝ ∞ (fun y => Real.log (Configuration.discriminant (f y))) S x := by
  have hd : ContDiffWithinAt ℝ ∞ (fun y => Configuration.discriminant (f y)) S x := by
    unfold Configuration.discriminant
    apply contDiffWithinAt_prod
    intro i _
    apply contDiffWithinAt_prod
    intro j hj
    exact ((contDiffWithinAt_pi.mp hf i).sub (contDiffWithinAt_pi.mp hf j)).norm ℂ
      (sub_ne_zero.mpr (hi.ne (Finset.ne_of_mem_erase hj).symm))
  exact hd.log (Configuration.discriminant_pos (f x) hi).ne'

theorem eventual_logProduct_contDiffWithinAt : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (σ : Fin m → ℝ) (x : FreeParameters m),
    (∀ j, |σ j| ≤ 1) → x ∈ domain hm →
    ContDiffWithinAt ℝ ∞ (logProduct hm σ) (domain hm) x := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  filter_upwards [eventual_size_conditions, hnat.eventually eventual_error_small] with m hsize herr
  intro hm σ x hσ hx
  have hroot := root_spec hsize.1 σ x hsize.2.1 hσ hx
  have hi := domain_configuration_injective (by omega : 8 ≤ m) x.1 x.2 σ (root hm σ x)
    hx hσ hroot.1 hroot.2 hsize.2.2.1 (by
      have hh : chordError (2 * m) < 1 := lt_of_le_of_lt herr.1 (by norm_num)
      simpa only [chordError, Nat.cast_mul, Nat.cast_ofNat] using hh)
  exact log_discriminant_contDiffWithinAt (fiber hm σ) (domain hm) x
    (fiber_contDiffWithinAt hsize.1 σ x hsize.2.1 hσ hx) hi

theorem eventual_logProduct_contDiffOn : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (σ : Fin m → ℝ), (∀ j, |σ j| ≤ 1) →
      ContDiffOn ℝ ∞ (logProduct hm σ) (domain hm) := by
  filter_upwards [eventual_logProduct_contDiffWithinAt] with m h
  intro hm σ hσ x hx
  exact h hm σ x hσ hx

theorem eventual_logProduct_continuousOn : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (σ : Fin m → ℝ), (∀ j, |σ j| ≤ 1) →
      ContinuousOn (logProduct hm σ) (domain hm) := by
  filter_upwards [eventual_logProduct_contDiffOn] with m h
  intro hm σ hσ
  exact (h hm σ hσ).continuousOn

end
end StructuralNote.CommonFiberCanonicalObjective

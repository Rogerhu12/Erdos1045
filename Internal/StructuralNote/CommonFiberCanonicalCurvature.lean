import StructuralNote.CommonFiberCanonicalPaths
import StructuralNote.CommonFiberLogCurvature

/-! Strict curvature for the canonical fiber itself. All implicit-root
derivatives, closure identities and root bounds are discharged internally. -/

namespace StructuralNote.CommonFiberCanonicalCurvature

open Erdos1045 Erdos1045.EventualExact Complex Filter
open SchurSpectrum LensClosure CommonDomainRadius CommonDomainClosure
open CommonTangentialParameters CommonFiberGeometry CommonFiberSmooth CommonFiberCanonical
open CommonFiberCanonicalPaths CommonFiberDifferentialEstimate CommonFiberLogCurvature
open scoped BigOperators Topology ContDiff
noncomputable section

theorem affine_angle_hasDerivAt {m : ℕ} (x d : FreeParameters m) (s : ℝ) (j : Fin (2 * m)) :
    HasDerivAt (fun r => (affinePath x d r).1 j) (d.1 j) s := by
  change HasDerivAt (fun r => x.1 j + r * d.1 j) (d.1 j) s
  simpa only [one_mul, id_eq] using ((hasDerivAt_id s).mul_const (d.1 j)).const_add (x.1 j)

theorem affine_center_hasDerivAt {m : ℕ} (x d : FreeParameters m) (s : ℝ) (j : Fin (2 * m)) :
    HasDerivAt (fun r => (affinePath x d r).2 j) (d.2 j) s := by
  change HasDerivAt (fun r => x.2 j + r • d.2 j) (d.2 j) s
  simpa only [one_smul, id_eq] using ((hasDerivAt_id s).smul_const (d.2 j)).const_add (x.2 j)

theorem eventual_canonical_affine_curvature : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (σ : Fin m → ℝ) (x d : FreeParameters m) (t : ℝ),
    (∀ j, |σ j| ≤ 1) →
    (∀ᶠ s in 𝓝 t, affinePath x d s ∈ domain hm) →
    HalfPeriodic hm (fun j => (d.1 j : ℂ)) → (∑ j, (d.1 j : ℂ)) = 0 →
    ParameterSpace hm d.2 → d ≠ 0 →
    deriv (deriv (fun s => Real.log (Configuration.discriminant
      (fiber hm σ (affinePath x d s))))) t < 0 := by
  filter_upwards [eventual_actual_strict_curvature, eventual_size_conditions] with m hcurv hsize
  intro hm σ x d t hσ hdom hdθ hdmean hdv hdne
  have hr := hsize.2.1
  have hderiv := affine_root_derivatives hsize.1 σ hr hσ x d t hdom
  have hfirst : ∀ᶠ s in 𝓝 t,
      (∀ j, HasDerivAt (fun r => (affinePath x d r).1 j) (d.1 j) s) ∧
      (∀ j, HasDerivAt (fun r => (affinePath x d r).2 j) (d.2 j) s) ∧
      HasDerivAt (fun r => root hm σ (affinePath x d r))
        (deriv (fun r => root hm σ (affinePath x d r)) s) s := by
    filter_upwards [hderiv.1] with s hs
    exact ⟨affine_angle_hasDerivAt x d s, affine_center_hasDerivAt x d s, hs⟩
  have hz := path_closure hsize.1 σ hr hσ (affinePath x d) t hdom
  have hs := root_spec hsize.1 σ (affinePath x d t) hr hσ hdom.self_of_nhds
  have hne : d.1 ≠ 0 ∨ d.2 ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hdne (Prod.ext hh.1 hh.2)
  exact hcurv hm (fun s => (affinePath x d s).1) (fun s => (affinePath x d s).2)
    (fun s => root hm σ (affinePath x d s)) (deriv (fun s => root hm σ (affinePath x d s)))
    d.1 d.2 (deriv (deriv (fun s => root hm σ (affinePath x d s))) t) t σ
    hfirst hderiv.2 hdom.self_of_nhds hs.1 hdθ hdmean hdv hσ hz hne

end
end StructuralNote.CommonFiberCanonicalCurvature

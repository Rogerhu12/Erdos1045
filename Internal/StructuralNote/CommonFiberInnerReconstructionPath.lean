import StructuralNote.CommonFiberInnerReconstructionEnergy
import StructuralNote.CommonFiberCanonicalDirections
import StructuralNote.CommonFiberHessianGeometryVelocity
import StructuralNote.CommonFiberRefinedRoot

/-! Integration of the actual canonical center derivative along a radial
parameter segment. No smoothness hypothesis on the selected root is used. -/

namespace StructuralNote.CommonFiberInnerReconstruction

open Erdos1045 Erdos1045.EventualExact Complex Filter SchurSpectrum
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure CommonDomainRadius
open CommonFiberGeometry CommonFiberSmooth CommonFiberCanonical CommonFiberCanonicalPaths
open CommonFiberCanonicalDirections CommonDomainSegments CommonFiberFirstDerivative
open CommonFiberDifferentialEstimate CommonFiberHessianGeometryVelocity CommonFiberRefinedRoot
open scoped BigOperators Topology ContDiff
noncomputable section

def centerAt {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (x : FreeParameters m) : Fin (2 * m) → ℂ :=
  center hm x.1 x.2 σ (CommonFiberCanonical.root hm σ x)

theorem zero_mem_domain {m : ℕ} (hm : 0 < m) (x : FreeParameters m) (hx : x ∈ domain hm) :
    (0 : FreeParameters m) ∈ domain hm := by
  refine ⟨fun _ => rfl, by simp, zero_parameterSpace hm, ?_⟩
  have he := add_nonneg (pairEnergy_nonneg (by omega) (fun j => (x.1 j : ℂ)))
    (pairEnergy_nonneg (by omega) x.2)
  simpa only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, ofReal_zero, ← Pi.zero_def,
    zero_pairEnergy, add_zero] using he.trans_lt hx.2.2.2

theorem affine_domain_near_at {m : ℕ} (hm : 0 < m) (x d : FreeParameters m) {t : ℝ}
    (hx : affinePath x d t ∈ domain hm) (hd : Admissible hm d) :
    ∀ᶠ s in 𝓝 t, affinePath x d s ∈ domain hm := by
  have ht : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
    simpa only [id_eq, sub_self] using ((continuousAt_id (x := t)).sub_const t)
  filter_upwards [ht.eventually (affine_domain_near_zero hm (affinePath x d t) d hx hd)] with s hs
  have he : affinePath (affinePath x d t) d (s - t) = affinePath x d s := by
    unfold affinePath
    module
  rwa [he] at hs

theorem radial_mem_domain {m : ℕ} (hm : 0 < m) (x : FreeParameters m) (hx : x ∈ domain hm)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : affinePath 0 x t ∈ domain hm := by
  simpa only [sub_zero] using affine_between_mem hm 0 x (zero_mem_domain hm x hx) hx ht

theorem radial_domain_near {m : ℕ} (hm : 0 < m) (x : FreeParameters m) (hx : x ∈ domain hm)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : ∀ᶠ s in 𝓝 t, affinePath 0 x s ∈ domain hm :=
  affine_domain_near_at hm 0 x (radial_mem_domain hm x hx ht) ⟨hx.1, hx.2.1, hx.2.2.1⟩

theorem eventual_radial_center_energy : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (σ : Fin m → ℝ) (x : FreeParameters m),
    (∀ j, |σ j| ≤ 1) → x ∈ domain hm →
    pairEnergy (by omega) (centerAt hm σ x - centerAt hm σ 0 - x.2) ≤
      4000000000 / (2 * m : ℝ) *
        (pairEnergy (by omega) (fun j => (x.1 j : ℂ)) + pairEnergy (by omega) x.2) := by
  filter_upwards [eventual_actual_first_derivative, eventual_size_conditions] with m hfirst hsize
  intro hm σ x hσ hx
  let p : ℝ → FreeParameters m := affinePath 0 x
  let ξ : ℝ → ℂ := fun t => CommonFiberCanonical.root hm σ (p t)
  let c : ℝ → Fin (2 * m) → ℂ := fun t => centerAt hm σ (p t) - t • x.2
  let c' : ℝ → Fin (2 * m) → ℂ := fun t =>
    centerVelocity hm (p t).1 (p t).2 σ (ξ t) x.1 x.2 (deriv ξ t) - x.2
  have hall (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      (∀ j, HasDerivAt (fun s => c s j) (c' t j) t) ∧
        pairEnergy (by omega) (c' t) ≤ 4000000000 / (2 * m : ℝ) *
          (pairEnergy (by omega) (fun j => (x.1 j : ℂ)) + pairEnergy (by omega) x.2) := by
    have hdom : ∀ᶠ s in 𝓝 t, p s ∈ domain hm := radial_domain_near hm x hx ht
    have hroot := root_spec hsize.1 σ (p t) hsize.2.1 hσ hdom.self_of_nhds
    have hξ : HasDerivAt ξ (deriv ξ t) t :=
      ((affine_contDiffAt hsize.1 σ hsize.2.1 hσ 0 x t hdom).1.differentiableAt
        (by simp)).hasDerivAt
    have hθ (j : Fin (2 * m)) : HasDerivAt (fun s => (p s).1 j) (x.1 j) t := by
      simpa [p, affinePath] using (hasDerivAt_id t).mul_const (x.1 j)
    have hv (j : Fin (2 * m)) : HasDerivAt (fun s => (p s).2 j) (x.2 j) t := by
      simpa [p, affinePath, real_smul] using (hasDerivAt_id t).ofReal_comp.mul_const (x.2 j)
    have hz := path_closure hsize.1 σ hsize.2.1 hσ p t hdom
    have h := hfirst hm (fun s => (p s).1) (fun s => (p s).2) ξ x.1 x.2 (deriv ξ t) t σ
      hθ hv hξ hdom.self_of_nhds hroot.1 hx.2.1 hx.2.2.1 hσ hz
    refine ⟨?_, ?_⟩
    · intro j
      simpa [c, c', centerAt, p, affinePath, ξ] using (h.1 j).fun_sub (hv j)
    · have hc := h.2
      have hl := logarithmic_coefficient (show 0 < 2 * m by omega)
        (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsize.2.1)
      simp only [Nat.cast_mul, Nat.cast_ofNat] at hl
      have hb : 4000000000 * (logOrder (2 * m) : ℝ) ^ 2 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 3 ≤
          4000000000 / (2 * m : ℝ) := by
        calc
          _ = 4000000000 * ((logOrder (2 * m) : ℝ) ^ 2 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 3) := by ring
          _ ≤ 4000000000 * (1 / (2 * m : ℝ)) := mul_le_mul_of_nonneg_left hl (by norm_num)
          _ = _ := by ring
      have ha := mul_le_mul_of_nonneg_right hb (pairEnergy_nonneg (by omega) x.2)
      change pairEnergy (by omega) (c' t) ≤ _ at hc
      nlinarith only [hc, ha]
  have he := energy_mean_value (by omega : 0 < 2 * m) c c'
    (mul_nonneg (by positivity) (add_nonneg (pairEnergy_nonneg _ _) (pairEnergy_nonneg _ _)))
    (fun t ht => (hall t ht).1) (fun t ht => (hall t ht).2)
  have hc : c 1 - c 0 = centerAt hm σ x - centerAt hm σ 0 - x.2 := by
    simp only [c, p, affinePath, one_smul, zero_add, zero_smul, sub_zero]
    abel
  rwa [hc] at he

theorem eventual_inner_path_remainder : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (σ : Fin m → ℝ) (x : FreeParameters m) (K : ℝ),
    (∀ j, |σ j| ≤ 1) → x ∈ domain hm →
    pairEnergy (by omega) (fun j => (x.1 j : ℂ)) + pairEnergy (by omega) x.2 ≤ K / (2 * m : ℝ) ^ 2 →
    pairEnergy (by omega) (centerAt hm σ x - centerAt hm σ 0 - x.2) ≤
      4000000000 * K / (2 * m : ℝ) ^ 3 := by
  filter_upwards [eventual_radial_center_energy] with m hpath
  intro hm σ x K hσ hx hK
  apply (hpath hm σ x hσ hx).trans
  calc
    _ ≤ 4000000000 / (2 * m : ℝ) * (K / (2 * m : ℝ) ^ 2) := by gcongr
    _ = _ := by ring

end
end StructuralNote.CommonFiberInnerReconstruction

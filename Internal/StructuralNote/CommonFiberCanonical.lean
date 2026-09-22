import StructuralNote.CommonFiberSmooth

/-! A single canonical common-fiber root, with its local smooth models. The
root is selected by the actual closure equation and its quantitative ball. -/

namespace StructuralNote.CommonFiberCanonical

open Erdos1045.EventualExact Complex Filter
open SchurSpectrum LensClosure CommonClosureEnergy CommonDomainRadius CommonDomainClosure
open CommonTangentialParameters CommonFiberGeometry CommonFiberSmooth
open scoped BigOperators Topology ContDiff
noncomputable section

def RootCondition {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (x : FreeParameters m) (ξ : ℂ) : Prop :=
  ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2 ∧ closureFamily (data hm σ x) ξ = 0

def root {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (x : FreeParameters m) : ℂ := by
  classical
  exact if he : ∃ ξ, RootCondition hm σ x ξ then Classical.choose he else 0

def fiber {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (x : FreeParameters m) : Fin (2 * m) → ℂ :=
  configuration hm x.1 x.2 σ (root hm σ x)

def domain {m : ℕ} (hm : 0 < m) : Set (FreeParameters m) := {x | InDomain hm x.1 x.2}

theorem domain_energies {m : ℕ} (hm : 0 < m) (x : FreeParameters m)
    (hr : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ)) (hx : x ∈ domain hm) :
    pairEnergy (by omega) (fun j => (x.1 j : ℂ)) ≤ 1 / (2 * m : ℝ) ∧
      pairEnergy (by omega) x.2 ≤ 1 / (2 * m : ℝ) := by
  have hs := hx.2.2.2.le.trans hr
  have hθ := pairEnergy_nonneg (by omega : 0 < 2 * m) (fun j => (x.1 j : ℂ))
  have hv := pairEnergy_nonneg (by omega : 0 < 2 * m) x.2
  constructor <;> linarith

theorem exists_unique_root {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ) (x : FreeParameters m)
    (hr : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ))
    (hσ : ∀ j, |σ j| ≤ 1) (hx : x ∈ domain (by omega)) :
    ∃! ξ, RootCondition (by omega) σ x ξ := by
  obtain ⟨hθ, hv⟩ := domain_energies (by omega) x hr hx
  exact exists_unique_parameter_root hm x.1 x.2 σ hx.2.1 hx.2.2.1 hθ hv hσ

theorem root_spec {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ) (x : FreeParameters m)
    (hr : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ))
    (hσ : ∀ j, |σ j| ≤ 1) (hx : x ∈ domain (by omega)) :
    RootCondition (by omega) σ x (root (by omega) σ x) := by
  have he := (exists_unique_root hm σ x hr hσ hx).exists
  rw [root, dif_pos he]
  exact Classical.choose_spec he

theorem root_eq_of_condition {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ) (x : FreeParameters m)
    (hr : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ))
    (hσ : ∀ j, |σ j| ≤ 1) (hx : x ∈ domain (by omega)) {ξ : ℂ}
    (hξ : RootCondition (by omega) σ x ξ) : root (by omega) σ x = ξ :=
  (exists_unique_root hm σ x hr hσ hx).unique (root_spec hm σ x hr hσ hx) hξ

theorem root_height_small {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ) (x : FreeParameters m)
    (hr : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ))
    (hσ : ∀ j, |σ j| ≤ 1) (hx : x ∈ domain (by omega)) (j : Fin m) :
    |heightParameter (coordinates (by omega) x.2) (root (by omega) σ x) j| < 2 := by
  obtain ⟨hθ, hv⟩ := domain_energies (by omega) x hr hx
  have hroot := (root_spec hm σ x hr hσ hx).1
  have hd := double_radius_small hm σ x hx.2.1 hθ hv j
  have hh : |heightParameter (coordinates (by omega) x.2) (root (by omega) σ x) j| ≤
      |coordinates (by omega) x.2 j| + ‖root (by omega) σ x‖ :=
    (abs_add_le _ _).trans (add_le_add le_rfl (harmonicFunctional_le_norm _ _))
  have hR : (0 : ℝ) ≤ 1024 / (2 * m : ℝ) ^ 2 := by positivity
  dsimp [data] at hd
  linarith [abs_nonneg (phase (by omega) x.1 j - LensClosure.midpoint m j)]

/-- The canonical root and reconstructed fiber agree locally on the actual
domain with one ambient smooth implicit-function model. -/
theorem exists_local_model {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ) (x : FreeParameters m)
    (hr : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ))
    (hσ : ∀ j, |σ j| ≤ 1) (hx : x ∈ domain (by omega)) :
    ∃ g : FreeParameters m → ℂ,
      g x = root (by omega) σ x ∧ ContDiffAt ℝ ∞ g x ∧
      ContDiffAt ℝ ∞ (fun y => configuration (by omega) y.1 y.2 σ (g y)) x ∧
      (∀ᶠ y in 𝓝 x, closureFamily (data (by omega) σ y) (g y) = 0 ∧
        (y ∈ domain (by omega) → g y = root (by omega) σ y)) := by
  obtain ⟨hθ, hv⟩ := domain_energies (by omega) x hr hx
  have hroot := root_spec hm σ x hr hσ hx
  obtain ⟨g, hgx, hg, hagree⟩ := exists_smooth_root hm σ x hσ hx.2.1 hθ hv hroot.1 hroot.2
  have hc : ContDiffAt ℝ ∞ (fun u : FreeParameters m × ℂ =>
      configuration (by omega) u.1.1 u.1.2 σ u.2) (x, g x) := by
    rw [hgx]
    exact configuration_contDiffAt (by omega) σ _ (root_height_small hm σ x hr hσ hx)
  have hp : ContDiffAt ℝ ∞ (fun y : FreeParameters m => (y, g y)) x := contDiffAt_id.prodMk hg
  refine ⟨g, hgx, hg, ?_, ?_⟩
  · simpa only [Function.comp_def] using hc.comp x hp
  · filter_upwards [hagree] with y hy
    refine ⟨hy.1, ?_⟩
    intro hyd
    have hyr := root_spec hm σ y hr hσ hyd
    obtain ⟨hyθ, hyv⟩ := domain_energies (by omega) y hr hyd
    exact hy.2 _ hyr.1 hyr.2 hyd.2.1 hyθ hyv

theorem root_contDiffWithinAt {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ) (x : FreeParameters m)
    (hr : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ))
    (hσ : ∀ j, |σ j| ≤ 1) (hx : x ∈ domain (by omega)) :
    ContDiffWithinAt ℝ ∞ (root (by omega) σ) (domain (by omega)) x := by
  obtain ⟨g, hgx, hg, _, he⟩ := exists_local_model hm σ x hr hσ hx
  apply hg.contDiffWithinAt.congr_of_eventuallyEq _ hgx.symm
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyd
  exact (hy.2 hyd).symm

theorem fiber_contDiffWithinAt {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ) (x : FreeParameters m)
    (hr : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ))
    (hσ : ∀ j, |σ j| ≤ 1) (hx : x ∈ domain (by omega)) :
    ContDiffWithinAt ℝ ∞ (fiber (by omega) σ) (domain (by omega)) x := by
  obtain ⟨g, hgx, _, hg, he⟩ := exists_local_model hm σ x hr hσ hx
  apply hg.contDiffWithinAt.congr_of_eventuallyEq _ ?_
  · filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hyd
    simp only [fiber, hy.2 hyd]
  · simp only [fiber, hgx]

end
end StructuralNote.CommonFiberCanonical

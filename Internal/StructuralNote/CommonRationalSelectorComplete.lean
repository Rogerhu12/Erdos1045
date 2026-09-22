import StructuralNote.CommonRationalSelector
import StructuralNote.CommonFiberDomainInjectivity

/-! Every common-domain parameter pair has an explicit rational representative
meeting the complete selector, including collision freedom and the unique root
window. Together with the forward selector this closes the two coordinate
descriptions, independently of the later stationary-point analysis. -/

namespace StructuralNote.CommonRationalSelectorComplete

open Erdos1045.EventualExact LensClosure SchurSpectrum
open CommonClosureEnergy CommonTangentialParameters CommonFiberGeometry CommonDomainClosure
open RationalCommonConfiguration RationalBranchSelector CommonSelectorRoot
open scoped BigOperators
noncomputable section

theorem injective_iff_of_rigid_motion {ι : Type*} (f g : ι → ℂ) (a : ℝ) (c : ℂ)
    (he : ∀ j, f j = unit a * (g j - c)) : Function.Injective f ↔ Function.Injective g := by
  have hu : unit a ≠ 0 := by
    intro hz
    have hn := norm_unit a
    rw [hz, norm_zero] at hn
    norm_num at hn
  constructor
  · intro hf i j hij
    apply hf
    rw [he i, he j, hij]
  · intro hg i j hij
    rw [he i, he j] at hij
    apply hg
    have hh := mul_left_cancel₀ hu hij
    linear_combination hh

theorem eventual_complete_inverse_selector :
    ∃ N : ℕ, ∀ (m : ℕ) (hm : N + 1048576 ≤ m) (θ : Fin (2 * m) → ℝ)
      (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ), InDomain (by omega) θ v →
      (∀ j, σ j ^ 2 = 1) → ∃ ξ : ℂ,
      let X := CommonRationalChart.parameters (by omega) θ v σ ξ
      ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2 ∧
        closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j))
          σ (coordinates (by omega) v) ξ = 0 ∧
        Selected (by omega) σ X ∧ RationalConfiguration.closure (by omega) σ X = 0 ∧
        theta (by omega) X = θ ∧ recoveredVector (by omega) σ X = v ∧
        recoveredCorrection (by omega) σ X = ξ ∧
        (∀ η : ℂ, ‖η‖ < rootWindow (2 * m) →
          closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j))
            σ (coordinates (by omega) v) η = 0 → η = ξ) ∧
        (∀ j, configuration (by omega) θ v σ ξ j = unit (CommonRationalChart.initialAngle (by omega) θ) *
          (RationalConfiguration.configuration (by omega) σ X j - centerMean (by omega) σ X)) := by
  obtain ⟨N₁, hN₁⟩ := CommonRationalSelector.eventual_inverse_chart
  obtain ⟨N₂, hN₂⟩ := CommonFiberDomainInjectivity.eventual_injective
  obtain ⟨N₃, hN₃⟩ := eventual_common_domain_window_root
  refine ⟨N₁ + N₂ + N₃, ?_⟩
  intro m hm θ v σ hdom hs
  obtain ⟨ξ, hb, _, hz, huniq⟩ := hN₃ m (by omega) θ v σ hdom (fun j => sign_bound (hs j))
  obtain ⟨hsmall, hθ, hv, hξ, hH, hwindow, henergy, hconfig⟩ :=
    hN₁ m (by omega) θ v σ ξ hdom hs hb hz
  have hi := hN₂ m (by omega) θ v σ ξ hdom hs hb hz
  have hir := (injective_iff_of_rigid_motion _ _ _ _ hconfig).1 hi
  exact ⟨ξ, hb, hz, ⟨hsmall, hir, hwindow, henergy⟩, hH, hθ, hv, hξ, huniq, hconfig⟩

end
end StructuralNote.CommonRationalSelectorComplete

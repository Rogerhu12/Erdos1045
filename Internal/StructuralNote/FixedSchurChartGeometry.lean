import StructuralNote.FixedSchurChartRadial
import StructuralNote.FixedSchurChartAdjacent
import StructuralNote.FixedSchurOffsetGeometry

/-! Feasibility and the complete diameter graph of the chosen fixed-Schur chart. -/

namespace StructuralNote.FixedSchurChartGeometry

open Complex Filter Erdos1045 Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonDomainClosure FixedSchurLinear FixedSchurEdgeGeometry FixedSchurChart
open FixedSchurChartSizes FixedSchurChartRadial FixedSchurChartAdjacent
open FixedSchurOffsetGeometry
open scoped Topology

noncomputable section

theorem eventual_offset_classification : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      ∀ r, r < 2 * m → ∀ j,
        ‖configuration (by omega) s θ v (cyclicAdvance j r) -
          configuration (by omega) s θ v j‖ ≤ 2 ∧
        (‖configuration (by omega) s θ v (cyclicAdvance j r) -
          configuration (by omega) s θ v j‖ = 2 ↔ OffsetEdge (FiniteBox.patternSign s) j r) := by
  filter_upwards [eventual_coordinate_properties, eventual_chart_small_steps,
    eventual_coordinate_radial, eventual_unselected_crossing_norm_lt_two,
    eventually_ge_atTop 8] with m hprops hsmall hrad hun hm8
  intro hm s θ v hdom r hr j
  have hp := hprops hm s θ v hdom
  obtain ⟨hθ, hstep⟩ := hsmall hm s θ v hdom
  have hC := center_halfPeriodic hm _ v hp.antiperiodic hdom.2.2.1.1
  apply offset_classification hm (configuration (by omega) s θ v)
    (FiniteBox.patternSign s) hp.matching _ _ r hr j
  · intro k
    exact next_classification hm θ _ _ hdom.1 hC k
      (FiniteBox.patternSign_is_sign s k) (hp.selected k) (hun hm s θ v hdom k)
  · intro r' hr' hprev hmatch hnext k
    exact nonlocal_strict hm8 hr' hprev hmatch hnext θ _ hdom.1 hC hθ hstep
      (hrad hm s θ v hdom) k

/-- The full word graph, expressed by the cyclic offset from the second label. -/
def WordEdge {m : ℕ} (σ : Fin (2 * m) → ℝ) (i j : Fin (2 * m)) : Prop :=
  OffsetEdge σ j (cyclicForwardDistance j i)

theorem eventual_diameter_and_graph : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      Configuration.DiameterAtMost 2 (configuration (by omega) s θ v) ∧
        (∀ i j, ‖configuration (by omega) s θ v i - configuration (by omega) s θ v j‖ = 2 ↔
          WordEdge (FiniteBox.patternSign s) i j) := by
  filter_upwards [eventual_offset_classification] with m hoff
  intro hm s θ v hdom
  have hh (i j : Fin (2 * m)) := hoff hm s θ v hdom (cyclicForwardDistance j i)
    (Nat.mod_lt (i.val + 2 * m - j.val) (by omega)) j
  simp only [CommonFiberNonlocalFeasibility.cyclicAdvance_forwardDistance] at hh
  exact ⟨fun i j => (hh i j).1, fun i j => (hh i j).2⟩

structure GeometricProperties {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (m := m) (by omega)) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) : Prop where
  coordinates : Properties hm θ v (FiniteBox.patternSign s) (coordinate (by omega) s θ v)
  injective : Function.Injective (configuration (by omega) s θ v)
  diameter : Configuration.DiameterAtMost 2 (configuration (by omega) s θ v)
  graph : ∀ i j, ‖configuration (by omega) s θ v i - configuration (by omega) s θ v j‖ = 2 ↔
    WordEdge (FiniteBox.patternSign s) i j

theorem eventual_geometric_properties : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      GeometricProperties hm s θ v := by
  filter_upwards [eventual_coordinate_properties, eventual_configuration_injective,
    eventual_diameter_and_graph] with m hp hi hg
  intro hm s θ v hdom
  exact ⟨hp hm s θ v hdom, hi hm s θ v hdom,
    (hg hm s θ v hdom).1, (hg hm s θ v hdom).2⟩

end
end StructuralNote.FixedSchurChartGeometry

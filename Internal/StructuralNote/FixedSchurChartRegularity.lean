import StructuralNote.FixedSchurChartSmooth
import StructuralNote.FixedSchurConfigurationSmooth
import StructuralNote.FixedSchurChartGeometry

/-! The complete feasible-coordinate endpoint: smoothness, injectivity,
all distance constraints, exact diameter graph, and Schur identities. -/

namespace StructuralNote.FixedSchurChartRegularity

open Complex Filter Erdos1045.EventualExact
open CommonDomainClosure FixedSchurChart FixedSchurChartSmooth
open FixedSchurEquationSmooth FixedSchurConfigurationSmooth FixedSchurChartGeometry
open scoped Topology ContDiff

noncomputable section

theorem eventual_configuration_contDiffWithinAt : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (s : FiniteBox.SignPattern hm) (x : SchurParameters m),
      x ∈ domain hm → ContDiffWithinAt ℝ ∞
        (fun y : SchurParameters m => configuration hm s y.1 y.2) (domain hm) x := by
  filter_upwards [eventual_local_model] with m hmodel
  intro hm s x hx
  obtain ⟨g, hgx, hg, he⟩ := hmodel hm s x hx
  have hparam : ContDiffAt ℝ ∞ (fun y => (y, g y)) x := contDiffAt_id.prodMk hg
  have hfamily : ContDiffAt ℝ ∞ (configurationFamily hm) (x, g x) :=
    (configurationFamily_contDiff hm).contDiffAt.of_le (by simp)
  have hc := hfamily.comp x hparam
  change ContDiffAt ℝ ∞ (fun y =>
    FixedSchurEdgeGeometry.vertex y.1 (FixedSchurLinear.center (g y) y.2)) x at hc
  apply hc.contDiffWithinAt.congr_of_eventuallyEq _ ?_
  · filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with y hy hyd
    simp only [configuration, hy.2.2 hyd]
  · simp only [configuration, hgx]

/-- Proposition 9.1 on the literal common domain, uniformly in every sign pattern. -/
theorem eventual_feasible_coordinates : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega)) (x : SchurParameters m),
      InDomain (by omega) x.1 x.2 →
      GeometricProperties hm s x.1 x.2 ∧
        ContDiffWithinAt ℝ ∞
          (fun y : SchurParameters m => coordinate (by omega) s y.1 y.2)
          (domain (by omega)) x ∧
        ContDiffWithinAt ℝ ∞
          (fun y : SchurParameters m => configuration (by omega) s y.1 y.2)
          (domain (by omega)) x ∧
        (∀ q : SchurState m,
          ‖q - FixedSchurDomainSmallness.baseWord (FiniteBox.patternSign s)‖ ≤
            FixedSchurDomainSmallness.radius (2 * m) →
          FixedSchurEquations.equationMap (by omega) x.1 x.2 (FiniteBox.patternSign s) q = q →
          q = coordinate (by omega) s x.1 x.2) := by
  filter_upwards [eventual_geometric_properties, eventual_coordinate_contDiffWithinAt,
    eventual_configuration_contDiffWithinAt, eventual_coordinate_unique] with m hgeo hq hz huniq
  intro hm s x hx
  exact ⟨hgeo hm s x.1 x.2 hx, hq (by omega) s x hx, hz (by omega) s x hx,
    huniq (by omega) s x.1 x.2 hx⟩

end
end StructuralNote.FixedSchurChartRegularity

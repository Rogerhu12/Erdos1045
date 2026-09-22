import StructuralNote.FixedSchurStationaryUniqueness
import StructuralNote.FixedSchurChartSelection

/-! Geometric extremality implies stationarity on the actual feasible chart. -/

namespace StructuralNote.FixedSchurGeometricStationarity

open Filter Erdos1045 Erdos1045.EventualExact
open FixedSchurEquationSmooth FixedSchurObjectivePaths FixedSchurStationaryUniqueness
open FixedSchurChart FixedSchurChartGeometry
open scoped Topology

noncomputable section

theorem eventual_geometric_extremal_stationary : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega)) (x : SchurParameters m),
      x ∈ FixedSchurChartSmooth.domain (by omega) →
      ExtremalNormalization.DiameterExtremal (configuration (by omega) s x.1 x.2) →
      Stationary (by omega) s x := by
  filter_upwards [eventual_geometric_properties] with m hgeo
  intro hm s x hx hmax
  apply global_max_stationary (by omega) s x hx
  intro y hy
  have hg := hgeo hm s y.1 y.2 hy
  exact Real.log_le_log (Configuration.discriminant_pos _ hg.injective) (hmax.2 _ hg.diameter)

theorem eventual_same_word_extremal_unique : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega)),
      ∀ x ∈ FixedSchurChartSmooth.domain (by omega), ∀ y ∈ FixedSchurChartSmooth.domain (by omega),
      ExtremalNormalization.DiameterExtremal (configuration (by omega) s x.1 x.2) →
      ExtremalNormalization.DiameterExtremal (configuration (by omega) s y.1 y.2) → x = y := by
  filter_upwards [eventual_geometric_extremal_stationary, eventual_stationary_unique] with m hstat huniq
  intro hm s x hx y hy hxmax hymax
  exact huniq hm s x hx y hy (hstat hm s x hx hxmax) (hstat hm s y hy hymax)

end
end StructuralNote.FixedSchurGeometricStationarity

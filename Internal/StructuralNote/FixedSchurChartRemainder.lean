import StructuralNote.FixedSchurRemainderIdentity
import StructuralNote.FixedSchurChartQuotients

/-! The exact analytic remainder identity on every actual fixed-Schur chart. -/

namespace StructuralNote.FixedSchurChartRemainder

open Complex Filter Erdos1045.EventualExact
open CommonDomainClosure FixedSchurChart FixedSchurLinear
open CommonFiberGeometry GeometricRelativeRemainder SignedPressureAngular
open FixedSchurRemainderIdentity FixedSchurRemainderScalar FixedSchurObjective
open scoped BigOperators Topology

noncomputable section

theorem eventual_remainder_identity : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      newRemainder (by omega) θ (FixedSchurLinear.center (coordinate (by omega) s θ v) v) =
        (∑ p : Fin (2 * m) × Fin (2 * m),
          (R (quotient (FixedSchurLinear.center (coordinate (by omega) s θ v) v)
              (root (2 * m)) p)
            (quotient (diameterVector θ - root (2 * m)) (root (2 * m)) p)).re) / 2 := by
  filter_upwards [eventual_coordinate_properties,
    FixedSchurChartQuotients.eventual_quotient_properties] with m hp hquot
  intro hm s θ v hdom
  have hq := hquot hm s θ v hdom
  exact newRemainder_eq_sum (by omega) θ _ hdom.1
    (FixedSchurLinear.center_halfPeriodic hm _ v (hp hm s θ v hdom).antiperiodic
      hdom.2.2.1.1)
    hq.1 (HessianAngularReference.root_injective (by omega))
    (fun p => (hq.2.2.2 p).trans_lt (by norm_num))

end
end StructuralNote.FixedSchurChartRemainder

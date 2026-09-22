import StructuralNote.FixedSchurObjective
import StructuralNote.FixedSchurChartRegularity

/-! Smoothness of the actual logarithmic discriminant objective on the chosen
fixed-Schur chart. -/

namespace StructuralNote.FixedSchurObjectiveSmooth

open Complex Filter
open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open CommonDomainClosure FixedSchurChart FixedSchurChartSmooth
open FixedSchurEquationSmooth
open FixedSchurChartGeometry FixedSchurChartRegularity FixedSchurObjective
open scoped Topology ContDiff

noncomputable section

theorem F_contDiffAt_of_injective {n : ℕ} {z : Fin n → ℂ}
    (hz : Function.Injective z) :
    ContDiffAt ℝ ∞ F z := by
  have hd : ContDiffAt ℝ ∞
      (fun w : Fin n → ℂ => Configuration.discriminant w) z := by
    unfold Configuration.discriminant
    apply contDiffAt_prod
    intro i _
    apply contDiffAt_prod
    intro j hj
    exact ((contDiffAt_apply ℝ ℂ i z).sub (contDiffAt_apply ℝ ℂ j z)).norm ℂ
      (sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hj) (hz h).symm))
  exact hd.log (Configuration.discriminant_pos z hz).ne'

theorem eventual_actual_objective_contDiffWithinAt : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (x : SchurParameters m), InDomain (by omega) x.1 x.2 →
      ContDiffWithinAt ℝ ∞
        (fun y : SchurParameters m =>
          F (FixedSchurChart.configuration (by omega) s y.1 y.2))
        (FixedSchurChartSmooth.domain (by omega)) x := by
  filter_upwards [eventual_configuration_contDiffWithinAt,
    eventual_geometric_properties] with m hconfig hgeo
  intro hm s x hx
  have hxdom : x ∈ FixedSchurChartSmooth.domain (by omega) := by
    exact hx
  have hconfig' := hconfig (by omega) s x hxdom
  have hgeom := hgeo hm s x.1 x.2 hx
  have hF := F_contDiffAt_of_injective hgeom.injective
  have hcomp := hF.comp_contDiffWithinAt x hconfig'
  simpa only [Function.comp_def] using hcomp

end
end StructuralNote.FixedSchurObjectiveSmooth

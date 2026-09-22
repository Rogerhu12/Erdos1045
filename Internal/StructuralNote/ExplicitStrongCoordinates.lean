import EventualExact.ExplicitLocalization
import StructuralNote.ExplicitPressureCoordinates
import StructuralNote.ExplicitStrongBudget

/-! Genuine diameter maximizers satisfy the strong budget above a closed threshold. -/

namespace StructuralNote.ExplicitStrongCoordinates

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization
open NormalizedPolarRepresentation ExtremalPolarCenter SchurLiftBounds
open SinglePressureEstimate
noncomputable section

def orderThreshold : ℕ :=
  max (ExplicitLocalization.localizationThreshold ExplicitStrongBudget.edgeTolerance)
    (max ExplicitPressureCoordinates.orderThreshold ExplicitStrongBudget.orderThreshold)

/-- No exterior model, energy estimate, pressure gap or local coordinate is an input. -/
theorem diameter_strong_coordinates {m : ℕ} {z : Points (2 * m)}
    (hz : ExtremalNormalization.DiameterExtremal z) (hn : orderThreshold ≤ 2 * m) :
    HasStrongCoordinates m z := by
  have hloc := (le_max_left _ _).trans hn
  have hpres := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hstrong := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hn256 : 256 ≤ 2 * m := (le_max_left _ _).trans hstrong
  have hm : 8 ≤ m := by omega
  obtain ⟨σ, α, β, u, η, hmodel, hboundary, hη⟩ :=
    ExplicitLocalization.extremal_localization (Or.inl hz) ExplicitStrongBudget.edgeTolerance_pos hloc
  have hη1024 : η ≤ 1 / 1024 := hη.le.trans (min_le_right _ _)
  obtain ⟨hc, hJ, herr, hG⟩ := ExplicitPressureCoordinates.model_pressure_coordinates
    (by omega : 2 ≤ m) hpres hη1024 hmodel hz hboundary
  have hmass := ActualSignedAngular.model_constraint_mass (show 2 ≤ m by omega)
    hmodel hη1024 hJ herr
  obtain ⟨hobj, hbudget⟩ := ExplicitStrongBudget.model_strong_budget hm hstrong hη.le
    hmodel hz hJ hc herr hG
  exact ⟨by omega, σ, α, β, u, η, hmodel, hc, hη1024, hmass, hG, hobj, hbudget⟩

/-- The same closed threshold also retains the scalar gap in the budget. -/
theorem diameter_scalar_gap_coordinates {m : ℕ} {z : Points (2 * m)}
    (hz : ExtremalNormalization.DiameterExtremal z) (hn : orderThreshold ≤ 2 * m) :
    MatchingActivityCrossingPressure.HasScalarGapCoordinates m z := by
  have hloc := (le_max_left _ _).trans hn
  have hpres := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hstrong := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hn256 : 256 ≤ 2 * m := (le_max_left _ _).trans hstrong
  have hm : 8 ≤ m := by omega
  obtain ⟨σ, α, β, u, η, hmodel, hboundary, hη⟩ :=
    ExplicitLocalization.extremal_localization (Or.inl hz) ExplicitStrongBudget.edgeTolerance_pos hloc
  have hη1024 : η ≤ 1 / 1024 := hη.le.trans (min_le_right _ _)
  obtain ⟨hc, hJ, herr, hG⟩ := ExplicitPressureCoordinates.model_pressure_coordinates
    (by omega : 2 ≤ m) hpres hη1024 hmodel hz hboundary
  have hmass := ActualSignedAngular.model_constraint_mass (show 2 ≤ m by omega)
    hmodel hη1024 hJ herr
  have hbudget := (ExplicitStrongBudget.model_scalar_gap_budget hm hstrong hη.le
    hmodel hz hJ hc herr hG).2
  refine ⟨by omega, σ, α, β, u, η, hmodel, hc, hη1024, hmass, hG, ?_⟩
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbudget

end
end StructuralNote.ExplicitStrongCoordinates

import EventualExact.ExplicitLocalizationNumerical
import EventualExact.AllOrderPerimeterExact

/-! A concrete threshold for perimeter rigidity, shared by all parities. -/

namespace Erdos1045.EventualExact.ExplicitPerimeter

open Erdos1045.Configuration HullGeometry GlobalProof
open ExplicitLocalization CommonLocalization
noncomputable section

/-- This integer suffices for perimeter rigidity and the odd diameter formula. -/
def orderThreshold : ℕ := 2 ^ 100000000

theorem localizationThreshold_le_orderThreshold :
    localizationThreshold (1 / 4000) ≤ orderThreshold :=
  ExplicitLocalizationNumerical.localizationThreshold_bound (by norm_num)

theorem orderThreshold_ge_four : 4 ≤ orderThreshold := by
  change 2 ^ 2 ≤ 2 ^ 100000000
  exact pow_le_pow_right₀ (a := (2 : ℕ)) (by decide) (show 2 ≤ 100000000 by decide)

/-- Explicit localization and strict local rigidity force every perimeter
maximizer above the displayed integer cutoff to be a regular polygon. -/
theorem perimeter_extremal_regular {n : ℕ} (hn : orderThreshold ≤ n)
    {z : Points n} (hz : PerimeterExtremal n z) : Configuration.IsRegular z := by
  have hn4 : 4 ≤ n := orderThreshold_ge_four.trans hn
  let H := classicalBackground_proved.toClassicalAnalysis.geometry
  obtain ⟨σ, α, β, u, η, hm, hboundary, hη⟩ :=
    extremal_localization (Or.inr hz) (by norm_num : (0 : ℝ) < 1 / 4000)
      (localizationThreshold_le_orderThreshold.trans hn)
  let v : Points n := fun i => LocalObjective.perturbedVertices n u i
  have hcoord : z ∘ σ = fun i => α + β * v i := by
    funext i
    exact hm.coordinates i
  have hinj : Function.Injective v :=
    LocalConfiguration.small_perturbation_injective ClosedFourier.geometricSine hn4 u
      hm.periodic hm.error_nonneg (by linarith) hm.relative_edges
  have hD : 0 < discriminant v := discriminant_pos v hinj
  have hL : 0 < boundaryLength v :=
    ExteriorLocalBridge.boundaryLength_pos_of_injective (by omega) hinj
  have hobj : objective (z ∘ σ) = objective v := by
    rw [hcoord]
    exact objective_affine v α β hm.scale_ne_zero hD hL
  have hmax : objective (regular n) ≤ objective (z ∘ σ) := by
    apply ExteriorLocalBridge.perimeterExtremal_objective H (by omega)
      (perimeterExtremal_perm H hz σ)
    rw [hullPerimeter_perm_proved]
    exact hboundary
  by_contra hnonregular
  have hv : ¬ Configuration.IsRegular v := by
    intro hv
    apply hnonregular
    apply isRegular_of_perm z σ
    rw [hcoord]
    exact isRegular_affine hv α β hm.scale_ne_zero
  have hstrict := LocalConfiguration.strict_local_rigidity ClosedFourier.dftInversion
    ClosedFourier.geometricSine LocalNonlinear.scalarLogTaylor hn4
    (ClosedFourier.orthogonality n (by omega)) u hm.periodic hm.error_nonneg
    hη.le hm.relative_edges hv
  exact (not_lt_of_ge (hobj ▸ hmax)) hstrict

/-- The sharp homogeneous perimeter bound, including its equality case. -/
theorem sharp_perimeter {n : ℕ} (hn : orderThreshold ≤ n) (z : Points n) :
    discriminant z ≤ AllOrderPerimeterExact.sharpBound n (hullPerimeter z) ∧
    (discriminant z = AllOrderPerimeterExact.sharpBound n (hullPerimeter z) ↔
      hullPerimeter z = 0 ∨ Configuration.IsRegular z) := by
  have hn3 : 3 ≤ n := by have := orderThreshold_ge_four.trans hn; omega
  exact ⟨AllOrderPerimeterExact.sharp_of_regular_extremals hn3
      (fun _ hz => perimeter_extremal_regular hn hz) z,
    AllOrderPerimeterExact.equality_of_regular_extremals hn3
      (fun _ hz => perimeter_extremal_regular hn hz) z⟩

/-- Exact odd diameter-two maximum and rigidity at the same explicit cutoff. -/
theorem odd_diameter_two_exact {n : ℕ} (hn : orderThreshold ≤ n) (hodd : Odd n) :
    (∀ z : Points n, DiameterAtMost 2 z → discriminant z ≤ diameterTwoMaximum n) ∧
    (DiameterAtMost 2 (diameterTwoRegular n) ∧
      discriminant (diameterTwoRegular n) = diameterTwoMaximum n) ∧
    (∀ z : Points n, DiameterAtMost 2 z → discriminant z = diameterTwoMaximum n →
      Configuration.IsRegular z) := by
  let H := classicalBackground_proved.toClassicalAnalysis.geometry
  have hn3 : 3 ≤ n := by have := orderThreshold_ge_four.trans hn; omega
  have hr := fun z (hz : PerimeterExtremal n z) => perimeter_extremal_regular hn hz
  exact ⟨fun z hz => diameter_two_bound_of_regular_extremals H hn3 hr z hz,
    ⟨diameterTwoRegular_diameter H hn3 hodd, diameterTwoRegular_discriminant H hn3⟩,
    fun z hz hD => diameter_two_equality_isRegular H hn3 hr z hz hD⟩

end
end Erdos1045.EventualExact.ExplicitPerimeter

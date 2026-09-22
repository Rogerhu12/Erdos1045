import StructuralNote.FixedSchurLinear
import StructuralNote.CommonDomainClosure
import StructuralNote.CommonDomainRadius
import StructuralNote.StrongObjectiveEstimate

/-! The exact projection from an actual half-periodic center into the fixed
Schur free-center space, together with the eventual strict energy-domain
wrapper.  No actual-maximizer or polar-coordinate hypothesis is used here. -/

namespace StructuralNote.FixedSchurProjectionDomain

open scoped BigOperators

open Erdos1045 Erdos1045.EventualExact
open Filter SchurSpectrum SchurLift
open CommonDomainClosure CommonDomainRadius CommonTangentialParameters
open FixedSchurLinear StrongObjectiveEstimate

noncomputable section

theorem projection_parameterSpace {m : ℕ} (hm : 2 ≤ m)
    {C : Fin (2 * m) → ℂ} (hC : HalfPeriodic (by omega) C)
    (hmean : (∑ j, C j) = 0) :
    ParameterSpace (by omega) (projection hm C) := by
  have hq : FiniteBox.Antiperiodic (by omega) (constraint (by omega) C) :=
    actual_constraint_antiperiodic (by omega) C hC
  have hlift : HalfPeriodic (by omega)
      (canonicalLift (constraint (by omega) C)) :=
    canonicalLift_halfTurn hm (constraint (by omega) C) hq
  have hv : HalfPeriodic (by omega) (projection hm C) := by
    intro j
    unfold projection
    simp only [Pi.sub_apply]
    rw [hC j, hlift j]
  have hsum : (∑ j, projection hm C j) = 0 := by
    simp only [projection, Pi.sub_apply, Finset.sum_sub_distrib, hmean,
      canonicalLift_mean_zero (show 0 < 2 * m by omega), sub_zero]
  exact ⟨hv, hsum, projection_constraint hm C⟩

theorem center_projection {m : ℕ} (hm : 2 ≤ m) (C : Fin (2 * m) → ℂ) :
    center (constraint (by omega) C) (projection hm C) = C := by
  funext j
  simp only [center, projection, Pi.add_apply, Pi.sub_apply]
  ring

theorem residualEnergy_eq_projection {m : ℕ} (hm : 2 ≤ m) (C : Fin (2 * m) → ℂ) :
    residualEnergy (by omega) C = pairEnergy (by omega) (projection hm C) := by
  rfl

theorem eventually_projection_inDomain (K : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ) (C : Fin (2 * m) → ℂ),
        HalfPeriodic (by omega) (fun j => (θ j : ℂ)) →
        (∑ j, (θ j : ℂ)) = 0 →
        HalfPeriodic (by omega) C →
        (∑ j, C j) = 0 →
        pairEnergy (by omega) (fun j => (θ j : ℂ)) +
            pairEnergy (by omega) (projection hm C) ≤ K / (2 * m : ℝ) ^ 2 →
        InDomain (by omega) θ (projection hm C) := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  have hstrict : ∀ᶠ m : ℕ in atTop,
      K / (2 * m : ℝ) ^ 2 < energyRadius (2 * m) := by
    filter_upwards [hnat.eventually (fixed_inner_radius_eventually_lt K)] with m hm
    simpa only [Set.mem_ofPred_eq, Nat.cast_mul, Nat.cast_ofNat] using hm
  filter_upwards [hstrict] with m hstrict
  intro hm θ C hθ hθmean hC hCmean henergy
  exact ⟨hθ, hθmean, projection_parameterSpace hm hC hCmean,
    henergy.trans_lt hstrict⟩

end
end StructuralNote.FixedSchurProjectionDomain

import StructuralNote.RationalCommonConfiguration
import StructuralNote.CommonSelectorRoot

/-! The geometric selector (10.7)--(10.9) in actual rational coordinates.
Energy-domain membership and the unique small closure root follow from its
displayed inequalities and the proved reconstruction identities. -/

namespace StructuralNote.RationalBranchSelector

open Erdos1045.EventualExact LensClosure SchurSpectrum
open RationalCommonConfiguration CommonSelectorRoot CommonDomainClosure CommonDomainRadius
open CommonTangentialParameters
open scoped BigOperators
noncomputable section

def EnergyWindow {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) : Prop :=
  pairEnergy (by omega) (fun j => (theta hm X j : ℂ)) + pairEnergy (by omega) (recoveredVector hm σ X) <
    energyRadius (2 * m)

def Selected {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) : Prop :=
  RationalAngleBranch.SmallWindow X ∧ Function.Injective (RationalConfiguration.configuration hm σ X) ∧
    ‖recoveredCorrection hm σ X‖ < rootWindow (2 * m) ∧ EnergyWindow hm σ X

theorem energyWindow_iff_inDomain {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) :
    EnergyWindow (by omega) σ X ↔ InDomain (by omega) (theta (by omega) X) (recoveredVector (by omega) σ X) := by
  constructor
  · intro h
    exact ⟨theta_halfPeriodic (by omega) X, theta_mean_zero (by omega) X,
      RationalBranchRecovery.freeVector_mem hm _, h⟩
  · exact fun h => h.2.2.2

theorem sign_bound {s : ℝ} (hs : s ^ 2 = 1) : |s| ≤ 1 := by
  nlinarith [sq_abs s, abs_nonneg s]

theorem selected_inDomain {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (hX : Selected (by omega) σ X) :
    InDomain (by omega) (theta (by omega) X) (recoveredVector (by omega) σ X) :=
  (energyWindow_iff_inDomain hm σ X).1 hX.2.2.2

/-- On every selected closed configuration, the correction is the already
constructed common-fiber root; no separate root-identification premise remains. -/
theorem eventual_selected_root_identification :
    ∃ N : ℕ, ∀ (m : ℕ) (hm : N + 1048576 ≤ m) (σ : Fin m → ℝ)
      (X : RationalConfiguration.Variables m → ℝ),
      (∀ j, σ j ^ 2 = 1) → RationalConfiguration.closure (by omega) σ X = 0 →
      Selected (by omega) σ X →
      ‖recoveredCorrection (by omega) σ X‖ ≤ 1024 / (2 * m : ℝ) ^ 2 ∧
      ∀ η : ℂ, ‖η‖ < rootWindow (2 * m) →
        closure (CommonClosureEnergy.phase (by omega) (theta (by omega) X))
          (fun j => 2 * Real.cos (CommonClosureEnergy.halfAngle (by omega) (theta (by omega) X) j))
          σ (coordinates (by omega) (recoveredVector (by omega) σ X)) η = 0 →
        η = recoveredCorrection (by omega) σ X := by
  obtain ⟨N, hN⟩ := eventual_common_domain_window_root
  refine ⟨N, ?_⟩
  intro m hm σ X hσ hH hX
  obtain ⟨ξ, hb, _, _, huniq⟩ := hN m hm (theta (by omega) X) (recoveredVector (by omega) σ X) σ
    (selected_inDomain (by omega) σ X hX) (fun j => sign_bound (hσ j))
  have he := huniq (recoveredCorrection (by omega) σ X) hX.2.2.1
    (recovered_closure_zero (by omega) σ X hX.1 hσ hH)
  refine ⟨?_, ?_⟩
  · rw [he]
    exact hb
  intro η hη hz
  exact (huniq η hη hz).trans he.symm

theorem pair_distance_eq {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (hX : RationalAngleBranch.SmallWindow X)
    (hσ : ∀ j, σ j ^ 2 = 1) (hH : RationalConfiguration.closure (by omega) σ X = 0) (i j : Fin (2 * m)) :
    ‖CommonFiberGeometry.configuration (by omega) (theta (by omega) X) (recoveredVector (by omega) σ X)
      σ (recoveredCorrection (by omega) σ X) i -
      CommonFiberGeometry.configuration (by omega) (theta (by omega) X) (recoveredVector (by omega) σ X)
        σ (recoveredCorrection (by omega) σ X) j‖ =
    ‖RationalConfiguration.configuration (by omega) σ X i - RationalConfiguration.configuration (by omega) σ X j‖ := by
  rw [configuration_eq_rigid_motion hm σ X hX hσ hH, configuration_eq_rigid_motion hm σ X hX hσ hH,
    ← mul_sub, norm_mul, norm_unit, one_mul]
  congr 1
  ring

theorem diameterAtMost_iff {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (hX : RationalAngleBranch.SmallWindow X)
    (hσ : ∀ j, σ j ^ 2 = 1) (hH : RationalConfiguration.closure (by omega) σ X = 0) (d : ℝ) :
    Erdos1045.Configuration.DiameterAtMost d
      (CommonFiberGeometry.configuration (by omega) (theta (by omega) X) (recoveredVector (by omega) σ X)
        σ (recoveredCorrection (by omega) σ X)) ↔
      Erdos1045.Configuration.DiameterAtMost d (RationalConfiguration.configuration (by omega) σ X) := by
  simp only [Erdos1045.Configuration.DiameterAtMost, pair_distance_eq hm σ X hX hσ hH]

theorem discriminant_eq {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (hX : RationalAngleBranch.SmallWindow X)
    (hσ : ∀ j, σ j ^ 2 = 1) (hH : RationalConfiguration.closure (by omega) σ X = 0) :
    Erdos1045.Configuration.discriminant
      (CommonFiberGeometry.configuration (by omega) (theta (by omega) X) (recoveredVector (by omega) σ X)
        σ (recoveredCorrection (by omega) σ X)) =
      Erdos1045.Configuration.discriminant (RationalConfiguration.configuration (by omega) σ X) := by
  simp only [Erdos1045.Configuration.discriminant, pair_distance_eq hm σ X hX hσ hH]

end
end StructuralNote.RationalBranchSelector

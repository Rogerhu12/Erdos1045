import StructuralNote.FixedSchurRationalStationarySelection
import StructuralNote.ReusedEvenLift

/-! The selected algebraic branch computes the actual diameter supremum. -/

namespace StructuralNote.RewrittenEvenAlgebraicMaximum

open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open RationalStationarySystem FixedSchurRationalWindowDomain
open FixedSchurRationalStationarySelection CommonDomainRadius
open FixedSchurCanonicalWordSymmetry
open FixedSchurRationalClosureMatrix
noncomputable section

theorem eventual_even_maximum_selected_root :
    ∃ m₀ : ℕ, ∀ m ≥ m₀,
      ∃ (hm : 3 ≤ m) (Y : RationalStationarySystem.Variables m → ℝ),
        let s := canonicalPattern hm
        selectedWindowEnergy (by omega) s (coordinates Y) <
          (logOrder (2 * m) : ℝ)^2 / (8 * (2 * m : ℝ)^2) ∧
        Stationary (by omega) (halfWord s) Y ∧
        (∀ Z : RationalStationarySystem.Variables m → ℝ,
          selectedWindowEnergy (by omega) s (coordinates Z) <
            (logOrder (2 * m) : ℝ)^2 / (8 * (2 * m : ℝ)^2) →
          Stationary (by omega) (halfWord s) Z → Z = Y) ∧
        M (2 * m) = discriminant
          (RationalConfiguration.configuration (by omega) (rationalSign s) (coordinates Y)) ∧
        IsAlgebraic ℚ (M (2 * m)) := by
  obtain ⟨m₀, hroot⟩ := eventual_actual_extremizer_unique_algebraic_root
  refine ⟨max m₀ 1, ?_⟩
  intro m hm
  obtain ⟨z, hz⟩ := WholeBoxLowerBound.exists_diameterExtremal (show 0 < 2 * m by omega)
  obtain ⟨hm3, x, Y, _, _, _, _, hwindow, hcoords, hstationary, _, _, _, huniq,
    _, _, _, halg, hdisc⟩ := hroot m (by omega) z hz
  have hM : M (2 * m) = discriminant z :=
    (M_eq_verified_diameterMaximum _).trans
      (WholeBoxLowerBound.diameterMaximum_eq_of_extremal hz)
  refine ⟨hm3, Y, ?_, hstationary, huniq, ?_, ?_⟩
  · simpa only [hcoords] using hwindow
  · rw [hcoords]
    exact hM.trans hdisc.symm
  · rwa [hdisc, ← hM] at halg

theorem eventual_even_maximum_algebraic :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, IsAlgebraic ℚ (M (2 * m)) := by
  obtain ⟨m₀, h⟩ := eventual_even_maximum_selected_root
  refine ⟨m₀, fun m hm => ?_⟩
  obtain ⟨_, _, _, _, _, _, halg⟩ := h m hm
  exact halg

end
end StructuralNote.RewrittenEvenAlgebraicMaximum

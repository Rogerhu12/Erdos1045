import StructuralNote.FixedSchurWordStability
import StructuralNote.FixedSchurLiftStability

/-! A change at finitely many word sites costs order 1/n in center energy,
while retaining exactly the same angle and free-center parameters. -/

namespace StructuralNote.FixedSchurWordEnergy

open Complex Filter Erdos1045.EventualExact
open SchurSpectrum SchurLiftBounds CommonDomainClosure
open FixedSchurLinear FixedSchurChart FixedSchurWordStability FixedSchurLiftStability
open scoped BigOperators Topology

noncomputable section

theorem eventual_meanSquare_stability : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s t : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      meanSquare (coordinate (by omega) s θ v - coordinate (by omega) t θ v) ≤
        200 * ((Finset.univ.filter
          (fun j => FiniteBox.patternSign s j ≠ FiniteBox.patternSign t j)).card : ℝ) /
            (2 * m : ℝ) := by
  classical
  filter_upwards [eventual_coordinate_properties, eventual_coordinate_l1_stability]
    with m hprops hstable
  intro hm s t θ v hdom
  have hs := hstable hm s t θ v hdom
  have hq := hprops hm s θ v hdom
  have hr := hprops hm t θ v hdom
  have hms := meanSquare_sub_le_l1 _ _ hq.norm_le hr.norm_le
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hms
  apply hms.trans
  calc
    _ ≤ 10 * (20 * ((Finset.univ.filter
        (fun j => FiniteBox.patternSign s j ≠ FiniteBox.patternSign t j)).card : ℝ)) /
          (2 * m : ℝ) := by gcongr
    _ = _ := by ring

theorem eventual_center_energy_stability : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s t : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      pairEnergy (by omega)
        (center (coordinate (by omega) s θ v) v - center (coordinate (by omega) t θ v) v) ≤
        6400 * ((Finset.univ.filter
          (fun j => FiniteBox.patternSign s j ≠ FiniteBox.patternSign t j)).card : ℝ) /
            (2 * m : ℝ) := by
  classical
  filter_upwards [eventual_coordinate_properties, eventual_coordinate_l1_stability]
    with m hprops hstable
  intro hm s t θ v hdom
  have hs := hstable hm s t θ v hdom
  have hq := hprops hm s θ v hdom
  have hr := hprops hm t θ v hdom
  have he := center_difference_energy_le hm _ _ v hq.antiperiodic hr.antiperiodic
    hq.norm_le hr.norm_le
  apply he.trans
  calc
    _ ≤ 320 * (20 * ((Finset.univ.filter
        (fun j => FiniteBox.patternSign s j ≠ FiniteBox.patternSign t j)).card : ℝ)) /
          (2 * m : ℝ) := by gcongr
    _ = _ := by ring

end
end StructuralNote.FixedSchurWordEnergy

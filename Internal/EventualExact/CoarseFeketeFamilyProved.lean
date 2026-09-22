import EventualExact.CoarseFeketeFamily
import Erdos1045.Main

/-! Discharge the classical analysis package by the verified exterior theory.
The final construction starts from normalized Fekete points and obtains the
ordered exterior data from the proved existence theorem. No parity is used. -/

namespace Erdos1045.EventualExact.CoarseFekete

open Filter
open scoped Topology
open Configuration HullGeometry ExteriorClassical MatrixDefect
noncomputable section

theorem Family.coarse_control_proved (s : Family) :
    ∃ C K D : ℝ, 0 < C ∧ 0 ≤ K ∧ 0 ≤ D ∧ ∀ᶠ j in atTop,
      (1 / 2 : ℝ) ≤ s.capacity j ∧
      FaberFourier.H1Sampling (fun i : Fin (s.size j) => (s.data j).angles.angle i) C ∧
      (s.size j : ℝ) ^ 2 * s.energySquared j ≤ K ∧ s.matrixError j ≤ D :=
  s.coarse_control classicalBackground_proved.toClassicalAnalysis

/-- Uniform inverse-square Laurent energy for normalized Fekete families of all orders. -/
theorem Family.inverse_square_energy_bounded (s : Family) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ j in atTop,
      (s.size j : ℝ) ^ 2 * (s.data j).energySquared ≤ K := by
  obtain ⟨C, K, D, hC, hK, hD, h⟩ := s.coarse_control_proved
  exact ⟨K, hK, h.mono fun _ hj => hj.2.2.1⟩

theorem Family.capacity_tendsto_one_proved (s : Family) :
    Tendsto s.capacity atTop (𝓝 1) :=
  s.capacity_tendsto_one classicalBackground_proved.toClassicalAnalysis

theorem Family.matrix_defect_bounded_proved (s : Family) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ j in atTop,
      0 ≤ defect (normalize (s.data j).matrix) ∧ defect (normalize (s.data j).matrix) ≤ D :=
  s.matrix_defect_bounded classicalBackground_proved.toClassicalAnalysis

theorem Family.circleEnergy_bounded_proved (s : Family) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ j in atTop, 0 ≤ s.circleEnergy j ∧ s.circleEnergy j ≤ D :=
  s.circleEnergy_bounded classicalBackground_proved.toClassicalAnalysis

theorem fekete_perm {n : ℕ} {z : Points n} (hz : Fekete z) (σ : Equiv.Perm (Fin n)) :
    Fekete (z ∘ σ) := by
  intro w hw
  rw [discriminant_perm]
  apply hz w
  simpa only [hull, σ.surjective.range_comp] using hw

/-- The exterior-map inputs are constructed from ordinary normalized Fekete
hypotheses. The only relabeling is the counterclockwise boundary order. -/
theorem normalized_fekete_inverse_square_energy {N : ℕ → ℕ}
    (hN4 : ∀ j, 4 ≤ N j) (hN : Tendsto N atTop atTop) (z : ∀ j, Points (N j))
    (hinj : ∀ j, Function.Injective (z j))
    (hP : ∀ j, hullPerimeter (z j) = 2 * Real.pi)
    (hF : ∀ j, Fekete (z j))
    (hΔ : ∀ j, (N j : ℝ) ^ N j ≤ discriminant (z j)) :
    ∃ σ : ∀ j, Equiv.Perm (Fin (N j)), ∃ d : ∀ j, ExteriorData (z j ∘ σ j),
      (∀ j, FaberIdentities (d j)) ∧ ∃ K : ℝ, 0 ≤ K ∧
        ∀ᶠ j in atTop, (N j : ℝ) ^ 2 * (d j).energySquared ≤ K := by
  classical
  have hmodel (j : ℕ) : ∃ σ : Equiv.Perm (Fin (N j)), Nonempty
      {d : ExteriorData (z j ∘ σ) // FaberIdentities d} :=
    classicalBackground_proved.exterior.model (N j) (by have := hN4 j; omega)
      (z j) (hinj j) (hP j) (hF j)
  choose σ hdata using hmodel
  let chosen (j : ℕ) := Classical.choice (hdata j)
  let s : Family :=
    { size := N
      size_ge := hN4
      size_tendsto := hN
      points := fun j => z j ∘ σ j
      injective := fun j => (hinj j).comp (σ j).injective
      fekete := fun j => fekete_perm (hF j) (σ j)
      discriminant_ge := fun j => by rw [discriminant_perm]; exact hΔ j
      data := fun j => (chosen j).val
      identities := fun j => (chosen j).property }
  exact ⟨σ, fun j => (chosen j).val, fun j => (chosen j).property,
    s.inverse_square_energy_bounded⟩

end
end Erdos1045.EventualExact.CoarseFekete

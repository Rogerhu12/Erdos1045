import StructuralNote.SinglePressureEstimate

/-! The unconditional O(n^-2) comparison of the actual even extremum with the finite box maximum. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.StrongBoxComparison

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization
open SchurSpectrum DiscreteEnergy ExtremalPolarCenter NormalizedPolarRepresentation
open SignedPressureRemainder StrongObjectiveEstimate SinglePressureEstimate

theorem comparisonConstant_nonneg : 0 ≤ comparisonConstant := by
  unfold comparisonConstant objectiveConstant ActualPressureAbsorption.pressureConstant
    PressureAngularAbsorption.angularConstant
  positivity

/-- The finite-box comparison contains the true diameter extremal value `M`.
Both error bounds follow from actual feasible competitors and actual maximizers. -/
theorem eventual_even_box_comparison :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ hm : 0 < m,
      -1000000 / ((2 * m : ℕ) : ℝ) ^ 2 ≤
        Real.log (M (2 * m) / ((2 * m : ℕ) : ℝ) ^ (2 * m)) - FiniteBox.B hm ∧
      Real.log (M (2 * m) / ((2 * m : ℕ) : ℝ) ^ (2 * m)) - FiniteBox.B hm ≤
        comparisonConstant / ((2 * m : ℕ) : ℝ) ^ 2 := by
  obtain ⟨m₀, h₀⟩ := eventual_diameter_single_pressure
  refine ⟨max m₀ 128, ?_⟩
  intro m hm
  have hmpos : 0 < m := by omega
  obtain ⟨z, hz⟩ := WholeBoxLowerBound.exists_diameterExtremal (show 0 < 2 * m by omega)
  obtain ⟨hmp, σ, α, β, u, η, h, _, _, _, _, hupper, _⟩ := h₀ m (by omega) z hz
  have hM : M (2 * m) = discriminant z :=
    (M_eq_verified_diameterMaximum _).trans (WholeBoxLowerBound.diameterMaximum_eq_of_extremal hz)
  have hn : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by positivity
  have hDz : 0 < discriminant z := (pow_pos hn (2 * m)).trans_le (hz.discriminant_ge (by omega))
  have hlog : Real.log (M (2 * m) / ((2 * m : ℕ) : ℝ) ^ (2 * m)) =
      Real.log (discriminant z) - ((2 * m : ℕ) : ℝ) * Real.log (2 * m : ℕ) := by
    rw [hM, Real.log_div hDz.ne' (pow_pos hn _).ne', Real.log_pow]
  have hτ : 0 ≤ radialMass m β u := by
    unfold radialMass
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun j _ => sub_nonneg.mpr
      (PolarRepresentation.model_radius_le_one hmpos h hz.1 j)
  have hD : 0 ≤ residualEnergy (by omega) (polarCenter m β u) := pairEnergy_nonneg (by omega) _
  have hE : 0 ≤ realEnergy (by omega) (normalizedAngle m u) := pairEnergy_nonneg (by omega) _
  refine ⟨hmpos, ?_, ?_⟩
  · have hlo := even_box_lower_bound (show 256 ≤ 2 * m by omega)
    rw [neg_div]
    linarith only [hlo]
  · rw [hlog]
    linarith only [hupper, hτ, hD, hE]

theorem eventual_even_box_absolute_error :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ hm : 0 < m,
      |Real.log (M (2 * m) / ((2 * m : ℕ) : ℝ) ^ (2 * m)) - FiniteBox.B hm| ≤
        (comparisonConstant + 1000000) / ((2 * m : ℕ) : ℝ) ^ 2 := by
  obtain ⟨m₀, h₀⟩ := eventual_even_box_comparison
  refine ⟨m₀, ?_⟩
  intro m hm
  obtain ⟨hmp, hlo, hup⟩ := h₀ m hm
  refine ⟨hmp, abs_le.mpr ⟨?_, ?_⟩⟩
  · rw [add_div]
    rw [neg_div] at hlo
    have hh : 0 ≤ comparisonConstant / ((2 * m : ℕ) : ℝ) ^ 2 :=
      div_nonneg comparisonConstant_nonneg (sq_nonneg _)
    linarith only [hlo, hh]
  · rw [add_div]
    have hh : 0 ≤ 1000000 / ((2 * m : ℕ) : ℝ) ^ 2 := by positivity
    linarith only [hup, hh]

end StructuralNote.StrongBoxComparison

import StructuralNote.RewrittenMainUniqueness

/-! Attainment and uniqueness stated directly for the literal suprema. -/

namespace StructuralNote.RewrittenMaxima

open Erdos1045 Erdos1045.Configuration Erdos1045.HullGeometry Erdos1045.EventualExact
open FixedSchurActualRigidEquivalence RewrittenMainUniqueness
noncomputable section

theorem diameterExtremal_iff_attains {n : ℕ} (hn : 0 < n) (z : Points n) :
    ExtremalNormalization.DiameterExtremal z ↔ DiameterAtMost 2 z ∧ discriminant z = M n := by
  constructor
  · intro hz
    exact ⟨hz.1, ((M_eq_verified_diameterMaximum n).trans
      (WholeBoxLowerBound.diameterMaximum_eq_of_extremal hz)).symm⟩
  · rintro ⟨hz, hD⟩
    refine ⟨hz, fun w hw => ?_⟩
    rw [hD, M_eq_verified_diameterMaximum]
    exact WholeBoxLowerBound.discriminant_le_diameterMaximum hn w hw

theorem eventual_diameter_maximum_attained_unique :
    ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n ≥ n₀,
      (∃ z : Points n, DiameterAtMost 2 z ∧ discriminant z = M n) ∧
      ∀ z w : Points n, DiameterAtMost 2 z → discriminant z = M n →
        DiameterAtMost 2 w → discriminant w = M n → DirectRigidRelabeling z w := by
  obtain ⟨n₀, hn₀, huniq⟩ := eventual_diameter_extremizers_unique
  refine ⟨n₀, hn₀, fun n hn => ⟨M_attained (by omega), ?_⟩⟩
  intro z w hz hDz hw hDw
  exact huniq n hn z w ((diameterExtremal_iff_attains (by omega) z).2 ⟨hz, hDz⟩)
    ((diameterExtremal_iff_attains (by omega) w).2 ⟨hw, hDw⟩)

theorem W_attained {n : ℕ} (hn : 0 < n) :
    ∃ z : Points n, hullPerimeter z ≤ 2 * Real.pi ∧ discriminant z = W n := by
  obtain ⟨z, hz⟩ := exists_perimeterExtremal
    classicalBackground_proved.toClassicalAnalysis.geometry hn
  refine ⟨z, hz.1, ?_⟩
  symm
  apply supremum_eq_of_attained_bound
  · exact ⟨z, hz.1, rfl⟩
  · rintro x ⟨w, hw, rfl⟩
    exact hz.2 w hw

end
end StructuralNote.RewrittenMaxima

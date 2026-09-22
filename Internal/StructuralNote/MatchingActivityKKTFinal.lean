import StructuralNote.MatchingActivityKKTOriginalCertificate
import StructuralNote.MatchingActivityKKTPositive

/-! The original point set has a unique strictly positive active KKT
certificate. No multiplier positivity or coordinate estimates are assumptions
of the eventual endpoint. -/

namespace StructuralNote.MatchingActivityKKTFinal

open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open MatchingActivityKKTOriginalCertificate MatchingActivityKKTPositive
open CommonClosureEnergy FiniteFourierLift NormalizedPolarRepresentation
open MatchingActivityRadialActual MatchingActivityActualChartSelection
open ActualCrossingGeometry MatchingActivityNonlocal FourierMultiplier
open StrongPointwiseCoordinates MatchingActivityCrossingExclusivity
open MatchingActivityActiveConstraintDifferentials
noncomputable section

structure PositiveOriginalCertificate {m : ℕ} (z : Points (2 * m)) (hm : 0 < m)
    (π : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ)
    extends OriginalCertificate z hm π α β u η where
  matching_pos : ∀ i, 0 < original.matching i
  crossing_pos : ∀ i, 0 < original.crossing i

def OriginalCertificate.withPositive {m : ℕ} {z : Points (2 * m)} {hm : 0 < m}
    {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (C : OriginalCertificate z hm π α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z) :
    PositiveOriginalCertificate z hm π α β u η where
  toOriginalCertificate := C
  matching_pos := by
    intro i
    rw [C.matching_eq]
    exact (model_actual_multipliers_positive C.conditions.large
      C.model hz C.conditions C.normalized i).1
  crossing_pos := by
    intro i
    rw [C.crossing_eq]
    exact (model_actual_multipliers_positive C.conditions.large
      C.model hz C.conditions C.normalized i).2

theorem eventual_positive_original_certificate :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (π : Equiv.Perm (Fin (2 * m))) (α β : ℂ)
        (u : ℕ → ℂ) (η : ℝ),
        Nonempty (PositiveOriginalCertificate z hm π α β u η) := by
  obtain ⟨m₀, hcertificate⟩ := eventual_actual_maximizer_original_certificate
  refine ⟨m₀, ?_⟩
  intro m hm z hz
  obtain ⟨hmp, π, α, β, u, η, ⟨C⟩⟩ := hcertificate m hm z hz
  exact ⟨hmp, π, α, β, u, η, ⟨OriginalCertificate.withPositive C hz⟩⟩

/-- Complementary slackness for the original matching squared distances. -/
theorem matching_complementary_slackness {m : ℕ} {z : Points (2 * m)} {hm : 0 < m}
    {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (C : PositiveOriginalCertificate z hm π α β u η) (i : Fin m) :
    C.original.matching i * (‖z (π (matchingFirst i)) -
      z (π (matchingSecond hm i))‖ ^ 2 - 4) = 0 := by
  have hm2 : 2 ≤ m := by have := C.conditions.large; omega
  rw [model_normalized_distance C.model,
    normalized_matching_active hm2 β u C.model.periodic C.conditions.saturated i]
  ring

/-- The two crossing branches satisfy complementary slackness for the actual
original squared-distance constraints, with exactly one positive branch. -/
theorem crossing_complementary_slackness {m : ℕ} {z : Points (2 * m)} {hm : 0 < m}
    {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (C : PositiveOriginalCertificate z hm π α β u η) (i : Fin m) :
    let s : Fin m → ℝ := fun j => activeHalfSign hm (normalizedAngle m u)
      (modelRadii m β u) (actualCenter m β u) j
    let lp := plusMultiplier s C.original.crossing i
    let lm := minusMultiplier s C.original.crossing i
    0 ≤ lp ∧ 0 ≤ lm ∧
      lp * (‖z (π (successor (by omega) (halfIndex i))) -
        z (π (halfTurn hm (halfIndex i)))‖ ^ 2 - 4) = 0 ∧
      lm * (‖z (π (halfIndex i)) -
        z (π (halfTurn hm (successor (by omega) (halfIndex i))))‖ ^ 2 - 4) = 0 ∧
      lp * lm = 0 ∧ 0 < lp + lm := by
  have hm2 : 2 ≤ m := by have := C.conditions.large; omega
  have hp : ‖z (π (successor (by omega) (halfIndex i))) -
      z (π (halfTurn hm (halfIndex i)))‖ =
      ‖plusCrossingVector hm (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i‖ := by
    rw [model_normalized_distance C.model,
      normalized_plus_crossing hm2 β u C.model.periodic C.conditions.saturated i]
  have hn : ‖z (π (halfIndex i)) -
      z (π (halfTurn hm (successor (by omega) (halfIndex i))))‖ =
      ‖minusCrossingVector hm (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i‖ := by
    rw [model_normalized_distance C.model,
      normalized_minus_crossing hm2 β u C.model.periodic C.conditions.saturated i]
  dsimp only
  rw [hp, hn]
  rcases C.conditions.active i with hactive | hactive
  · norm_num [plusMultiplier, minusMultiplier, activeHalfSign, hactive.1,
      C.crossing_pos i, (C.crossing_pos i).le]
  · norm_num [plusMultiplier, minusMultiplier, activeHalfSign, ne_of_lt hactive.1,
      hactive.2, C.crossing_pos i, (C.crossing_pos i).le]

end
end StructuralNote.MatchingActivityKKTFinal

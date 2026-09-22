import Erdos1045.Statement
import StructuralNote.ExplicitKKTThreshold

open StructuralNote

/-! Proof adapter from the internal normalized-coordinate construction to the
public KKT statement.  No implementation object occurs in the public type. -/

namespace Erdos1045.Statement.KKT

open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open StructuralNote.MatchingActivityActiveConstraintDifferentials
open StructuralNote.MatchingActivityActiveEdgeCover
open StructuralNote.MatchingActivityKKTAnalytic
open StructuralNote.MatchingActivityKKTRigidTransport
open StructuralNote.MatchingActivityKKTOriginalCertificate
open StructuralNote.MatchingActivityKKTFinal
open StructuralNote.CommonClosureEnergy
open StructuralNote.MatchingActivityActualChartSelection
open StructuralNote.MatchingActivityRadialActual
open NormalizedPolarRepresentation
open StructuralNote.ActualCrossingGeometry
open StructuralNote.StrongPointwiseCoordinates
open scoped BigOperators

noncomputable section

/-- Forget the normalized-coordinate implementation of a certificate, keeping
only its original vertices, complete active edge family, and KKT data. -/
def ofPositiveOriginalCertificate {m : ℕ} {z : Points (2 * m)} {hm : 0 < m}
    {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (C : PositiveOriginalCertificate z hm π α β u η) : PositiveKKT z := by
  let s : Fin m → ℝ := fun i =>
    activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) i
  let first : ActiveIndex m → Fin (2 * m)
    | .inl i => π (matchingFirst i)
    | .inr i => π (selectedFirst hm s i)
  let second : ActiveIndex m → Fin (2 * m)
    | .inl i => π (matchingSecond hm i)
    | .inr i => π (selectedSecond hm s i)
  let multiplier : ActiveIndex m → ℝ
    | .inl i => C.original.matching i
    | .inr i => C.original.crossing i
  have hlog :
      (Erdos1045.Statement.KKT.logDiscriminant :
        Erdos1045.Statement.Points (2 * m) → ℝ) =
      (StructuralNote.MatchingActivityKKTAnalytic.logDiscriminant :
        Erdos1045.Configuration.Points (2 * m) → ℝ) := by
    rfl
  refine
    { first := first
      second := second
      active_exact := ?_
      licq := ?_
      multiplier := multiplier
      positive := ?_
      stationarity := ?_
      unique := ?_
      complementary_slackness := ?_ }
  · intro p q
    constructor
    · intro hpq
      have hcovered : CoveredByActiveEdges hm s (π.symm p) (π.symm q) :=
        (by
          simpa only [s] using
            (C.active_edges (π.symm p) (π.symm q)).1 (by simpa using hpq))
      rcases hcovered with ⟨i, h | h⟩ | ⟨i, h | h⟩
      · refine ⟨.inl i, Or.inl ⟨?_, ?_⟩⟩
        · simpa [first] using congrArg π h.1
        · simpa [second] using congrArg π h.2
      · refine ⟨.inl i, Or.inr ⟨?_, ?_⟩⟩
        · simpa [first] using congrArg π h.1
        · simpa [second] using congrArg π h.2
      · refine ⟨.inr i, Or.inl ⟨?_, ?_⟩⟩
        · simpa [first] using congrArg π h.1
        · simpa [second] using congrArg π h.2
      · refine ⟨.inr i, Or.inr ⟨?_, ?_⟩⟩
        · simpa [first] using congrArg π h.1
        · simpa [second] using congrArg π h.2
    · rintro ⟨k, h | h⟩
      · have hcovered : CoveredByActiveEdges hm s (π.symm p) (π.symm q) := by
          rcases k with i | i
          · left
            refine ⟨i, Or.inl ⟨?_, ?_⟩⟩
            · simpa [first] using congrArg π.symm h.1
            · simpa [second] using congrArg π.symm h.2
          · right
            refine ⟨i, Or.inl ⟨?_, ?_⟩⟩
            · simpa [first] using congrArg π.symm h.1
            · simpa [second] using congrArg π.symm h.2
        have hcovered' := hcovered
        dsimp only [s] at hcovered'
        simpa using (C.active_edges (π.symm p) (π.symm q)).2 hcovered'
      · have hcovered : CoveredByActiveEdges hm s (π.symm p) (π.symm q) := by
          rcases k with i | i
          · left
            refine ⟨i, Or.inr ⟨?_, ?_⟩⟩
            · simpa [first] using congrArg π.symm h.1
            · simpa [second] using congrArg π.symm h.2
          · right
            refine ⟨i, Or.inr ⟨?_, ?_⟩⟩
            · simpa [first] using congrArg π.symm h.1
            · simpa [second] using congrArg π.symm h.2
        have hcovered' := hcovered
        dsimp only [s] at hcovered'
        simpa using (C.active_edges (π.symm p) (π.symm q)).2 hcovered'
  · intro c hc
    obtain ⟨hmatching, hcrossing⟩ := C.licq
      (fun i => c (.inl i)) (fun i => c (.inr i)) (by
        intro U
        have hU := hc U
        rw [Fintype.sum_sum_type] at hU
        simpa only [s, first, second,
          Erdos1045.Statement.KKT.edgeDifferential,
          StructuralNote.MatchingActivityActiveConstraintDifferentials.edgeDifferential]
          using hU)
    funext k
    rcases k with i | i
    · exact congrFun hmatching i
    · exact congrFun hcrossing i
  · intro k
    rcases k with i | i
    · exact C.matching_pos i
    · exact C.crossing_pos i
  · intro U
    rw [hlog]
    rw [Fintype.sum_sum_type]
    simpa only [s, first, second, multiplier,
      Erdos1045.Statement.KKT.edgeDifferential,
      StructuralNote.MatchingActivityActiveConstraintDifferentials.edgeDifferential]
      using C.original.stationarity U
  · intro μ hμ
    let L : RelabeledMultipliers hm
        (fun i => activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i) π z :=
      { matching := fun i => μ (.inl i)
        crossing := fun i => μ (.inr i)
        stationarity := by
          intro U
          have hU := hμ U
          rw [hlog] at hU
          rw [Fintype.sum_sum_type] at hU
          simpa only [s, first, second,
            Erdos1045.Statement.KKT.edgeDifferential,
            StructuralNote.MatchingActivityActiveConstraintDifferentials.edgeDifferential]
            using hU }
    have hL : L = C.original := C.unique L
    funext k
    rcases k with i | i
    · change L.matching i = C.original.matching i
      exact congrArg (fun K : RelabeledMultipliers hm
        (fun j => activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) j) π z => K.matching i) hL
    · change L.crossing i = C.original.crossing i
      exact congrArg (fun K : RelabeledMultipliers hm
        (fun j => activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) j) π z => K.crossing i) hL
  · intro k
    have hactive : ‖z (first k) - z (second k)‖ = 2 := by
      rcases k with i | i
      · simpa [first, second] using
          (C.active_edges (matchingFirst i) (matchingSecond hm i)).2
            (Or.inl ⟨i, Or.inl ⟨rfl, rfl⟩⟩)
      · simpa [s, first, second] using
          (C.active_edges
            (selectedFirst hm (fun j => activeHalfSign hm (normalizedAngle m u)
              (modelRadii m β u) (actualCenter m β u) j) i)
            (selectedSecond hm (fun j => activeHalfSign hm (normalizedAngle m u)
              (modelRadii m β u) (actualCenter m β u) j) i)).2
            (Or.inr ⟨i, Or.inl ⟨rfl, rfl⟩⟩)
    rw [Erdos1045.Statement.KKT.edgeSquaredDistance]
    rw [hactive]
    norm_num

/-- Every even-order diameter extremizer at the concrete cutoff has the
original-configuration KKT certificate, with unique strictly positive multipliers. -/
theorem unique_positive_kkt : UniquePositiveKKT := by
  intro m hm z hz
  obtain ⟨hmp, π, α, β, u, η, ⟨C⟩⟩ :=
    StructuralNote.ExplicitKKTThreshold.positive_original_certificate hm z hz
  exact ⟨ofPositiveOriginalCertificate C⟩

end

end Erdos1045.Statement.KKT

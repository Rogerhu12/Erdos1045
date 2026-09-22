import Erdos1045.FamilyFine
import Erdos1045.FinalReduction
import Erdos1045.ClosedHullGeometry
import Erdos1045.ClosedCircle
import Erdos1045.ClosedMatrix
import Erdos1045.ClosedMatrixSpectral
import Erdos1045.ClosedCosine
import Erdos1045.ClosedDFT
import Erdos1045.ClosedGeometricSine
import Erdos1045.ClosedLogTaylor
import Erdos1045.ClosedSine
import Erdos1045.ClosedHolder
import Erdos1045.ClosedDifferenceDerivative
import Erdos1045.ClosedLevel
import Erdos1045.ClosedLevelActual
import Erdos1045.ClosedExteriorActual
import ReinhardtSharp

/-!
# Erdős 1045 for sufficiently large odd sizes

Every analytic and geometric interface is constructed below. The exterior
model comes from a proved Riemann mapping theorem; the needed Faber bound,
energy and perimeter estimates use its interior analytic model. The final
theorems have no classical-background parameter.
-/

namespace Erdos1045

open Filter
open scoped Topology
open Configuration HullGeometry ExteriorClassical GlobalProof
noncomputable section

/-- A compatibility bundle, now inhabited by the concrete proofs below. -/
structure ClassicalBackground : Prop where
  reinhardt : ReinhardtPerimeterInequality
  level : RemainingLevelAnalysis
  exterior : ClassicalExteriorExistence

theorem classicalBackground_proved : ClassicalBackground where
  reinhardt := ExteriorReduction.Reinhardt.reinhardtPerimeterInequality_proved
  level := remainingLevelAnalysis_proved
  exterior := classicalExteriorExistence_proved

/-- Recover the analysis API from its proved component interfaces. -/
theorem ClassicalBackground.toClassicalAnalysis (B : ClassicalBackground) : ClassicalAnalysis where
  geometry := classicalHullGeometry_of_reinhardt B.reinhardt
  circle := CircleMatrix.classicalCircleIdentities
  matrix := MatrixDefect.classicalMatrixFacts
  hadamard := MatrixDefect.classicalMatrixHadamard
  fourier := FaberFourier.classicalFourierFacts
  moment := ClosedSeries.geometric_moment
  laurent := ClosedSeries.laurentAnalysis
  series := classicalLaurentSeries
  level := B.level.toClassical
  sequence := ClosedSeries.sequenceFacts
  cosine := KernelWeights.classicalCosineFourier
  sine := ClosedSeries.sineExpansion

theorem extremal_family_eventually_regular (s : ExtremalFamily) :
    ∀ᶠ j in atTop, Configuration.IsRegular (s.points j) := by
  let B := classicalBackground_proved
  obtain ⟨C, K, D, hC, hK, hD, hb⟩ := s.coarse_control B.toClassicalAnalysis
  exact ExteriorLocalBridge.eventually_regular_of_eventual_bounds
    B.toClassicalAnalysis.geometry ClosedSeries.laurentAnalysis
    ClosedFourier.dftInversion ClosedFourier.geometricSine LocalNonlinear.scalarLogTaylor
    s.size_ge s.size_tendsto s.points s.maximal s.data
    (fun j => ClosedFourier.orthogonality (s.size j) (by have := s.size_ge j; omega))
    (s.circleEnergy_tendsto_zero B.toClassicalAnalysis) (hb.mono fun _ h => h.1) K
    (hb.mono fun _ h => h.2.2.1)

/-- Every perimeter extremizer in every sufficiently large odd dimension is
a regular polygon, with arbitrary translation, rotation, scale, and labeling. -/
theorem large_odd_perimeter_extremizers_regular :
    ∃ M : ℕ, 4 ≤ M ∧ ∀ n : ℕ, M ≤ n → Odd n →
      ∀ z : Points n, PerimeterExtremal n z → Configuration.IsRegular z :=
  eventual_regular_extremals classicalBackground_proved.toClassicalAnalysis
    classicalBackground_proved.exterior extremal_family_eventually_regular

/-- The requested diameter-two theorem, including attainment and rigidity.
The ordered product of distances in `discriminant` equals the product of
squared distances over unordered pairs. No numerical threshold is asserted. -/
theorem erdos1045_large_odd :
    ∃ M : ℕ, 4 ≤ M ∧ ∀ n : ℕ, M ≤ n → Odd n →
      (∀ z : Points n, DiameterAtMost 2 z →
        discriminant z ≤ (n : ℝ) ^ n / Real.cos (Real.pi / (2 * n)) ^ (n * (n - 1))) ∧
      (DiameterAtMost 2 (diameterTwoRegular n) ∧
        discriminant (diameterTwoRegular n) =
          (n : ℝ) ^ n / Real.cos (Real.pi / (2 * n)) ^ (n * (n - 1))) ∧
      (∀ z : Points n, DiameterAtMost 2 z →
        discriminant z = (n : ℝ) ^ n / Real.cos (Real.pi / (2 * n)) ^ (n * (n - 1)) →
          Configuration.IsRegular z) :=
  eventual_diameter_two_maximum classicalBackground_proved.toClassicalAnalysis
    classicalBackground_proved.exterior extremal_family_eventually_regular

#print axioms erdos1045_large_odd

end
end Erdos1045

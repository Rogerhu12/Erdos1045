import Erdos1045.Statement
import StructuralNote.FixedSchurRationalWindowEnergy

open StructuralNote

namespace Erdos1045.Statement.Algebraic

open Erdos1045 Erdos1045.EventualExact

theorem pairEnergy_eq {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    pairEnergy hn c = SchurSpectrum.pairEnergy hn c := rfl

theorem referenceEquation_eq {m : ℕ} (hm : 0 < m)
    (σ q : Fin (2 * m) → ℝ) :
    referenceEquation hm σ q = FixedSchurEquations.equationMap hm 0 0 σ q := by
  funext j
  simp [referenceEquation, referenceChord, firstCoefficient, frame, character,
    regularRoot, cyclicShiftIndex, FixedSchurEquations.equationMap,
    FixedSchurContraction.crossingMap, FixedSchurScalarRoot.rootValue,
    FixedSchurData.epsilon, FixedSchurData.X, FixedSchurData.Y,
    FixedSchurData.chordField, CommonFiberGeometry.diameterVector,
    EdgeCoordinates.tangent, EdgeCoordinates.J, SchurSpectrum.edgeRatio,
    SchurSpectrum.periodize, LocalDFT.pairRatio, SchurLift.frame,
    SchurLift.firstCoefficient, FourierMultiplier.character,
    FiniteFourierLift.successor, LocalPhase.phase, LocalPhase.regularRoot,
    LensClosure.unit]

theorem canonicalLift_eq {n : ℕ} (q : Fin n → ℝ) :
    canonicalLift q = SchurLift.canonicalLift q := by
  funext j
  simp only [canonicalLift, liftIncrement, firstCoefficient, frame, character,
    fourierCoefficient, regularRoot, SchurLift.canonicalLift,
    SchurLift.increment, SchurLift.firstCoefficient, SchurLift.frame,
    FiniteFourierLift.integral, FiniteFourierLift.integralCoefficients,
    FiniteFourierLift.differenceSymbol, FourierMultiplier.synthesis,
    FourierMultiplier.coefficient, FourierMultiplier.character,
    LocalPhase.regularRoot, LocalPhase.phase, Nat.cast_one]

theorem referenceCenter_eq {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm) :
    referenceCenter hm (FiniteBox.patternSign s) =
      FixedSchurRationalWindowEnergy.fixedReferenceCenter hm s := by
  have hq : referenceCoordinate hm (FiniteBox.patternSign s) =
      FixedSchurChart.coordinate hm s 0 0 := by
    have he : referenceEquation hm (FiniteBox.patternSign s) =
        FixedSchurEquations.equationMap hm 0 0 (FiniteBox.patternSign s) :=
      funext (referenceEquation_eq hm (FiniteBox.patternSign s))
    unfold referenceCoordinate
    rw [he]
    rfl
  unfold referenceCenter FixedSchurRationalWindowEnergy.fixedReferenceCenter
  rw [hq]
  change canonicalLift _ = SchurLift.canonicalLift _ + 0
  rw [add_zero]
  exact canonicalLift_eq _

end Erdos1045.Statement.Algebraic

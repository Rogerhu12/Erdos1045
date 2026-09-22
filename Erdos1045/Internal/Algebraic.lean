import Erdos1045.Statement
import Erdos1045.Internal.Geometry
import Erdos1045.Internal.Reference
import Erdos1045.Internal.Expressions
import StructuralNote.RewrittenEvenCertificate

open StructuralNote

/-! Bridge from the implementation certificate to the Mathlib-only public
algebraic statement. -/

namespace Erdos1045.Internal.Algebraic

open Filter MvPolynomial Erdos1045 Erdos1045.Configuration
open Erdos1045.EventualExact Erdos1045.EventualExact.FiniteBox
open FixedSchurCanonicalWordSymmetry FixedSchurRationalClosureMatrix
open FixedSchurRationalWindowDomain
open scoped Topology
noncomputable section

theorem canonicalSign_eq_internal {m : ℕ} (hm : 3 ≤ m) :
    Statement.Algebraic.canonicalSign m = patternSign (canonicalPattern hm) := by
  classical
  funext j
  unfold Statement.Algebraic.canonicalSign
  by_cases hn : Statement.canonicalNegative m j
  · simp only [if_pos hn]
    exact (Erdos1045.Internal.Geometry.canonicalSign_negative_iff hm j).2 hn |>.symm
  · simp only [if_neg hn]
    rcases patternSign_is_sign (canonicalPattern hm) j with hp | hneg
    · exact hp.symm
    · exact (hn ((Erdos1045.Internal.Geometry.canonicalSign_negative_iff hm j).1 hneg)).elim

theorem canonicalHalfWord_eq_internal {m : ℕ} (hm : 3 ≤ m) :
    Statement.Algebraic.canonicalHalfWord m = halfWord (canonicalPattern hm) := by
  funext j
  unfold Statement.Algebraic.canonicalHalfWord halfWord
  rw [canonicalSign_eq_internal hm]
  unfold patternSign boolSign
  cases h : (canonicalPattern hm).val ⟨j.val, by omega⟩ <;>
    norm_num [boolSign, h]

theorem canonicalHalfSign_eq_internal {m : ℕ} (hm : 3 ≤ m) :
    Statement.Algebraic.canonicalHalfSign m = rationalSign (canonicalPattern hm) := by
  funext j
  unfold Statement.Algebraic.canonicalHalfSign rationalSign
  rw [canonicalHalfWord_eq_internal hm]
  unfold halfWord patternSign boolSign
  cases h : (canonicalPattern hm).val ⟨j.val, by omega⟩ <;>
    norm_num [boolSign, h]

theorem configuration_eq_internal {m : ℕ} (hm : 0 < m)
    (σ : Fin m → ℝ) (X : Statement.Algebraic.ConfigVariables m → ℝ) :
    Statement.Algebraic.configuration hm σ X =
      RationalConfiguration.configuration hm σ X := by
  rfl

theorem selectedWindowEnergy_eq_internal {m : ℕ} (hm : 3 ≤ m)
    (X : Statement.Algebraic.ConfigVariables m → ℝ) :
    Statement.Algebraic.selectedWindowEnergy hm X =
      selectedWindowEnergy (by omega) (canonicalPattern hm) X := by
  unfold Statement.Algebraic.selectedWindowEnergy selectedWindowEnergy
  rw [Statement.Algebraic.pairEnergy_eq, Statement.Algebraic.pairEnergy_eq,
    canonicalHalfSign_eq_internal hm, canonicalSign_eq_internal hm,
    Statement.Algebraic.referenceCenter_eq (by omega) (canonicalPattern hm)]
  rfl

theorem angleExpr_toInternal {m : ℕ} (j : Fin m) :
    (Statement.Algebraic.angleExpr j).toInternal =
      RationalConfigurationPolynomials.angle j := by
  unfold Statement.Algebraic.angleExpr RationalConfigurationPolynomials.angle
  split <;> simp

theorem crossingAngleExpr_toInternal {m : ℕ} (j : Fin m) :
    (Statement.Algebraic.crossingAngleExpr j).toInternal =
      RationalConfigurationPolynomials.crossingAngle j := by
  rfl

theorem diameterExpr_toInternal {m : ℕ} (hm : 0 < m) (j : ℕ) :
    (Statement.Algebraic.diameterExpr hm j).toInternal =
      RationalConfigurationPolynomials.diameter hm j := by
  simp [Statement.Algebraic.diameterExpr,
    RationalConfigurationPolynomials.diameter, angleExpr_toInternal]

theorem crossingUnitExpr_toInternal {m : ℕ} (j : Fin m) :
    (Statement.Algebraic.crossingUnitExpr j).toInternal =
      RationalConfigurationPolynomials.crossingUnit j := by
  simp [Statement.Algebraic.crossingUnitExpr,
    RationalConfigurationPolynomials.crossingUnit, crossingAngleExpr_toInternal]

theorem signExpr_toInternal {m : ℕ} (σ : Fin m → Bool) (j : Fin m) :
    (Statement.Algebraic.signExpr σ j).toInternal =
      RationalConfigurationPolynomials.signExpr σ j := by
  rfl

theorem incrementExpr_toInternal {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (j : Fin m) :
    (Statement.Algebraic.incrementExpr hm σ j).toInternal =
      RationalConfigurationPolynomials.increment hm σ j := by
  simp [Statement.Algebraic.incrementExpr,
    RationalConfigurationPolynomials.increment, signExpr_toInternal,
    crossingUnitExpr_toInternal, diameterExpr_toInternal]

theorem centerPrefixExpr_toInternal {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (r : ℕ) :
    (Statement.Algebraic.centerPrefixExpr hm σ r).toInternal =
      RationalConfigurationPolynomials.centerPrefix hm σ r := by
  unfold Statement.Algebraic.centerPrefixExpr
    RationalConfigurationPolynomials.centerPrefix
  rw [Statement.Algebraic.ComplexExpression.toInternal_sum]
  congr 1
  funext a
  split <;> simp [incrementExpr_toInternal]

theorem closureExpr_toInternal {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) :
    (Statement.Algebraic.closureExpr hm σ).toInternal =
      RationalConfigurationPolynomials.closure hm σ := by
  simp [Statement.Algebraic.closureExpr,
    RationalConfigurationPolynomials.closure, incrementExpr_toInternal]

theorem pointExpr_toInternal {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (j : ℕ) :
    (Statement.Algebraic.pointExpr hm σ j).toInternal =
      RationalConfigurationPolynomials.point hm σ j := by
  simp [Statement.Algebraic.pointExpr,
    RationalConfigurationPolynomials.point, centerPrefixExpr_toInternal,
    diameterExpr_toInternal]

theorem configurationExpr_toInternal {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (j : Fin (2 * m)) :
    (Statement.Algebraic.configurationExpr hm σ j).toInternal =
      RationalConfigurationPolynomials.configuration hm σ j := by
  simp [Statement.Algebraic.configurationExpr,
    RationalConfigurationPolynomials.configuration, pointExpr_toInternal]

theorem squaredDistanceExpr_toInternal {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (i j : Fin (2 * m)) :
    (Statement.Algebraic.squaredDistanceExpr hm σ i j).toInternal =
      RationalConfigurationPolynomials.squaredDistance hm σ i j := by
  simp [Statement.Algebraic.squaredDistanceExpr,
    RationalConfigurationPolynomials.squaredDistance,
    configurationExpr_toInternal hm σ]

theorem closureCoordinate_toInternal {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (k : Fin 2) :
    (Statement.Algebraic.closureCoordinate hm σ k).toInternal =
      RationalStationarySystem.closureCoordinate hm σ k := by
  unfold Statement.Algebraic.closureCoordinate
    RationalStationarySystem.closureCoordinate
  split
  · simpa using congrArg RationalExpressions.ComplexExpression.re
      (closureExpr_toInternal hm σ)
  · simpa using congrArg RationalExpressions.ComplexExpression.im
      (closureExpr_toInternal hm σ)

theorem pairs_eq_internal (m : ℕ) :
    Statement.Algebraic.pairs m = RationalStationarySystem.pairs m := rfl

theorem gradient_toInternal {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (i : Statement.Algebraic.ConfigVariables m) :
    (Statement.Algebraic.gradient hm σ i).toInternal =
      RationalStationarySystem.gradient hm σ i := by
  simp [Statement.Algebraic.gradient, RationalStationarySystem.gradient,
    squaredDistanceExpr_toInternal hm σ, pairs_eq_internal]

theorem systemExpression_toInternal {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (i : Statement.Algebraic.Variables m) :
    (Statement.Algebraic.systemExpression hm σ i).toInternal =
      RationalStationarySystem.systemExpression hm σ i := by
  cases i with
  | inl i =>
      simp [Statement.Algebraic.systemExpression,
        RationalStationarySystem.systemExpression,
        Statement.Algebraic.residual, RationalStationarySystem.residual,
        gradient_toInternal hm σ, closureCoordinate_toInternal hm σ]
  | inr k =>
      simp [Statement.Algebraic.systemExpression,
        RationalStationarySystem.systemExpression,
        closureCoordinate_toInternal hm σ]

theorem polynomials_eq_internal {m : ℕ} (hm : 3 ≤ m) :
    Statement.Algebraic.polynomials (by omega)
        (Statement.Algebraic.canonicalHalfWord m) =
      RationalStationarySystem.polynomials (by omega)
        (halfWord (canonicalPattern hm)) := by
  rw [canonicalHalfWord_eq_internal hm]
  funext q
  exact congrArg RationalExpressions.Expression.numerator
    (systemExpression_toInternal (by omega) (halfWord (canonicalPattern hm)) q)

theorem objective_eq_internal {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (X : Statement.Algebraic.ConfigVariables m → ℝ) :
    Statement.Algebraic.objective hm σ X =
      RationalStationarySystem.objective hm σ X := by
  unfold Statement.Algebraic.objective RationalStationarySystem.objective
  simp only [RationalConfigurationPolynomials.squaredDistance_eval]
  rw [pairs_eq_internal]
  change (∑ p ∈ RationalStationarySystem.pairs m,
      Real.log (Complex.normSq
        (Statement.Algebraic.configuration hm
            (RationalConfigurationPolynomials.sign σ) X p.1 -
          Statement.Algebraic.configuration hm
            (RationalConfigurationPolynomials.sign σ) X p.2))) / 2 = _
  rw [configuration_eq_internal hm (RationalConfigurationPolynomials.sign σ) X]

theorem closureCoordinate_eval_eq_internal {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (k : Fin 2)
    (X : Statement.Algebraic.ConfigVariables m → ℝ) :
    (Statement.Algebraic.closureCoordinate hm σ k).eval X =
      (RationalStationarySystem.closureCoordinate hm σ k).eval X := by
  rw [← Statement.Algebraic.Expression.toInternal_eval,
    closureCoordinate_toInternal]

theorem stationary_eq_internal {m : ℕ} (hm : 3 ≤ m)
    (Y : Statement.Algebraic.Variables m → ℝ) :
    Statement.Algebraic.Stationary (by omega)
        (Statement.Algebraic.canonicalHalfWord m) Y ↔
      RationalStationarySystem.Stationary (by omega)
        (halfWord (canonicalPattern hm)) Y := by
  rw [canonicalHalfWord_eq_internal hm]
  unfold Statement.Algebraic.Stationary RationalStationarySystem.Stationary
  simp only [Statement.Algebraic.coordinates, RationalStationarySystem.coordinates,
    Statement.Algebraic.multiplier, RationalStationarySystem.multiplier,
    objective_eq_internal, closureCoordinate_eval_eq_internal]
  rfl

theorem rationalJacobian_eq_internal {m : ℕ} (hm : 3 ≤ m)
    (Y : Statement.Algebraic.Variables m → ℝ) :
    Statement.Algebraic.rationalJacobian
        (Statement.Algebraic.systemExpression (by omega)
          (Statement.Algebraic.canonicalHalfWord m)) Y =
      RationalSystemAlgebraicity.jacobian
        (RationalStationarySystem.systemExpression (by omega)
          (halfWord (canonicalPattern hm))) Y := by
  rw [canonicalHalfWord_eq_internal hm]
  funext i j
  unfold Statement.Algebraic.rationalJacobian
    RationalSystemAlgebraicity.jacobian
  change deriv (fun t =>
      ((Statement.Algebraic.systemExpression (by omega)
        (halfWord (canonicalPattern hm)) i).toInternal).eval
          (Function.update Y j t)) (Y j) = _
  rw [systemExpression_toInternal]

theorem polynomialJacobian_eq_internal {m : ℕ} (hm : 3 ≤ m)
    (Y : Statement.Algebraic.Variables m → ℝ) :
    Statement.Algebraic.polynomialJacobian
        (Statement.Algebraic.polynomials (by omega)
          (Statement.Algebraic.canonicalHalfWord m)) Y =
      PolynomialAlgebraicity.jacobian
        (RationalStationarySystem.polynomials (by omega)
          (halfWord (canonicalPattern hm))) Y := by
  rw [polynomials_eq_internal hm]
  rfl

noncomputable def publicCertificate_of_internal {m : ℕ}
    (c : RewrittenEvenCertificate.Certificate m) :
      Statement.Algebraic.Certificate m := by
  refine {
    large := c.large
    root := c.root
    window := c.window
    dimension := c.dimension
    window_spec := ?_
    in_window := c.in_window
    stationary := ?_
    polynomial_root := ?_
    system_iff := ?_
    unique_root := ?_
    rational_nonsingular := ?_
    polynomial_nonsingular := ?_
    algebraic := c.algebraic
    geometric_algebraic := ?_
    distances_algebraic := ?_
    extremal := ?_
    maximum := ?_
    maximum_algebraic := ?_ }
  · intro X
    rw [selectedWindowEnergy_eq_internal c.large]
    exact c.window_spec X
  · exact (stationary_eq_internal c.large c.root).2 c.stationary
  · intro q
    rw [polynomials_eq_internal c.large]
    exact c.polynomial_root q
  · intro Y hY
    rw [polynomials_eq_internal c.large, stationary_eq_internal c.large Y]
    exact c.system_iff Y hY
  · intro Y hY hzero
    apply c.unique_root Y hY
    rwa [← polynomials_eq_internal c.large]
  · rw [rationalJacobian_eq_internal c.large]
    exact c.rational_nonsingular
  · rw [polynomialJacobian_eq_internal c.large]
    exact c.polynomial_nonsingular
  · intro j
    rw [configuration_eq_internal, canonicalHalfSign_eq_internal c.large]
    exact c.geometric_algebraic j
  · intro i j
    rw [configuration_eq_internal, canonicalHalfSign_eq_internal c.large]
    exact c.distances_algebraic i j
  · rw [configuration_eq_internal, canonicalHalfSign_eq_internal c.large]
    exact c.extremal
  · rw [configuration_eq_internal, canonicalHalfSign_eq_internal c.large]
    exact c.maximum
  · exact c.maximum_algebraic

end
end Erdos1045.Internal.Algebraic

import StructuralNote.FixedSchurRationalWindowCrossingChart
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The full real derivative of the literal rational closure map. -/

namespace StructuralNote.FixedSchurRationalWindowClosureDerivative

open Erdos1045 Erdos1045.EventualExact Complex Filter
open RationalChart RationalAngleBranch RationalCommonConfiguration
open CommonDomainRadius
open FixedSchurRationalWindowEnergy FixedSchurRationalWindowDomain
open FixedSchurRationalWindowCrossingChart LensClosure
open scoped BigOperators Topology
noncomputable section

theorem rotation_hasDerivAt (t : ℝ) :
    HasDerivAt RationalChart.rotation
      (RationalChart.rotation t * (((2 / (1 + t ^ 2) : ℝ) : ℂ) * I)) t := by
  have h := LensIncrementDerivatives.unit_path_hasDerivAt (angle_hasDerivAt t)
  rw [show RationalChart.rotation = fun s : ℝ => unit (2 * Real.arctan s) by
    funext s
    exact rotation_eq_unit_arctan s]
  simpa only [rotation_eq_unit_arctan] using h

theorem rotation_differentiable : Differentiable ℝ RationalChart.rotation :=
  fun t => (rotation_hasDerivAt t).differentiableAt

private theorem angleParameter_differentiable {m : ℕ} (j : Fin m) :
    Differentiable ℝ (fun Z : RationalConfiguration.Variables m → ℝ =>
      RationalConfiguration.angleParameter Z j) := by
  unfold RationalConfiguration.angleParameter
  split
  · fun_prop
  · fun_prop

private theorem crossingParameter_differentiable {m : ℕ} (j : Fin m) :
    Differentiable ℝ (fun Z : RationalConfiguration.Variables m → ℝ =>
      RationalConfiguration.crossingParameter Z j) := by
  unfold RationalConfiguration.crossingParameter
  fun_prop

theorem rational_closure_differentiable {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) :
    Differentiable ℝ (RationalConfiguration.closure hm σ) := by
  unfold RationalConfiguration.closure
  have hinc (j : Fin m) : Differentiable ℝ
      (fun Z : RationalConfiguration.Variables m → ℝ =>
        RationalConfiguration.increment hm σ Z j) := by
    unfold RationalConfiguration.increment RationalChart.crossingIncrement
    have hd₀ : Differentiable ℝ (fun Z : RationalConfiguration.Variables m → ℝ =>
        RationalConfiguration.diameter hm Z j) := by
      unfold RationalConfiguration.diameter
      exact (differentiable_const _).mul
        (rotation_differentiable.comp (angleParameter_differentiable _))
    have hd₁ : Differentiable ℝ (fun Z : RationalConfiguration.Variables m → ℝ =>
        RationalConfiguration.diameter hm Z (j.val + 1)) := by
      unfold RationalConfiguration.diameter
      exact (differentiable_const _).mul
        (rotation_differentiable.comp (angleParameter_differentiable _))
    have hU : Differentiable ℝ (fun Z : RationalConfiguration.Variables m → ℝ =>
        RationalConfiguration.crossingUnit Z j) := by
      unfold RationalConfiguration.crossingUnit
      exact (differentiable_const _).mul
        (rotation_differentiable.comp (crossingParameter_differentiable _))
    exact (differentiable_const _).mul
      ((((differentiable_const _).mul hU).sub hd₀).sub hd₁)
  have hsum (S : Finset (Fin m)) : Differentiable ℝ
      (fun Z : RationalConfiguration.Variables m → ℝ =>
        ∑ j ∈ S, RationalConfiguration.increment hm σ Z j) := by
    induction S using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; fun_prop
    | @insert a S ha ih =>
        simp only [Finset.sum_insert ha]
        exact (hinc a).add ih
  simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
    hsum (Finset.univ : Finset (Fin m))

/-- The actual full real derivative of the literal rational closure. -/
def closureFDeriv {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (Z : RationalConfiguration.Variables m → ℝ) :
    (RationalConfiguration.Variables m → ℝ) →L[ℝ] ℂ :=
  fderiv ℝ (RationalConfiguration.closure hm σ) Z

theorem closure_hasFDerivAt {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (Z : RationalConfiguration.Variables m → ℝ) :
    HasFDerivAt (RationalConfiguration.closure hm σ)
      (closureFDeriv hm σ Z) Z := by
  exact (rational_closure_differentiable hm σ Z).hasFDerivAt

/-- The unit tangent vector in the literal rational `y_j` coordinate. -/
def crossingDirection {m : ℕ} (j : Fin m) :
    RationalConfiguration.Variables m → ℝ :=
  fun i => if i = .inr j then 1 else 0

theorem crossingCoordinateLine_hasDerivAt {m : ℕ}
    (Z : RationalConfiguration.Variables m → ℝ) (j : Fin m) :
    HasDerivAt (fun t : ℝ => crossingCoordinateLine Z j t)
      (crossingDirection j) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  by_cases hi : i = .inr j
  · subst i
    simp only [crossingCoordinateLine, Function.update_self, crossingDirection, if_pos]
    exact (hasDerivAt_id 0).const_add (Z (.inr j))
  · simp only [crossingCoordinateLine, Function.update_of_ne hi, crossingDirection, hi,
      if_false]
    exact hasDerivAt_const 0 _

/-- The full Fréchet derivative evaluates to the previously computed actual
`y_j` closure column. -/
theorem closureFDeriv_crossingDirection {m : ℕ} (hm : 0 < m)
    (σ : Fin m → ℝ) (Z : RationalConfiguration.Variables m → ℝ) (j : Fin m) :
    closureFDeriv hm σ Z (crossingDirection j) = closureCrossingColumn σ Z j := by
  have hzero : crossingCoordinateLine Z j 0 = Z := by
    funext i
    by_cases hi : i = .inr j
    · subst i
      simp [crossingCoordinateLine]
    · simp [crossingCoordinateLine, hi]
  have houter : HasFDerivAt (RationalConfiguration.closure hm σ)
      (closureFDeriv hm σ Z) (crossingCoordinateLine Z j 0) := by
    simpa only [hzero] using closure_hasFDerivAt hm σ Z
  have hfull := houter.comp_hasDerivAt 0
    (crossingCoordinateLine_hasDerivAt Z j)
  exact hfull.unique (closure_crossingLine_hasDerivAt hm σ Z j)

/-- On the manuscript's actual single window, the literal rational closure
has a full Fréchet derivative and that real derivative is onto `ℂ`. -/
theorem eventual_selectedWindow_closure_hasFDerivAt_surjective :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (Z : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s Z <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        RationalConfiguration.closure (by omega) (rationalSign s) Z = 0 →
        HasFDerivAt
            (RationalConfiguration.closure (by omega) (rationalSign s))
            (closureFDeriv (by omega) (rationalSign s) Z) Z ∧
          Function.Surjective (closureFDeriv (by omega) (rationalSign s) Z) := by
  filter_upwards [eventual_selectedWindow_closure_y_rank_two] with m hrank
  intro hm s Z hwindow hclosure
  have hspan := (hrank hm s Z hwindow hclosure).2
  refine ⟨closure_hasFDerivAt (by omega) (rationalSign s) Z, ?_⟩
  intro z
  rcases hspan z with ⟨u, hu⟩
  let j₀ : Fin m := ⟨0, by omega⟩
  let k : Fin m := transverseCrossingIndex m (by omega)
  refine ⟨u.1 • crossingDirection j₀ + u.2 • crossingDirection k, ?_⟩
  rw [map_add, map_smul, map_smul,
    closureFDeriv_crossingDirection (by omega) (rationalSign s) Z j₀,
    closureFDeriv_crossingDirection (by omega) (rationalSign s) Z k]
  simpa only [j₀, k, Complex.real_smul] using hu

end
end StructuralNote.FixedSchurRationalWindowClosureDerivative

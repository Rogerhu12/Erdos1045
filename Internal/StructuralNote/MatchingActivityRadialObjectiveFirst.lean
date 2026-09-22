import StructuralNote.MatchingActivityRadialModelCenterError
import StructuralNote.RadialObjectivePrice

/-! Exact differentiation of the genuine outward path and the leading
two-vertex radial gain. -/

namespace StructuralNote.MatchingActivityRadialObjectiveFirst

open Erdos1045 Erdos1045.EventualExact Complex Configuration
open FiniteFourierLift FourierMultiplier SchurSpectrum SchurLift LensClosure
open CommonFiberGeometry CommonClosureEnergy
open MatchingActivityRadialGeometry MatchingActivityRadialIntegration MatchingActivityRadialPath
open MatchingActivityRadialVelocity MatchingActivityRadialFeasible MatchingActivityRadialClosure MatchingActivityRadialPair
open MatchingActivityRadialSource MatchingActivityRadialProjection MatchingActivityRadialCenterFirst
open LocalGradient
open scoped BigOperators
noncomputable section

def directVelocity {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (i : Fin m) : Points (2 * m) :=
  fun j => (radiusFull hm (radiusVelocity i) j : ℂ) * diameterVector θ j

theorem radiusVelocity_full_sum {m : ℕ} (hm : 0 < m) (i : Fin m) :
    (∑ j : Fin (2 * m), radiusFull hm (radiusVelocity i) j) = 2 := by
  rw [real_half_sum hm _ (radiusFull_halfTurn hm (radiusVelocity i))]
  simp only [radiusFull_halfIndex, radiusVelocity_sum, mul_one]

theorem directVelocity_eq_price {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (i : Fin m) (j : Fin (2 * m)) :
    directVelocity hm θ i j = -RadialObjectivePrice.velocity θ (radiusFull hm (radiusVelocity i)) j := by
  simp only [directVelocity, RadialObjectivePrice.velocity, diameterVector, character,
    Nat.mul_one]
  change (_ : ℂ) * (_ * LensClosure.unit _) = -(-(_ : ℂ) * (LensClosure.unit _ * _))
  ring

theorem outwardPath_hasDerivAt {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ) (i : Fin m)
    (hchart : IsFeasibleRadialChart hm θ σ ν r a g)
    (hpos : ∀ j, 0 < (pair (halfAngle hm θ j) (r j) (r (nextIndex hm j))).re)
    (ht : ∀ j, ν j ^ 2 < 4) (j : Fin (2 * m)) :
    HasDerivAt (fun t => outwardPath hm θ σ ν r a g i t j)
      (directVelocity hm θ i j + centerVelocity hm θ σ ν r g i j) 0 := by
  have hr := (radiusPath_hasDerivAt r i ⟨j.val % m, Nat.mod_lt _ hm⟩).ofReal_comp.mul_const (diameterVector θ j)
  have hc := radialCenter_hasDerivAt hm θ σ ν r a g i hchart hpos ht j
  exact (hr.add hc).add_const a

theorem centerFirst_eq_pairing {n : ℕ} (D C U : Points n) :
    centerFirst D C U = ∑ j, inner ℝ (realGradient (GeometricRelativeRemainder.configuration D C) j) (U j) := by
  rw [centerFirst, Fintype.sum_prod_type]
  exact RadialObjectivePrice.pair_derivative_sum _ _

theorem directDerivative_lower {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (z : Points (2 * m)) (i : Fin m)
    {ε δ : ℝ} (hgrad : RadialObjectivePrice.gradientDeviation z ≤ ε) (hδ : 0 ≤ δ)
    (hθ : ∀ j, |θ j| ≤ δ) :
    2 * (2 * m : ℝ) - 2 - 2 * (2 * m : ℝ) * ε - 2 * (2 * m : ℝ) * δ ≤
      ∑ j, inner ℝ (realGradient z j) (directVelocity hm θ i j) := by
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have hb (j : Fin (2 * m)) : 0 ≤ radiusFull hm (radiusVelocity i) j := by
    unfold radiusFull radiusVelocity
    split <;> norm_num
  have he := Finset.sum_le_sum (s := Finset.univ) (fun j _ => RadialObjectivePrice.vertex_derivative_bound
    (show 0 < 2 * m by omega) θ (radiusFull hm (radiusVelocity i)) z hgrad hδ j (hb j) (hθ j))
  have heq (j : Fin (2 * m)) : inner ℝ (realGradient z j) (RadialObjectivePrice.velocity θ (radiusFull hm (radiusVelocity i)) j) =
      -inner ℝ (realGradient z j) (directVelocity hm θ i j) := by rw [directVelocity_eq_price, inner_neg_right, neg_neg]
  simp_rw [heq] at he
  simp only [Finset.sum_neg_distrib, ← Finset.mul_sum, radiusVelocity_full_sum,
    Nat.cast_mul, Nat.cast_ofNat] at he
  have hid : -(1 - 1 / (2 * m : ℝ) - ε - δ) * ((2 * m : ℝ) * 2) =
      -(2 * (2 * m : ℝ) - 2 - 2 * (2 * m : ℝ) * ε - 2 * (2 * m : ℝ) * δ) := by field_simp
  rw [hid] at he
  linarith

theorem outwardPath_log_derivative {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ) (i : Fin m)
    (hchart : IsFeasibleRadialChart hm θ σ ν r a g)
    (hpos : ∀ j, 0 < (pair (halfAngle hm θ j) (r j) (r (nextIndex hm j))).re)
    (ht : ∀ j, ν j ^ 2 < 4) (D C : Points (2 * m))
    (hbase : outwardPath hm θ σ ν r a g i 0 = GeometricRelativeRemainder.configuration D C)
    (hinj : Function.Injective (GeometricRelativeRemainder.configuration D C)) :
    HasDerivAt (fun t => Real.log (discriminant (outwardPath hm θ σ ν r a g i t)))
      ((∑ j, inner ℝ (realGradient (GeometricRelativeRemainder.configuration D C) j) (directVelocity hm θ i j)) +
        centerFirst D C (centerVelocity hm θ σ ν r g i)) 0 := by
  have he := RadialObjectivePrice.hasDerivAt_log_discriminant_path
    (outwardPath_hasDerivAt hm θ σ ν r a g i hchart hpos ht) (hbase ▸ hinj)
  rw [hbase] at he
  simpa only [inner_add_right, Finset.sum_add_distrib, centerFirst_eq_pairing] using he

end
end StructuralNote.MatchingActivityRadialObjectiveFirst

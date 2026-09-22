import Erdos1045.ExteriorBoundary
import Erdos1045.HullGeometry
import Erdos1045.CyclicAngles
import Erdos1045.FaberAlgebra
import Erdos1045.FaberMatrix
import Mathlib.Analysis.Convex.Hull

/-!
# Concrete exterior-map interfaces

The Laurent coefficients, their Sobolev summability and their energy are
derived from the analytic model at infinity. The Faber generating function
and exterior bijection are ordinary map properties, constructed together in
ClosedExteriorActual. Segments are allowed without a non-collinearity premise.
-/

namespace Erdos1045.ExteriorClassical

open MeasureTheory
open scoped BigOperators
open ExteriorBoundary Configuration
noncomputable section

def hull {n : ℕ} (z : Points n) : Set ℂ := convexHull ℝ (Set.range z)

def Fekete {n : ℕ} (z : Points n) : Prop :=
  ∀ w : Points n, Set.range w ⊆ hull z → discriminant w ≤ discriminant z

structure ExteriorData {n : ℕ} (z : Points n) extends BoundaryData where
  offset : ℂ
  angles : CyclicAngles.Angles n
  angle_range : ∀ i : Fin n, 0 ≤ angles.angle i ∧ angles.angle i < 2 * Real.pi
  model_node_identity : ∀ i : Fin n, z i = (capacity : ℂ) * unit (angles.angle i) + offset +
    laurent (ExteriorReduction.modelLaurentCoefficient model) (unit (angles.angle i))
  boundary_perimeter : boundaryLength z ≤ HullGeometry.hullPerimeter z

def ExteriorData.coefficient {n : ℕ} {z : Points n} (d : ExteriorData z) : ℕ → ℂ :=
  ExteriorReduction.modelLaurentCoefficient d.model

theorem ExteriorData.node_identity {n : ℕ} {z : Points n} (d : ExteriorData z) (i : Fin n) :
    z i = (d.capacity : ℂ) * unit (d.angles.angle i) + d.offset +
      laurent d.coefficient (unit (d.angles.angle i)) := d.model_node_identity i

theorem ExteriorData.sobolev {n : ℕ} {z : Points n} (d : ExteriorData z) :
    SobolevCoefficients d.coefficient :=
  ExteriorReduction.model_laurent_sobolev_of_criterion d.model_analytic d.model_zero_ne
    d.model_derivative_ne d.model_criterion

theorem ExteriorData.parseval_identity {n : ℕ} {z : Points n} (d : ExteriorData z) :
    d.energySquared = sobolevEnergySquared d.coefficient := rfl

theorem ExteriorData.derivative_identity {n : ℕ} {z : Points n} (d : ExteriorData z)
    (w : ℂ) (hw : 1 < ‖w‖) :
    d.derivative w = (d.capacity : ℂ) + laurentDerivative d.coefficient w := by
  have he := ExteriorReduction.exterior_derivative_laurent
    d.model_analytic d.model_zero_ne (0 : ℂ) hw
  rw [(ExteriorReduction.hasDerivAt_laurentExterior d.model_analytic (0 : ℂ) hw).deriv,
    d.model_zero] at he
  have hd : d.derivative w = ExteriorReduction.derivativeNumerator d.model w⁻¹ := by
    dsimp [BoundaryData.derivative, ExteriorReduction.modelDerivative]
    rw [d.model_zero]
    field_simp [Complex.ofReal_ne_zero.mpr d.capacity_pos.ne']
  rw [hd]
  simpa only [laurentDerivative, sub_eq_add_neg, ExteriorData.coefficient] using he

def ExteriorData.map {n : ℕ} {z : Points n} (d : ExteriorData z) (w : ℂ) : ℂ :=
  (d.capacity : ℂ) * w + d.offset + laurent d.coefficient w

def ExteriorData.faber {n : ℕ} {z : Points n} (d : ExteriorData z)
    (k : ℕ) (x : ℂ) : ℂ :=
  (FaberAlgebra.normalizedFaber (fun m => d.coefficient m / d.capacity) k).eval
    ((x - d.offset) / d.capacity)

def ExteriorData.matrix {n : ℕ} {z : Points n} (d : ExteriorData z) : MatrixDefect.Mat n :=
  fun i k => d.faber k (z i)

def ExteriorData.circleMatrix {n : ℕ} {z : Points n} (d : ExteriorData z) : MatrixDefect.Mat n :=
  fun i k => unit (d.angles.angle i) ^ (k : ℕ)

def ExteriorData.remainder {n : ℕ} {z : Points n} (d : ExteriorData z)
    (i : Fin n) (k : ℕ) : ℂ := d.faber k (z i) - unit (d.angles.angle i) ^ k

def ExteriorData.firstOrderMatrix {n : ℕ} {z : Points n} (d : ExteriorData z) : MatrixDefect.Mat n :=
  FaberFourier.coefficientMatrix (fun i => FaberFourier.firstOrder
    (FaberFourier.coefficient d.capacity d.coefficient (fun j : Fin n => d.angles.angle j) i))

def ExteriorData.quotient {n : ℕ} {z : Points n} (d : ExteriorData z)
    (i : Fin n) (v : ℂ) : ℂ :=
  (laurent d.coefficient v - laurent d.coefficient (unit (d.angles.angle i))) /
    ((d.capacity : ℂ) * (v - unit (d.angles.angle i)))

def ExteriorData.enclosed {n : ℕ} {z : Points n} (d : ExteriorData z) (r : ℝ) : Set ℂ :=
  (d.map '' {w : ℂ | r < ‖w‖})ᶜ

/-- Raw classical Faber identities, stated for every point of the convex hull. -/
structure FaberIdentities {n : ℕ} {z : Points n} (d : ExteriorData z) : Prop where
  map_bijective : Set.BijOn d.map {w : ℂ | 1 < ‖w‖} (hull z)ᶜ
  map_continuous : ContinuousOn d.map {w : ℂ | 1 ≤ ‖w‖}
  map_derivative : ∀ w : ℂ, 1 < ‖w‖ → HasDerivAt d.map (d.derivative w) w
  boundary_image : d.map '' {w : ℂ | ‖w‖ = 1} = frontier (hull z)
  norm_bound : ∀ k, 1 ≤ k → ∀ x ∈ hull z, ‖d.faber k x‖ ≤ 2
  generating : ∀ x ∈ hull z, ∀ r : ℝ, 1 < r → ∀ t : ℝ,
    FaberFourier.series (fun k => ((1 / r : ℝ) : ℂ) ^ k * d.faber k x) t =
      ((r : ℂ) * unit t) * d.derivative ((r : ℂ) * unit t) /
        (d.map ((r : ℂ) * unit t) - x)
  generating_summable : ∀ x ∈ hull z, ∀ r : ℝ, 1 < r →
    Summable (fun k => ‖((1 / r : ℝ) : ℂ) ^ k * d.faber k x‖)
  map_avoids_hull : ∀ v : ℂ, 1 < ‖v‖ → d.map v ∉ hull z

/-- Generic estimates for arbitrary H1 Laurent series. The two energy
normalizations are explicit, so no factor of `2π` is implicit. -/
structure ClassicalLaurentAnalysis : Prop where
  absolute : ∀ a, SobolevCoefficients a → Summable (fun m => ‖a m‖)
  holder : ∃ H : ℝ, 0 < H ∧ ∀ a, SobolevCoefficients a →
    ∀ u v : ℂ, 1 ≤ ‖u‖ → 1 ≤ ‖v‖ →
      ‖laurent a u - laurent a v‖ ≤
        H * Real.sqrt (sobolevEnergySquared a) * Real.sqrt ‖u - v‖
  interval_sobolev : ∀ a, SobolevCoefficients a → ∀ s t : ℝ,
    ‖laurent a (unit t) - laurent a (unit s)‖ ≤
      Real.sqrt (sobolevEnergySquared a) * Real.sqrt |t - s|
  hardy_evaluation : ∀ a, SobolevCoefficients a → ∀ w : ℂ, 1 < ‖w‖ →
    ‖laurentDerivative a w‖ ^ 2 ≤ sobolevEnergySquared a /
      (2 * Real.pi * ‖w‖ ^ 2 * (‖w‖ ^ 2 - 1))

/-- Compatibility interface for the constructed exterior model. `Fekete` is
obtained from global extremality; ClosedExteriorActual proves this interface. -/
structure ClassicalExteriorExistence : Prop where
  model : ∀ n, 3 ≤ n → ∀ z : Points n, Function.Injective z →
    HullGeometry.hullPerimeter z = 2 * Real.pi → Fekete z →
    ∃ σ : Equiv.Perm (Fin n), Nonempty
      {d : ExteriorData (z ∘ σ) // FaberIdentities d}

end
end Erdos1045.ExteriorClassical

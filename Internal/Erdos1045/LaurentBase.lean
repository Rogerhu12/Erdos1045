import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The Laurent coefficient definitions are independent of boundary geometry. -/

namespace Erdos1045.ExteriorClassical
noncomputable section

def laurent (a : ℕ → ℂ) (w : ℂ) : ℂ := ∑' m, a m * w⁻¹ ^ m

def laurentDerivative (a : ℕ → ℂ) (w : ℂ) : ℂ :=
  -∑' m : ℕ, (m : ℂ) * a m * w⁻¹ ^ (m + 1)

def sobolevEnergySquared (a : ℕ → ℂ) : ℝ :=
  2 * Real.pi * ∑' m : ℕ, (m : ℝ) ^ 2 * ‖a m‖ ^ 2

def SobolevCoefficients (a : ℕ → ℂ) : Prop :=
  a 0 = 0 ∧ Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖a m‖ ^ 2)

end
end Erdos1045.ExteriorClassical

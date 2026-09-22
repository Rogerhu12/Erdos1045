import Erdos1045.Statement

/-! Proof-internal parity packages used to assemble the single public
diameter characterization. They are not separate submitted conclusions. -/

namespace Erdos1045.Internal
open Statement
noncomputable section

/-- Even-order attainment, direct-rigid uniqueness, diameter geometry, and a
unique nonsingular algebraic stationary root in the selected polynomial window,
valid at every even order at least `evenThreshold`. -/
def EvenThresholdClaims : Prop :=
  ∀ m : ℕ, evenThreshold ≤ 2 * m →
    (∃ z : Points (2 * m), DiameterExtremal z) ∧
    (∀ z w : Points (2 * m), DiameterExtremal z → DiameterExtremal w →
      DirectRigidRelabeling z w) ∧
    (∀ z : Points (2 * m), DiameterExtremal z → Nonempty (EvenGeometry m z)) ∧
    Nonempty (Algebraic.Certificate m)

/-- Exact odd diameter maximum, attainment, regularity and rigid uniqueness
above the common regular-polygon threshold. -/
def OddThresholdClaims : Prop :=
  ∀ n : ℕ, regularThreshold ≤ n → Odd n →
    M n = (n : ℝ) ^ n / Real.cos (Real.pi / (2 * n)) ^ (n * (n - 1)) ∧
    (∃ z : Points n, DiameterAtMost 2 z ∧ discriminant z = M n) ∧
    (∀ z : Points n, DiameterAtMost 2 z → discriminant z = M n → Statement.IsRegular z) ∧
    (∀ z w : Points n, DiameterAtMost 2 z → discriminant z = M n →
      DiameterAtMost 2 w → discriminant w = M n → DirectRigidRelabeling z w)

end
end Erdos1045.Internal

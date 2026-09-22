import StructuralNote.CommonDomainRadius
import StructuralNote.CommonTangentialParameters

/-! Closure on the literal common energy domain. The hypotheses below are only
membership in that parameter domain and a bounded word. Tangential closure,
pointwise bounds, the nonlinear source estimate, and contraction are proved. -/

namespace StructuralNote.CommonDomainClosure

open Erdos1045.EventualExact Complex Filter
open SchurSpectrum LensClosure CommonClosureEnergy CommonDomainRadius
open CommonTangentialParameters
open scoped BigOperators
noncomputable section

def InDomain {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) : Prop :=
  HalfPeriodic hm (fun j => (θ j : ℂ)) ∧ (∑ j, (θ j : ℂ)) = 0 ∧
    ParameterSpace hm v ∧
    pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v < energyRadius (2 * m)

theorem coordinates_complex_closed {m : ℕ} (hm : 0 < m) (v : Fin (2 * m) → ℂ)
    (hv : ParameterSpace hm v) :
    (∑ j, unit (midpoint m j) * ((coordinates hm v j : ℂ) * I)) = 0 := by
  have hc := (closed_iff_increment_sum _).mp (coordinates_closed hm v hv.1 hv.2.2)
  calc
    _ = ∑ j, halfIncrement (coordinates hm v) j := by
      apply Finset.sum_congr rfl
      intro j _
      unfold halfIncrement
      ring
    _ = 0 := hc

theorem exists_unique_parameter_root {m : ℕ} (hm : 128 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ)
    (hmean : ∑ j, (θ j : ℂ) = 0) (hv : ParameterSpace (by omega) v)
    (hθA : pairEnergy (by omega) (fun j => (θ j : ℂ)) ≤ 1 / (2 * m))
    (hvA : pairEnergy (by omega) v ≤ 1 / (2 * m)) (hσ : ∀ j, |σ j| ≤ 1) :
    ∃! ξ : ℂ, ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2 ∧
      closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j))
        σ (coordinates (by omega) v) ξ = 0 := by
  apply exists_unique_energy_root hm θ v (coordinates (by omega) v) σ hmean hθA hvA
  · exact coordinates_abs_le (by omega) v
  · exact coordinates_complex_closed (by omega) v hv
  · exact hσ

/-- The root conclusion in Lemma 9.1, on exactly the domain in (9.5), uniformly
over all sign words (and even over the whole real box). Pair feasibility is separate. -/
theorem eventual_common_domain_root :
    ∃ m₀ : ℕ, ∀ (m : ℕ) (hm : m₀ + 128 ≤ m)
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ),
      InDomain (by omega) θ v → (∀ j, |σ j| ≤ 1) →
      ∃! ξ : ℂ, ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2 ∧
        closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j))
          σ (coordinates (by omega) v) ξ = 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventual_radius_le_inverse
  refine ⟨N, ?_⟩
  intro m hm θ v σ hdom hσ
  have hm128 : 128 ≤ m := by omega
  have hnN : N ≤ 2 * m := by omega
  have hr := hN (2 * m) hnN
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hr
  have hsum := hdom.2.2.2.le.trans hr
  have hθ0 := pairEnergy_nonneg (by omega) (fun j => (θ j : ℂ))
  have hv0 := pairEnergy_nonneg (by omega) v
  exact exists_unique_parameter_root hm128 θ v σ hdom.2.1 hdom.2.2.1
    (by linarith) (by linarith) hσ

end
end StructuralNote.CommonDomainClosure

import StructuralNote.CommonFiberInjectivity

/-! Every constructed closure root on the literal common energy domain gives
a collision-free configuration for all sufficiently large even orders. -/

namespace StructuralNote.CommonFiberDomainInjectivity

open Erdos1045.EventualExact LensClosure FiniteFourierLift SchurSpectrum
open CommonClosureEnergy CommonTangentialParameters CommonFiberGeometry CommonDomainClosure
open CommonFiberInjectivity
open scoped BigOperators
noncomputable section

theorem small_angles_halfAngle {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (hθ : ∀ j, |θ j| ≤ 1 / (8 * (2 * m : ℝ))) (j : Fin m) :
    |halfAngle hm θ j| ≤ 5 / (2 * m : ℝ) := by
  have hn0 : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hd : |angleDifference (by omega) θ (CommonClosureEnergy.halfIndex j)| ≤
      1 / (4 * (2 * m : ℝ)) := by
    unfold angleDifference
    have he := abs_sub_le (θ (successor (by omega) (CommonClosureEnergy.halfIndex j))) 0
      (θ (CommonClosureEnergy.halfIndex j))
    simp only [sub_zero, zero_sub, abs_neg] at he
    have hnum : 1 / (4 * (2 * m : ℝ)) = 1 / (8 * (2 * m : ℝ)) + 1 / (8 * (2 * m : ℝ)) := by ring
    rw [hnum]
    exact he.trans (add_le_add (hθ _) (hθ _))
  unfold halfAngle
  have he := abs_add_le (Real.pi / (2 * m : ℝ))
    (angleDifference (by omega) θ (CommonClosureEnergy.halfIndex j) / 2)
  rw [abs_of_pos (by positivity : 0 < Real.pi / (2 * m : ℝ)), abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] at he
  have hp : Real.pi / (2 * m : ℝ) ≤ 4 / (2 * m : ℝ) := div_le_div_of_nonneg_right Real.pi_lt_four.le hn0.le
  have hnum : 4 / (2 * m : ℝ) + (1 / (4 * (2 * m : ℝ))) / 2 ≤ 5 / (2 * m : ℝ) := by
    field_simp
    linarith
  linarith

theorem eventual_injective :
    ∃ N : ℕ, ∀ (m : ℕ) (hm : N + 4096 ≤ m) (θ : Fin (2 * m) → ℝ)
      (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ), InDomain (by omega) θ v →
      (∀ j, σ j ^ 2 = 1) → ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2 →
      closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j))
        σ (coordinates (by omega) v) ξ = 0 → Function.Injective (configuration (by omega) θ v σ ξ) := by
  obtain ⟨N, hN⟩ := CommonRationalWindowBounds.eventual_domain_chart_bounds
  refine ⟨N, ?_⟩
  intro m hm θ v σ ξ hdom hs hξ hz
  obtain ⟨hθ, ht⟩ := hN m hm θ v hdom ξ hξ
  have hm0 : 0 < m := by omega
  have hinc (j : Fin m) : ‖fiberIncrement hm0 θ v σ ξ j‖ ≤ 1 / (2 * (2 * m : ℝ)) := by
    have hs' : |σ j| ≤ 1 := by nlinarith [hs j, sq_abs (σ j), abs_nonneg (σ j)]
    exact lens_increment_small (by exact_mod_cast (show 208 ≤ 2 * m by omega))
      (small_angles_halfAngle hm0 θ (fun j => (hθ j).le) j) hs' (ht j)
  apply small_center_step_injective (by omega : 4 ≤ 2 * m) θ (center hm0 θ v σ ξ)
  · intro j
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hθ j).le
  · intro j
    rw [center_difference hm0 θ v σ ξ hz]
    change ‖fiberIncrement hm0 θ v σ ξ ⟨j.val % m, Nat.mod_lt _ hm0⟩‖ ≤ _
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hinc ⟨j.val % m, Nat.mod_lt _ hm0⟩

end
end StructuralNote.CommonFiberDomainInjectivity

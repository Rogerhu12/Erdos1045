import StructuralNote.CommonRationalChart
import EventualExact.WholeBoxObjective
import Erdos1045.LocalConfiguration
import Erdos1045.ClosedRegularGeometry

/-! Collision freedom of the actual common-fiber configurations follows from
their small angular displacement and their uniformly small center increments. -/

namespace StructuralNote.CommonFiberInjectivity

open Erdos1045 Erdos1045.EventualExact LensClosure FiniteFourierLift FourierMultiplier SchurSpectrum
open CommonClosureEnergy CommonTangentialParameters CommonFiberGeometry CommonDomainClosure
open scoped BigOperators
noncomputable section

theorem diameter_displacement {n : ℕ} (θ : Fin n → ℝ) (j : Fin n) :
    ‖diameterVector θ j - character n 1 j‖ ≤ |θ j| := by
  have he : diameterVector θ j - character n 1 j = character n 1 j * (unit (θ j) - 1) := by
    unfold diameterVector
    ring
  rw [he, norm_mul]
  have hc : ‖character n 1 j‖ = 1 := by simp [character, norm_pow, ClosedFourier.root_norm]
  rw [hc, one_mul]
  simpa only [unit, Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_zero] using norm_unit_sub_le (θ j) 0

theorem small_center_step_injective {n : ℕ} (hn : 4 ≤ n) (θ : Fin n → ℝ) (c : Fin n → ℂ)
    (hθ : ∀ j, |θ j| ≤ 1 / (8 * (n : ℝ)))
    (hc : ∀ j, ‖difference (by omega) c j‖ ≤ 1 / (2 * (n : ℝ))) :
    Function.Injective (fun j => diameterVector θ j + c j) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let u : Fin n → ℂ := fun j => diameterVector θ j - character n 1 j + c j
  have hstep (j : Fin n) : ‖difference (by omega) u j‖ ≤ 1 / (n : ℝ) := by
    have he : difference (by omega) u j =
        (diameterVector θ (successor (by omega) j) - character n 1 (successor (by omega) j)) -
        (diameterVector θ j - character n 1 j) + difference (by omega) c j := by
      unfold difference u
      ring
    rw [he]
    have hb : ‖(diameterVector θ (successor (by omega) j) - character n 1 (successor (by omega) j)) -
        (diameterVector θ j - character n 1 j) + difference (by omega) c j‖ ≤
        ‖diameterVector θ (successor (by omega) j) - character n 1 (successor (by omega) j)‖ +
        ‖diameterVector θ j - character n 1 j‖ + ‖difference (by omega) c j‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    have h₁ := (diameter_displacement θ (successor (by omega) j)).trans (hθ _)
    have h₂ := (diameter_displacement θ j).trans (hθ j)
    have hsum : 1 / (8 * (n : ℝ)) + 1 / (8 * (n : ℝ)) + 1 / (2 * (n : ℝ)) ≤ 1 / n := by
      field_simp
      nlinarith
    exact hb.trans ((add_le_add (add_le_add h₁ h₂) (hc j)).trans hsum)
  have hinj := LocalConfiguration.small_perturbation_injective ClosedFourier.geometricSine hn
    (periodize (by omega) u) (periodize_periodic _ _)
    (η := 1 / 4) (by norm_num) (by norm_num) (by
      intro j
      rw [WholeBoxObjective.periodize_difference]
      have he : (1 : ℝ) / n = (1 / 4) * (4 / n) := by ring
      exact (hstep _).trans (he ▸ mul_le_mul_of_nonneg_left (GapRigidity.root_edge_lower (by omega)) (by norm_num)))
  have he (j : Fin n) : LocalObjective.perturbedVertices n (periodize (by omega) u) j =
      diameterVector θ j + c j := by
    have hr : LocalObjective.regularVertices n j = character n 1 j := by
      simp [LocalObjective.regularVertices, character]
    simp only [LocalObjective.perturbedVertices, periodize, Nat.mod_eq_of_lt j.isLt, hr, u]
    ring
  intro i j hij
  exact hinj ((he i).trans (hij.trans (he j).symm))

theorem lens_increment_small {n a s t β : ℝ} (hn : 208 ≤ n) (ha : |a| ≤ 5 / n)
    (hs : |s| ≤ 1) (ht : |t| ≤ 1 / (4 * n)) :
    ‖increment β (2 * Real.cos a) s t‖ ≤ 1 / (2 * n) := by
  have hn0 : 0 < n := by linarith
  have ht1 : |t| ≤ 1 := ht.trans ((div_le_one (by positivity)).2 (by linarith))
  have ht4 : t ^ 2 ≤ 4 := by nlinarith [sq_abs t, abs_nonneg t]
  have hcos : |2 - 2 * Real.cos a| ≤ a ^ 2 := by
    rw [abs_of_nonneg (by linarith [Real.cos_le_one a])]
    linarith [Real.one_sub_sq_div_two_le_cos (x := a)]
  have hw : |Lens.height t - 2 * Real.cos a| ≤ t ^ 2 / 2 + a ^ 2 := by
    have he : Lens.height t - 2 * Real.cos a = (Lens.height t - 2) + (2 - 2 * Real.cos a) := by ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add (BoxLensLift.height_defect ht4) hcos)
  have hta : t ^ 2 ≤ 1 / (16 * n ^ 2) := by
    have hh := pow_le_pow_left₀ (abs_nonneg t) ht 2
    simpa only [sq_abs, div_pow, one_pow, mul_pow, show (4 : ℝ) ^ 2 = 16 by norm_num] using hh
  have haa : a ^ 2 ≤ 25 / n ^ 2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg a) ha 2
    simpa only [sq_abs, div_pow, show (5 : ℝ) ^ 2 = 25 by norm_num] using hh
  rw [increment, norm_mul, norm_unit, one_mul]
  unfold Lens.width
  have hb := norm_add_le (((s * (Lens.height t - 2 * Real.cos a) : ℝ) : ℂ)) ((t : ℂ) * Complex.I)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hb
  have hs' := mul_le_mul_of_nonneg_right hs (abs_nonneg (Lens.height t - 2 * Real.cos a))
  have he : 1 / (16 * n ^ 2) / 2 + 25 / n ^ 2 + 1 / (4 * n) ≤ 1 / (2 * n) := by
    field_simp
    nlinarith
  nlinarith

end
end StructuralNote.CommonFiberInjectivity

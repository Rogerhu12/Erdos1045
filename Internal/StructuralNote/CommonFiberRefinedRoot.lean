import StructuralNote.CommonFiberCanonical
import StructuralNote.CommonClosureIncrements
import EventualExact.AngularObjectiveCurvature

/-! The first-moment refinement of the actual canonical closure root at zero
continuous parameters. Smallness of this explicit word moment remains an input. -/

namespace StructuralNote.CommonFiberRefinedRoot

open Erdos1045.EventualExact Complex LensClosure
open FiniteFourierLift SchurLift SchurSpectrum AngularObjectiveCurvature
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure
open CommonFiberGeometry CommonFiberSmooth CommonFiberCanonical CommonClosureDifference
open scoped BigOperators
noncomputable section

/-- The normalized first harmonic of the actual half word in midpoint coordinates. -/
def firstMoment {m : ℕ} (σ : Fin m → ℝ) : ℂ :=
  (∑ j, unit (midpoint m j) * (σ j : ℂ)) / (m : ℂ)

def zeroWidth (n : ℕ) : ℝ := 2 - 2 * Real.cos (Real.pi / n)

theorem zeroWidth_nonneg (n : ℕ) : 0 ≤ zeroWidth n := by
  unfold zeroWidth
  linarith [Real.cos_le_one (Real.pi / n)]

theorem zeroWidth_bound {n : ℕ} (hn : 0 < n) : zeroWidth n ≤ 16 / (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := Real.one_sub_sq_div_two_le_cos (x := Real.pi / n)
  have hp : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hb := div_le_div_of_nonneg_right hp (sq_nonneg (n : ℝ))
  unfold zeroWidth
  rw [div_pow] at hc
  linarith

theorem zeroWidth_eq (n : ℕ) : Lens.width (2 * Real.cos (Real.pi / n)) 0 = zeroWidth n := by
  norm_num [Lens.width, Lens.height, zeroWidth]

theorem zero_phase {m : ℕ} (hm : 0 < m) : phase hm (0 : Fin (2 * m) → ℝ) = midpoint m := by
  funext j
  simp [phase, angleAverage]

theorem zero_halfAngle {m : ℕ} (hm : 0 < m) (j : Fin m) :
    halfAngle hm (0 : Fin (2 * m) → ℝ) j = Real.pi / (2 * m : ℝ) := by
  simp [halfAngle, angleDifference]

theorem zero_coordinates {m : ℕ} (hm : 0 < m) : coordinates hm (0 : Fin (2 * m) → ℂ) = 0 := by
  funext j
  simp [coordinates, difference]

theorem zero_parameterSpace {m : ℕ} (hm : 0 < m) : ParameterSpace hm (0 : Fin (2 * m) → ℂ) := by
  refine ⟨fun _ => rfl, by simp, ?_⟩
  funext j
  simp [constraint, difference]

theorem zero_pairEnergy {n : ℕ} (hn : 0 < n) : pairEnergy hn (0 : Fin n → ℂ) = 0 := by
  rw [pairEnergy_eq_chord_sum]
  simp

theorem canonical_zero_spec {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ) (hσ : ∀ j, |σ j| ≤ 1) :
    RootCondition (by omega) σ (0, 0) (root (by omega) σ (0, 0)) := by
  have he : ∃! ξ, RootCondition (by omega) σ (0, 0) ξ := by
    apply exists_unique_parameter_root hm 0 0 σ
    · simp
    · exact zero_parameterSpace (by omega)
    · simpa only [Pi.zero_apply, ofReal_zero, ← Pi.zero_def, zero_pairEnergy] using
        (show (0 : ℝ) ≤ 1 / (2 * m : ℝ) by positivity)
    · rw [zero_pairEnergy]
      positivity
    · exact hσ
  have hex := he.exists
  rw [root, dif_pos hex]
  exact Classical.choose_spec hex

theorem closure_at_zero {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) :
    closure (midpoint m) (fun _ => 2 * Real.cos (Real.pi / (2 * m : ℝ))) σ 0 0 =
      ((zeroWidth (2 * m) : ℝ) : ℂ) * (m : ℂ) * firstMoment σ := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hj (j : Fin m) : increment (midpoint m j) (2 * Real.cos (Real.pi / (2 * m : ℝ)))
      (σ j) (heightParameter 0 0 j) =
      (zeroWidth (2 * m) : ℂ) * (unit (midpoint m j) * (σ j : ℂ)) := by
    simp only [heightParameter, Pi.zero_apply, map_zero, add_zero, LensClosure.increment,
      ofReal_zero, zero_mul, add_zero]
    have hw : Lens.width (2 * Real.cos (Real.pi / (2 * m : ℝ))) 0 = zeroWidth (2 * m) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using zeroWidth_eq (2 * m)
    rw [hw, ofReal_mul]
    ring
  simp only [LensClosure.closure, hj, ← Finset.mul_sum, firstMoment]
  field_simp

theorem actual_zero_root_bound {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ)
    (hσ : ∀ j, |σ j| ≤ 1) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hz : closure (midpoint m) (fun _ => 2 * Real.cos (Real.pi / (2 * m : ℝ))) σ 0 ξ = 0) :
    ‖ξ‖ ≤ 64 * ‖firstMoment σ‖ / (2 * m : ℝ) ^ 2 := by
  have hmR : (128 : ℝ) ≤ m := by exact_mod_cast hm
  have hR0 : (0 : ℝ) ≤ 1024 / (2 * m : ℝ) ^ 2 := by positivity
  have hR : (1024 : ℝ) / (2 * m : ℝ) ^ 2 ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 * m : ℝ) ^ 2)).mpr
    nlinarith
  have hb := root_residual_bound (by omega : 2 ≤ m) (midpoint m)
    (fun _ => 2 * Real.cos (Real.pi / (2 * m : ℝ))) σ 0 hσ
    (fun j => by simpa only [sub_self, abs_zero, Pi.zero_apply, zero_add] using hR)
    hξ (show ‖(0 : ℂ)‖ ≤ 1024 / (2 * m : ℝ) ^ 2 by simpa only [norm_zero] using hR0) hz
  rw [sub_zero, closure_at_zero (by omega), norm_mul, norm_mul, norm_real,
    Real.norm_eq_abs, abs_of_nonneg (zeroWidth_nonneg _), norm_natCast] at hb
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have he : (4 / m : ℝ) * (zeroWidth (2 * m) * m * ‖firstMoment σ‖) =
      4 * zeroWidth (2 * m) * ‖firstMoment σ‖ := by field_simp
  rw [he] at hb
  have hw := zeroWidth_bound (show 0 < 2 * m by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hw
  apply hb.trans
  calc
    _ ≤ 4 * (16 / (2 * m : ℝ) ^ 2) * ‖firstMoment σ‖ := by gcongr
    _ = _ := by ring

theorem canonical_zero_root_bound {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ)
    (hσ : ∀ j, |σ j| ≤ 1) :
    ‖root (by omega) σ (0, 0)‖ ≤ 64 * ‖firstMoment σ‖ / (2 * m : ℝ) ^ 2 := by
  have hs := canonical_zero_spec hm σ hσ
  have hz : closure (midpoint m) (fun _ => 2 * Real.cos (Real.pi / (2 * m : ℝ))) σ 0
      (root (by omega) σ (0, 0)) = 0 := by
    simpa only [RootCondition, closureFamily, data, zero_phase, zero_halfAngle, zero_coordinates] using hs.2
  exact actual_zero_root_bound hm σ hσ hs.1 hz

theorem canonical_zero_root_cubic {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ)
    (hσ : ∀ j, |σ j| ≤ 1) {B : ℝ} (hM : ‖firstMoment σ‖ ≤ B / (2 * m : ℝ)) :
    ‖root (by omega) σ (0, 0)‖ ≤ 64 * B / (2 * m : ℝ) ^ 3 := by
  apply (canonical_zero_root_bound hm σ hσ).trans
  calc
    _ ≤ 64 * (B / (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by gcongr
    _ = _ := by ring

theorem canonical_zero_height_cubic {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ)
    (hσ : ∀ j, |σ j| ≤ 1) {B : ℝ} (hM : ‖firstMoment σ‖ ≤ B / (2 * m : ℝ)) (j : Fin m) :
    |heightParameter (coordinates (by omega) (0 : Fin (2 * m) → ℂ))
      (root (by omega) σ (0, 0)) j| ≤ 64 * B / (2 * m : ℝ) ^ 3 := by
  rw [zero_coordinates, heightParameter, Pi.zero_apply, zero_add]
  exact (harmonicFunctional_le_norm _ _).trans (canonical_zero_root_cubic hm σ hσ hM)

theorem canonical_zero_root_eq_zero {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ)
    (hσ : ∀ j, |σ j| ≤ 1) (hM : firstMoment σ = 0) : root (by omega) σ (0, 0) = 0 := by
  have h := canonical_zero_root_bound hm σ hσ
  rw [hM, norm_zero, mul_zero, zero_div] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

end
end StructuralNote.CommonFiberRefinedRoot

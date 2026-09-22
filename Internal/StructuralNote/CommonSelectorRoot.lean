import StructuralNote.CommonDomainClosure
import EventualExact.LensClosureSmooth

/-! The literal n^(-3/2) selector window contains the constructed closure root
and has no additional roots on the common energy domain. -/

namespace StructuralNote.CommonSelectorRoot

open Erdos1045.EventualExact LensClosure SchurSpectrum
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure CommonDomainRadius
open scoped BigOperators
noncomputable section

def rootWindow (n : ℕ) : ℝ := 1 / ((n : ℝ) * Real.sqrt n)

theorem rootWindow_eq_rpow {n : ℕ} (hn : 0 < n) : rootWindow n = (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show -(3 / 2 : ℝ) = -(1 + 1 / 2) by norm_num,
    Real.rpow_neg hnR.le, Real.rpow_add hnR, Real.rpow_one, ← Real.sqrt_eq_rpow]
  simp only [rootWindow, one_div]

theorem rootWindow_pos {n : ℕ} (hn : 0 < n) : 0 < rootWindow n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold rootWindow
  positivity

theorem rootWindow_le_inverse {n : ℕ} (hn : 1 ≤ n) : rootWindow n ≤ 1 / (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt n := (Real.one_le_sqrt).2 hnR
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem constructed_radius_lt_window {n : ℕ} (hn : 2097152 ≤ n) :
    1024 / (n : ℝ) ^ 2 < rootWindow n := by
  have hnR : (2097152 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hs2 := Real.sq_sqrt hn0.le
  have hs : 1024 < Real.sqrt n := by nlinarith
  have hmul := mul_pos (sub_pos.mpr hs) hs0
  have hmul' := mul_pos hn0 (show 0 < (n : ℝ) - 1024 * Real.sqrt n by nlinarith)
  unfold rootWindow
  apply (div_lt_div_iff₀ (sq_pos_of_pos hn0) (mul_pos hn0 hs0)).2
  nlinarith

theorem closure_window_small {m : ℕ} (hm : 1048576 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hmean : ∑ j, (θ j : ℂ) = 0)
    (hθ : pairEnergy (by omega) (fun j => (θ j : ℂ)) ≤ 1 / (2 * m))
    (hv : pairEnergy (by omega) v ≤ 1 / (2 * m)) (j : Fin m) :
    |phase (by omega) θ j - midpoint m j| + |coordinates (by omega) v j| + rootWindow (2 * m) ≤ 1 / 4 := by
  have hmR : (1048576 : ℝ) ≤ m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have hθ' : pairEnergy (by omega) (fun j => (θ j : ℂ)) ≤ 1 / ((2 * m : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hθ
  have hv' : pairEnergy (by omega) v ≤ 1 / ((2 * m : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hv
  have ha := angleAverage_le (by omega : 2 ≤ 2 * m) θ hmean hθ' (CommonClosureEnergy.halfIndex j)
  have ht := (coordinates_abs_le (by omega) v j).trans
    (difference_of_small_energy (by omega) v hv' (BoxLensLift.halfIndex j))
  have hr := rootWindow_le_inverse (show 1 ≤ 2 * m by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at ha ht hr
  have he : 4 / (2 * (m : ℝ)) + 10 / (2 * (m : ℝ)) + 1 / (2 * (m : ℝ)) ≤ 1 / 4 := by
    apply (le_of_mul_le_mul_right ?_ hn0)
    field_simp
    linarith
  simpa only [phase, add_sub_cancel_left] using (add_le_add (add_le_add ha ht) hr).trans he

/-- The wider selector window identifies exactly the constructed small root. -/
theorem parameter_window_root {m : ℕ} (hm : 1048576 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ)
    (hmean : ∑ j, (θ j : ℂ) = 0) (hv : ParameterSpace (by omega) v)
    (hθA : pairEnergy (by omega) (fun j => (θ j : ℂ)) ≤ 1 / (2 * m))
    (hvA : pairEnergy (by omega) v ≤ 1 / (2 * m)) (hσ : ∀ j, |σ j| ≤ 1) :
    ∃ ξ : ℂ, ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2 ∧ ‖ξ‖ < rootWindow (2 * m) ∧
      closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j))
        σ (coordinates (by omega) v) ξ = 0 ∧
      ∀ η : ℂ, ‖η‖ < rootWindow (2 * m) →
        closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j))
          σ (coordinates (by omega) v) η = 0 → η = ξ := by
  obtain ⟨ξ, hξ, _⟩ := exists_unique_parameter_root (by omega : 128 ≤ m) θ v σ hmean hv hθA hvA hσ
  have hr : 1024 / (2 * m : ℝ) ^ 2 < rootWindow (2 * m) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using constructed_radius_lt_window (show 2097152 ≤ 2 * m by omega)
  refine ⟨ξ, hξ.1, hξ.1.trans_lt hr, hξ.2, ?_⟩
  intro η hη hz
  exact closure_roots_eq_on_ball (by omega)
    (phase (by omega) θ, (fun j => 2 * Real.cos (halfAngle (by omega) θ j)), σ, coordinates (by omega) v)
    hσ (closure_window_small hm θ v hmean hθA hvA) hη.le (hξ.1.trans hr.le) hz hξ.2

theorem eventual_common_domain_window_root :
    ∃ N : ℕ, ∀ (m : ℕ) (hm : N + 1048576 ≤ m)
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ),
      InDomain (by omega) θ v → (∀ j, |σ j| ≤ 1) →
      ∃ ξ : ℂ, ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2 ∧ ‖ξ‖ < rootWindow (2 * m) ∧
        closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j))
          σ (coordinates (by omega) v) ξ = 0 ∧
        ∀ η : ℂ, ‖η‖ < rootWindow (2 * m) →
          closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j))
            σ (coordinates (by omega) v) η = 0 → η = ξ := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp eventual_radius_le_inverse
  refine ⟨N, ?_⟩
  intro m hm θ v σ hdom hσ
  have hr := hN (2 * m) (show N ≤ 2 * m by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hr
  have hsum := hdom.2.2.2.le.trans hr
  have hθ0 := pairEnergy_nonneg (by omega) (fun j => (θ j : ℂ))
  have hv0 := pairEnergy_nonneg (by omega) v
  exact parameter_window_root (by omega) θ v σ hdom.2.1 hdom.2.2.1 (by linarith) (by linarith) hσ

end
end StructuralNote.CommonSelectorRoot

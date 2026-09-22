import StructuralNote.CommonFiberHessianGeometryEnergy
import StructuralNote.CommonFiberFullSecond

/-! The actual common-fiber velocity approaches its regular linear model in
pair energy, uniformly over all directions of unit total energy. -/

namespace StructuralNote.CommonFiberHessianGeometryVelocity

open Erdos1045 Erdos1045.EventualExact Complex Filter LensClosure
open FiniteFourierLift SchurSpectrum AngularObjectiveCurvature DiscreteEnergy
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure CommonDomainRadius
open CommonFiberGeometry CommonFiberFirstDerivative CommonFiberFullSecond
open CommonFiberHessianGeometryChord CommonFiberHessianGeometryEnergy
open CommonFiberDifferentialEstimate SignedPressureAngular
open scoped BigOperators Topology
noncomputable section

def velocityError {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ) (ξ' : ℂ) :
    Fin (2 * m) → ℂ :=
  fun j => fullVelocity hm θ v σ ξ η h ξ' j - (I * root (2 * m) j * (η j : ℂ) + h j)

theorem velocityError_eq {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (ξ' : ℂ) :
    velocityError hm θ v σ ξ η h ξ' =
      (fun j => I * angularError θ j * (η j : ℂ)) +
        (centerVelocity hm θ v σ ξ η h ξ' - h) := by
  funext j
  simp only [velocityError, fullVelocity, Pi.add_apply, Pi.sub_apply, angularError]
  ring

theorem logarithmic_coefficient {n : ℕ} (hn : 0 < n)
    (hr : energyRadius n ≤ 1 / (n : ℝ)) :
    (logOrder n : ℝ) ^ 2 * Real.log n / (n : ℝ) ^ 3 ≤ 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hnR).trans (by linarith)
  calc
    _ ≤ (logOrder n : ℝ) ^ 2 * n / (n : ℝ) ^ 3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl (sq_nonneg _)) (by positivity)
    _ = energyRadius n := by unfold energyRadius; field_simp
    _ ≤ _ := hr

theorem velocity_energy_coarse {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (ξ' : ℂ)
    (hdom : InDomain hm θ v) (hmean : ∑ j, (η j : ℂ) = 0)
    (hr : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ))
    (hc : pairEnergy (by omega) (centerVelocity hm θ v σ ξ η h ξ' - h) ≤
      4000000000 / (2 * m : ℝ) * realEnergy (by omega) η +
      4000000000 * (logOrder (2 * m) : ℝ) ^ 2 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 3 *
        pairEnergy (by omega) h) :
    pairEnergy (by omega) (velocityError hm θ v σ ξ η h ξ') ≤
      10000000000 / (2 * m : ℝ) * (realEnergy (by omega) η + pairEnergy (by omega) h) := by
  have hA := pairEnergy_nonneg (by omega : 0 < 2 * m) h
  have hE : 0 ≤ realEnergy (by omega) η := pairEnergy_nonneg _ _
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hlog := logarithmic_coefficient (by omega : 0 < 2 * m)
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hr)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hlog
  have hcoef : 4000000000 * (logOrder (2 * m) : ℝ) ^ 2 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 3 ≤
      4000000000 / (2 * m : ℝ) := by
    calc
      _ = 4000000000 * ((logOrder (2 * m) : ℝ) ^ 2 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 3) := by ring
      _ ≤ 4000000000 * (1 / (2 * m : ℝ)) := mul_le_mul_of_nonneg_left hlog (by norm_num)
      _ = _ := by ring
  have hc' : pairEnergy (by omega) (centerVelocity hm θ v σ ξ η h ξ' - h) ≤
      4000000000 / (2 * m : ℝ) * (realEnergy (by omega) η + pairEnergy (by omega) h) := by
    have hh := mul_le_mul_of_nonneg_right hcoef hA
    nlinarith only [hc, hh]
  have ha := domain_angularError_energy hm θ v hdom η hmean
  have hra : 600 * (logOrder (2 * m) : ℝ) ^ 2 / (2 * m : ℝ) ^ 2 ≤ 600 / (2 * m : ℝ) := by
    have ht := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 600)
    simpa only [energyRadius, Nat.cast_mul, Nat.cast_ofNat, ← mul_div_assoc, mul_one] using ht
  have ha' := ha.trans (mul_le_mul_of_nonneg_right hra hE)
  rw [velocityError_eq]
  have hs := QuadraticStability.pairEnergy_add_le (by omega : 0 < 2 * m)
    (fun j => I * angularError θ j * (η j : ℂ)) (centerVelocity hm θ v σ ξ η h ξ' - h)
  have hn0 : 0 ≤ (2 * m : ℝ)⁻¹ := inv_nonneg.mpr hn.le
  simp only [div_eq_mul_inv] at hc' ha' ⊢
  nlinarith only [hs, hc', ha', mul_nonneg hn0 hE, mul_nonneg hn0 hA]

theorem eventual_actual_velocity_error : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (θ : ℝ → Fin (2 * m) → ℝ) (v : ℝ → Fin (2 * m) → ℂ)
      (ξ : ℝ → ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ) (ξ' : ℂ) (x : ℝ) (σ : Fin m → ℝ),
    (∀ j, HasDerivAt (fun s => θ s j) (η j) x) →
    (∀ j, HasDerivAt (fun s => v s j) (h j) x) → HasDerivAt ξ ξ' x →
    InDomain hm (θ x) (v x) → ‖ξ x‖ ≤ 1024 / (2 * m : ℝ) ^ 2 →
    (∑ j, (η j : ℂ)) = 0 → ParameterSpace hm h → (∀ j, |σ j| ≤ 1) →
    (∀ᶠ s in 𝓝 x, closure (phase hm (θ s)) (fun j => 2 * Real.cos (halfAngle hm (θ s) j))
      σ (coordinates hm (v s)) (ξ s) = 0) →
    pairEnergy (by omega) (velocityError hm (θ x) (v x) σ (ξ x) η h ξ') ≤
      10000000000 / (2 * m : ℝ) * (realEnergy (by omega) η + pairEnergy (by omega) h) := by
  filter_upwards [eventual_actual_first_derivative, eventual_size_conditions] with m hfirst hsize
  intro hm θ v ξ η h ξ' x σ hθ hv hξ hdom hroot hmean hh hσ hz
  have hf := (hfirst hm θ v ξ η h ξ' x σ hθ hv hξ hdom hroot hmean hh hσ hz).2
  exact velocity_energy_coarse hm (θ x) (v x) σ (ξ x) η h ξ' hdom hmean hsize.2.1 hf

theorem eventual_actual_velocity_error_small (ε : ℝ) (hε : 0 < ε) : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (θ : ℝ → Fin (2 * m) → ℝ) (v : ℝ → Fin (2 * m) → ℂ)
      (ξ : ℝ → ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ) (ξ' : ℂ) (x : ℝ) (σ : Fin m → ℝ),
    (∀ j, HasDerivAt (fun s => θ s j) (η j) x) →
    (∀ j, HasDerivAt (fun s => v s j) (h j) x) → HasDerivAt ξ ξ' x →
    InDomain hm (θ x) (v x) → ‖ξ x‖ ≤ 1024 / (2 * m : ℝ) ^ 2 →
    (∑ j, (η j : ℂ)) = 0 → ParameterSpace hm h → (∀ j, |σ j| ≤ 1) →
    (∀ᶠ s in 𝓝 x, closure (phase hm (θ s)) (fun j => 2 * Real.cos (halfAngle hm (θ s) j))
      σ (coordinates hm (v s)) (ξ s) = 0) →
    pairEnergy (by omega) (velocityError hm (θ x) (v x) σ (ξ x) η h ξ') ≤
      ε ^ 2 * (realEnergy (by omega) η + pairEnergy (by omega) h) := by
  have hreal : Tendsto (fun m : ℕ => (2 * m : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hlim : Tendsto (fun m : ℕ => 10000000000 / (2 * m : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using (tendsto_inv_atTop_zero.comp hreal).const_mul 10000000000
  filter_upwards [eventual_actual_velocity_error,
    hlim.eventually (gt_mem_nhds (sq_pos_of_pos hε))] with m herror hcoef
  intro hm θ v ξ η h ξ' x σ hθ hv hξ hdom hroot hmean hh hσ hz
  apply (herror hm θ v ξ η h ξ' x σ hθ hv hξ hdom hroot hmean hh hσ hz).trans
  exact mul_le_mul_of_nonneg_right hcoef.le (add_nonneg (pairEnergy_nonneg _ _) (pairEnergy_nonneg _ _))

end
end StructuralNote.CommonFiberHessianGeometryVelocity

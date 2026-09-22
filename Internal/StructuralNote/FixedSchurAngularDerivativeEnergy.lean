import StructuralNote.FixedSchurChartQuotients
import StructuralNote.CommonFiberHessianGeometryEnergy

/-! Physical angular velocity and acceleration energies for the literal
fixed-Schur domain. No angular L-infinity hypothesis is supplied separately. -/

namespace StructuralNote.FixedSchurAngularDerivativeEnergy

open Complex Filter Erdos1045.EventualExact SchurSpectrum
open CommonDomainClosure CommonFiberGeometry CommonFiberHessianGeometryEnergy
open GeometricRelativeRemainder SignedPressureAngular FixedSchurChartQuotients
open scoped BigOperators Topology

noncomputable section

theorem diameter_quotient_le {n : ℕ} (θ : Fin n → ℝ)
    (hx : ∀ p, ‖quotient (diameterVector θ - root n) (root n) p‖ ≤ 1 / 4)
    (i j : Fin n) : ‖quotient (diameterVector θ) (root n) (i, j)‖ ≤ 2 := by
  have he : quotient (diameterVector θ) (root n) (i, j) =
      quotient (diameterVector θ - root n) (root n) (i, j) +
        quotient (root n) (root n) (i, j) := by
    simp only [quotient, Pi.sub_apply]
    ring
  have hr : ‖quotient (root n) (root n) (i, j)‖ ≤ 1 := by
    by_cases hz : root n i - root n j = 0
    · simp [quotient, hz]
    · simp [quotient, div_self hz]
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add (hx (i, j)) hr).trans (by norm_num))

theorem angular_velocity_energy {n : ℕ} (hn : 2 ≤ n) (θ η : Fin n → ℝ)
    (hmean : ∑ j, (η j : ℂ) = 0)
    (hq : ∀ i j, ‖quotient (diameterVector θ) (root n) (i, j)‖ ≤ 2) :
    pairEnergy (by omega) (fun j => diameterVector θ j * (η j : ℂ)) ≤
      18 * pairEnergy (by omega) (fun j => (η j : ℂ)) := by
  have h := product_energy hn (diameterVector θ) η hmean
    (fun j => (diameterVector_norm θ j).le) hq
  norm_num at h
  exact h

theorem angular_acceleration_energy {n : ℕ} (hn : 2 ≤ n) (θ η : Fin n → ℝ)
    (hmean : ∑ j, (η j : ℂ) = 0)
    (hq : ∀ i j, ‖quotient (diameterVector θ) (root n) (i, j)‖ ≤ 2) :
    pairEnergy (by omega) (fun j => -diameterVector θ j * (η j : ℂ) ^ 2) ≤
      500 * Real.log (n : ℝ) / (n : ℝ) ^ 2 *
        pairEnergy (by omega) (fun j => (η j : ℂ)) ^ 2 := by
  let e : Fin n → ℂ := fun j => (η j : ℂ)
  let d : Fin n → ℂ := fun j => diameterVector θ j * e j
  have hn0 : 0 < n := by omega
  have hE := pairEnergy_nonneg hn0 e
  have hd : pairEnergy hn0 d ≤ 18 * pairEnergy hn0 e := angular_velocity_energy hn θ η hmean hq
  have hd_norm : ‖d‖ ≤ ‖e‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg e)).2
    intro j
    simpa only [d, norm_mul, diameterVector_norm, one_mul] using norm_le_pi_norm e j
  have hd_sq := pow_le_pow_left₀ (norm_nonneg d) hd_norm 2
  have hp := pairEnergy_mul_le hn0 d e
  have hmain : pairEnergy hn0 (fun j => d j * e j) ≤ 38 * ‖e‖ ^ 2 * pairEnergy hn0 e := by
    have h1 := mul_le_mul_of_nonneg_right hd_sq hE
    have h2 := mul_le_mul_of_nonneg_left hd (sq_nonneg ‖e‖)
    nlinarith only [hp, h1, h2]
  have hs := DiscreteSobolev.sup_sq_le hn e hmean
  have hb := mul_le_mul_of_nonneg_right hs hE
  have he : (fun j => -diameterVector θ j * (η j : ℂ) ^ 2) =
      fun j => (-1 : ℂ) * (d j * e j) := by funext j; dsimp [d, e]; ring
  rw [he, RadialInterpolationEnergy.pairEnergy_scale, norm_neg, norm_one, one_pow, one_mul]
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hnonneg : 0 ≤ Real.log (n : ℝ) / (n : ℝ) ^ 2 * pairEnergy hn0 e ^ 2 := by positivity
  change _ ≤ 500 * Real.log (n : ℝ) / (n : ℝ) ^ 2 * pairEnergy hn0 e ^ 2
  ring_nf at hmain hb hnonneg ⊢
  linarith only [hmain, hb, hnonneg]

theorem eventual_angular_derivative_energy : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
      (θ η : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → (∑ j, (η j : ℂ) = 0) →
      pairEnergy (by omega) (fun j => I * diameterVector θ j * (η j : ℂ)) ≤
        18 * pairEnergy (by omega) (fun j => (η j : ℂ)) ∧
      pairEnergy (by omega) (fun j => -diameterVector θ j * (η j : ℂ) ^ 2) ≤
        500 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 *
          pairEnergy (by omega) (fun j => (η j : ℂ)) ^ 2 := by
  filter_upwards [eventual_quotient_properties] with m hquot
  intro hm s θ η v hdom hmean
  have hq := diameter_quotient_le θ (hquot hm s θ v hdom).2.2.1
  constructor
  · have he : (fun j => I * diameterVector θ j * (η j : ℂ)) =
        fun j => I * (diameterVector θ j * (η j : ℂ)) := by funext j; ring
    rw [he, RadialInterpolationEnergy.pairEnergy_scale, norm_I, one_pow, one_mul]
    exact angular_velocity_energy (by omega) θ η hmean hq
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using angular_acceleration_energy (by omega) θ η hmean hq

end
end StructuralNote.FixedSchurAngularDerivativeEnergy

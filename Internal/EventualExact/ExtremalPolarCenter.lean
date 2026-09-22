import EventualExact.ExtremalPolarAngles
import EventualExact.PolarCenterNormalization

/-! The corrected polar center and its strict Schur gap for genuine extremizers. -/

namespace Erdos1045.EventualExact.ExtremalPolarCenter

open Complex Filter Configuration CommonLocalization AntipodalDecomposition FourierMultiplier
open FiniteFourierLift SchurLift SchurSpectrum SchurLiftBounds PolarAngleControl
open PolarCenterNormalization ExtremalEnergyBound
open scoped BigOperators Topology
noncomputable section

def angles (m : ℕ) (u : ℕ → ℂ) : Fin (2 * m) → ℝ := fun j => angle m u j

def physicalCenter (m : ℕ) (β : ℂ) (u : ℕ → ℂ) : Fin (2 * m) → ℂ :=
  fun j => (‖β‖ : ℂ) * evenSequence m u j

def polarCenter (m : ℕ) (β : ℂ) (u : ℕ → ℂ) : Fin (2 * m) → ℂ :=
  correctedCenter (angles m u) (physicalCenter m β u)

def polarConstraint {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ) : Fin (2 * m) → ℝ :=
  constraint (by omega) (polarCenter m β u)

def constraintErrorBudget (n : ℕ) : ℝ :=
  4352 * Real.pi ^ 4 * n * sizeBudget n + 64 * Real.pi ^ 2 * (256 * Real.pi ^ 2 / (n : ℝ) ^ 2) ^ 2

theorem sizeBudget_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ sizeBudget n := by
  unfold sizeBudget
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  positivity

theorem sup_sq_of_pointwise {ι : Type*} [Fintype ι] (f : ι → ℂ) {S : ℝ}
    (hS : 0 ≤ S) (hf : ∀ j, ‖f j‖ ^ 2 ≤ S) : ‖f‖ ^ 2 ≤ S := by
  have hb : ‖f‖ ≤ Real.sqrt S := (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    (fun j => Real.le_sqrt_of_sq_le (hf j))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rwa [Real.sq_sqrt hS] at hs

theorem physicalCenter_mean_zero {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (hmean : (∑ j ∈ Finset.range (2 * m), u j) = 0) :
    ∑ j, physicalCenter m β u j = 0 := by
  simp only [physicalCenter, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (evenSequence m u), evenSequence_mean_zero hm u hu hmean, mul_zero]

theorem even_full_period {m : ℕ} (u : ℕ → ℂ) (hu : Function.Periodic u (2 * m)) :
    Function.Periodic (evenSequence m u) (2 * m) := by
  intro j
  rw [show j + 2 * m = (j + m) + m by omega, evenSequence_periodic m u hu, evenSequence_periodic m u hu]

theorem physicalCenter_halfPeriodic {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) : HalfPeriodic hm (physicalCenter m β u) := by
  intro j
  change (‖β‖ : ℂ) * evenSequence m u ((j.val + m) % (2 * m)) = _
  rw [← CyclicAngles.periodic_mod _ (even_full_period u hu), evenSequence_periodic m u hu]
  rfl

theorem angles_halfPeriodic {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) : ∀ j, angles m u (halfTurn hm j) = angles m u j := by
  have hp : Function.Periodic (angle m u) (2 * m) := by
    intro j
    rw [show j + 2 * m = (j + m) + m by omega, angle_periodic hm u hu, angle_periodic hm u hu]
  intro j
  change angle m u ((j.val + m) % (2 * m)) = _
  rw [← CyclicAngles.periodic_mod _ hp, angle_periodic hm u hu]
  rfl

theorem physicalCenter_size {m : ℕ} (hm : 0 < m) {β : ℂ} (hβ : ‖β‖ ≤ 1)
    (u : ℕ → ℂ) {η : ℝ} (h : PolarBounds m u η) :
    ‖physicalCenter m β u‖ ^ 2 ≤ sizeBudget (2 * m) := by
  apply sup_sq_of_pointwise _ (sizeBudget_nonneg (by omega))
  intro j
  have hn : ‖physicalCenter m β u j‖ ≤ ‖evenSequence m u j‖ := by
    simp only [physicalCenter, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    nlinarith [norm_nonneg (evenSequence m u j)]
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (h.even_size j)

theorem angles_size {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) {η : ℝ} (h : PolarBounds m u η) :
    ‖angles m u‖ ^ 2 ≤ 4 * sizeBudget (2 * m) := by
  have hs := sup_sq_of_pointwise (fun j : Fin (2 * m) => (angles m u j : ℂ))
    (show 0 ≤ 4 * sizeBudget (2 * m) from
      mul_nonneg (by norm_num) (sizeBudget_nonneg (show 1 ≤ 2 * m by omega)))
    (fun j => by simpa only [angles, Complex.norm_real, Real.norm_eq_abs] using h.angle_size j)
  rwa [PolarCenterEnergy.realColumn_norm] at hs

theorem pairEnergy_real_scale {n : ℕ} (hn : 0 < n) (r : ℝ) (e : Fin n → ℂ) :
    pairEnergy hn (fun j => (r : ℂ) * e j) = r ^ 2 * pairEnergy hn e := by
  have he (j h : ℕ) : LocalDFT.pairRatio n (periodize hn (fun j => (r : ℂ) * e j)) j h =
      (r : ℂ) * LocalDFT.pairRatio n (periodize hn e) j h := by
    unfold LocalDFT.pairRatio periodize
    ring
  simp only [pairEnergy, LocalDFT.energyA, he, normSq_mul, normSq_ofReal, ← Finset.mul_sum]
  ring

theorem constraint_real_scale {n : ℕ} (hn : 0 < n) (r : ℝ) (e : Fin n → ℂ) :
    constraint hn (fun j => (r : ℂ) * e j) = fun j => r * constraint hn e j := by
  funext j
  have hd : difference hn (fun j => (r : ℂ) * e j) j = (r : ℂ) * difference hn e j := by
    unfold difference
    ring
  simp only [constraint, hd]
  rw [show (starRingEnd ℂ) (frame n j) * ((r : ℂ) * difference hn e j) =
    (r : ℂ) * ((starRingEnd ℂ) (frame n j) * difference hn e j) by ring]
  simp
  ring

theorem physicalCenter_energy_le {m : ℕ} (hm : 0 < m) {β : ℂ} (hβ : ‖β‖ ≤ 1)
    (u : ℕ → ℂ) (hu : Function.Periodic u (2 * m))
    (hE : totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2) :
    pairEnergy (by omega) (physicalCenter m β u) ≤ 32 * Real.pi ^ 2 := by
  unfold physicalCenter
  rw [pairEnergy_real_scale, pairEnergy_restrict (by omega) _ (even_full_period u hu)]
  have he := (even_energyA_le hm u hu).trans (model_pair_energy_le u hE)
  have hp : ‖β‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg β]
  have hA : 0 ≤ LocalDFT.energyA (2 * m) (evenSequence m u) := LocalMaximum.energyA_nonneg _ _
  nlinarith

theorem angles_energy_le {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) {η : ℝ} (h : PolarBounds m u η) :
    DiscreteEnergy.realEnergy (by omega) (angles m u) ≤ 512 * Real.pi ^ 2 := by
  have hp : Function.Periodic (fun j => (angle m u j : ℂ)) (2 * m) := by
    intro j
    dsimp
    rw [show j + 2 * m = (j + m) + m by omega, h.angle_period, h.angle_period]
  unfold DiscreteEnergy.realEnergy angles
  rw [pairEnergy_restrict (by omega) _ hp]
  exact h.angle_energy

theorem even_constraint_eq {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) :
    constraint (by omega) (fun j : Fin (2 * m) => evenSequence m u j) = ExtremalSchurGap.evenConstraint m u := by
  funext j
  rw [constraint_eq_edgeImaginary (by omega), edgeRatio,
    periodize_restrict (by omega) _ (even_full_period u hu)]
  simp only [ExtremalSchurGap.evenConstraint, Nat.cast_mul, Nat.cast_ofNat]

theorem physical_constraint_eq {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) :
    constraint (by omega) (physicalCenter m β u) =
      fun j => ‖β‖ * ExtremalSchurGap.evenConstraint m u j := by
  unfold physicalCenter
  rw [constraint_real_scale, even_constraint_eq hm u hu]

theorem meanSquare_triangle {n : ℕ} (f g h : Fin n → ℝ) :
    meanSquare (f - h) ≤ 2 * meanSquare (f - g) + 2 * meanSquare (g - h) := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    show (f j - h j) ^ 2 ≤ 2 * (f j - g j) ^ 2 + 2 * (g j - h j) ^ 2 by
      nlinarith [sq_nonneg (f j - 2 * g j + h j)])
  have hh := div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  simpa only [meanSquare, Pi.sub_apply, add_div, mul_div_assoc] using hh

theorem meanSquare_scale_difference {n : ℕ} (r : ℝ) (q : Fin n → ℝ) :
    meanSquare ((fun j => r * q j) - q) = (r - 1) ^ 2 * meanSquare q := by
  have he (j : Fin n) : (r * q j - q j) ^ 2 = (r - 1) ^ 2 * q j ^ 2 := by ring
  simp only [meanSquare, Pi.sub_apply, he, ← Finset.mul_sum]
  ring

theorem scale_distance_le {n : ℕ} (hn : 0 < n) {β : ℂ} (hβ : ‖β‖ ≤ 1)
    (hscale : (n : ℝ) ^ 2 * (1 - ‖β‖ ^ 2) ≤ 256 * Real.pi ^ 2) :
    |‖β‖ - 1| ≤ 256 * Real.pi ^ 2 / (n : ℝ) ^ 2 := by
  rw [abs_of_nonpos (sub_nonpos.mpr hβ)]
  apply (le_div_iff₀ (by positivity : 0 < (n : ℝ) ^ 2)).mpr
  have hb : 1 - ‖β‖ ≤ 1 - ‖β‖ ^ 2 := by nlinarith [norm_nonneg β]
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (n : ℝ))
  nlinarith

theorem evenConstraint_le_total {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (hE : totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2) :
    meanSquare (ExtremalSchurGap.evenConstraint m u) ≤ 32 * Real.pi ^ 2 := by
  have h := ExtremalSchurGap.evenConstraint_budget hm u hu
  have hA := LocalMaximum.energyA_nonneg (2 * m) u
  unfold totalEnergy at hE
  push_cast at hE
  linarith

theorem model_constraint_error {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ) {η : ℝ}
    (hu : Function.Periodic u (2 * m)) (hmean : (∑ j ∈ Finset.range (2 * m), u j) = 0)
    (hE : totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2) (hp : PolarBounds m u η)
    (hβ : ‖β‖ ≤ 1) (hscale : ((2 * m : ℕ) : ℝ) ^ 2 * (1 - ‖β‖ ^ 2) ≤ 256 * Real.pi ^ 2)
    (hS : sizeBudget (2 * m) ≤ 1 / 16) :
    meanSquare (polarConstraint hm β u - ExtremalSchurGap.evenConstraint m u) ≤
      constraintErrorBudget (2 * m) := by
  have hS0 := sizeBudget_nonneg (show 1 ≤ 2 * m by omega)
  have hT := angles_size hm u hp
  have hC := physicalCenter_size hm hβ u hp
  have hTsmall : ‖angles m u‖ ≤ 1 / 2 := by nlinarith [norm_nonneg (angles m u)]
  have hCm := physicalCenter_mean_zero hm β u hu hmean
  have hCA := physicalCenter_energy_le hm hβ u hu hE
  have hTA := angles_energy_le hm u hp
  have hcorr := correctedCenter_constraint_difference_le (by omega : 2 ≤ 2 * m)
    (angles m u) (physicalCenter m β u) hTsmall hCm
  have htprod := mul_le_mul hT hCA (pairEnergy_nonneg (by omega) (physicalCenter m β u))
    (mul_nonneg (by norm_num) hS0)
  have hcprod := mul_le_mul hC hTA
    (pairEnergy_nonneg (by omega) (fun j => (angles m u j : ℂ))) hS0
  have hbracket : ‖angles m u‖ ^ 2 * pairEnergy (by omega) (physicalCenter m β u) +
      4 * ‖physicalCenter m β u‖ ^ 2 * DiscreteEnergy.realEnergy (by omega) (angles m u) ≤
        2176 * Real.pi ^ 2 * sizeBudget (2 * m) := by
    nlinarith
  have hcorr' : meanSquare (polarConstraint hm β u - constraint (by omega) (physicalCenter m β u)) ≤
      2176 * Real.pi ^ 4 * ((2 * m : ℕ) : ℝ) * sizeBudget (2 * m) := by
    calc
      _ ≤ _ := hcorr.trans (mul_le_mul_of_nonneg_left hbracket (by positivity))
      _ = _ := by ring
  have hscaleq : meanSquare (constraint (by omega) (physicalCenter m β u) - ExtremalSchurGap.evenConstraint m u) ≤
      (256 * Real.pi ^ 2 / ((2 * m : ℕ) : ℝ) ^ 2) ^ 2 * (32 * Real.pi ^ 2) := by
    rw [physical_constraint_eq hm β u hu, meanSquare_scale_difference]
    have hs := pow_le_pow_left₀ (abs_nonneg _) (scale_distance_le (by omega) hβ hscale) 2
    rw [sq_abs] at hs
    exact mul_le_mul hs (evenConstraint_le_total hm u hu hE)
      (meanSquare_nonneg _) (sq_nonneg _)
  have htri := meanSquare_triangle (polarConstraint hm β u)
    (constraint (by omega) (physicalCenter m β u)) (ExtremalSchurGap.evenConstraint m u)
  unfold constraintErrorBudget
  linarith

structure CenterBounds {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ) : Prop where
  half_periodic : HalfPeriodic hm (polarCenter m β u)
  mean_zero : ∑ j, polarCenter m β u j = 0
  energy : pairEnergy (by omega) (polarCenter m β u) ≤ 320 * Real.pi ^ 2
  size : ‖polarCenter m β u‖ ^ 2 ≤ 4 * sizeBudget (2 * m)
  constraint_error : meanSquare (polarConstraint hm β u - ExtremalSchurGap.evenConstraint m u) ≤
    constraintErrorBudget (2 * m)

theorem model_center_bounds {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ) {η : ℝ}
    (hu : Function.Periodic u (2 * m)) (hmean : (∑ j ∈ Finset.range (2 * m), u j) = 0)
    (hE : totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2) (hp : PolarBounds m u η)
    (hβ : ‖β‖ ≤ 1) (hscale : ((2 * m : ℕ) : ℝ) ^ 2 * (1 - ‖β‖ ^ 2) ≤ 256 * Real.pi ^ 2)
    (hS : sizeBudget (2 * m) ≤ 1 / 16) : CenterBounds hm β u := by
  have hS0 := sizeBudget_nonneg (show 1 ≤ 2 * m by omega)
  have hT := angles_size hm u hp
  have hC := physicalCenter_size hm hβ u hp
  have hTsmall : ‖angles m u‖ ≤ 1 / 2 := by nlinarith [norm_nonneg (angles m u)]
  have hCm := physicalCenter_mean_zero hm β u hu hmean
  refine ⟨correctedCenter_halfPeriodic hm _ _ (angles_halfPeriodic hm u hu)
    (physicalCenter_halfPeriodic hm β u hu), correctedCenter_mean_zero (by omega) _ _ hTsmall, ?_, ?_,
    model_constraint_error hm β u hu hmean hE hp hβ hscale hS⟩
  · have h := correctedCenter_energy_le (by omega) (angles m u) (physicalCenter m β u) hTsmall hCm
    have hCA := physicalCenter_energy_le hm hβ u hu hE
    have hTA := angles_energy_le hm u hp
    have hprod := mul_le_mul hC hTA (pairEnergy_nonneg (by omega) (fun j => (angles m u j : ℂ))) hS0
    have hS' := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ 4096 * Real.pi ^ 2)
    change pairEnergy (by omega) (correctedCenter (angles m u) (physicalCenter m β u)) ≤ _
    nlinarith
  · have h := pow_le_pow_left₀ (norm_nonneg _)
      (correctedCenter_norm_le (by omega) (angles m u) (physicalCenter m β u) hTsmall hCm) 2
    change ‖correctedCenter (angles m u) (physicalCenter m β u)‖ ^ 2 ≤ _
    nlinarith

theorem order_mul_sizeBudget (n : ℕ) : (n : ℝ) * sizeBudget n =
    384 * Real.pi ^ 2 * Real.log n / n := by
  by_cases hn : n = 0
  · simp [hn, sizeBudget]
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    unfold sizeBudget
    field_simp

theorem constraintErrorBudget_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto (fun k => constraintErrorBudget (N k)) atTop (𝓝 0) := by
  have hNr : Tendsto (fun k => (N k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp hNr
  have hlog' : Tendsto (fun k => Real.log (N k) / N k) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using hlog
  have hsize : Tendsto (fun k => (N k : ℝ) * sizeBudget (N k)) atTop (𝓝 0) := by
    simpa only [order_mul_sizeBudget, mul_zero, mul_div_assoc] using hlog'.const_mul (384 * Real.pi ^ 2)
  have hinv : Tendsto (fun k => (N k : ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hNr
  have hsmall : Tendsto (fun k => 256 * Real.pi ^ 2 / (N k : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using
      (hinv.pow 2).const_mul (256 * Real.pi ^ 2)
  have he := (hsize.const_mul (4352 * Real.pi ^ 4)).add ((hsmall.pow 2).const_mul (64 * Real.pi ^ 2))
  simpa only [constraintErrorBudget, mul_assoc, mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add] using he

theorem operator_gap_of_difference {m : ℕ} (hm : 2048 ≤ 2 * m) (q qe : Fin (2 * m) → ℝ)
    (hqe : ‖operator (2 * m) qe‖ ≤ 7 * Real.pi / 8)
    (hdiff : meanSquare (q - qe) ≤ Real.pi ^ 2 / 256) :
    ‖operator (2 * m) q‖ ≤ 15 * Real.pi / 16 := by
  have h := SchurOperatorBounds.operator_sup_sq_le_fifteen_thirtytwo hm (q - qe)
  have hnorm : ‖operator (2 * m) (q - qe)‖ ≤ Real.pi / 16 := by
    nlinarith [norm_nonneg (operator (2 * m) (q - qe)), Real.pi_pos]
  have he : operator (2 * m) q = operator (2 * m) (q - qe) + operator (2 * m) qe := by
    rw [map_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

theorem constraint_size_of_difference {n : ℕ} (q qe : Fin n → ℝ)
    (hqe : meanSquare qe ≤ 32 * Real.pi ^ 2)
    (hdiff : meanSquare (q - qe) ≤ Real.pi ^ 2 / 256) :
    meanSquare q ≤ 65 * Real.pi ^ 2 := by
  have h := meanSquare_triangle q qe 0
  simp only [sub_zero] at h
  nlinarith [sq_nonneg Real.pi]

/-- Actual corrected centers of a genuine extremizing sequence share the original
localization coordinates, satisfy all finite center bounds, and retain a strict Schur gap. -/
theorem diameter_sequence_center_bounds {M : ℕ → ℕ} (hM2 : ∀ k, 2 ≤ M k)
    (hM : Tendsto M atTop atTop) (z : ∀ k, Points (2 * M k))
    (hz : ∀ k, ExtremalNormalization.DiameterExtremal (z k)) :
    ∃ (σ : ∀ k, Equiv.Perm (Fin (2 * M k))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ),
      Tendsto η atTop (𝓝 0) ∧
      Tendsto (fun k => sizeBudget (2 * M k)) atTop (𝓝 0) ∧
      Tendsto (fun k => angleStepBudget (2 * M k) (η k)) atTop (𝓝 0) ∧
      Tendsto (fun k => meanSquare (polarConstraint (by have := hM2 k; omega) (β k) (u k) -
        ExtremalSchurGap.evenConstraint (M k) (u k))) atTop (𝓝 0) ∧
      ∀ᶠ k in atTop,
        NormalizedRelativeEdgeModel (z k) (σ k) (α k) (β k) (u k) (η k) ∧
        totalEnergy (2 * M k) (u k) ≤ 32 * Real.pi ^ 2 ∧
        PolarBounds (M k) (u k) (η k) ∧
        ‖β k‖ ≤ 1 ∧ (2 * M k : ℝ) ^ 2 * (1 - ‖β k‖ ^ 2) ≤ 256 * Real.pi ^ 2 ∧
        (2 * M k : ℝ) * (∑ j, (1 - ‖oddPart (halfTurn (by have := hM2 k; omega))
          (z k ∘ σ k) j‖)) ≤ 256 * Real.pi ^ 2 ∧
        CenterBounds (m := M k) (by have := hM2 k; omega) (β k) (u k) ∧
        meanSquare (polarConstraint (m := M k) (by have := hM2 k; omega) (β k) (u k)) ≤ 65 * Real.pi ^ 2 ∧
        ‖operator (2 * M k) (polarConstraint (by have := hM2 k; omega) (β k) (u k))‖ ≤
          15 * Real.pi / 16 := by
  obtain ⟨σ, α, β, u, η, hη, hsize, hstep, hmodel⟩ := diameter_sequence_polar_bounds hM2 hM z hz
  have hN : Tendsto (fun k => 2 * M k) atTop atTop := tendsto_atTop_mono (fun _ => by omega) hM
  have hsmall := hsize.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 16)
  have hcenter : ∀ᶠ k in atTop, CenterBounds (m := M k) (by have := hM2 k; omega) (β k) (u k) := by
    filter_upwards [hmodel, hsmall] with k hk hs
    apply model_center_bounds (by have := hM2 k; omega) (β k) (u k)
      hk.1.periodic hk.1.mean_zero hk.2.1 hk.2.2.1 hk.2.2.2.1
    · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hk.2.2.2.2.1
    · exact hs
  have hlim : Tendsto (fun k => meanSquare (polarConstraint (by have := hM2 k; omega) (β k) (u k) -
      ExtremalSchurGap.evenConstraint (M k) (u k))) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun k => meanSquare_nonneg _)) _ (constraintErrorBudget_tendsto hN)
    filter_upwards [hcenter] with k hk
    exact hk.constraint_error
  refine ⟨σ, α, β, u, η, hη, hsize, hstep, hlim, ?_⟩
  filter_upwards [hmodel, hcenter,
    hlim.eventually_le_const (by positivity : (0 : ℝ) < Real.pi ^ 2 / 256),
    hN.eventually (eventually_ge_atTop 2048)] with k hk hc he hn
  refine ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2.1, hc, ?_, ?_⟩
  · exact constraint_size_of_difference _ _
      (evenConstraint_le_total (by have := hM2 k; omega) _ hk.1.periodic hk.2.1) he
  · exact operator_gap_of_difference hn _ _ hk.2.2.2.2.2.2 he

end
end Erdos1045.EventualExact.ExtremalPolarCenter

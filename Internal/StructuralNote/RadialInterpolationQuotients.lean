import StructuralNote.RadialInterpolationEnergy
import StructuralNote.ActualSignedAngular

/-! Small actual chord quotients along the radial interpolation, uniformly in its parameter. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.RadialInterpolationQuotients

open Erdos1045 Erdos1045.EventualExact Complex
open Configuration CommonLocalization AntipodalDecomposition
open PolarAngleControl PolarRepresentation PolarCenterEnergy RadialDeficitControl
open SchurSpectrum RadialInterpolationEnergy

theorem deficit_abs_le {m : ℕ} {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u : ℕ → ℂ) (j : ℕ) : |deficit m r u j| ≤ |1 - r| + ‖oddSequence m u j‖ := by
  have hd := abs_norm_sub_norm_le (1 + rotatedOdd m u j) (1 : ℂ)
  simp only [norm_one, add_sub_cancel_left, rotatedOdd_norm] at hd
  have he : deficit m r u j = (1 - r) + r * (1 - ‖1 + rotatedOdd m u j‖) := by
    unfold deficit radius
    ring
  rw [he]
  have hh := abs_add_le (1 - r) (r * (1 - ‖1 + rotatedOdd m u j‖))
  rw [abs_mul, abs_of_nonneg hr] at hh
  rw [abs_sub_comm 1 ‖1 + rotatedOdd m u j‖] at hh
  have hmul := mul_le_mul_of_nonneg_left hd hr
  have hdrop := mul_le_of_le_one_left (norm_nonneg (oddSequence m u j)) hr1
  linarith only [hh, hmul, hdrop]

theorem deficit_abs_le_one {m : ℕ} {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u : ℕ → ℂ) (j : ℕ) (hsmall : ‖oddSequence m u j‖ ≤ 1 / 2) : |deficit m r u j| ≤ 1 := by
  have hn := norm_add_le (1 : ℂ) (rotatedOdd m u j)
  rw [norm_one, rotatedOdd_norm] at hn
  have hu : radius m r u j ≤ 3 / 2 := by
    unfold radius
    exact (mul_le_of_le_one_left (norm_nonneg _) hr1).trans (by linarith)
  have hl := radius_nonneg m hr u j
  unfold deficit
  apply abs_le.mpr
  constructor <;> linarith only [hu, hl]

theorem radial_column_pair_le {m : ℕ} (hm : 0 < m) (b : ℕ → ℝ)
    {h : ℕ} (hh : 0 < h) (hhn : h < 2 * m) (j : ℕ) :
    ‖LocalDFT.pairRatio (2 * m) (fun k => (b k : ℂ) * reference m k) j h‖ ≤
      ‖LocalDFT.pairRatio (2 * m) (fun k => (b k : ℂ)) j h‖ + |b j| := by
  have hd := LocalDFT.vertex_difference_ne_zero (show 0 < 2 * m by omega) hh hhn j
  have he : LocalDFT.pairRatio (2 * m) (fun k => (b k : ℂ) * reference m k) j h =
      reference m (j + h) * LocalDFT.pairRatio (2 * m) (fun k => (b k : ℂ)) j h + (b j : ℂ) := by
    unfold LocalDFT.pairRatio reference
    field_simp
    ring
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [norm_mul, reference_norm, one_mul, norm_real, Real.norm_eq_abs])

theorem deficit_pair_le {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u : ℕ → ℂ) {h : ℕ} (hh : 0 < h) (hhn : h < 2 * m) (j : ℕ) :
    ‖LocalDFT.pairRatio (2 * m) (fun k => (deficit m r u k : ℂ)) j h‖ ≤
      ‖LocalDFT.pairRatio (2 * m) (oddSequence m u) j h‖ + ‖oddSequence m u j‖ := by
  have hb := radius_difference_le m hr u j (j + h)
  have hdrop := mul_le_of_le_one_left (show 0 ≤ ‖oddSequence m u (j + h) - oddSequence m u j‖ +
    ‖oddSequence m u j‖ * ‖reference m (j + h) - reference m j‖ by positivity) hr1
  have hd : 0 < ‖reference m (j + h) - reference m j‖ :=
    norm_pos_iff.mpr (LocalDFT.vertex_difference_ne_zero (by omega) hh hhn j)
  have he : |deficit m r u (j + h) - deficit m r u j| =
      |radius m r u (j + h) - radius m r u j| := by
    unfold deficit
    rw [sub_sub_sub_cancel_left, abs_sub_comm]
  simp only [LocalDFT.pairRatio, ← ofReal_sub, norm_div, norm_real, Real.norm_eq_abs, he]
  apply (div_le_iff₀ hd).2
  have hc : ‖oddSequence m u (j + h) - oddSequence m u j‖ /
      ‖reference m (j + h) - reference m j‖ * ‖reference m (j + h) - reference m j‖ =
        ‖oddSequence m u (j + h) - oddSequence m u j‖ := div_mul_cancel₀ _ hd.ne'
  change _ = _ at hc
  change _ ≤ (_ / ‖reference m (j + h) - reference m j‖ + _) * ‖reference m (j + h) - reference m j‖
  nlinarith only [hb, hdrop, hc]

def correctionSequence (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (j : ℕ) : ℂ :=
  phase (-angle m u j) * ((deficit m r u j : ℂ) * reference m j)

def pathSequence (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (t : ℝ) (j : ℕ) : ℂ :=
  ((r - 1 : ℝ) : ℂ) * reference m j + (r : ℂ) * u j +
    ((1 - t : ℝ) : ℂ) * correctionSequence m r u j

theorem correction_pair_le {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u : ℕ → ℂ) (hsmall : ∀ j, ‖oddSequence m u j‖ ≤ 1 / 2)
    {h : ℕ} (hh : 0 < h) (hhn : h < 2 * m) (j : ℕ) :
    ‖LocalDFT.pairRatio (2 * m) (correctionSequence m r u) j h‖ ≤
      3 * ‖LocalDFT.pairRatio (2 * m) (oddSequence m u) j h‖ +
        4 * ‖oddSequence m u j‖ + |1 - r| := by
  have hcol := radial_column_pair_le hm (deficit m r u) hh hhn j
  have hdef := deficit_pair_le hm hr hr1 u hh hhn j
  have hang := angle_pairRatio_bound hm u hsmall hh hhn j
  have hcenter := center_pairRatio_bound (1 : ℂ) (fun k => -angle m u k)
    (fun k => (deficit m r u k : ℂ) * reference m k) (by norm_num : (0 : ℝ) ≤ 1)
    (fun k => by
      simpa only [norm_mul, norm_real, Real.norm_eq_abs, reference_norm, mul_one] using
        deficit_abs_le_one hr hr1 u k (hsmall k)) (2 * m) j h
  have he : center 1 (fun k => -angle m u k)
      (fun k => (deficit m r u k : ℂ) * reference m k) = correctionSequence m r u := by
    funext k
    simp only [center, one_mul, correctionSequence]
  have hneg : LocalDFT.pairRatio (2 * m) (fun k => (-angle m u k : ℂ)) j h =
      -LocalDFT.pairRatio (2 * m) (fun k => (angle m u k : ℂ)) j h := by
    unfold LocalDFT.pairRatio
    push_cast
    ring
  rw [he, norm_one, one_mul, one_mul] at hcenter
  simp only [ofReal_neg, hneg, norm_neg] at hcenter
  nlinarith only [hcenter, hcol, hdef, hang, deficit_abs_le (m := m) hr hr1 u j]

theorem path_pair_identity {m : ℕ} (hm : 0 < m) (r : ℝ) (u : ℕ → ℂ) (t : ℝ)
    {h : ℕ} (hh : 0 < h) (hhn : h < 2 * m) (j : ℕ) :
    LocalDFT.pairRatio (2 * m) (pathSequence m r u t) j h =
      ((r - 1 : ℝ) : ℂ) + (r : ℂ) * LocalDFT.pairRatio (2 * m) u j h +
        ((1 - t : ℝ) : ℂ) * LocalDFT.pairRatio (2 * m) (correctionSequence m r u) j h := by
  have hd := LocalDFT.vertex_difference_ne_zero (show 0 < 2 * m by omega) hh hhn j
  unfold LocalDFT.pairRatio pathSequence reference
  field_simp
  ring

theorem path_pair_le {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (u : ℕ → ℂ) (hsmall : ∀ j, ‖oddSequence m u j‖ ≤ 1 / 2)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) {h : ℕ} (hh : 0 < h) (hhn : h < 2 * m)
    {η : ℝ} (hpair : ∀ j, ‖LocalDFT.pairRatio (2 * m) u j h‖ ≤ η) (j : ℕ) :
    ‖LocalDFT.pairRatio (2 * m) (pathSequence m r u t) j h‖ ≤
      4 * η + 4 * ‖oddSequence m u j‖ + 2 * |1 - r| := by
  have ho : ‖LocalDFT.pairRatio (2 * m) (oddSequence m u) j h‖ ≤ η := by
    rw [pairRatio_oddSequence hm, norm_div]
    norm_num only [norm_ofNat]
    have ha := norm_add_le (LocalDFT.pairRatio (2 * m) u j h)
      (LocalDFT.pairRatio (2 * m) u (j + m) h)
    linarith [hpair j, hpair (j + m)]
  have hc := correction_pair_le hm hr hr1 u hsmall hh hhn j
  have hnorm := norm_add_le
    (((r - 1 : ℝ) : ℂ) + (r : ℂ) * LocalDFT.pairRatio (2 * m) u j h)
    (((1 - t : ℝ) : ℂ) * LocalDFT.pairRatio (2 * m) (correctionSequence m r u) j h)
  have hnorm' := norm_add_le ((r - 1 : ℝ) : ℂ) ((r : ℂ) * LocalDFT.pairRatio (2 * m) u j h)
  simp only [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
    abs_of_nonneg (sub_nonneg.mpr ht.2)] at hnorm hnorm'
  have hd := mul_le_of_le_one_left (norm_nonneg (LocalDFT.pairRatio (2 * m) u j h)) hr1
  have he := mul_le_of_le_one_left
    (norm_nonneg (LocalDFT.pairRatio (2 * m) (correctionSequence m r u) j h))
    (show 1 - t ≤ 1 by linarith [ht.1])
  rw [path_pair_identity hm r u t hh hhn j]
  rw [abs_sub_comm r 1] at hnorm'
  linarith only [ho, hc, hnorm, hnorm', hd, he, hpair j]

def pairBudget (n : ℕ) (η : ℝ) : ℝ :=
  8 * η + 4 * Real.sqrt (sizeBudget n) + 512 * Real.pi ^ 2 / (n : ℝ) ^ 2

theorem model_path_pair_le {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η) (hη : η ≤ 1 / 4)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hE : ExtremalEnergyBound.totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2)
    (hp : PolarBounds m u η) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    {h : ℕ} (hh : 0 < h) (hhn : h < 2 * m) (j : ℕ) :
    ‖LocalDFT.pairRatio (2 * m) (pathSequence m ‖β‖ u t) j h‖ ≤ pairBudget (2 * m) η := by
  have hb := ExtremalScaleBound.model_matching_deficit_bound hm hmodel hη hz hE
  have hdef : ((2 * m : ℕ) : ℝ) ^ 2 * (1 - ‖β‖ ^ 2) ≤ 256 * Real.pi ^ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hb.2.1
  have hlo := ExtremalScaleBound.norm_scale_lower_of_deficit (by omega) hb.1 hdef
  have hpair (k : ℕ) : ‖LocalDFT.pairRatio (2 * m) u k h‖ ≤ 2 * η := by
    exact LocalMaximum.pair_ratio_bound ClosedFourier.geometricSine (by omega) u
      hmodel.periodic hmodel.error_nonneg hmodel.relative_edges
      (Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr hhn⟩) k
  have hp' := path_pair_le (by omega) (norm_nonneg β) hb.1 u hp.odd_small ht hh hhn hpair j
  have hs : ‖oddSequence m u j‖ ≤ Real.sqrt (sizeBudget (2 * m)) :=
    Real.le_sqrt_of_sq_le (hp.odd_size j)
  rw [abs_of_nonneg (sub_nonneg.mpr hb.1)] at hp'
  unfold pairBudget
  linear_combination hp' + 4 * hs + 2 * hlo

theorem pathSequence_periodic {m : ℕ} (hm : 0 < m) (r : ℝ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (t : ℝ) :
    Function.Periodic (pathSequence m r u t) (2 * m) := by
  intro j
  have ha := angle_periodic hm u hu
  have hr := radius_periodic hm r u hu
  have hroot : reference m (j + 2 * m) = reference m j := by
    simp only [reference, pow_add, LocalDFT.regularRoot_pow (show 0 < 2 * m by omega), mul_one]
  dsimp only [pathSequence, correctionSequence, deficit]
  rw [hu j, hroot]
  rw [show j + 2 * m = j + m + m by omega, ha (j + m), ha j, hr (j + m), hr j]

theorem model_path_sequence_energy {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η) (hη : η ≤ 1 / 4)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hE : ExtremalEnergyBound.totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2)
    (hp : PolarBounds m u η) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    LocalDFT.energyA (2 * m) (pathSequence m ‖β‖ u t) ≤
      32768 * Real.pi ^ 4 + 2688 * Real.pi ^ 2 := by
  have he := model_path_energy hm hmodel hη hz hE hp ht
  have hfun : pathDeviation m ‖β‖ u t = fun j : Fin (2 * m) => pathSequence m ‖β‖ u t j := rfl
  rw [hfun, pairEnergy_restrict (by omega) _ (pathSequence_periodic (by omega) ‖β‖ u hmodel.periodic t)] at he
  exact he

open Filter

theorem pairBudget_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {η : ℕ → ℝ}
    (hη : Tendsto η atTop (𝓝 0)) : Tendsto (fun j => pairBudget (N j) (η j)) atTop (𝓝 0) := by
  have hs := (Real.continuous_sqrt.tendsto 0).comp (sizeBudget_tendsto hN)
  have hi : Tendsto (fun j => ((N j : ℝ) ^ 2)⁻¹) atTop (𝓝 0) := by
    have hh := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN) :
      Tendsto (fun j => (N j : ℝ)⁻¹) atTop (𝓝 0)).pow 2
    simpa only [Function.comp_def, inv_pow, zero_pow (by norm_num : 2 ≠ 0)] using hh
  have h := ((hη.const_mul 8).add (hs.const_mul 4)).add (hi.const_mul (512 * Real.pi ^ 2))
  simpa only [pairBudget, Function.comp_def, Real.sqrt_zero, mul_zero, add_zero, div_eq_mul_inv] using h

end StructuralNote.RadialInterpolationQuotients

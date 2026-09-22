import EventualExact.GradientTail
import EventualExact.QuarticWindowBound
import EventualExact.FeketeStationarity
import Erdos1045.LocalConfiguration

/-! Uniform control of the actual logarithmic discriminant gradient. -/

namespace Erdos1045.EventualExact.LocalGradient

open Complex Configuration
open scoped BigOperators ComplexConjugate
noncomputable section

theorem inverse_perturbation_bound {a b : ℂ} (ha : a ≠ 0)
    (hq : ‖b / a‖ ≤ 1 / 2) :
    ‖(a + b)⁻¹ - a⁻¹‖ ≤ 2 * ‖b / a‖ / ‖a‖ := by
  have hfac : a + b = a * (1 + b / a) := by field_simp
  have hnorm : (1 : ℝ) / 2 ≤ ‖1 + b / a‖ := by
    have h := norm_sub_le (1 + b / a) (b / a)
    simp only [add_sub_cancel_right, norm_one] at h
    linarith
  have hone : 1 + b / a ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hab : a + b ≠ 0 := by rw [hfac]; exact mul_ne_zero ha hone
  have he : (a + b)⁻¹ - a⁻¹ = -(b / a) / (a * (1 + b / a)) := by
    rw [← hfac]
    field_simp
    ring
  rw [he, norm_div, norm_neg, norm_mul]
  have haN := norm_pos_iff.mpr ha
  apply (div_le_iff₀ (mul_pos haN (by linarith))).2
  have heq : (2 * ‖b / a‖ / ‖a‖) * (‖a‖ * ‖1 + b / a‖) =
      2 * ‖b / a‖ * ‖1 + b / a‖ := by field_simp
  rw [heq]
  nlinarith [norm_nonneg (b / a)]

theorem reciprocal_chord_bound {n h : ℕ} (hn : 0 < n)
    (hh : 0 < h) (hhn : h < n) (j : ℕ) :
    1 / ‖LocalPhase.regularRoot n ^ (j + h) - LocalPhase.regularRoot n ^ j‖ ≤
      (n : ℝ) / 4 * (1 / (h : ℝ) + 1 / ((n - h : ℕ) : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hnhR : (0 : ℝ) < (n - h : ℕ) := by exact_mod_cast (show 0 < n - h by omega)
  have hnorm := norm_pos_iff.mpr (LocalDFT.vertex_difference_ne_zero hn hh hhn j)
  by_cases hshort : 2 * h ≤ n
  · have hl := QuarticWindowBound.short_chord_lower hn hshort j
    have hb : 1 / ‖LocalPhase.regularRoot n ^ (j + h) - LocalPhase.regularRoot n ^ j‖ ≤
        (n : ℝ) / (4 * h) := by
      apply (div_le_iff₀ hnorm).2
      have hm := mul_le_mul_of_nonneg_left hl (le_of_lt (by positivity : (0 : ℝ) < n / (4 * h)))
      have he : (n : ℝ) / (4 * h) * (4 * h / n) = 1 := by field_simp
      rw [he] at hm
      exact hm
    apply hb.trans
    have : (0 : ℝ) ≤ n / 4 * (1 / ((n - h : ℕ) : ℝ)) := by positivity
    calc
      (n : ℝ) / (4 * h) = (n : ℝ) / 4 * (1 / (h : ℝ)) := by ring
      _ ≤ _ := by nlinarith
  · have hl := QuarticWindowBound.short_chord_lower hn (show 2 * (n - h) ≤ n by omega) (j + h)
    rw [show j + h + (n - h) = j + n by omega, pow_add,
      LocalDFT.regularRoot_pow hn, mul_one, norm_sub_rev] at hl
    have hb : 1 / ‖LocalPhase.regularRoot n ^ (j + h) - LocalPhase.regularRoot n ^ j‖ ≤
        (n : ℝ) / (4 * (n - h : ℕ)) := by
      apply (div_le_iff₀ hnorm).2
      have hm := mul_le_mul_of_nonneg_left hl
        (le_of_lt (by positivity : (0 : ℝ) < n / (4 * (n - h : ℕ))))
      have he : (n : ℝ) / (4 * (n - h : ℕ)) * (4 * (n - h : ℕ) / n) = 1 := by field_simp
      rw [he] at hm
      exact hm
    apply hb.trans
    have : (0 : ℝ) ≤ n / 4 * (1 / (h : ℝ)) := by positivity
    calc
      (n : ℝ) / (4 * (n - h : ℕ)) = (n : ℝ) / 4 * (1 / ((n - h : ℕ) : ℝ)) := by ring
      _ ≤ _ := by nlinarith

theorem row_energy_le {n : ℕ} (u : ℕ → ℂ) (i : Fin n) :
    (∑ h ∈ Finset.Ico 1 n, ‖LocalDFT.pairRatio n u i h‖ ^ 2) ≤
      2 * LocalDFT.energyA n u := by
  have he : Finset.Ico 1 n = (Finset.range n).erase 0 := by
    ext h
    simp only [Finset.mem_Ico, Finset.mem_erase, Finset.mem_range]
    omega
  rw [he]
  unfold LocalDFT.energyA
  rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  apply Finset.sum_le_sum
  intro h _
  rw [← Complex.normSq_eq_norm_sq]
  exact Finset.single_le_sum (f := fun j => Complex.normSq (LocalDFT.pairRatio n u j h))
    (fun j _ => Complex.normSq_nonneg _) (Finset.mem_range.mpr i.isLt)

theorem periodic_complex_sum_shift {n : ℕ} (f : ℕ → ℂ) (hf : Function.Periodic f n) (i : ℕ) :
    (∑ h ∈ Finset.range n, f (i + h)) = ∑ h ∈ Finset.range n, f h := by
  apply Complex.ext
  · simpa only [Complex.re_sum, Nat.add_comm, mul_zero, add_zero] using
      CyclicAngles.sum_shift_of_drift (n := n) (fun j => (f j).re) 0
        (fun j => by rw [hf j]; simp) i
  · simpa only [Complex.im_sum, Nat.add_comm, mul_zero, add_zero] using
      CyclicAngles.sum_shift_of_drift (n := n) (fun j => (f j).im) 0
        (fun j => by rw [hf j]; simp) i

theorem nodeGradient_eq_lags {n : ℕ} (hn : 0 < n) (z : ℕ → ℂ)
    (hz : Function.Periodic z n) (i : Fin n) :
    FeketeStationarity.nodeGradient (fun j : Fin n => z j) i =
      conj (∑ h ∈ Finset.Ico 1 n, (z i - z (i + h))⁻¹) := by
  rw [FeketeStationarity.nodeGradient_eq_univ]
  congr 1
  rw [← Finset.sum_range (fun j => (z i - z j)⁻¹),
    ← periodic_complex_sum_shift (fun j => (z i - z j)⁻¹) (fun j => by dsimp; rw [hz j]) i]
  have he : Finset.Ico 1 n = (Finset.range n).erase 0 := by
    ext h
    simp only [Finset.mem_Ico, Finset.mem_erase, Finset.mem_range]
    omega
  rw [he, Finset.sum_erase_eq_sub (Finset.mem_range.mpr hn)]
  simp

theorem nodeGradient_difference_bound {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    (u : ℕ → ℂ) (hu : Function.Periodic u n) {η : ℝ} (hη : 0 ≤ η)
    (hsmall : η ≤ 1 / 2)
    (hpair : ∀ i : Fin n, ∀ h ∈ Finset.Ico 1 n, ‖LocalDFT.pairRatio n u i h‖ ≤ η)
    (i : Fin n) :
    ‖FeketeStationarity.nodeGradient (fun j : Fin n => LocalPhase.regularRoot n ^ (j : ℕ) + u j) i -
      FeketeStationarity.nodeGradient (fun j : Fin n => LocalPhase.regularRoot n ^ (j : ℕ)) i‖ ≤
      (n : ℝ) * (η * (harmonic K : ℝ) +
        Real.sqrt (2 * LocalDFT.energyA n u) * Real.sqrt (1 / (K : ℝ))) := by
  let w (j : ℕ) := LocalPhase.regularRoot n ^ j
  let p (j : ℕ) := w j + u j
  have hw : Function.Periodic w n := by
    intro j
    dsimp [w]
    rw [pow_add, LocalDFT.regularRoot_pow hn, mul_one]
  have hp : Function.Periodic p n := by intro j; dsimp [p]; rw [hw j, hu j]
  let q (h : ℕ) := ‖LocalDFT.pairRatio n u i h‖
  let g (h : ℕ) := (p i - p (i + h))⁻¹ - (w i - w (i + h))⁻¹
  have hlocal (h : ℕ) (hh : h ∈ Finset.Ico 1 n) :
      ‖g h‖ ≤ (n : ℝ) / 2 * (q h * (1 / (h : ℝ) + 1 / ((n - h : ℕ) : ℝ))) := by
    have ht := Finset.mem_Ico.mp hh
    have ha : w i - w (i + h) ≠ 0 := by
      exact sub_ne_zero.mpr (sub_ne_zero.mp
        (LocalDFT.vertex_difference_ne_zero hn (by omega) ht.2 i)).symm
    have hqeq : (u i - u (i + h)) / (w i - w (i + h)) = LocalDFT.pairRatio n u i h := by
      dsimp [LocalDFT.pairRatio, w]
      rw [← neg_div_neg_eq]
      congr 1 <;> ring
    have hb := inverse_perturbation_bound ha (by rw [hqeq]; exact (hpair i h hh).trans hsmall)
    have hg : ‖g h‖ ≤ 2 * q h / ‖w (i + h) - w i‖ := by
      convert hb using 1
      · congr 2
        dsimp [g, p]
        congr 1
        ring
      · rw [hqeq, norm_sub_rev]
    apply hg.trans
    calc
      _ = (2 * q h) * (1 / ‖w (i + h) - w i‖) := by ring
      _ ≤ (2 * q h) * ((n : ℝ) / 4 * (1 / (h : ℝ) + 1 / ((n - h : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (reciprocal_chord_bound hn (by omega) ht.2 i)
          (mul_nonneg (by norm_num) (norm_nonneg _))
      _ = _ := by ring
  have hs := weighted_cycle_bound hK q hη (fun h hh => ⟨norm_nonneg _, hpair i h hh⟩)
    (row_energy_le u i)
  change ‖FeketeStationarity.nodeGradient (fun j : Fin n => p j) i -
    FeketeStationarity.nodeGradient (fun j : Fin n => w j) i‖ ≤ _
  rw [nodeGradient_eq_lags hn p hp, nodeGradient_eq_lags hn w hw, ← map_sub,
    Complex.norm_conj, ← Finset.sum_sub_distrib]
  calc
    ‖∑ h ∈ Finset.Ico 1 n, g h‖ ≤ ∑ h ∈ Finset.Ico 1 n, ‖g h‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Ico 1 n,
        (n : ℝ) / 2 * (q h * (1 / (h : ℝ) + 1 / ((n - h : ℕ) : ℝ))) :=
      Finset.sum_le_sum hlocal
    _ = (n : ℝ) / 2 * ∑ h ∈ Finset.Ico 1 n,
        q h * (1 / (h : ℝ) + 1 / ((n - h : ℕ) : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (n : ℝ) / 2 * (2 * (η * (harmonic K : ℝ) +
        Real.sqrt (2 * LocalDFT.energyA n u) * Real.sqrt (1 / (K : ℝ)))) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- The Euclidean gradient in one complex coordinate of `log discriminant`. -/
def realGradient {n : ℕ} (z : Points n) (i : Fin n) : ℂ :=
  2 * FeketeStationarity.nodeGradient z i

theorem realGradient_difference_bound {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    (u : ℕ → ℂ) (hu : Function.Periodic u n) {η : ℝ} (hη : 0 ≤ η)
    (hsmall : η ≤ 1 / 2)
    (hpair : ∀ i : Fin n, ∀ h ∈ Finset.Ico 1 n, ‖LocalDFT.pairRatio n u i h‖ ≤ η)
    (i : Fin n) :
    ‖realGradient (fun j : Fin n => LocalPhase.regularRoot n ^ (j : ℕ) + u j) i -
      realGradient (fun j : Fin n => LocalPhase.regularRoot n ^ (j : ℕ)) i‖ / (n : ℝ) ≤
      2 * (η * (harmonic K : ℝ) +
        Real.sqrt (2 * LocalDFT.energyA n u) * Real.sqrt (1 / (K : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [realGradient, realGradient, ← mul_sub, norm_mul]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ hnR).2
  have h := nodeGradient_difference_bound hn hK u hu hη hsmall hpair i
  nlinarith

end
end Erdos1045.EventualExact.LocalGradient

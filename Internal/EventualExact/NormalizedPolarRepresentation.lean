import EventualExact.PolarRepresentation
import EventualExact.PolarCenterNormalization

/-! Simultaneous center and angle normalization by actual rigid motions. -/

namespace Erdos1045.EventualExact.NormalizedPolarRepresentation

open Complex Configuration CommonLocalization AntipodalDecomposition
open PolarAngleControl PolarRepresentation PolarCenterEnergy PolarCenterNormalization
open SchurSpectrum FourierMultiplier
open scoped BigOperators
noncomputable section

def rawAngle (m : ℕ) (u : ℕ → ℂ) : Fin (2 * m) → ℝ := fun j => angle m u j

def rawCenter (m : ℕ) (r : ℝ) (u : ℕ → ℂ) : Fin (2 * m) → ℂ := fun j => physicalCenter m r u j

def meanAngle (m : ℕ) (u : ℕ → ℂ) : ℝ := (∑ j, rawAngle m u j) / (2 * m : ℝ)

def normalizedAngle (m : ℕ) (u : ℕ → ℂ) (j : Fin (2 * m)) : ℝ := rawAngle m u j - meanAngle m u

def normalizedCenter (m : ℕ) (r : ℝ) (u : ℕ → ℂ) : Fin (2 * m) → ℂ :=
  correctedCenter (rawAngle m u) (rawCenter m r u)

def physicalTranslation (m : ℕ) (r : ℝ) (u : ℕ → ℂ) : ℂ :=
  translation (rawAngle m u) (rawCenter m r u)

theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp only [phase, neg_add_rev, GapRigidity.circle_add]
  ring

theorem rawCenter_mean_zero {m : ℕ} (hm : 0 < m) (r : ℝ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (hmean : (∑ j ∈ Finset.range (2 * m), u j) = 0) :
    (∑ j, rawCenter m r u j) = 0 := by
  simp only [rawCenter, physicalCenter, ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (evenSequence m u), evenSequence_mean_zero hm u hu hmean, mul_zero]

theorem meanAngle_abs_le {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) :
    |meanAngle m u| ≤ ‖rawAngle m u‖ := by
  have hn : (0 : ℝ) < 2 * m := by positivity
  unfold meanAngle
  rw [abs_div, abs_of_pos hn]
  apply (div_le_iff₀ hn).2
  calc
    _ ≤ ∑ j, |rawAngle m u j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin (2 * m), ‖rawAngle m u‖ := Finset.sum_le_sum fun j _ => by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (rawAngle m u) j
    _ = _ := by simp; ring

theorem normalizedAngle_mean_zero {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) :
    (∑ j, normalizedAngle m u j) = 0 := by
  simp only [normalizedAngle, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, meanAngle]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  ring

theorem normalizedAngle_norm_le {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) :
    ‖normalizedAngle m u‖ ≤ 2 * ‖rawAngle m u‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro j
  rw [Real.norm_eq_abs]
  exact (abs_sub (rawAngle m u j) (meanAngle m u)).trans (by
    have h1 : |rawAngle m u j| ≤ ‖rawAngle m u‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (rawAngle m u) j
    linarith [meanAngle_abs_le hm u])

theorem rawAngle_halfPeriodic {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (j : Fin (2 * m)) :
    rawAngle m u (halfTurn hm j) = rawAngle m u j := by
  have hp := angle_periodic hm u hu
  have hn : Function.Periodic (angle m u) (2 * m) := by
    intro k
    rw [show k + 2 * m = k + m + m by omega, hp (k + m), hp k]
  change angle m u ((j.val + m) % (2 * m)) = angle m u j
  rw [← CyclicAngles.periodic_mod _ hn, hp j]

theorem rawCenter_halfPeriodic {m : ℕ} (hm : 0 < m) (r : ℝ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) : HalfPeriodic hm (rawCenter m r u) := by
  intro j
  have hp := center_periodic m r u hu
  have hn : Function.Periodic (physicalCenter m r u) (2 * m) := by
    intro k
    rw [show k + 2 * m = k + m + m by omega, hp (k + m), hp k]
  change physicalCenter m r u ((j.val + m) % (2 * m)) = physicalCenter m r u j
  rw [← CyclicAngles.periodic_mod _ hn, hp j]

theorem normalizedAngle_halfPeriodic {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (j : Fin (2 * m)) :
    normalizedAngle m u (halfTurn hm j) = normalizedAngle m u j := by
  simp only [normalizedAngle, rawAngle_halfPeriodic hm u hu j]

theorem normalizedCenter_halfPeriodic {m : ℕ} (hm : 0 < m) (r : ℝ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) : HalfPeriodic hm (normalizedCenter m r u) :=
  correctedCenter_halfPeriodic hm _ _ (rawAngle_halfPeriodic hm u hu) (rawCenter_halfPeriodic hm r u hu)

theorem normalizedCenter_mean_zero {m : ℕ} (hm : 0 < m) (r : ℝ) (u : ℕ → ℂ)
    (hsmall : ‖rawAngle m u‖ ≤ 1 / 2) : (∑ j, normalizedCenter m r u j) = 0 :=
  correctedCenter_mean_zero (by omega) _ _ hsmall

theorem normalizedAngle_energy {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) :
    DiscreteEnergy.realEnergy (by omega : 0 < 2 * m) (normalizedAngle m u) =
      DiscreteEnergy.realEnergy (by omega) (rawAngle m u) := by
  change pairEnergy (by omega) (fun j => ((rawAngle m u j - meanAngle m u : ℝ) : ℂ)) = _
  simp only [Complex.ofReal_sub]
  exact pairEnergy_sub_const (by omega) (fun j => (rawAngle m u j : ℂ)) (meanAngle m u)

theorem normalized_identity (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (j : Fin (2 * m)) :
    (r : ℂ) * (reference m j + u j) = physicalTranslation m r u +
      phase (-meanAngle m u) * phase (-normalizedAngle m u j) *
        ((radius m r u j : ℂ) * reference m j + normalizedCenter m r u j) := by
  have hp : phase (-meanAngle m u) * phase (-normalizedAngle m u j) = phase (-angle m u j) := by
    rw [← phase_add]
    congr 1
    unfold normalizedAngle rawAngle
    ring
  rw [hp, polar_identity, mul_add, mul_add]
  change phase (-angle m u j) * ((radius m r u j : ℂ) * reference m j) +
      phase (-angle m u j) * (phase (angle m u j) * physicalCenter m r u j) =
    physicalTranslation m r u + (phase (-angle m u j) * ((radius m r u j : ℂ) * reference m j) +
      phase (-angle m u j) * correctedCenter (rawAngle m u) (rawCenter m r u) j)
  have hcancel : phase (-angle m u j) * (phase (angle m u j) * physicalCenter m r u j) =
      physicalCenter m r u j := by rw [← mul_assoc, PolarRepresentation.phase_inverse, one_mul]
  rw [hcancel]
  have hcorr := physical_center_translation (rawAngle m u) (rawCenter m r u) j
  change phase (-angle m u j) * correctedCenter (rawAngle m u) (rawCenter m r u) j =
    physicalCenter m r u j - physicalTranslation m r u at hcorr
  rw [hcorr]
  ring

theorem model_normalized_coordinates {m : ℕ} {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (j : Fin (2 * m)) :
    z (σ j) = (α + (β / (‖β‖ : ℂ)) * physicalTranslation m ‖β‖ u) +
      ((β / (‖β‖ : ℂ)) * phase (-meanAngle m u)) * phase (-normalizedAngle m u j) *
        ((radius m ‖β‖ u j : ℂ) * reference m j + normalizedCenter m ‖β‖ u j) := by
  have hn : (‖β‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h.scale_ne_zero)
  calc
    _ = α + (β / (‖β‖ : ℂ)) * ((‖β‖ : ℂ) * (reference m j + u j)) := by
      rw [← mul_assoc, div_mul_cancel₀ _ hn]
      exact h.coordinates j
    _ = _ := by rw [normalized_identity]; ring

theorem normalizedRotation_norm {m : ℕ} {β : ℂ} (hβ : β ≠ 0) (u : ℕ → ℂ) :
    ‖(β / (‖β‖ : ℂ)) * phase (-meanAngle m u)‖ = 1 := by
  rw [norm_mul, unitScale_norm hβ, phase_norm, mul_one]

end
end Erdos1045.EventualExact.NormalizedPolarRepresentation

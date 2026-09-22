import EventualExact.ExtremalPolarAngles
import EventualExact.PolarCenterEnergy

/-! Exact polar coordinates for the original points, retaining the actual radial deficits. -/

namespace Erdos1045.EventualExact.PolarRepresentation

open Complex Configuration CommonLocalization AntipodalDecomposition
open PolarAngleControl PolarCenterEnergy FourierMultiplier
open scoped BigOperators
noncomputable section

def reference (m j : ℕ) : ℂ := LocalPhase.regularRoot (2 * m) ^ j

def physicalCenter (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (j : ℕ) : ℂ := (r : ℂ) * evenSequence m u j

def radius (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (j : ℕ) : ℝ := r * ‖1 + rotatedOdd m u j‖

def deangledCenter (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (j : ℕ) : ℂ :=
  phase (angle m u j) * physicalCenter m r u j

theorem reference_norm (m j : ℕ) : ‖reference m j‖ = 1 := by
  simp only [reference, norm_pow, LocalChord.root_norm, one_pow]

theorem reference_ne_zero (m j : ℕ) : reference m j ≠ 0 := by
  intro h
  have := reference_norm m j
  simp [h] at this

theorem rotated_odd_identity (m : ℕ) (u : ℕ → ℂ) (j : ℕ) :
    reference m j * (1 + rotatedOdd m u j) = reference m j + oddSequence m u j := by
  unfold rotatedOdd
  change reference m j * (1 + oddSequence m u j / reference m j) = _
  field_simp [reference_ne_zero m j]

theorem odd_polar_identity (m : ℕ) (u : ℕ → ℂ) (j : ℕ) :
    reference m j + oddSequence m u j =
      phase (-angle m u j) * (‖1 + rotatedOdd m u j‖ : ℂ) * reference m j := by
  have hp := Complex.norm_mul_exp_arg_mul_I (1 + rotatedOdd m u j)
  rw [← rotated_odd_identity m u j]
  calc
    _ = reference m j * ((‖1 + rotatedOdd m u j‖ : ℂ) *
        Complex.exp (((1 + rotatedOdd m u j).arg : ℂ) * Complex.I)) := congrArg (reference m j * ·) hp.symm
    _ = _ := by simp only [phase, GapRigidity.circle, neg_neg, angle]; ring

theorem odd_polar_norm (m : ℕ) (u : ℕ → ℂ) (j : ℕ) :
    ‖reference m j + oddSequence m u j‖ = ‖1 + rotatedOdd m u j‖ := by
  rw [← rotated_odd_identity, norm_mul, reference_norm, one_mul]

theorem phase_inverse (t : ℝ) : phase (-t) * phase t = 1 := by
  simp only [phase, neg_neg, ← GapRigidity.circle_add, add_neg_cancel]
  simp [GapRigidity.circle]

theorem polar_identity (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (j : ℕ) :
    (r : ℂ) * (reference m j + u j) =
      phase (-angle m u j) * ((radius m r u j : ℂ) * reference m j + deangledCenter m r u j) := by
  have hu : u j = oddSequence m u j + evenSequence m u j := by
    unfold oddSequence evenSequence
    ring
  rw [hu, ← add_assoc, odd_polar_identity]
  simp only [radius, Complex.ofReal_mul, deangledCenter, physicalCenter, mul_add]
  have hp := phase_inverse (angle m u j)
  linear_combination -(r : ℂ) * evenSequence m u j * hp

theorem radius_nonneg (m : ℕ) {r : ℝ} (hr : 0 ≤ r) (u : ℕ → ℂ) (j : ℕ) :
    0 ≤ radius m r u j := mul_nonneg hr (norm_nonneg _)

theorem radius_periodic {m : ℕ} (hm : 0 < m) (r : ℝ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) : Function.Periodic (radius m r u) m := by
  intro j
  simp only [radius, rotatedOdd_periodic hm u hu j]

theorem center_periodic (m : ℕ) (r : ℝ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) : Function.Periodic (physicalCenter m r u) m := by
  intro j
  simp only [physicalCenter, evenSequence_periodic m u hu j]

theorem deangledCenter_periodic {m : ℕ} (hm : 0 < m) (r : ℝ) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) : Function.Periodic (deangledCenter m r u) m := by
  intro j
  simp only [deangledCenter, angle_periodic hm u hu j, center_periodic m r u hu j]

theorem oddPart_restrict {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (j : Fin (2 * m)) :
    oddPart (halfTurn hm) (fun k : Fin (2 * m) => u k) j = oddSequence m u j := by
  unfold oddPart oddSequence
  change (u j - u ((j.val + m) % (2 * m))) / 2 = _
  rw [← CyclicAngles.periodic_mod u hu (j.val + m)]

theorem model_matching_norm {m : ℕ} (hm : 0 < m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (j : Fin (2 * m)) :
    ‖oddPart (halfTurn hm) (z ∘ σ) j‖ = radius m ‖β‖ u j := by
  have hw (i : Fin (2 * m)) : reference m (halfTurn hm i) = -reference m i := by
    simpa only [character, mul_one, reference] using character_halfTurn hm (by decide : Odd 1) i
  have he : z ∘ σ = fun i : Fin (2 * m) => α + β * (reference m i + u i) := funext h.coordinates
  rw [he, oddPart_affine _ _ _ hw, oddPart_restrict hm u h.periodic,
    norm_mul, odd_polar_norm]
  rfl

theorem model_radius_le_one {m : ℕ} (hm : 0 < m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z) (j : Fin (2 * m)) :
    radius m ‖β‖ u j ≤ 1 := by
  rw [← model_matching_norm hm h j]
  exact matching_norm_le _ _ (fun i k => hz (σ i) (σ k)) j

theorem unitScale_norm {β : ℂ} (hβ : β ≠ 0) : ‖β / (‖β‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr hβ)]

theorem model_polar_coordinates {m : ℕ} {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (j : Fin (2 * m)) :
    z (σ j) = α + (β / (‖β‖ : ℂ)) *
      (phase (-angle m u j) * ((radius m ‖β‖ u j : ℂ) * reference m j + deangledCenter m ‖β‖ u j)) := by
  rw [← polar_identity]
  have hn : (‖β‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h.scale_ne_zero)
  rw [← mul_assoc, div_mul_cancel₀ _ hn]
  exact h.coordinates j

end
end Erdos1045.EventualExact.PolarRepresentation

import StructuralNote.ActualRadialPrice
import StructuralNote.AngularObjectiveLoss

/-! The actual radial comparison in the same normalized coordinates as the pressure field. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.NormalizedRadialPrice

open Erdos1045 Erdos1045.EventualExact Complex Filter Configuration CommonLocalization
open PolarAngleControl PolarRepresentation PolarCenterEnergy NormalizedPolarRepresentation
open ActualRadialGradient ActualRadialPrice RadialObjectivePrice AngularObjectiveCurvature
open GeometricRelativeRemainder SignedPressureAngular

theorem actualPath_one (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (j : Fin (2 * m)) :
    actualPath m r u 1 j = (r : ℂ) * (reference m j + u j) := by
  rw [actualPath, radial_path_identity]
  simp only [RadialInterpolationQuotients.pathSequence, sub_self, ofReal_zero, zero_mul, add_zero]
  unfold reference
  push_cast
  ring

theorem model_discriminant_one {m : ℕ} {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η) :
    discriminant (actualPath m ‖β‖ u 1) = discriminant z := by
  have hrep : z ∘ σ = fun j => α + (β / (‖β‖ : ℂ)) * actualPath m ‖β‖ u 1 j := by
    funext j
    rw [actualPath_one, ← mul_assoc, div_mul_cancel₀ _
      (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hmodel.scale_ne_zero))]
    exact hmodel.coordinates j
  rw [← HullGeometry.discriminant_perm z σ, hrep, discriminant_affine, unitScale_norm hmodel.scale_ne_zero,
    one_pow, one_mul]

theorem phase_normalized_angle (m : ℕ) (u : ℕ → ℂ) (j : Fin (2 * m)) :
    phase (-meanAngle m u) * phase (-normalizedAngle m u j) = phase (-angle m u j) := by
  rw [← phase_add]
  congr 1
  unfold normalizedAngle rawAngle
  ring

theorem actualPath_zero_normalized (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (j : Fin (2 * m)) :
    actualPath m r u 0 j = physicalTranslation m r u + phase (-meanAngle m u) *
      angularOrbit (normalizedAngle m u j)
        (configuration (root (2 * m)) (normalizedCenter m r u) j) 1 := by
  have ha : angularOrbit (normalizedAngle m u j)
      (configuration (root (2 * m)) (normalizedCenter m r u) j) 1 =
      phase (-normalizedAngle m u j) * (reference m j + normalizedCenter m r u j) := by
    simp only [angularOrbit, one_mul, phase, neg_neg, GapRigidity.circle, configuration, root, reference]
  rw [ha, ← mul_assoc, phase_normalized_angle]
  have hc := PolarCenterNormalization.physical_center_translation (rawAngle m u) (rawCenter m r u) j
  change phase (-angle m u j) * normalizedCenter m r u j =
    PolarRepresentation.physicalCenter m r u j - physicalTranslation m r u at hc
  have he : actualPath m r u 0 j = phase (-angle m u j) * reference m j +
      PolarRepresentation.physicalCenter m r u j := by
    simp only [actualPath, path, zero_mul, sub_zero, ofReal_one, one_mul,
      deangledCenter, mul_add]
    have hp : ExteriorBoundary.unit (angle m u j) = phase (-angle m u j) := by
      simp only [ExteriorBoundary.unit, phase, neg_neg, GapRigidity.circle]
    rw [hp, ← mul_assoc, PolarRepresentation.phase_inverse, one_mul]
    rfl
  rw [he, mul_add, hc]
  ring

theorem discriminant_zero_normalized (m : ℕ) (β : ℂ) (u : ℕ → ℂ) :
    Real.log (discriminant (actualPath m ‖β‖ u 0)) =
      angularLogDiscriminant (normalizedAngle m u)
        (configuration (root (2 * m)) (ExtremalPolarCenter.polarCenter m β u)) 1 := by
  have hrep : actualPath m ‖β‖ u 0 = fun j => physicalTranslation m ‖β‖ u + phase (-meanAngle m u) *
      angularOrbit (normalizedAngle m u j)
        (configuration (root (2 * m)) (normalizedCenter m ‖β‖ u) j) 1 := by
    funext j
    exact actualPath_zero_normalized m ‖β‖ u j
  rw [hrep, discriminant_affine, phase_norm, one_pow, one_mul]
  rfl

theorem eventual_model_normalized_price {M : ℕ → ℕ} (hM : Tendsto M atTop atTop)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ (z : Points (2 * M k)) (σ : Equiv.Perm (Fin (2 * M k)))
      (α β : ℂ) (u : ℕ → ℂ),
      NormalizedRelativeEdgeModel z σ α β u (η k) → ExtremalNormalization.DiameterExtremal z →
      ExtremalEnergyBound.totalEnergy (2 * M k) u ≤ 32 * Real.pi ^ 2 →
      Real.log (discriminant z) ≤ angularLogDiscriminant (normalizedAngle (M k) u)
        (configuration (root (2 * M k)) (ExtremalPolarCenter.polarCenter (M k) β u)) 1 -
          (1 - ε) * actualMass (M k) ‖β‖ u := by
  filter_upwards [eventual_model_radial_price hM hη hε] with k hk
  intro z σ α β u hmodel hz hE
  have h := hk z σ α β u hmodel hz hE
  rwa [model_discriminant_one hmodel, discriminant_zero_normalized] at h

end StructuralNote.NormalizedRadialPrice

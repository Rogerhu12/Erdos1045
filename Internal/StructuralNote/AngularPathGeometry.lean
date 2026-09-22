import StructuralNote.AngularObjectiveLoss

/-! Point and chord control for the actual angular orbit from its initial coordinates. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.AngularPathGeometry

open Erdos1045 Erdos1045.EventualExact Complex Configuration
open PolarCenterEnergy AngularObjectiveCurvature GeometricRelativeRemainder
open SignedPressureAngular AngularObjectiveLoss ActualAngularFirst SchurSpectrum DiscreteEnergy

theorem orbit_eq_phase (θ : ℝ) (Y : ℂ) (t : ℝ) :
    angularOrbit θ Y t = phase (-t * θ) * Y := by
  simp only [angularOrbit, phase, GapRigidity.circle, neg_mul, neg_neg]

theorem scaled_phase_small {t : ℝ} (ht : t ∈ Set.Icc 0 1) (θ : ℝ) :
    ‖phase (-t * θ) - 1‖ ≤ |θ| := by
  have hp := phase_sub_one (-t * θ)
  rw [abs_mul, abs_neg, abs_of_nonneg ht.1] at hp
  exact hp.trans (mul_le_of_le_one_left (abs_nonneg θ) ht.2)

theorem scaled_phase_difference {t : ℝ} (ht : t ∈ Set.Icc 0 1) (θ φ : ℝ) :
    ‖phase (-t * θ) - phase (-t * φ)‖ ≤ |θ - φ| := by
  have hp := phase_lipschitz (-t * θ) (-t * φ)
  rw [show -t * θ - -t * φ = -t * (θ - φ) by ring, abs_mul, abs_neg, abs_of_nonneg ht.1] at hp
  exact hp.trans (mul_le_of_le_one_left (abs_nonneg _) ht.2)

theorem orbit_vertex_bound {t : ℝ} (ht : t ∈ Set.Icc 0 1) (θ : ℝ) (w c : ℂ)
    (hw : ‖w‖ = 1) : ‖angularOrbit θ (w + c) t - w‖ ≤ |θ| + ‖c‖ := by
  rw [orbit_eq_phase]
  have he : phase (-t * θ) * (w + c) - w = (phase (-t * θ) - 1) * w + phase (-t * θ) * c := by ring
  rw [he]
  have hn := norm_add_le ((phase (-t * θ) - 1) * w) (phase (-t * θ) * c)
  simp only [norm_mul, hw, mul_one, phase_norm, one_mul] at hn
  linarith only [hn, scaled_phase_small ht θ]

theorem orbit_chord_bound {n : ℕ} (w c : Points n) (θ : Fin n → ℝ)
    (hw : ∀ i, ‖w i‖ = 1) {t : ℝ} (ht : t ∈ Set.Icc 0 1) (i j : Fin n)
    (hd : w i ≠ w j) :
    ‖(angularOrbit (θ i) (w i + c i) t - angularOrbit (θ j) (w j + c j) t) /
      (w i - w j) - 1‖ ≤ |θ i| + ‖quotient c w (i, j)‖ +
        (1 + ‖c j‖) * ‖quotient (fun k => (θ k : ℂ)) w (i, j)‖ := by
  let A := fun k => phase (-t * θ k)
  have he : (angularOrbit (θ i) (w i + c i) t - angularOrbit (θ j) (w j + c j) t) /
      (w i - w j) - 1 =
      (A i - 1) + A i * quotient c w (i, j) + (A i - A j) * (w j + c j) / (w i - w j) := by
    simp only [orbit_eq_phase, A, quotient]
    field_simp [sub_ne_zero.mpr hd]
    ring
  have hn := norm_add_le ((A i - 1) + A i * quotient c w (i, j))
    ((A i - A j) * (w j + c j) / (w i - w j))
  have hn' := norm_add_le (A i - 1) (A i * quotient c w (i, j))
  have hAn : ‖A i‖ = 1 := phase_norm _
  rw [norm_mul, hAn, one_mul] at hn'
  have hsum : ‖w j + c j‖ ≤ 1 + ‖c j‖ := by simpa only [hw j] using norm_add_le (w j) (c j)
  have hp := scaled_phase_difference ht (θ i) (θ j)
  have hprod := mul_le_mul hp hsum (norm_nonneg _) (abs_nonneg _)
  have hdiv := div_le_div_of_nonneg_right hprod (norm_nonneg (w i - w j))
  have hquot : ‖quotient (fun k => (θ k : ℂ)) w (i, j)‖ = |θ i - θ j| / ‖w i - w j‖ := by
    simp only [quotient, ← ofReal_sub, norm_div, norm_real, Real.norm_eq_abs]
  rw [he, hquot]
  simp only [norm_div, norm_mul] at hn
  dsimp only [A] at hn hn'
  have hsmall := scaled_phase_small ht (θ i)
  calc
    _ ≤ |θ i| + ‖quotient c w (i, j)‖ +
        |θ i - θ j| * (1 + ‖c j‖) / ‖w i - w j‖ := by linarith only [hn, hn', hdiv, hsmall]
    _ = _ := by ring

theorem angular_loss_of_coordinate_bounds {m : ℕ} (hm : 0 < m)
    (c : Points (2 * m)) (θ : Fin (2 * m) → ℝ)
    (hc : HalfPeriodic hm c) (hθ : ∀ j, θ (FourierMultiplier.halfTurn hm j) = θ j)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / 512) (hcsize : ‖c‖ ≤ δ) (hθsize : ‖θ‖ ≤ δ)
    (hcq : ∀ p, ‖quotient c (root (2 * m)) p‖ ≤ δ)
    (hθq : ∀ p, ‖quotient (fun j => (θ j : ℂ)) (root (2 * m)) p‖ ≤ δ) :
    angularLogDiscriminant θ (configuration (root (2 * m)) c) 1 ≤
      angularLogDiscriminant θ (configuration (root (2 * m)) c) 0 +
        8 * Real.sqrt (AntipodalLog.fourthEnergy (2 * m) (periodize (by omega) c) +
          ‖c‖ ^ 2 * pairEnergy (by omega) c) * Real.sqrt (realEnergy (by omega) θ) -
        realEnergy (by omega) θ / 2 := by
  have hcv (i : Fin (2 * m)) : ‖c i‖ ≤ δ := (norm_le_pi_norm c i).trans hcsize
  have hθv (i : Fin (2 * m)) : |θ i| ≤ δ := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm θ i).trans hθsize
  apply antipodal_angular_loss hm c θ hc hθ (fun p => (hcq p).trans (by linarith))
  · intro t ht i
    have hh := orbit_vertex_bound ht (θ i) (root (2 * m) i) (c i) (root_norm _ _)
    change _ ≤ _
    exact hh.trans (by linarith [hcv i, hθv i])
  · intro t ht i j hij
    have hh := orbit_chord_bound (root (2 * m)) c θ (root_norm _) ht i j ((root_injective (by omega)).ne hij)
    have hprod := mul_le_mul (show 1 + ‖c j‖ ≤ 1 + δ by linarith only [hcv j]) (hθq (i, j))
      (norm_nonneg _) (by positivity : 0 ≤ 1 + δ)
    dsimp only [configuration]
    nlinarith only [hh, hprod, hcq (i, j), hθv i, hsmall, hδ]

end StructuralNote.AngularPathGeometry

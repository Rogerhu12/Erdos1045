import StructuralNote.ActualAngularFirst

/-! Integration of the actual negative angular curvature, including the initial error. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.AngularObjectiveLoss

open Erdos1045 Erdos1045.EventualExact Complex Set
open AngularObjectiveCurvature SignedPressureAngular DiscreteEnergy
open GeometricRelativeRemainder ActualAngularFirst SchurSpectrum

theorem angular_path_injective {n : ℕ} (_hn : 0 < n) (θ : Fin n → ℝ) (Y : Fin n → ℂ)
    (t : ℝ) (hc : ∀ i j, i ≠ j →
      ‖(angularOrbit (θ i) (Y i) t - angularOrbit (θ j) (Y j) t) /
        (root n i - root n j) - 1‖ ≤ 1 / 64) :
    Function.Injective (fun i => angularOrbit (θ i) (Y i) t) := by
  intro i j he
  dsimp only at he
  by_contra hne
  have h := hc i j hne
  rw [he, sub_self, zero_div, zero_sub, norm_neg, norm_one] at h
  norm_num at h

theorem finite_angular_loss {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (Y : Fin n → ℂ)
    (hvertex : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i,
      ‖angularOrbit (θ i) (Y i) t - root n i‖ ≤ 1 / 64)
    (hchord : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j, i ≠ j →
      ‖(angularOrbit (θ i) (Y i) t - angularOrbit (θ j) (Y j) t) /
        (root n i - root n j) - 1‖ ≤ 1 / 64) :
    angularLogDiscriminant θ Y 1 ≤ angularLogDiscriminant θ Y 0 +
      angularFirst θ Y 0 - realEnergy hn θ / 2 := by
  have hi (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := angular_path_injective hn θ Y t (hchord t ht)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := angularFirst_hasDerivAt θ Y t (hi t ht)
  have hcurv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      angularCurvature θ Y t ≤ -realEnergy hn θ := by
    have h := angularCurvature_negative θ Y (root n) t (root_norm n) (root_injective hn)
      (hvertex t ht) (hchord t ht)
    change angularCurvature θ Y t ≤ -angularChordEnergy
      (fun i => LocalPhase.regularRoot n ^ (i : ℕ)) θ at h
    rwa [angularChordEnergy_eq_pairEnergy hn] at h
  have hfirst (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      angularFirst θ Y t ≤ angularFirst θ Y 0 - realEnergy hn θ * t := by
    have hc : ContinuousOn (angularFirst θ Y) (Icc (0 : ℝ) 1) :=
      fun s hs => (hd s hs).continuousAt.continuousWithinAt
    have hf : DifferentiableOn ℝ (angularFirst θ Y) (interior (Icc (0 : ℝ) 1)) :=
      fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
    have hb : ∀ s ∈ interior (Icc (0 : ℝ) 1), deriv (angularFirst θ Y) s ≤ -realEnergy hn θ := by
      intro s hs
      rw [(hd s (interior_subset hs)).deriv]
      exact hcurv s (interior_subset hs)
    have h := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hf hb
      0 ⟨le_rfl, zero_le_one⟩ t ht ht.1
    simp only [sub_zero, neg_mul] at h
    linarith only [h]
  let K (t : ℝ) := angularLogDiscriminant θ Y t - angularFirst θ Y 0 * t + realEnergy hn θ / 2 * t ^ 2
  have hK (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt K
      (angularFirst θ Y t - angularFirst θ Y 0 + realEnergy hn θ * t) t := by
    have h := ((angularLogDiscriminant_hasDerivAt θ Y t (hi t ht)).sub
      ((hasDerivAt_id t).const_mul (angularFirst θ Y 0))).add
        (((hasDerivAt_id t).pow 2).const_mul (realEnergy hn θ / 2))
    convert h using 1 <;> first | rfl | (dsimp only [id_eq]; ring)
  have hc : ContinuousOn K (Icc (0 : ℝ) 1) := fun t ht => (hK t ht).continuousAt.continuousWithinAt
  have hf : DifferentiableOn ℝ K (interior (Icc (0 : ℝ) 1)) :=
    fun t ht => (hK t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hb : ∀ t ∈ interior (Icc (0 : ℝ) 1), deriv K t ≤ 0 := by
    intro t ht
    rw [(hK t (interior_subset ht)).deriv]
    linarith only [hfirst t (interior_subset ht)]
  have h := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hc hf hb
    0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩ zero_le_one
  dsimp only [K] at h
  norm_num only [mul_zero, mul_one, zero_pow, one_pow, add_zero, sub_zero, zero_mul] at h
  linarith only [h]

/-- A genuine objective estimate using only smallness of actual points and
chords along the angular interpolation, with the antipodal error proved. -/
theorem antipodal_angular_loss {m : ℕ} (hm : 0 < m)
    (c : Fin (2 * m) → ℂ) (θ : Fin (2 * m) → ℝ)
    (hc : HalfPeriodic hm c) (hθ : ∀ j, θ (FourierMultiplier.halfTurn hm j) = θ j)
    (hsmall : ∀ p, ‖quotient c (root (2 * m)) p‖ ≤ 1 / 2)
    (hvertex : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i,
      ‖angularOrbit (θ i) (configuration (root (2 * m)) c i) t - root (2 * m) i‖ ≤ 1 / 64)
    (hchord : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j, i ≠ j →
      ‖(angularOrbit (θ i) (configuration (root (2 * m)) c i) t -
        angularOrbit (θ j) (configuration (root (2 * m)) c j) t) /
          (root (2 * m) i - root (2 * m) j) - 1‖ ≤ 1 / 64) :
    angularLogDiscriminant θ (configuration (root (2 * m)) c) 1 ≤
      angularLogDiscriminant θ (configuration (root (2 * m)) c) 0 +
        8 * Real.sqrt (AntipodalLog.fourthEnergy (2 * m) (periodize (by omega) c) +
          ‖c‖ ^ 2 * pairEnergy (by omega) c) * Real.sqrt (realEnergy (by omega) θ) -
        realEnergy (by omega) θ / 2 := by
  have hl := finite_angular_loss (show 0 < 2 * m by omega) θ
    (configuration (root (2 * m)) c) hvertex hchord
  have hfirst := (le_abs_self _).trans (angularFirst_halfPeriodic_bound hm c θ hc hθ hsmall)
  linarith only [hl, hfirst]

end StructuralNote.AngularObjectiveLoss

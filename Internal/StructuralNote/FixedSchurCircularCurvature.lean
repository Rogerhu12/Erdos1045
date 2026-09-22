import StructuralNote.FixedSchurChosenRemainderSecond
import StructuralNote.HessianAngularReference
import StructuralNote.HessianDenominator

/-! The circular contribution to the true fixed-Schur Hessian is
-2 E(eta), with a uniform O(logOrder(n)/n) relative error. -/

namespace StructuralNote.FixedSchurCircularCurvature

open Complex Filter Erdos1045 Erdos1045.EventualExact SchurSpectrum
open CommonDomainClosure CommonDomainRadius CommonFiberGeometry CommonFiberCanonicalPaths
open FixedSchurChosenPath FixedSchurConfigurationDerivatives FixedSchurChosenRemainderSecond
open GeometricRelativeRemainder SignedPressureAngular LogDiscriminantSecondDerivative
open HessianAngularReference HessianDenominator CommonFiberHessianGeometryEnergy
open FixedSchurChartQuotients AngularObjectiveCurvature
open scoped BigOperators Topology

noncomputable section

theorem ratio_norm_square_difference_bound {a b c : ℂ} {δ : ℝ}
    (ha : a ≠ 0) (hδ : δ ≤ 1 / 2) (hr : ‖b / a - 1‖ ≤ δ) :
    |‖c / b‖ ^ 2 - ‖c / a‖ ^ 2| ≤ 10 * δ * ‖c / a‖ ^ 2 := by
  have h := abs_norm_sub_norm_le ((c / b) ^ 2) ((c / a) ^ 2)
  simp only [norm_pow] at h
  exact h.trans (ratio_square_difference_bound ha hδ hr)

theorem circular_second_eq {n : ℕ} (z : Fin n → ℂ) (η : Fin n → ℝ)
    (hz : ∀ j, ‖z j‖ = 1) (hi : Function.Injective z) :
    second z (fun j => I * z j * (η j : ℂ)) (fun j => -z j * (η j : ℂ) ^ 2) =
      -(∑ i, ∑ j, ‖((η i - η j : ℝ) : ℂ) / (z i - z j)‖ ^ 2) := by
  unfold second
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j; simp
  · rw [pair_angular_second (hz i) (hz j) (hi.ne hij)]
    simp only [norm_div, div_pow, norm_real, Real.norm_eq_abs, sq_abs]
    ring

theorem circular_second_error {n : ℕ} (hn : 4 ≤ n) (z : Fin n → ℂ) (η : Fin n → ℝ)
    (hz : ∀ j, ‖z j‖ = 1) (hi : Function.Injective z) {δ : ℝ}
    (hδ : δ ≤ 1 / 2)
    (hr : ∀ i j, i ≠ j → ‖(z i - z j) / (root n i - root n j) - 1‖ ≤ δ) :
    |second z (fun j => I * z j * (η j : ℂ)) (fun j => -z j * (η j : ℂ) ^ 2) +
      2 * pairEnergy (by omega) (fun j => (η j : ℂ))| ≤
        20 * δ * pairEnergy (by omega) (fun j => (η j : ℂ)) := by
  have hw := root_injective hn
  have hp (i j : Fin n) :
      |‖((η i - η j : ℝ) : ℂ) / (z i - z j)‖ ^ 2 -
        ‖((η i - η j : ℝ) : ℂ) / (root n i - root n j)‖ ^ 2| ≤
          10 * δ * ‖((η i - η j : ℝ) : ℂ) / (root n i - root n j)‖ ^ 2 := by
    by_cases hij : i = j
    · subst j; simp
    · exact ratio_norm_square_difference_bound (sub_ne_zero.mpr (hw.ne hij)) hδ (hr i j hij)
  have hs := (Finset.abs_sum_le_sum_abs
    (fun i => ∑ j, (‖((η i - η j : ℝ) : ℂ) / (z i - z j)‖ ^ 2 -
      ‖((η i - η j : ℝ) : ℂ) / (root n i - root n j)‖ ^ 2)) Finset.univ).trans
      (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hp i j))))
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have he : (∑ i, ∑ j, ‖((η i - η j : ℝ) : ℂ) / (root n i - root n j)‖ ^ 2) =
      2 * pairEnergy (by omega) (fun j => (η j : ℂ)) := by
    rw [pairEnergy_eq_chord_sum]
    simp only [root, normSq_eq_norm_sq, norm_div, div_pow, ← ofReal_sub]
    ring
  rw [circular_second_eq z η hz hi]
  have hneg := hs
  rw [he] at hneg
  rw [show -(∑ i, ∑ j, ‖((η i - η j : ℝ) : ℂ) / (z i - z j)‖ ^ 2) +
      2 * pairEnergy (by omega) (fun j => (η j : ℂ)) =
      -((∑ i, ∑ j, ‖((η i - η j : ℝ) : ℂ) / (z i - z j)‖ ^ 2) -
        2 * pairEnergy (by omega) (fun j => (η j : ℂ))) by ring, abs_neg]
  exact hneg.trans_eq (by ring)

theorem circular_log_second {m : ℕ} (θ η : Fin (2 * m) → ℝ)
    (v h : Fin (2 * m) → ℂ) (hi : Function.Injective (diameterVector θ)) :
    HasDerivAt (deriv (fun t => FixedSchurObjective.F
      (diameterVector (chosenParameterPath θ η v h t).1)))
      (second (diameterVector θ) (fun j => I * diameterVector θ j * (η j : ℂ))
        (angularAcceleration θ η)) 0 := by
  have hfirst : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ j,
      HasDerivAt (fun r => diameterVector (chosenParameterPath θ η v h r).1 j)
        (angularVelocityPath θ η v h t j) t := by
    filter_upwards [] with t
    intro j
    have hd := (LensIncrementDerivatives.unit_path_hasDerivAt
      (parameter_angle_hasDerivAt θ η v h j t)).const_mul (FourierMultiplier.character (2 * m) 1 j)
    apply hd.congr_deriv
    unfold angularVelocityPath diameterVector
    ring
  have hi' : Function.Injective (diameterVector (chosenParameterPath θ η v h 0).1) := by
    simpa only [chosenParameterPath, affinePath, zero_smul, add_zero] using hi
  have hd := log_second_derivative hfirst (angularVelocityPath_hasDerivAt θ η v h) hi'
  have hvel : angularVelocityPath θ η v h 0 =
      fun j => I * diameterVector θ j * (η j : ℂ) := by
    funext j
    simp only [angularVelocityPath, chosenParameterPath, affinePath, zero_smul, add_zero]
  rw [hvel] at hd
  simpa only [FixedSchurObjective.F, angularVelocityPath, chosenParameterPath,
    affinePath, zero_smul, add_zero] using hd

theorem eventual_circular_curvature : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (_s : FiniteBox.SignPattern (m := m) (by omega))
      (θ η : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      |second (diameterVector θ) (fun j => I * diameterVector θ j * (η j : ℂ))
        (angularAcceleration θ η) + 2 * pairEnergy (by omega) (fun j => (η j : ℂ))| ≤
          220 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) *
            pairEnergy (by omega) (fun j => (η j : ℂ)) := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hlim := HessianErrorLimits.logOrder_div_tendsto.comp hnat
  filter_upwards [eventual_quotient_properties,
    hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 22 by norm_num))] with m hq hsmall
  intro hm s θ η v hdom
  have hδ : 11 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ≤ 1 / 2 := by
    simp only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] at hsmall
    rw [mul_div_assoc]
    linarith
  have hr (i j : Fin (2 * m)) (hij : i ≠ j) :
      ‖(diameterVector θ i - diameterVector θ j) / (root (2 * m) i - root (2 * m) j) - 1‖ ≤
        11 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
    have hroot : root (2 * m) i - root (2 * m) j ≠ 0 :=
      sub_ne_zero.mpr ((root_injective (show 4 ≤ 2 * m by omega)).ne hij)
    have he : (diameterVector θ i - diameterVector θ j) / (root (2 * m) i - root (2 * m) j) - 1 =
        quotient (diameterVector θ - root (2 * m)) (root (2 * m)) (i, j) := by
      simp only [quotient, Pi.sub_apply]
      field_simp [hroot]
      ring
    rw [he]
    exact domain_angularError_ratio (by omega) θ v hdom i j
  have hb := circular_second_error (show 4 ≤ 2 * m by omega) (diameterVector θ) η
    (diameterVector_norm θ) (hq hm s θ v hdom).1 hδ hr
  exact hb.trans_eq (by ring)

end
end StructuralNote.FixedSchurCircularCurvature

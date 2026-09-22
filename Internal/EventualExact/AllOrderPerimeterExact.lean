import EventualExact.AllOrderPerimeter
import EventualExact.NormalizedExtremalFekete

/-! The sharp homogeneous perimeter inequality, its degenerate equality case,
and the attained odd diameter-two maximum. -/

namespace Erdos1045.EventualExact.AllOrderPerimeterExact

open Configuration HullGeometry GlobalProof
noncomputable section

def sharpBound (n : ℕ) (P : ℝ) : ℝ :=
  (n : ℝ) ^ n * (P / circlePerimeter n) ^ exponent n

private theorem geometry : ClassicalHullGeometry :=
  classicalBackground_proved.toClassicalAnalysis.geometry

theorem discriminant_zero_of_perimeter_zero {n : ℕ} (hn : 2 ≤ n) {z : Points n}
    (hP : hullPerimeter z = 0) : discriminant z = 0 := by
  apply le_antisymm _ (discriminant_nonneg z)
  apply le_of_not_gt
  intro hD
  have h := ExtremalNormalization.perimeter_pos_of_discriminant_pos hn hD
  rw [hP] at h
  exact lt_irrefl _ h

theorem perimeter_zero_iff_constant {n : ℕ} (hn : 0 < n) (z : Points n) :
    hullPerimeter z = 0 ↔ ∀ i k, z i = z k := by
  constructor
  · intro hP i k
    have h := geometry.distance_le_half n z i k
    rw [hP, zero_div] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  · intro hz
    let i : Fin n := ⟨0, hn⟩
    have he : z = fun _ => z i + (0 : ℂ) * (0 : Points n) i := by
      funext k
      simpa using hz k i
    rw [he, geometry.affine]
    simp

theorem sharpBound_scale {n : ℕ} {P : ℝ} (hP : P ≠ 0) :
    (2 * Real.pi / P) ^ exponent n * sharpBound n P = perimeterMaximum n := by
  unfold sharpBound perimeterMaximum
  rw [mul_left_comm, ← mul_pow,
    show (2 * Real.pi / P) * (P / circlePerimeter n) =
      2 * Real.pi / circlePerimeter n by field_simp]
  ring

theorem normalized_perimeter {n : ℕ} (z : Points n) (hP : 0 < hullPerimeter z) :
    hullPerimeter (ExtremalNormalization.normalize z) = 2 * Real.pi := by
  have hr : 0 < 2 * Real.pi / hullPerimeter z := by positivity
  have h := geometry.affine n z 0 (((2 * Real.pi / hullPerimeter z : ℝ) : ℂ))
  simp only [zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h
  change hullPerimeter (ExtremalNormalization.normalize z) = _ at h
  rw [h]
  field_simp

theorem normalized_discriminant {n : ℕ} (z : Points n) (hP : 0 < hullPerimeter z) :
    discriminant (ExtremalNormalization.normalize z) =
      (2 * Real.pi / hullPerimeter z) ^ exponent n * discriminant z := by
  have hr : 0 < 2 * Real.pi / hullPerimeter z := by positivity
  exact ExtremalNormalization.discriminant_scale _ z |>.trans
    (by rw [abs_of_pos hr])

theorem sharp_of_regular_extremals {n : ℕ} (hn : 3 ≤ n)
    (hregular : ∀ z : Points n, PerimeterExtremal n z → Configuration.IsRegular z)
    (z : Points n) : discriminant z ≤ sharpBound n (hullPerimeter z) := by
  by_cases hP : hullPerimeter z = 0
  · rw [discriminant_zero_of_perimeter_zero (by omega) hP]
    simp [sharpBound, hP, exponent, show n - 1 ≠ 0 by omega, show n ≠ 0 by omega]
  have hPpos : 0 < hullPerimeter z := lt_of_le_of_ne (geometry.nonneg n z) (Ne.symm hP)
  have hr : 0 < 2 * Real.pi / hullPerimeter z := by positivity
  have hb := perimeter_bound_of_regular_extremals geometry hn hregular
    (ExtremalNormalization.normalize z) (normalized_perimeter z hPpos).le
  rw [normalized_discriminant z hPpos, ← sharpBound_scale hP] at hb
  exact le_of_mul_le_mul_left hb (pow_pos hr _)

theorem equality_of_regular_extremals {n : ℕ} (hn : 3 ≤ n)
    (hregular : ∀ z : Points n, PerimeterExtremal n z → Configuration.IsRegular z)
    (z : Points n) :
    discriminant z = sharpBound n (hullPerimeter z) ↔
      hullPerimeter z = 0 ∨ Configuration.IsRegular z := by
  constructor
  · intro hD
    by_cases hP : hullPerimeter z = 0
    · exact Or.inl hP
    have hPpos : 0 < hullPerimeter z := lt_of_le_of_ne (geometry.nonneg n z) (Ne.symm hP)
    have hr : 0 < 2 * Real.pi / hullPerimeter z := by positivity
    have hnormD : discriminant (ExtremalNormalization.normalize z) = perimeterMaximum n := by
      rw [normalized_discriminant z hPpos, hD, sharpBound_scale hP]
    have hreg := hregular _ (perimeterExtremal_of_attains geometry hn hregular _
      (normalized_perimeter z hPpos).le hnormD)
    right
    apply isRegular_of_affine z 0 (((2 * Real.pi / hullPerimeter z : ℝ) : ℂ))
      (Complex.ofReal_ne_zero.mpr hr.ne')
    change Configuration.IsRegular (fun i =>
      (((2 * Real.pi / hullPerimeter z : ℝ) : ℂ)) * z i) at hreg
    simpa only [zero_add] using hreg
  · rintro (hP | hreg)
    · rw [discriminant_zero_of_perimeter_zero (by omega) hP]
      simp [sharpBound, hP, exponent, show n - 1 ≠ 0 by omega, show n ≠ 0 by omega]
    · rw [regular_discriminant_from_perimeter geometry hn hreg]
      exact mul_comm _ _

theorem eventual_sharp_perimeter :
    ∃ M : ℕ, 4 ≤ M ∧ ∀ n : ℕ, M ≤ n → ∀ z : Points n,
      discriminant z ≤ (n : ℝ) ^ n *
        (hullPerimeter z / (2 * n * Real.sin (Real.pi / n))) ^ (n * (n - 1)) ∧
      (discriminant z = (n : ℝ) ^ n *
        (hullPerimeter z / (2 * n * Real.sin (Real.pi / n))) ^ (n * (n - 1)) ↔
        (∀ i k, z i = z k) ∨ Configuration.IsRegular z) := by
  obtain ⟨M, hM, hregular⟩ := AllOrderPerimeter.large_perimeter_extremizers_regular
  refine ⟨M, hM, fun n hn z => ⟨?_, ?_⟩⟩
  · exact sharp_of_regular_extremals (by omega) (hregular n hn) z
  · simpa only [sharpBound, circlePerimeter, exponent, perimeter_zero_iff_constant (by omega) z]
      using equality_of_regular_extremals (by omega) (hregular n hn) z

theorem eventual_nondegenerate_equality :
    ∃ M : ℕ, 4 ≤ M ∧ ∀ n : ℕ, M ≤ n → ∀ z : Points n, 0 < discriminant z →
      (discriminant z = sharpBound n (hullPerimeter z) ↔ Configuration.IsRegular z) := by
  obtain ⟨M, hM, hregular⟩ := AllOrderPerimeter.large_perimeter_extremizers_regular
  refine ⟨M, hM, fun n hn z hD => ?_⟩
  have hP := ExtremalNormalization.perimeter_pos_of_discriminant_pos (by omega) hD
  simpa only [ne_of_gt hP, false_or] using
    equality_of_regular_extremals (by omega) (hregular n hn) z

/-- The attained odd diameter-two maximum, now a corollary of all-order perimeter rigidity. -/
theorem eventual_odd_diameter_two_exact :
    ∃ M : ℕ, 4 ≤ M ∧ ∀ n : ℕ, M ≤ n → Odd n →
      (∀ z : Points n, DiameterAtMost 2 z →
        discriminant z ≤ (n : ℝ) ^ n / Real.cos (Real.pi / (2 * n)) ^ (n * (n - 1))) ∧
      (DiameterAtMost 2 (diameterTwoRegular n) ∧
        discriminant (diameterTwoRegular n) =
          (n : ℝ) ^ n / Real.cos (Real.pi / (2 * n)) ^ (n * (n - 1))) ∧
      (∀ z : Points n, DiameterAtMost 2 z →
        discriminant z = (n : ℝ) ^ n / Real.cos (Real.pi / (2 * n)) ^ (n * (n - 1)) →
        Configuration.IsRegular z) := by
  obtain ⟨M, hM, hregular⟩ := AllOrderPerimeter.large_perimeter_extremizers_regular
  refine ⟨M, hM, fun n hn hodd => ?_⟩
  have hn3 : 3 ≤ n := by omega
  exact ⟨fun z hz => diameter_two_bound_of_regular_extremals geometry hn3 (hregular n hn) z hz,
    ⟨diameterTwoRegular_diameter geometry hn3 hodd, diameterTwoRegular_discriminant geometry hn3⟩,
    fun z hz hD => diameter_two_equality_isRegular geometry hn3 (hregular n hn) z hz hD⟩

theorem diameter_two_equality_iff {n : ℕ} (hn : 3 ≤ n)
    (hregular : ∀ z : Points n, PerimeterExtremal n z → Configuration.IsRegular z)
    (z : Points n) (hz : DiameterAtMost 2 z) :
    discriminant z = diameterTwoMaximum n ↔
      Configuration.IsRegular z ∧ hullPerimeter z = 2 * diameterPerimeterBound n := by
  let w : Points n := fun i => (1 / 2 : ℂ) * z i
  have hw : DiameterAtMost 1 w := by
    simpa [w] using diameter_affine hz 0 (1 / 2 : ℂ)
  have hDw : discriminant w = (1 / 2 : ℝ) ^ exponent n * discriminant z := by
    simpa only [zero_add, norm_div, norm_one, Complex.norm_ofNat] using
      discriminant_affine z 0 (1 / 2 : ℂ)
  have hPw : hullPerimeter w = (1 / 2 : ℝ) * hullPerimeter z := by
    simpa only [zero_add, norm_div, norm_one, Complex.norm_ofNat] using
      geometry.affine n z 0 (1 / 2 : ℂ)
  have hD : discriminant w = diameterMaximum n ↔ discriminant z = diameterTwoMaximum n := by
    rw [hDw, ← half_scale_maximum]
    exact mul_right_inj' (pow_ne_zero _ (by norm_num : (1 / 2 : ℝ) ≠ 0))
  rw [← hD, HullGeometry.diameter_equality_iff geometry hn hregular w hw]
  constructor
  · rintro ⟨hr, hP⟩
    refine ⟨?_, ?_⟩
    · apply isRegular_of_affine z 0 (1 / 2 : ℂ) (by norm_num)
      simpa only [zero_add] using hr
    · rw [hPw] at hP
      linarith
  · rintro ⟨hr, hP⟩
    refine ⟨?_, ?_⟩
    · simpa only [zero_add] using isRegular_affine hr 0 (1 / 2 : ℂ) (by norm_num)
    · rw [hPw, hP]
      ring

theorem eventual_odd_diameter_two_equality_iff :
    ∃ M : ℕ, 4 ≤ M ∧ ∀ n : ℕ, M ≤ n → Odd n → ∀ z : Points n, DiameterAtMost 2 z →
      (discriminant z = (n : ℝ) ^ n / Real.cos (Real.pi / (2 * n)) ^ (n * (n - 1)) ↔
        Configuration.IsRegular z ∧
          hullPerimeter z = 4 * n * Real.sin (Real.pi / (2 * n))) := by
  obtain ⟨M, hM, hregular⟩ := AllOrderPerimeter.large_perimeter_extremizers_regular
  refine ⟨M, hM, fun n hn _ z hz => ?_⟩
  have h := diameter_two_equality_iff (by omega) (hregular n hn) z hz
  simpa only [diameterTwoMaximum, exponent, diameterPerimeterBound,
    show (2 : ℝ) * (2 * n * Real.sin (Real.pi / (2 * n))) =
      4 * n * Real.sin (Real.pi / (2 * n)) by ring] using h

end
end Erdos1045.EventualExact.AllOrderPerimeterExact

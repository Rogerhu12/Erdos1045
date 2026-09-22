import StructuralNote.FixedSchurRationalWindowDomain

/-! Reverse energy bounds for the literal rational coordinates. The reference
center is the selected fixed-Schur center, as in the rewritten manuscript. -/

namespace StructuralNote.FixedSchurRationalReverseEnergy

open Complex Erdos1045 Erdos1045.EventualExact LensClosure SchurSpectrum
open CommonClosureEnergy
open RationalCommonConfiguration RationalAngleBranch FixedSchurRationalWindowEnergy
open FixedSchurRationalWindowDomain AngularObjectiveCurvature
open scoped BigOperators
noncomputable section

theorem tan_difference_le {a b : ℝ}
    (ha : (1 / 2 : ℝ) ≤ Real.cos a) (hb : (1 / 2 : ℝ) ≤ Real.cos b) :
    |Real.tan a - Real.tan b| ≤ 4 * |a - b| := by
  have ha0 : 0 < Real.cos a := by linarith
  have hb0 : 0 < Real.cos b := by linarith
  have hid : Real.tan a - Real.tan b =
      Real.sin (a - b) / (Real.cos a * Real.cos b) := by
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.sin_sub]
    field_simp
  rw [hid, abs_div, abs_of_pos (mul_pos ha0 hb0)]
  apply (div_le_iff₀ (mul_pos ha0 hb0)).2
  have hprod : (1 / 4 : ℝ) ≤ Real.cos a * Real.cos b := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hprod (abs_nonneg (a - b))
  nlinarith [Real.abs_sin_le_abs (x := a - b)]

theorem cos_arctan_ge_half {x : ℝ} (hx : |x| ≤ 1) :
    (1 / 2 : ℝ) ≤ Real.cos (Real.arctan x) := by
  rw [Real.cos_arctan]
  have hs : Real.sqrt (1 + x ^ 2) ≤ 2 := by
    apply Real.sqrt_le_iff.2
    refine ⟨by norm_num, ?_⟩
    nlinarith [sq_abs x, (abs_le.mp hx).1, (abs_le.mp hx).2]
  exact (le_div_iff₀ (Real.sqrt_pos.2 (by positivity))).2 (by linarith)

theorem parameter_difference_le {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |x - y| ≤ 2 * |2 * Real.arctan x - 2 * Real.arctan y| := by
  have h := tan_difference_le (cos_arctan_ge_half hx) (cos_arctan_ge_half hy)
  rw [Real.tan_arctan, Real.tan_arctan] at h
  have he : |2 * Real.arctan x - 2 * Real.arctan y| =
      2 * |Real.arctan x - Real.arctan y| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [he]
  linarith

theorem parameter_energy_le_four {m : ℕ} (hm : 0 < m)
    (X : RationalConfiguration.Variables m → ℝ)
    (hX : ∀ j, |extendedAngleParameter hm X j| ≤ 1) :
    pairEnergy (by omega) (fun j => (extendedAngleParameter hm X j : ℂ)) ≤
      4 * pairEnergy (by omega) (fun j => (theta hm X j : ℂ)) := by
  have hp (i j : Fin (2 * m)) :
      normSq ((extendedAngleParameter hm X i : ℂ) - (extendedAngleParameter hm X j : ℂ)) ≤
        4 * normSq ((theta hm X i : ℂ) - (theta hm X j : ℂ)) := by
    have hh := parameter_difference_le (hX i) (hX j)
    have hs := pow_le_pow_left₀ (abs_nonneg _) hh 2
    have he : theta hm X i - theta hm X j =
        2 * Real.arctan (extendedAngleParameter hm X i) -
          2 * Real.arctan (extendedAngleParameter hm X j) := by
      simp only [theta, angle, extendedAngleParameter]
      ring
    simp only [← ofReal_sub, normSq_ofReal]
    rw [he]
    norm_num [mul_pow, sq_abs] at hs
    simpa only [pow_two] using hs
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      div_le_div_of_nonneg_right (hp i j)
        (normSq_nonneg (LocalPhase.regularRoot (2 * m) ^ (i : ℕ) -
          LocalPhase.regularRoot (2 * m) ^ (j : ℕ)))))
  simp only [mul_div_assoc, ← Finset.mul_sum] at hs
  rw [pairEnergy_eq_chord_sum, pairEnergy_eq_chord_sum]
  linarith only [hs]

theorem rawCenter_sub_reference {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) (X : RationalConfiguration.Variables m → ℝ)
    (j : Fin (2 * m)) :
    (rationalCenter hm (rationalSign s) X - fixedReferenceCenter hm s) j =
      unit (angleMean hm X) *
        ((normalizedCenter hm (rationalSign s) X - fixedReferenceCenter hm s) j) +
      (unit (angleMean hm X) - 1) * fixedReferenceCenter hm s j +
      centerMean hm (rationalSign s) X := by
  have hu : unit (angleMean hm X) * unit (-angleMean hm X) = 1 := by
    rw [← CommonFiberGeometry.unit_add]
    simp [unit]
  simp only [Pi.sub_apply, normalizedCenter, rationalCenter]
  linear_combination -(RationalConfiguration.centerPrefix hm (rationalSign s) X
    (j.val % m) - centerMean hm (rationalSign s) X) * hu

theorem rawCenter_reference_energy_le {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) (X : RationalConfiguration.Variables m → ℝ) :
    pairEnergy (by omega)
        (rationalCenter hm (rationalSign s) X - fixedReferenceCenter hm s) ≤
      (5 / 4 : ℝ) * pairEnergy (by omega)
        (normalizedCenter hm (rationalSign s) X - fixedReferenceCenter hm s) +
      5 * angleMean hm X ^ 2 * pairEnergy (by omega) (fixedReferenceCenter hm s) := by
  let u := unit (angleMean hm X)
  let D := normalizedCenter hm (rationalSign s) X - fixedReferenceCenter hm s
  have heq : rationalCenter hm (rationalSign s) X - fixedReferenceCenter hm s =
      fun j => u * D j + (u - 1) * fixedReferenceCenter hm s j +
        centerMean hm (rationalSign s) X := by
    funext j
    exact rawCenter_sub_reference hm s X j
  have htranslation {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (a : ℂ) :
      pairEnergy hn (fun j => c j + a) = pairEnergy hn c := by
    simp only [pairEnergy_eq_chord_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    ring
  rw [heq, htranslation]
  have hy := pairEnergy_add_le_five_four (by omega : 0 < 2 * m)
    (fun j => u * D j) (fun j => (u - 1) * fixedReferenceCenter hm s j)
  rw [RadialInterpolationEnergy.pairEnergy_scale,
    RadialInterpolationEnergy.pairEnergy_scale] at hy
  have hu : ‖u‖ = 1 := norm_unit _
  have hn : ‖u - 1‖ ≤ |angleMean hm X| := by
    simpa only [u, unit, ofReal_zero, zero_mul, exp_zero, sub_zero] using
      norm_unit_sub_le (angleMean hm X) 0
  have hsq : ‖u - 1‖ ^ 2 ≤ angleMean hm X ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [hu, one_pow, one_mul] at hy
  have href := mul_le_mul_of_nonneg_right hsq
    (pairEnergy_nonneg (by omega : 0 < 2 * m) (fixedReferenceCenter hm s))
  change _ ≤ (5 / 4 : ℝ) * pairEnergy (by omega) D + _
  linarith only [hy, href]

end
end StructuralNote.FixedSchurRationalReverseEnergy

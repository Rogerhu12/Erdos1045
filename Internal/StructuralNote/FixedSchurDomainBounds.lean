import StructuralNote.FixedSchurData
import StructuralNote.CommonFiberBounds
import StructuralNote.CommonFiberSmallCoefficients
import StructuralNote.CommonTangentialReconstruction

/-! Quantitative bounds for the actual fixed-Schur coordinates on the literal
    common energy domain. -/

namespace StructuralNote.FixedSchurDomainBounds

open scoped BigOperators

open Erdos1045 Erdos1045.EventualExact
open Complex FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open CommonClosureEnergy CommonDomainClosure CommonDomainRadius
open CommonFiberBounds CommonFiberSmallCoefficients
open CommonFiberNormalProjectionScaled CommonTangentialParameters
open EdgeCoordinates FixedSchurData

noncomputable section

theorem epsilon_le {n : ℕ} (hn : 2 ≤ n) :
    epsilon n ≤ 8 / (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : Real.sin (Real.pi / n) ≤ Real.pi / n :=
    Real.sin_le (by positivity)
  unfold epsilon
  calc
    2 * Real.sin (Real.pi / n) / n ≤ 2 * (Real.pi / n) / n := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs (by norm_num)) hnR.le
    _ = 2 * Real.pi / (n : ℝ) ^ 2 := by ring
    _ ≤ 8 / (n : ℝ) ^ 2 := by
      apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hnR)).2
      nlinarith [Real.pi_lt_four]

private theorem tangent_abs_le_scale_difference {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → ℂ) (j : Fin n) :
    |EdgeCoordinates.tangent (by omega) v j| ≤
      CommonFiberNormalProjectionScaled.scale n *
        ‖difference (by omega) v j‖ := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsin : 0 < Real.sin (Real.pi / n) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · apply (div_lt_iff₀ hnR).2
      have hnR2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [Real.pi_pos]
  have htan : |EdgeCoordinates.tangent (by omega) v j| ≤
      ‖(n : ℂ) * edgeRatio (by omega) v j‖ := by
    calc
      |EdgeCoordinates.tangent (by omega) v j| ≤
          ‖(EdgeCoordinates.tangent (by omega) v j : ℂ) -
            I * (EdgeCoordinates.normal (by omega) v j : ℂ)‖ := by
        have h := Complex.abs_re_le_norm
          ((EdgeCoordinates.tangent (by omega) v j : ℂ) -
            I * (EdgeCoordinates.normal (by omega) v j : ℂ))
        simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
          sub_zero] using h
      _ = ‖(n : ℂ) * edgeRatio (by omega) v j‖ := by
        rw [EdgeCoordinates.scaled_edgeRatio (by omega) v j]
  have href :
      ‖difference (by omega) (fun k => character n 1 k) j‖ =
        2 * Real.sin (Real.pi / n) := by
    rw [SchurLift.reference_difference (by omega) j]
    simp only [norm_mul, norm_real, Real.norm_eq_abs, Complex.norm_I,
      FixedSchurData.norm_frame]
    rw [abs_of_pos hsin]
    norm_num
  calc
    |EdgeCoordinates.tangent (by omega) v j| ≤
        ‖(n : ℂ) * edgeRatio (by omega) v j‖ := htan
    _ = (n : ℝ) * ‖edgeRatio (by omega) v j‖ := by
      simp only [norm_mul, Complex.norm_natCast]
    _ = (n : ℝ) *
        (‖difference (by omega) v j‖ /
          (2 * Real.sin (Real.pi / n))) := by
      rw [edgeRatio_eq_difference, norm_div, href]
    _ = CommonFiberNormalProjectionScaled.scale n *
        ‖difference (by omega) v j‖ := by
      unfold CommonFiberNormalProjectionScaled.scale
      field_simp

theorem domain_tangent_bound {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v) (j : Fin (2 * m)) :
    |EdgeCoordinates.tangent (by omega) v j| ≤
      (5 / 2 : ℝ) * (logOrder (2 * m) : ℝ) := by
  let n : ℕ := 2 * m
  let L : ℝ := (logOrder n : ℝ)
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have henergy : pairEnergy (by omega) v ≤ L ^ 2 / (n : ℝ) ^ 2 := by
    have h := (domain_energy_bounds hm θ v hdom).2
    simpa only [n, L, energyRadius, Nat.cast_mul, Nat.cast_ofNat] using h
  have hd := difference_of_scaled_energy (by omega) v hL henergy j
  have hs := scale_bounds hn
  have ht := tangent_abs_le_scale_difference hn v j
  have hmul :
      scale n * ‖difference (by omega) v j‖ ≤
        ((n : ℝ) ^ 2 / 4) * (10 * L / (n : ℝ) ^ 2) := by
    exact mul_le_mul hs.2 hd (norm_nonneg _) (by positivity)
  have hmain : |EdgeCoordinates.tangent (by omega) v j| ≤ (5 / 2 : ℝ) * L :=
    ht.trans (hmul.trans (by field_simp; linarith))
  simpa only [n, L, Nat.cast_mul, Nat.cast_ofNat] using hmain

theorem domain_angleAverage_bound {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain hm θ v) (j : Fin m) :
    |angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j)| ≤
      4 * (logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) /
        (2 * m : ℝ) ^ 2 := by
  have h₁ := domain_theta_bound hm θ v hdom (CommonClosureEnergy.halfIndex j)
  have h₂ := domain_theta_bound hm θ v hdom
    (successor (by omega) (CommonClosureEnergy.halfIndex j))
  dsimp [angleAverage]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := abs_add_le (θ (CommonClosureEnergy.halfIndex j))
    (θ (successor (by omega) (CommonClosureEnergy.halfIndex j)))
  linarith

private theorem domain_Y_halfIndex_bound {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain hm θ v) (j : Fin m) :
    |FixedSchurData.Y (by omega) θ (CommonClosureEnergy.halfIndex j)| ≤
      8 * (logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) /
        (2 * m : ℝ) ^ 2 := by
  have ha := domain_angleAverage_bound hm θ v hdom j
  have hc : |Real.cos (halfAngle hm θ j)| ≤ 1 := Real.abs_cos_le_one _
  have hs : |Real.sin (angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j))| ≤
      |angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j)| := Real.abs_sin_le_abs
  rw [FixedSchurData.Y_halfIndex hm θ j]
  calc
    |2 * Real.cos (halfAngle hm θ j) *
        Real.sin (angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j))| =
        2 * |Real.cos (halfAngle hm θ j)| *
          |Real.sin (angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j))| := by
      rw [abs_mul, abs_mul]
      norm_num
    _ ≤ 2 * |angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j)| := by
      calc
        2 * |Real.cos (halfAngle hm θ j)| *
            |Real.sin (angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j))| ≤
            2 * 1 * |Real.sin (angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j))| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hc (by norm_num)) (abs_nonneg _)
        _ ≤ 2 * 1 * |angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j)| :=
          mul_le_mul_of_nonneg_left hs (by norm_num)
        _ = 2 * |angleAverage (by omega) θ (halfIndex j)| := by ring
    _ ≤ 2 * (4 * (logOrder (2 * m) : ℝ) *
        Real.sqrt (Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left ha (by norm_num)
    _ = 8 * (logOrder (2 * m) : ℝ) *
        Real.sqrt (Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 := by ring

theorem domain_Y_bound {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain hm θ v) (j : Fin (2 * m)) :
    |FixedSchurData.Y (by omega) θ j| ≤
      8 * (logOrder (2 * m) : ℝ) * Real.sqrt (Real.log (2 * m : ℝ)) /
        (2 * m : ℝ) ^ 2 := by
  have hk (k : Fin m) : BoxLensLift.halfIndex k =
      CommonClosureEnergy.halfIndex k := by
    apply Fin.ext
    rfl
  obtain ⟨k, hj | hj⟩ := half_decomposition hm j
  · rw [hj, hk]
    exact domain_Y_halfIndex_bound hm θ v hdom k
  · rw [hj, FixedSchurData.Y_halfTurn hm θ hdom.1, hk]
    exact domain_Y_halfIndex_bound hm θ v hdom k

end

end StructuralNote.FixedSchurDomainBounds

import StructuralNote.FixedSchurRationalWindowDomain
import StructuralNote.FixedSchurLogBoundedRepresentation

/-! The literal rational single window supplies the logarithmic normal bound
and the exact selected crossings needed by the fixed-Schur representation
theorem.  No small rational-coordinate window or branch hypothesis is used. -/

namespace StructuralNote.FixedSchurRationalWindowRepresentation

open Erdos1045 Erdos1045.EventualExact Complex Filter
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open RationalCommonConfiguration RationalAngleBranch RationalChart
open CommonTangentialParameters CommonFiberBounds CommonFiberGeometry
open CommonDomainClosure CommonDomainRadius CommonFiberNormalProjectionScaled
open EdgeCoordinates FixedSchurData FixedSchurLinear FixedSchurProjectionDomain
open FixedSchurChart FixedSchurEdgeGeometry FixedSchurLogBoundedRepresentation
open FixedSchurDomainSmallness
open FixedSchurRationalWindowEnergy FixedSchurRationalWindowDomain
open LensClosure
open scoped BigOperators Topology
noncomputable section

/-- An explicit logarithmic bound sufficient for the actual normal coordinate. -/
def representationConstraintConstant : ℝ := 7

theorem representationConstraintConstant_nonneg :
    0 ≤ representationConstraintConstant := by
  norm_num [representationConstraintConstant]

private theorem normal_abs_le_scale_difference {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → ℂ) (j : Fin n) :
    |EdgeCoordinates.normal (by omega) v j| ≤
      scale n * ‖difference (by omega) v j‖ := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsin : 0 < Real.sin (Real.pi / n) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · apply (div_lt_iff₀ hnR).2
      have hnR2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [Real.pi_pos]
  have hnormal : |EdgeCoordinates.normal (by omega) v j| ≤
      ‖(n : ℂ) * edgeRatio (by omega) v j‖ := by
    calc
      |EdgeCoordinates.normal (by omega) v j| ≤
          ‖(EdgeCoordinates.tangent (by omega) v j : ℂ) -
            I * (EdgeCoordinates.normal (by omega) v j : ℂ)‖ := by
        have h := Complex.abs_im_le_norm
          ((EdgeCoordinates.tangent (by omega) v j : ℂ) -
            I * (EdgeCoordinates.normal (by omega) v j : ℂ))
        simpa only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
          zero_add, zero_sub, abs_neg] using h
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
    |EdgeCoordinates.normal (by omega) v j| ≤
        ‖(n : ℂ) * edgeRatio (by omega) v j‖ := hnormal
    _ = (n : ℝ) * ‖edgeRatio (by omega) v j‖ := by
      simp only [norm_mul, Complex.norm_natCast]
    _ = (n : ℝ) *
        (‖difference (by omega) v j‖ / (2 * Real.sin (Real.pi / n))) := by
      rw [edgeRatio_eq_difference, norm_div, href]
    _ = scale n * ‖difference (by omega) v j‖ := by
      unfold scale
      field_simp

private theorem rotationEnergyCoefficient_tendsto :
    Tendsto (fun m : ℕ =>
      384480 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  have hl : Tendsto (fun m : ℕ =>
      Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2) atTop (𝓝 0) := by
    have hh := (isLittleO_log_rpow_atTop
      (by norm_num : (0 : ℝ) < 2)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, Real.rpow_two, Nat.cast_mul, Nat.cast_ofNat] using
      hh.comp (tendsto_natCast_atTop_atTop.comp hnat)
  simpa only [mul_div_assoc, mul_zero] using hl.const_mul 384480

private theorem eventual_reference_constraint_norm :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m)),
        ‖constraint (by omega) (fixedReferenceCenter (by omega) s)‖ ≤ 5 := by
  filter_upwards [eventual_coordinate_properties] with m hprops
  intro hm s
  have hp := hprops hm s (0 : Fin (2 * m) → ℝ) (0 : Fin (2 * m) → ℂ)
    (zero_inDomain (by omega : 0 < m))
  have heq : constraint (by omega) (fixedReferenceCenter (by omega) s) =
      coordinate (by omega) s 0 0 := by
    unfold fixedReferenceCenter
    apply center_constraint hm
    funext j
    simp [constraint, difference]
  rw [heq]
  exact hp.norm_le

/-- The rational single window bounds the actual normalized center's normal
coordinate by a fixed multiple of the logarithmic scale. -/
theorem eventual_normalizedCenter_constraint_bound :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        ‖constraint (by omega)
          (normalizedCenter (by omega) (rationalSign s) X)‖ ≤
            representationConstraintConstant * (logOrder (2 * m) : ℝ) := by
  have herr := rotationEnergyCoefficient_tendsto.eventually
    (gt_mem_nhds (show (0 : ℝ) < 3 / 4 by norm_num))
  filter_upwards [eventual_fixedReferenceCenter_data,
    eventual_reference_constraint_norm, herr] with m href hrefNorm herr
  intro hm s X hwindow
  let C := normalizedCenter (by omega : 0 < m) (rationalSign s) X
  let R := fixedReferenceCenter (by omega : 0 < m) s
  let D := C - R
  let Ex := pairEnergy (by omega : 0 < 2 * m)
    (fun j => (extendedAngleParameter (by omega : 0 < m) X j : ℂ))
  let AR := pairEnergy (by omega : 0 < 2 * m)
    (rationalCenter (by omega : 0 < m) (rationalSign s) X - R)
  let Aref := pairEnergy (by omega : 0 < 2 * m) R
  let L : ℝ := logOrder (2 * m)
  have hEx0 : 0 ≤ Ex := pairEnergy_nonneg _ _
  have hAR0 : 0 ≤ AR := pairEnergy_nonneg _ _
  have hAref0 : 0 ≤ Aref := pairEnergy_nonneg _ _
  have hL0 : 0 ≤ L := by positivity
  have halpha := angleMean_sq_le (by omega : 0 < m) X
  have hcenter := normalizedCenter_reference_energy_le (by omega : 0 < m) s X
  have hrot : 5 * angleMean (by omega : 0 < m) X ^ 2 * Aref ≤
      (384480 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2) * Ex := by
    have h1 := mul_le_mul_of_nonneg_left halpha (by norm_num : (0 : ℝ) ≤ 5)
    have h2 := mul_le_mul_of_nonneg_right h1 hAref0
    have hbound := (href hm s).2.2
    have hlog0 : 0 ≤ Real.log (2 * m : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 2 * m by omega)
    have hcoef0 : 0 ≤ 5 *
        (48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * Ex) := by
      positivity
    calc
      _ ≤ 5 * (48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * Ex) * Aref := by
        simpa only [Ex, Aref] using h2
      _ ≤ 5 * (48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * Ex) * 1602 :=
        mul_le_mul_of_nonneg_left hbound hcoef0
      _ = _ := by ring
  have hrot' : 5 * angleMean (by omega : 0 < m) X ^ 2 * Aref ≤
      (3 / 4 : ℝ) * Ex :=
    hrot.trans (mul_le_mul_of_nonneg_right herr.le hEx0)
  have hDenergy : pairEnergy (by omega) D ≤ 2 * (Ex + AR) := by
    change pairEnergy _
      (normalizedCenter (by omega) (rationalSign s) X -
        fixedReferenceCenter (by omega) s) ≤ _
    change pairEnergy _ _ ≤ (5 / 4 : ℝ) * AR +
      5 * angleMean (by omega : 0 < m) X ^ 2 * Aref at hcenter
    nlinarith only [hcenter, hrot', hEx0, hAR0]
  have hQ : Ex + AR < L ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
    simpa only [selectedWindowEnergy, Ex, AR, R, L] using hwindow
  have hDscaled : pairEnergy (by omega) D ≤ (L / 2) ^ 2 / (2 * m : ℝ) ^ 2 := by
    calc
      _ ≤ 2 * (Ex + AR) := hDenergy
      _ ≤ 2 * (L ^ 2 / (8 * (2 * m : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hQ.le (by norm_num)
      _ = _ := by ring
  have hDscaled' : pairEnergy (by omega) D ≤
      (L / 2) ^ 2 / ((2 * m : ℕ) : ℝ) ^ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hDscaled
  have hnormalD : ‖constraint (by omega) D‖ ≤ (5 / 4 : ℝ) * L := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hL0)).2
    intro j
    rw [← normal_eq_constraint hm D]
    simp only [Real.norm_eq_abs]
    have hn := normal_abs_le_scale_difference (show 2 ≤ 2 * m by omega) D j
    have hd := difference_of_scaled_energy (show 0 < 2 * m by omega) D
      (L := L / 2) (div_nonneg hL0 (by norm_num)) hDscaled' j
    have hd' : ‖difference (by omega) D j‖ ≤
        10 * (L / 2) / (2 * m : ℝ) ^ 2 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hd
    have hs := (scale_bounds (show 2 ≤ 2 * m by omega)).2
    have hs' : scale (2 * m) ≤ (2 * m : ℝ) ^ 2 / 4 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs
    calc
      _ ≤ scale (2 * m) * ‖difference (by omega) D j‖ := hn
      _ ≤ ((2 * m : ℝ) ^ 2 / 4) *
          (10 * (L / 2) / (2 * m : ℝ) ^ 2) :=
        mul_le_mul hs' hd' (norm_nonneg _) (by positivity)
      _ = (5 / 4 : ℝ) * L := by field_simp; ring
  have hconstraint : constraint (by omega) C =
      constraint (by omega) D + constraint (by omega) R := by
    rw [← constraint_add (show 2 ≤ 2 * m by omega)]
    congr 1
    dsimp [D]
    abel
  rw [hconstraint]
  calc
    _ ≤ ‖constraint (by omega) D‖ + ‖constraint (by omega) R‖ := norm_add_le _ _
    _ ≤ (5 / 4 : ℝ) * L + 5 := add_le_add hnormalD (hrefNorm hm s)
    _ ≤ representationConstraintConstant * L := by
      have hL1 : 1 ≤ L := by
        dsimp [L]
        exact FixedSchurDomainSmallness.logOrder_one_le (show 2 ≤ 2 * m by omega)
      norm_num [representationConstraintConstant]
      linarith

/-- The normalized fixed-Schur vertices are exactly a rotation and translation
of the actual rational configuration.  This identity is global in the rational
variables and needs no small-window assumption. -/
theorem vertex_normalizedCenter_eq_rigid {m : ℕ} (hm : 0 < m)
    (σ : Fin m → ℝ) (X : RationalConfiguration.Variables m → ℝ) :
    vertex (theta hm X) (normalizedCenter hm σ X) = fun j =>
      unit (-angleMean hm X) *
        (RationalConfiguration.configuration hm σ X j - centerMean hm σ X) := by
  funext j
  rw [vertex, normalized_diameter]
  unfold normalizedCenter RationalConfiguration.configuration RationalConfiguration.point
  ring

private theorem crossingVector_halfTurn {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega : 0 < m))
    (X : RationalConfiguration.Variables m → ℝ) (j : Fin (2 * m)) :
    crossingVector hm (theta (by omega) X)
        (normalizedCenter (by omega) (rationalSign s) X)
        (FiniteBox.patternSign s) (halfTurn (by omega) j) =
      -crossingVector hm (theta (by omega) X)
        (normalizedCenter (by omega) (rationalSign s) X)
        (FiniteBox.patternSign s) j := by
  have hθ := theta_halfPeriodic (by omega : 0 < m) X
  have hC := normalizedCenter_halfPeriodic (by omega : 0 < m) (rationalSign s) X
  unfold crossingVector
  rw [diameterVector_halfTurn (by omega) _ hθ,
    ← halfTurn_successor,
    diameterVector_halfTurn (by omega) _ hθ,
    hC (successor (by omega) j), hC j,
    FiniteBox.patternSign_antiperiodic s j]
  push_cast
  ring

/-- Rational closure and the sign pattern give all actual selected crossings
length two after normalization, without invoking a lens-branch formula. -/
theorem normalizedCenter_selectedCrossing {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega : 0 < m))
    (X : RationalConfiguration.Variables m → ℝ)
    (hclosure : RationalConfiguration.closure (by omega) (rationalSign s) X = 0) :
    ∀ j, ‖crossingVector hm (theta (by omega) X)
      (normalizedCenter (by omega) (rationalSign s) X)
      (FiniteBox.patternSign s) j‖ = 2 := by
  have hhalf (k : Fin m) : ‖crossingVector hm (theta (by omega) X)
      (normalizedCenter (by omega) (rationalSign s) X)
      (FiniteBox.patternSign s) (BoxLensLift.halfIndex k)‖ = 2 := by
    rw [show BoxLensLift.halfIndex k = CommonClosureEnergy.halfIndex k by
      apply Fin.ext
      rfl]
    have hdiff := normalizedCenter_half_difference (by omega : 0 < m)
      (rationalSign s) X hclosure k
    have hsign : rationalSign s k = 1 ∨ rationalSign s k = -1 :=
      FiniteBox.patternSign_is_sign s _
    have hcore :
        RationalConfiguration.diameter (by omega) X k +
            RationalConfiguration.diameter (by omega) X (k.val + 1) +
          ((rationalSign s k : ℝ) : ℂ) *
            RationalConfiguration.increment (by omega) (rationalSign s) X k =
          2 * RationalConfiguration.crossingUnit X k := by
      unfold RationalConfiguration.increment RationalChart.crossingIncrement
      rcases hsign with hs | hs <;> rw [hs] <;> norm_num
    have hvec : crossingVector hm (theta (by omega) X)
        (normalizedCenter (by omega) (rationalSign s) X)
        (FiniteBox.patternSign s) (CommonClosureEnergy.halfIndex k) =
      unit (-angleMean (by omega) X) *
        (2 * RationalConfiguration.crossingUnit X k) := by
      unfold crossingVector
      rw [normalized_diameter, normalized_diameter,
        successor_half_val (by omega : 0 < m) k]
      change unit (-angleMean (by omega) X) *
          RationalConfiguration.diameter (by omega) X k +
        unit (-angleMean (by omega) X) *
          RationalConfiguration.diameter (by omega) X (k.val + 1) +
        ((rationalSign s k : ℝ) : ℂ) * difference (by omega)
        (normalizedCenter (by omega) (rationalSign s) X)
          (CommonClosureEnergy.halfIndex k) = _
      rw [hdiff]
      change unit (-angleMean (by omega) X) *
          RationalConfiguration.diameter (by omega) X k +
        unit (-angleMean (by omega) X) *
          RationalConfiguration.diameter (by omega) X (k.val + 1) +
        ((rationalSign s k : ℝ) : ℂ) *
          (unit (-angleMean (by omega) X) *
            RationalConfiguration.increment (by omega) (rationalSign s) X k) = _
      calc
        _ = unit (-angleMean (by omega) X) *
            (RationalConfiguration.diameter (by omega) X k +
              RationalConfiguration.diameter (by omega) X (k.val + 1) +
              ((rationalSign s k : ℝ) : ℂ) *
                RationalConfiguration.increment (by omega) (rationalSign s) X k) := by ring
        _ = _ := by rw [hcore]
    rw [hvec, norm_mul, norm_mul, norm_unit,
      RationalConfiguration.crossingUnit_norm]
    norm_num
  intro j
  obtain ⟨k, hj | hj⟩ := half_decomposition (by omega : 0 < m) j
  · rw [hj]
    exact hhalf k
  · rw [hj, crossingVector_halfTurn hm s X, norm_neg]
    exact hhalf k

/-- The complete representation consequence of the literal rational window.
The only extra rational hypothesis is the actual polygon closure; the sign
condition is carried by `s`. -/
theorem eventual_selectedWindow_representation :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        RationalConfiguration.closure (by omega) (rationalSign s) X = 0 →
        let C := normalizedCenter (by omega) (rationalSign s) X
        let v := projection hm C
        constraint (by omega) C = coordinate (by omega) s (theta (by omega) X) v ∧
          C = center (coordinate (by omega) s (theta (by omega) X) v) v ∧
          vertex (theta (by omega) X) C =
            FixedSchurChart.configuration (by omega) s (theta (by omega) X) v ∧
          (vertex (theta (by omega) X) C = fun j =>
            unit (-angleMean (by omega) X) *
              (RationalConfiguration.configuration (by omega) (rationalSign s) X j -
                centerMean (by omega) (rationalSign s) X)) ∧
          ‖constraint (by omega) C - baseWord (FiniteBox.patternSign s)‖ ≤
            radius (2 * m) := by
  filter_upwards [eventual_selectedWindow_inDomain,
    eventual_normalizedCenter_constraint_bound,
    eventually_representation_of_selected_crossing_log_bounded
      representationConstraintConstant representationConstraintConstant_nonneg,
    eventual_coordinate_properties] with m hdomain hnormal hrepresentation hprops
  intro hm s X hwindow hclosure
  dsimp only
  let C := normalizedCenter (by omega : 0 < m) (rationalSign s) X
  let v := projection hm C
  have hC := normalizedCenter_halfPeriodic (by omega : 0 < m) (rationalSign s) X
  have hmean := normalizedCenter_mean_zero (by omega : 0 < m) (rationalSign s) X
  have hdom := hdomain hm s X hwindow
  have hqnorm := hnormal hm s X hwindow
  have hcross := normalizedCenter_selectedCrossing hm s X hclosure
  have hrep := hrepresentation hm s (theta (by omega) X) C hC hmean hdom hqnorm hcross
  have hrigid := vertex_normalizedCenter_eq_rigid (by omega : 0 < m)
    (rationalSign s) X
  have hp := hprops hm s (theta (by omega) X) v hdom
  refine ⟨hrep.1, hrep.2.1, hrep.2.2, hrigid, ?_⟩
  rw [hrep.1]
  exact hp.close

end
end StructuralNote.FixedSchurRationalWindowRepresentation

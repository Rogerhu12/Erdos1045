import StructuralNote.FixedSchurRationalWindowEnergy
import StructuralNote.FixedSchurLiftStability
import StructuralNote.RadialInterpolationEnergy

/-! The literal Section 11 single energy window implies membership in the
fixed-Schur common domain.  This file only proves the energy-domain bridge;
branch selection and collision exclusion remain separate statements. -/

namespace StructuralNote.FixedSchurRationalWindowDomain

open Erdos1045 Erdos1045.EventualExact Complex Filter
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open RationalCommonConfiguration RationalAngleBranch
open CommonTangentialParameters FixedSchurLinear FixedSchurProjectionDomain
open CommonDomainClosure CommonDomainRadius
open FixedSchurRationalWindowEnergy FixedSchurLiftStability
open AngularObjectiveCurvature LensClosure
open scoped BigOperators Topology
noncomputable section

/-- Restriction of an antiperiodic fixed-Schur sign word to the rational
configuration's first half. -/
def rationalSign {m : ℕ} {hm : 0 < m} (s : FiniteBox.SignPattern hm) : Fin m → ℝ :=
  fun j => FiniteBox.patternSign s ⟨j.val, by omega⟩

/-- The unnormalized center column in the rational base-edge gauge. -/
def rationalCenter {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (j : Fin (2 * m)) : ℂ :=
  RationalConfiguration.centerPrefix hm σ X (j.val % m)

/-- The single selected-window energy from Section 11: the energy of the
half-angle variables plus the energy of the displacement from the fixed-Schur
reference center. -/
def selectedWindowEnergy {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) (X : RationalConfiguration.Variables m → ℝ) : ℝ :=
  pairEnergy (by omega) (fun j => (extendedAngleParameter hm X j : ℂ)) +
    pairEnergy (by omega)
      (rationalCenter hm (rationalSign s) X - fixedReferenceCenter hm s)

theorem selectedWindowEnergy_nonneg {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) (X : RationalConfiguration.Variables m → ℝ) :
    0 ≤ selectedWindowEnergy hm s X :=
  add_nonneg (pairEnergy_nonneg (by omega) _ ) (pairEnergy_nonneg (by omega) _)

/-- The exact rotation and translation taking the rational center gauge to the
mean-zero gauge, written relative to the fixed-Schur reference. -/
theorem normalizedCenter_sub_reference {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) (X : RationalConfiguration.Variables m → ℝ)
    (j : Fin (2 * m)) :
    normalizedCenter hm (rationalSign s) X j - fixedReferenceCenter hm s j =
      unit (-angleMean hm X) *
          ((rationalCenter hm (rationalSign s) X -
            fixedReferenceCenter hm s) j) +
        (unit (-angleMean hm X) - 1) * fixedReferenceCenter hm s j -
        unit (-angleMean hm X) * centerMean hm (rationalSign s) X := by
  simp only [normalizedCenter, rationalCenter, Pi.sub_apply]
  ring

private theorem normSq_add_young (z w : ℂ) :
    normSq (z + w) ≤ (5 / 4 : ℝ) * normSq z + 5 * normSq w := by
  simp only [normSq_apply, add_re, add_im]
  nlinarith [sq_nonneg (z.re / 2 - 2 * w.re),
    sq_nonneg (z.im / 2 - 2 * w.im)]

/-- A fixed-coefficient Young inequality for pair energy. -/
theorem pairEnergy_add_le_five_four {n : ℕ} (hn : 0 < n)
    (c d : Fin n → ℂ) :
    pairEnergy hn (fun j => c j + d j) ≤
      (5 / 4 : ℝ) * pairEnergy hn c + 5 * pairEnergy hn d := by
  have hp (i j : Fin n) := div_le_div_of_nonneg_right
    (normSq_add_young (c i - c j) (d i - d j))
    (normSq_nonneg (LocalPhase.regularRoot n ^ (i : ℕ) -
      LocalPhase.regularRoot n ^ (j : ℕ)))
  simp_rw [show ∀ i j : Fin n, (c i - c j) + (d i - d j) =
    (c i + d i) - (c j + d j) by intros; ring] at hp
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
  simp only [add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  simp only [pairEnergy_eq_chord_sum]
  change _ ≤ (5 / 4 : ℝ) *
      ((∑ i, ∑ j, normSq (c i - c j) /
        normSq (LocalPhase.regularRoot n ^ (i : ℕ) -
          LocalPhase.regularRoot n ^ (j : ℕ))) / 2) +
    5 * ((∑ i, ∑ j, normSq (d i - d j) /
      normSq (LocalPhase.regularRoot n ^ (i : ℕ) -
        LocalPhase.regularRoot n ^ (j : ℕ))) / 2)
  linarith only [hs]

private theorem pairEnergy_sub_constant {n : ℕ} (hn : 0 < n)
    (c : Fin n → ℂ) (a : ℂ) :
    pairEnergy hn (fun j => c j - a) = pairEnergy hn c := by
  rw [pairEnergy_eq_chord_sum, pairEnergy_eq_chord_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  ring

private theorem projection_sub {m : ℕ} (hm : 2 ≤ m)
    (C D : Fin (2 * m) → ℂ) :
    projection hm (C - D) = projection hm C - projection hm D := by
  unfold projection
  rw [constraint_sub (show 2 ≤ 2 * m by omega), canonicalLift_sub]
  abel

/-- Formula (11.8) before the fixed-Schur projection: rotation of the raw
displacement costs nothing, while rotation of the fixed reference is controlled
by the square of the mean angle. -/
theorem normalizedCenter_reference_energy_le {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) (X : RationalConfiguration.Variables m → ℝ) :
    pairEnergy (by omega)
        (normalizedCenter hm (rationalSign s) X - fixedReferenceCenter hm s) ≤
      (5 / 4 : ℝ) * pairEnergy (by omega)
        (rationalCenter hm (rationalSign s) X - fixedReferenceCenter hm s) +
      5 * angleMean hm X ^ 2 * pairEnergy (by omega) (fixedReferenceCenter hm s) := by
  let u : ℂ := unit (-angleMean hm X)
  let R := rationalCenter hm (rationalSign s) X - fixedReferenceCenter hm s
  let D := fun j : Fin (2 * m) => u * R j + (u - 1) * fixedReferenceCenter hm s j
  have hfun : normalizedCenter hm (rationalSign s) X - fixedReferenceCenter hm s =
      fun j => D j - u * centerMean hm (rationalSign s) X := by
    funext j
    exact normalizedCenter_sub_reference hm s X j
  have hyoung := pairEnergy_add_le_five_four (show 0 < 2 * m by omega)
    (fun j => u * R j) (fun j => (u - 1) * fixedReferenceCenter hm s j)
  have hu : ‖u‖ = 1 := by
    simp [u, norm_unit]
  have hrot : pairEnergy (by omega) (fun j => u * R j) = pairEnergy (by omega) R := by
    rw [RadialInterpolationEnergy.pairEnergy_scale, hu, one_pow, one_mul]
  have href : pairEnergy (by omega)
      (fun j => (u - 1) * fixedReferenceCenter hm s j) =
      ‖u - 1‖ ^ 2 * pairEnergy (by omega) (fixedReferenceCenter hm s) := by
    rw [RadialInterpolationEnergy.pairEnergy_scale]
  have hnorm : ‖u - 1‖ ≤ |angleMean hm X| := by
    simpa only [u, unit, Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_zero,
      sub_zero, abs_neg] using norm_unit_sub_le (-angleMean hm X) 0
  have hsq : ‖u - 1‖ ^ 2 ≤ angleMean hm X ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [hfun, pairEnergy_sub_constant]
  change pairEnergy (by omega) D ≤
    (5 / 4 : ℝ) * pairEnergy (by omega) R +
      5 * angleMean hm X ^ 2 * pairEnergy (by omega) (fixedReferenceCenter hm s)
  rw [show D = (fun j => u * R j +
    (u - 1) * fixedReferenceCenter hm s j) from rfl]
  rw [hrot, href] at hyoung
  have href0 := pairEnergy_nonneg (show 0 < 2 * m by omega) (fixedReferenceCenter hm s)
  nlinarith only [hyoung, mul_le_mul_of_nonneg_right hsq href0]

/-- The actual fixed-Schur projected center obeys the quantitative second
estimate in (11.8). -/
theorem projected_normalizedCenter_energy_le {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega : 0 < m))
    (X : RationalConfiguration.Variables m → ℝ)
    (hrefHalf : HalfPeriodic (by omega) (fixedReferenceCenter (by omega) s))
    (hrefMean : (∑ j, fixedReferenceCenter (by omega) s j) = 0) :
    pairEnergy (by omega)
        (projection hm (normalizedCenter (by omega) (rationalSign s) X)) ≤
      (15 / 2 : ℝ) * pairEnergy (by omega)
        (rationalCenter (by omega) (rationalSign s) X -
          fixedReferenceCenter (by omega) s) +
      30 * angleMean (by omega) X ^ 2 *
        pairEnergy (by omega) (fixedReferenceCenter (by omega) s) := by
  let C := normalizedCenter (by omega : 0 < m) (rationalSign s) X
  let R := fixedReferenceCenter (by omega : 0 < m) s
  have hCHalf := normalizedCenter_halfPeriodic (by omega : 0 < m)
    (rationalSign s) X
  have hCMean := normalizedCenter_mean_zero (by omega : 0 < m)
    (rationalSign s) X
  have hdiffHalf : HalfPeriodic (by omega) (C - R) := by
    intro j
    simp only [Pi.sub_apply, C, R]
    rw [hCHalf j, hrefHalf j]
  have hdiffMean : (∑ j, (C - R) j) = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, C, R, hCMean, hrefMean, sub_zero]
  have hprojEq : projection hm C = projection hm (C - R) := by
    rw [projection_sub, fixedReferenceCenter_projection hm s, sub_zero]
  have hp := projection_pairEnergy_le_six hm (C - R) hdiffHalf hdiffMean
  have hc := normalizedCenter_reference_energy_le (by omega : 0 < m) s X
  rw [hprojEq]
  nlinarith only [hp, hc]

private theorem errorCoefficient_tendsto :
    Tendsto (fun m : ℕ =>
      2306880 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2)
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
  simpa only [mul_div_assoc, mul_zero] using hl.const_mul 2306880

/-- The literal single window `E(x) + A(C-Cref) < L_n²/(8n²)` puts the
recovered mean-angle and actual fixed-Schur projected center in the common
energy domain.  No `SmallWindow` or branch-positivity hypothesis is used. -/
theorem eventual_selectedWindow_inDomain :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        InDomain (by omega) (theta (by omega) X)
          (projection hm
            (normalizedCenter (by omega) (rationalSign s) X)) := by
  have herr := errorCoefficient_tendsto.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [eventual_fixedReferenceCenter_data, herr] with m href herr
  intro hm s X hwindow
  have hrefData := href hm s
  let Ex := pairEnergy (by omega : 0 < 2 * m)
    (fun j => (extendedAngleParameter (by omega : 0 < m) X j : ℂ))
  let AR := pairEnergy (by omega : 0 < 2 * m)
    (rationalCenter (by omega : 0 < m) (rationalSign s) X -
      fixedReferenceCenter (by omega) s)
  let Aref := pairEnergy (by omega : 0 < 2 * m)
    (fixedReferenceCenter (by omega : 0 < m) s)
  have hEx0 : 0 ≤ Ex := pairEnergy_nonneg _ _
  have hAR0 : 0 ≤ AR := pairEnergy_nonneg _ _
  have hAref0 : 0 ≤ Aref := pairEnergy_nonneg _ _
  have htheta := theta_energy_le_four (by omega : 0 < m) X
  have halpha := angleMean_sq_le (by omega : 0 < m) X
  have hproject := projected_normalizedCenter_energy_le hm s X hrefData.1 hrefData.2.1
  have hrotation :
      30 * angleMean (by omega : 0 < m) X ^ 2 * Aref ≤
        (2306880 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2) * Ex := by
    have h1 := mul_le_mul_of_nonneg_left halpha (by norm_num : (0 : ℝ) ≤ 30)
    have h2 := mul_le_mul_of_nonneg_right h1 hAref0
    have hbound := hrefData.2.2
    have hlog0 : 0 ≤ Real.log (2 * m : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 2 * m by omega)
    have hcoef0 : 0 ≤ 30 * (48 * Real.log (2 * m : ℝ) /
        (2 * m : ℝ) ^ 2 * Ex) := by positivity
    calc
      _ ≤ 30 * (48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * Ex) * Aref := by
        simpa only [Ex] using h2
      _ ≤ 30 * (48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * Ex) * 1602 :=
        mul_le_mul_of_nonneg_left hbound hcoef0
      _ = _ := by ring
  have herrle :
      2306880 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 ≤ 1 / 2 := herr.le
  have hrotation' : 30 * angleMean (by omega : 0 < m) X ^ 2 * Aref ≤
      (1 / 2 : ℝ) * Ex :=
    hrotation.trans (mul_le_mul_of_nonneg_right herrle hEx0)
  have htotal :
      pairEnergy (by omega) (fun j => (theta (by omega) X j : ℂ)) +
          pairEnergy (by omega)
            (projection hm
              (normalizedCenter (by omega) (rationalSign s) X)) ≤
        (15 / 2 : ℝ) * (Ex + AR) := by
    change pairEnergy _ _ ≤ 4 * Ex at htheta
    change pairEnergy _ _ ≤ (15 / 2 : ℝ) * AR +
      30 * angleMean (by omega : 0 < m) X ^ 2 * Aref at hproject
    nlinarith only [htheta, hproject, hrotation', hEx0, hAR0]
  have hQ : Ex + AR <
      (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
    simpa only [selectedWindowEnergy, Ex, AR] using hwindow
  have hQ0 : 0 ≤ Ex + AR := add_nonneg hEx0 hAR0
  have hstrict :
      pairEnergy (by omega) (fun j => (theta (by omega) X j : ℂ)) +
          pairEnergy (by omega)
            (projection hm
              (normalizedCenter (by omega) (rationalSign s) X)) <
        energyRadius (2 * m) := by
    have h75lt8 : (15 / 2 : ℝ) * (Ex + AR) < 8 * (Ex + AR) ∨ Ex + AR = 0 := by
      rcases hQ0.eq_or_lt with hzero | hpos
      · exact Or.inr hzero.symm
      · left
        nlinarith
    have h8 : 8 * (Ex + AR) < energyRadius (2 * m) := by
      have hmul := mul_lt_mul_of_pos_left hQ (show (0 : ℝ) < 8 by norm_num)
      have heq :
          8 * ((logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2)) =
            energyRadius (2 * m) := by
        unfold energyRadius
        field_simp
        norm_num [Nat.cast_mul]
        ring
      exact hmul.trans_eq heq
    rcases h75lt8 with hlt | hzero
    · exact htotal.trans_lt (hlt.trans h8)
    · rw [hzero, mul_zero] at htotal
      rw [hzero, mul_zero] at h8
      exact htotal.trans_lt h8
  exact ⟨theta_halfPeriodic (by omega) X, theta_mean_zero (by omega) X,
    projection_parameterSpace hm
      (normalizedCenter_halfPeriodic (by omega) (rationalSign s) X)
      (normalizedCenter_mean_zero (by omega) (rationalSign s) X),
    hstrict⟩

end
end StructuralNote.FixedSchurRationalWindowDomain

import StructuralNote.RationalCommonConfiguration
import StructuralNote.FixedSchurProjectionDomain
import StructuralNote.FixedSchurChartCenterBounds
import StructuralNote.EdgeEnergyComparison
import EventualExact.DiscreteSobolev

/-! Quantitative energy bridges from the rational half-angle coordinates to
the fixed-Schur mean-angle and free-center coordinates. -/

namespace StructuralNote.FixedSchurRationalWindowEnergy

open Erdos1045 Erdos1045.EventualExact Complex Filter
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open RationalCommonConfiguration RationalAngleBranch
open CommonTangentialParameters FixedSchurLinear FixedSchurProjectionDomain
open EdgeCoordinates EdgeEnergyComparison AngularObjectiveCurvature
open CommonDomainClosure CommonDomainRadius FixedSchurChart
open FixedSchurChartCenterBounds
open scoped BigOperators Topology
noncomputable section

/-- The half-periodic extension of the rational diameter half-angle parameter. -/
def extendedAngleParameter {m : ℕ} (hm : 0 < m)
    (X : RationalConfiguration.Variables m → ℝ) (j : Fin (2 * m)) : ℝ :=
  RationalConfiguration.angleParameter X ⟨j.val % m, Nat.mod_lt _ hm⟩

/-- The map `x ↦ 2 arctan x` is globally two-Lipschitz. -/
theorem angle_difference_le (x y : ℝ) :
    |2 * Real.arctan x - 2 * Real.arctan y| ≤ 2 * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun t : ℝ => 2 * Real.arctan t) (s := Set.univ) (C := 2)
    (fun t _ => (angle_hasDerivAt t).differentiableAt)
    (fun t _ => show ‖deriv (fun x : ℝ => 2 * Real.arctan x) t‖ ≤ (2 : ℝ) by
      rw [(angle_hasDerivAt t).deriv, Real.norm_eq_abs,
        abs_of_pos (angle_derivative_pos t)]
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2)).2
        (by nlinarith [sq_nonneg t]))
    (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    (x := y) (y := x) (by trivial) (by trivial)
  simpa only [Real.norm_eq_abs, dist_eq] using h

/-- Formula (11.7), first part: subtracting the mean does not change pair
differences, and `2 arctan` costs at most a factor four in energy. -/
theorem theta_energy_le_four {m : ℕ} (hm : 0 < m)
    (X : RationalConfiguration.Variables m → ℝ) :
    pairEnergy (by omega) (fun j => (theta hm X j : ℂ)) ≤
      4 * pairEnergy (by omega) (fun j => (extendedAngleParameter hm X j : ℂ)) := by
  rw [pairEnergy_eq_chord_sum, pairEnergy_eq_chord_sum]
  have hsum :
      (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
          normSq ((theta hm X i : ℂ) - (theta hm X j : ℂ)) /
            normSq (LocalPhase.regularRoot (2 * m) ^ (i : ℕ) -
              LocalPhase.regularRoot (2 * m) ^ (j : ℕ))) ≤
        4 * (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
          normSq ((extendedAngleParameter hm X i : ℂ) -
              (extendedAngleParameter hm X j : ℂ)) /
            normSq (LocalPhase.regularRoot (2 * m) ^ (i : ℕ) -
              LocalPhase.regularRoot (2 * m) ^ (j : ℕ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _
      (normSq_nonneg (LocalPhase.regularRoot (2 * m) ^ (i : ℕ) -
        LocalPhase.regularRoot (2 * m) ^ (j : ℕ)))
    have h := angle_difference_le (extendedAngleParameter hm X i)
      (extendedAngleParameter hm X j)
    have hs :
        (2 * Real.arctan (extendedAngleParameter hm X i) -
            2 * Real.arctan (extendedAngleParameter hm X j)) ^ 2 ≤
          4 * (extendedAngleParameter hm X i - extendedAngleParameter hm X j) ^ 2 := by
      have hsquare := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 h
      norm_num [mul_pow, sq_abs] at hsquare ⊢
      exact hsquare
    simp only [← ofReal_sub, normSq_ofReal]
    have heq : theta hm X i - theta hm X j =
        2 * Real.arctan (extendedAngleParameter hm X i) -
          2 * Real.arctan (extendedAngleParameter hm X j) := by
      simp only [theta, angle, extendedAngleParameter]
      ring
    rw [heq]
    simpa only [pow_two] using hs
  nlinarith only [hsum]

/-- Formula (11.7), second part, with an explicit constant.  The base-edge
gauge has `x₀ = 0`, so the mean angle is the value at zero of the mean-zero
angle column. -/
theorem angleMean_sq_le {m : ℕ} (hm : 0 < m)
    (X : RationalConfiguration.Variables m → ℝ) :
    angleMean hm X ^ 2 ≤
      48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 *
        pairEnergy (by omega) (fun j => (extendedAngleParameter hm X j : ℂ)) := by
  let j₀ : Fin (2 * m) := ⟨0, by omega⟩
  have hp := DiscreteSobolev.pointwise_sq_le (show 2 ≤ 2 * m by omega)
    (fun j => (theta hm X j : ℂ)) (theta_mean_zero hm X) j₀
  have hp' : normSq ((theta hm X j₀ : ℝ) : ℂ) ≤
      12 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 *
        pairEnergy (by omega) (fun j => (theta hm X j : ℂ)) := by
    rw [normSq_eq_norm_sq]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hp
  have he := theta_energy_le_four hm X
  have hcoef : 0 ≤ 12 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 := by
    have hn : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hn)) (sq_nonneg _)
  have hzero : theta hm X j₀ = -angleMean hm X := by
    simp [j₀, theta, angle, RationalConfiguration.angleParameter]
  calc
    angleMean hm X ^ 2 = normSq ((theta hm X j₀ : ℝ) : ℂ) := by
      rw [hzero]
      simp only [normSq_ofReal]
      ring
    _ ≤ 12 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 *
        pairEnergy (by omega) (fun j => (theta hm X j : ℂ)) := hp'
    _ ≤ 12 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 *
        (4 * pairEnergy (by omega)
          (fun j => (extendedAngleParameter hm X j : ℂ))) :=
      mul_le_mul_of_nonneg_left he hcoef
    _ = _ := by ring

/-- The actual fixed-Schur projection has pair-energy operator norm at most
`sqrt 6` on half-periodic mean-zero centers.  This is the quantitative
projection estimate used in (11.8). -/
theorem projection_pairEnergy_le_six {m : ℕ} (hm : 2 ≤ m)
    (C : Fin (2 * m) → ℂ) (hC : HalfPeriodic (by omega) C)
    (hmean : (∑ j, C j) = 0) :
    pairEnergy (by omega) (projection hm C) ≤ 6 * pairEnergy (by omega) C := by
  let v := projection hm C
  have hv := projection_parameterSpace hm hC hmean
  have hfirstC : centerCoefficient (by omega) C 0 = 0 :=
    centerCoefficient_even_zero (by omega) C hC 0 (by decide)
  have hfirstv : centerCoefficient (by omega) v 0 = 0 :=
    centerCoefficient_even_zero (by omega) v hv.1 0 (by decide)
  have hnormalv : normal (by omega) v = 0 := by
    change normal (by omega) (projection hm C) = 0
    rw [normal_eq_constraint hm, projection_constraint]
  have htangent : tangent (by omega) v = freeTangent (by omega) C := by
    have h := center_tangent hm (constraint (by omega) C) v
    change tangent (by omega) (center (constraint (by omega) C) (projection hm C)) =
      J (constraint (by omega) C) + tangent (by omega) v at h
    rw [center_projection hm C] at h
    rw [freeTangent, normal_eq_constraint hm C, h]
    abel
  have hJ0 : J (0 : Fin (2 * m) → ℝ) = 0 := by
    funext j
    simp [J, firstCoefficient]
  have hfreev : freeTangent (by omega) v = freeTangent (by omega) C := by
    rw [freeTangent, hnormalv, hJ0, sub_zero, htangent]
  have hfirstv0 : firstEnergy (by omega) v = 0 := by
    rw [firstEnergy_eq_chi (show 3 ≤ 2 * m by omega) v, hnormalv]
    simp [firstMass, firstCoefficient]
  have hvaluev0 : EdgeNormalForm.value (normal (by omega) v) = 0 := by
    rw [hnormalv]
    simp [EdgeNormalForm.value, midpointCoefficient]
  have hu : pairEnergy (by omega) v ≤
      6 * EdgeNormalForm.value (freeTangent (by omega) C) := by
    calc
      _ ≤ firstEnergy (by omega) v +
          6 * (EdgeNormalForm.value (normal (by omega) v) +
            EdgeNormalForm.value (freeTangent (by omega) v)) :=
        (energy_comparison (show 3 ≤ 2 * m by omega) v hfirstv).2
      _ = _ := by rw [hfirstv0, hvaluev0, hfreev]; ring
  have hfirstC0 : 0 ≤ firstEnergy (by omega) C := by
    unfold firstEnergy
    have hn0 : (0 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by positivity
    have hn2 : (0 : ℝ) ≤ ((2 * m : ℕ) : ℝ) - 2 := by
      have : (2 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
        exact_mod_cast (show 2 ≤ 2 * m by omega)
      linarith
    exact mul_nonneg (mul_nonneg hn0 hn2) (normSq_nonneg _)
  have hnormalC0 : 0 ≤ EdgeNormalForm.value (normal (by omega) C) :=
    EdgeNormalForm.value_nonneg _
  have hfreele : EdgeNormalForm.value (freeTangent (by omega) C) ≤
      pairEnergy (by omega) C := by
    have hl := (energy_comparison (show 3 ≤ 2 * m by omega) C hfirstC).1
    linarith
  exact hu.trans (mul_le_mul_of_nonneg_left hfreele (by norm_num))

/-- The reference center in Section 11 is the fixed-Schur center at zero free
parameters, rather than the zero point of the older tangential chart. -/
def fixedReferenceCenter {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) : Fin (2 * m) → ℂ :=
  center (coordinate hm s 0 0) 0

theorem fixedReferenceCenter_projection {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (by omega : 0 < m)) :
    projection hm (fixedReferenceCenter (by omega) s) = 0 := by
  unfold fixedReferenceCenter
  apply projection_center hm _ 0
  funext j
  simp [constraint, difference]

theorem zero_inDomain {m : ℕ} (hm : 0 < m) :
    InDomain hm (0 : Fin (2 * m) → ℝ) (0 : Fin (2 * m) → ℂ) := by
  have hnR : (2 : ℝ) ≤ 2 * m := by exact_mod_cast (show 2 ≤ 2 * m by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (2 * m : ℝ) :=
    Real.log_le_log (by norm_num) hnR
  have hratio : (1 : ℝ) ≤ Real.log (2 * m : ℝ) / Real.log 2 :=
    (le_div_iff₀ hlog2).2 (by simpa using hlog)
  have hceil : Real.log (2 * m : ℝ) / Real.log 2 ≤
      (logOrder (2 * m) : ℝ) := by
    simpa only [logOrder, Nat.cast_mul, Nat.cast_ofNat] using
      (Nat.le_ceil (Real.log ((2 * m : ℕ) : ℝ) / Real.log 2))
  have hL : (1 : ℝ) ≤ (logOrder (2 * m) : ℝ) := hratio.trans hceil
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    rfl
  · simp
  · refine ⟨?_, ?_, ?_⟩
    · intro j
      rfl
    · simp
    · funext j
      simp [constraint, difference]
  · have hz : pairEnergy (by omega) (0 : Fin (2 * m) → ℂ) = 0 := by
      rw [pairEnergy_eq_chord_sum]
      simp
    simp only [Pi.zero_apply, ofReal_zero, ← Pi.zero_def, hz, add_zero]
    unfold energyRadius
    exact div_pos (sq_pos_of_pos (lt_of_lt_of_le (by norm_num) hL)) (by positivity)

theorem eventual_fixedReferenceCenter_data :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m)),
        HalfPeriodic (by omega) (fixedReferenceCenter (by omega) s) ∧
          (∑ j, fixedReferenceCenter (by omega) s j) = 0 ∧
          pairEnergy (by omega) (fixedReferenceCenter (by omega) s) ≤ 1602 := by
  filter_upwards [eventual_coordinate_properties, eventual_center_bounds] with m hprops hcenter
  intro hm s
  have hdom := zero_inDomain (by omega : 0 < m)
  have hp := hprops hm s 0 0 hdom
  refine ⟨?_, ?_, (hcenter hm s 0 0 hdom).2⟩
  · unfold fixedReferenceCenter
    exact center_halfPeriodic hm _ 0 hp.antiperiodic (by intro j; rfl)
  · simpa only [fixedReferenceCenter] using hp.mean_zero

end
end StructuralNote.FixedSchurRationalWindowEnergy

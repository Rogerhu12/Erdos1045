import StructuralNote.ExplicitHessianThresholdFixedSchur
import StructuralNote.ExplicitComparisonScalars
import StructuralNote.FixedSchurWordEnergy
import StructuralNote.FixedSchurHammingStability
import StructuralNote.FixedSchurRotatedStability

/-! Word and center stability at the explicit fixed-Schur order. -/
namespace StructuralNote.ExplicitComparisonStability
open scoped BigOperators Topology
open Complex Erdos1045 Erdos1045.EventualExact
open FiniteBox FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum SchurLiftBounds
open CommonDomainClosure EdgeCoordinates FixedSchurData FixedSchurLinear FixedSchurChart
open FixedSchurContraction FixedSchurDomainSmallness FixedSchurEquations
open FixedSchurHarmonicBounds FixedSchurScalarRoot FixedSchurLiftStability
open SolWordHamming SignPatternSymmetry FixedSchurRotatedStability
open FixedSchurNormalExpansion CommonClosureEnergy
noncomputable section
private theorem root_difference_same_sign {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ τ q r : Fin (2 * m) → ℝ)
    (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hτ : ∀ j, τ j = 1 ∨ τ j = -1)
    (hq : Properties hm θ v σ q) (hr : Properties hm θ v τ r)
    (hsmallσ : ∀ j, |Y (by omega) θ j| + epsilon (2 * m) *
      (|tangent (by omega) v j| + 2 * (‖baseWord σ‖ + radius (2 * m))) ≤ 1 / 4)
    (hsmallτ : ∀ j, |Y (by omega) θ j| + epsilon (2 * m) *
      (|tangent (by omega) v j| + 2 * (‖baseWord τ‖ + radius (2 * m))) ≤ 1 / 4)
    {j : Fin (2 * m)} (hji : σ j = τ j) :
    |q j - r j| ≤
      (1 / (2 * (2 * m : ℝ))) * ∑ i : Fin (2 * m), |q i - r i| := by
  have hε : 0 < epsilon (2 * m) := epsilon_pos (show 2 ≤ 2 * m by omega)
  have hqmem : q ∈ Metric.closedBall (baseWord σ) (radius (2 * m)) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hq.close
  have hrmem : r ∈ Metric.closedBall (baseWord τ) (radius (2 * m)) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hr.close
  have hinq := ball_input_bound (n := 2 * m) (by omega) hε
    (Y (by omega) θ) (tangent (by omega) v) σ (baseWord σ) hσ hsmallσ hqmem j
  have hinr := ball_input_bound (n := 2 * m) (by omega) hε
    (Y (by omega) θ) (tangent (by omega) v) τ (baseWord τ) hτ hsmallτ hrmem j
  have hinr' :
      |Y (by omega) θ j + σ j * epsilon (2 * m) *
        (tangent (by omega) v j + J r j)| ≤ 1 / 4 := by
    simpa only [hji] using hinr
  have hlip := rootValue_lipschitz_of_le_one (X := X (by omega) θ j)
    (hσ j) hε (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 1) hinq hinr'
  have hqroot := congrFun hq.fixed j
  have hrroot := congrFun hr.fixed j
  change rootValue (σ j) (epsilon (2 * m)) (X (by omega) θ j)
      (Y (by omega) θ j)
      (tangent (by omega) v j + J q j) = q j at hqroot
  change rootValue (τ j) (epsilon (2 * m)) (X (by omega) θ j)
      (Y (by omega) θ j)
      (tangent (by omega) v j + J r j) = r j at hrroot
  rw [← hji] at hrroot
  calc
    |q j - r j| =
        |rootValue (σ j) (epsilon (2 * m)) (X (by omega) θ j)
            (Y (by omega) θ j) (tangent (by omega) v j + J q j) -
          rootValue (σ j) (epsilon (2 * m)) (X (by omega) θ j)
            (Y (by omega) θ j) (tangent (by omega) v j + J r j)| := by
      rw [hqroot, hrroot]
    _ ≤ (1 / 4 : ℝ) * |J q j - J r j| := by
      convert hlip using 1
      ring
    _ ≤ (1 / 4 : ℝ) *
        ((2 : ℝ) / (2 * m : ℝ) * ∑ i : Fin (2 * m), |q i - r i|) := by
      have hJ := J_pointwise_l1 (show 0 < 2 * m by omega) (q - r) j
      rw [J_sub] at hJ
      have hJ' : |J q j - J r j| ≤
          (2 : ℝ) / (2 * m : ℝ) * ∑ i : Fin (2 * m), |q i - r i| := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat, Pi.sub_apply] using hJ
      gcongr
    _ = (1 / (2 * (2 * m : ℝ))) *
        ∑ i : Fin (2 * m), |q i - r i| := by ring

private theorem pointwise_coordinate_difference {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ τ q r : Fin (2 * m) → ℝ)
    (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hτ : ∀ j, τ j = 1 ∨ τ j = -1)
    (hq : Properties hm θ v σ q) (hr : Properties hm θ v τ r)
    (hsmallσ : ∀ j, |Y (by omega) θ j| + epsilon (2 * m) *
      (|tangent (by omega) v j| + 2 * (‖baseWord σ‖ + radius (2 * m))) ≤ 1 / 4)
    (hsmallτ : ∀ j, |Y (by omega) θ j| + epsilon (2 * m) *
      (|tangent (by omega) v j| + 2 * (‖baseWord τ‖ + radius (2 * m))) ≤ 1 / 4)
    (j : Fin (2 * m)) :
    |q j - r j| ≤ if σ j = τ j then
      (1 / (2 * (2 * m : ℝ))) * ∑ i : Fin (2 * m), |q i - r i| else 10 := by
  by_cases hji : σ j = τ j
  · simp only [hji, if_pos]
    exact root_difference_same_sign hm θ v σ τ q r hσ hτ hq hr hsmallσ hsmallτ hji
  · simp only [hji, if_false]
    have hqj : |q j| ≤ ‖q‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm q j
    have hrj : |r j| ≤ ‖r‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm r j
    calc
      |q j - r j| = |q j + (-r j)| := by congr 1
      _ ≤ |q j| + |(-r j)| := abs_add_le _ _
      _ = |q j| + |r j| := by rw [abs_neg]
      _ ≤ ‖q‖ + ‖r‖ := add_le_add hqj hrj
      _ ≤ 10 := by nlinarith [hq.norm_le, hr.norm_le]

private theorem absorb_coordinate_sum {n : ℕ} (hn : 0 < n)
    (q r : Fin n → ℝ) (D : Finset (Fin n))
    (hD : ∀ j ∈ D, |q j - r j| ≤ 10)
    (hC : ∀ j ∉ D, |q j - r j| ≤
      (1 / (2 * (n : ℝ))) * ∑ i : Fin n, |q i - r i|) :
    ∑ j : Fin n, |q j - r j| ≤ 20 * (D.card : ℝ) := by
  let S : ℝ := ∑ j : Fin n, |q j - r j|
  let C : Finset (Fin n) := Finset.univ \ D
  have hdis : Disjoint D C := by
    refine Finset.disjoint_left.2 ?_
    intro j hjD hjC
    exact (Finset.mem_sdiff.mp hjC).2 hjD
  have hunion : D ∪ C = (Finset.univ : Finset (Fin n)) := by
    ext j
    by_cases hj : j ∈ D <;> simp [C, hj]
  have hDsum : ∑ j ∈ D, |q j - r j| ≤ 10 * (D.card : ℝ) := by
    calc
      ∑ j ∈ D, |q j - r j| ≤ ∑ _j ∈ D, (10 : ℝ) :=
        Finset.sum_le_sum (fun j hj => hD j hj)
      _ = 10 * (D.card : ℝ) := by simp; ring
  have hC' (j : Fin n) (hj : j ∈ C) :
      |q j - r j| ≤ (1 / (2 * (n : ℝ))) * S := by
    apply hC j
    exact (Finset.mem_sdiff.mp hj).2
  have hCsum : ∑ j ∈ C, |q j - r j| ≤
      (C.card : ℝ) * ((1 / (2 * (n : ℝ))) * S) := by
    calc
      ∑ j ∈ C, |q j - r j| ≤
          ∑ _j ∈ C, ((1 / (2 * (n : ℝ))) * S) :=
        Finset.sum_le_sum (fun j hj => hC' j hj)
      _ = (C.card : ℝ) * ((1 / (2 * (n : ℝ))) * S) := by simp
  have hCcardNat : C.card ≤ (Finset.univ : Finset (Fin n)).card := by
    exact Finset.card_le_card (by intro j hj; simp)
  have hCcard : (C.card : ℝ) ≤ (n : ℝ) := by
    have hCcardNat' : C.card ≤ n := by simpa using hCcardNat
    exact_mod_cast hCcardNat'
  have hcoef : 0 ≤ (1 / (2 * (n : ℝ))) * S := by
    positivity
  have hCsum' : ∑ j ∈ C, |q j - r j| ≤
      (n : ℝ) * ((1 / (2 * (n : ℝ))) * S) :=
    hCsum.trans (mul_le_mul_of_nonneg_right hCcard hcoef)
  have hdecomp : S =
      (∑ j ∈ D, |q j - r j|) + ∑ j ∈ C, |q j - r j| := by
    dsimp [S]
    rw [← Finset.sum_union hdis, hunion]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhalf : (n : ℝ) * ((1 / (2 * (n : ℝ))) * S) = S / 2 := by
    field_simp [ne_of_gt hnR]
  have hbound : S ≤ 10 * (D.card : ℝ) + S / 2 := by
    calc
      S = (∑ j ∈ D, |q j - r j|) + ∑ j ∈ C, |q j - r j| := hdecomp
      _ ≤ 10 * (D.card : ℝ) +
          (n : ℝ) * ((1 / (2 * (n : ℝ))) * S) :=
        add_le_add hDsum hCsum'
      _ = 10 * (D.card : ℝ) + S / 2 := by rw [hhalf]
  have hfinal : S ≤ 20 * (D.card : ℝ) := by
    nlinarith
  simpa only [S] using hfinal

private theorem coordinate_l1_of_properties {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ τ q r : Fin (2 * m) → ℝ)
    (hσ : ∀ j, σ j = 1 ∨ σ j = -1)
    (hτ : ∀ j, τ j = 1 ∨ τ j = -1)
    (hq : Properties hm θ v σ q) (hr : Properties hm θ v τ r)
    (hsmallσ : ∀ j, |Y (by omega) θ j| + epsilon (2 * m) *
      (|tangent (by omega) v j| + 2 * (‖baseWord σ‖ + radius (2 * m))) ≤ 1 / 4)
    (hsmallτ : ∀ j, |Y (by omega) θ j| + epsilon (2 * m) *
      (|tangent (by omega) v j| + 2 * (‖baseWord τ‖ + radius (2 * m))) ≤ 1 / 4) :
    ∑ j : Fin (2 * m), |q j - r j| ≤
      20 * ((Finset.univ.filter (fun j => σ j ≠ τ j)).card : ℝ) := by
  let D : Finset (Fin (2 * m)) := Finset.univ.filter (fun j => σ j ≠ τ j)
  have hpoint (j : Fin (2 * m)) :
      |q j - r j| ≤ if j ∈ D then 10 else
        (1 / (2 * (2 * m : ℝ))) * ∑ i : Fin (2 * m), |q i - r i| := by
    have hp := pointwise_coordinate_difference hm θ v σ τ q r hσ hτ hq hr
      hsmallσ hsmallτ j
    by_cases hj : j ∈ D
    · have hne : σ j ≠ τ j := by
        simpa [D] using hj
      simpa [D, hj, hne] using hp
    · have heq : σ j = τ j := by
        simpa [D] using hj
      simpa [hj, heq] using hp
  apply absorb_coordinate_sum (show 0 < 2 * m by omega) q r D
  · intro j hj
    exact (hpoint j).trans (by simp [hj])
  · intro j hj
    exact (hpoint j).trans (by simp [hj])

theorem coordinate_l1_stability {m : ℕ} (hn : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s t : SignPattern (by omega))
        (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
        ∑ j : Fin (2 * m),
            |coordinate (by omega) s θ v j - coordinate (by omega) t θ v j| ≤
          20 * ((Finset.univ.filter
            (fun j => patternSign s j ≠ patternSign t j)).card : ℝ) := by
  have hsmall := ExplicitHessianThresholdFixedSchur.domain_smallness hn
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties hn
  intro hm s t θ v hdom
  have hq := hprops hm s θ v hdom
  have hr := hprops hm t θ v hdom
  have hσ := patternSign_is_sign s
  have hτ := patternSign_is_sign t
  have hsml := hsmall (by omega) θ v (patternSign s) hdom hσ
  have htm := hsmall (by omega) θ v (patternSign t) hdom hτ
  exact coordinate_l1_of_properties hm θ v (patternSign s) (patternSign t)
    (coordinate (by omega) s θ v) (coordinate (by omega) t θ v)
    hσ hτ hq hr hsml.2.2 htm.2.2

theorem J_pointwise_stability {m : ℕ} (hn : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s t : SignPattern (by omega))
        (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
        ∀ j : Fin (2 * m),
          |J (coordinate (by omega) s θ v) j -
              J (coordinate (by omega) t θ v) j| ≤
            40 * ((Finset.univ.filter
              (fun i => patternSign s i ≠ patternSign t i)).card : ℝ) /
              (2 * m : ℝ) := by
  have hstable := coordinate_l1_stability hn
  intro hm s t θ v hdom j
  have hsum := hstable hm s t θ v hdom
  have hJ := J_pointwise_l1 (show 0 < 2 * m by omega)
    (coordinate (by omega) s θ v - coordinate (by omega) t θ v) j
  rw [J_sub] at hJ
  have hJ' :
      |J (coordinate (by omega) s θ v) j -
          J (coordinate (by omega) t θ v) j| ≤
        (2 : ℝ) / (2 * m : ℝ) *
          ∑ i : Fin (2 * m),
            |coordinate (by omega) s θ v i - coordinate (by omega) t θ v i| := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Pi.sub_apply] using hJ
  have hcoef : 0 ≤ (2 : ℝ) / (2 * m : ℝ) := by positivity
  calc
    |J (coordinate (by omega) s θ v) j -
        J (coordinate (by omega) t θ v) j| ≤
        (2 : ℝ) / (2 * m : ℝ) *
          ∑ i : Fin (2 * m),
            |coordinate (by omega) s θ v i - coordinate (by omega) t θ v i| := hJ'
    _ ≤ (2 : ℝ) / (2 * m : ℝ) *
        (20 * ((Finset.univ.filter
          (fun i => patternSign s i ≠ patternSign t i)).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum hcoef
    _ = 40 * ((Finset.univ.filter
          (fun i => patternSign s i ≠ patternSign t i)).card : ℝ) /
          (2 * m : ℝ) := by ring


theorem center_energy_stability {m : ℕ} (hn : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s t : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      pairEnergy (by omega)
        (center (coordinate (by omega) s θ v) v - center (coordinate (by omega) t θ v) v) ≤
        6400 * ((Finset.univ.filter
          (fun j => FiniteBox.patternSign s j ≠ FiniteBox.patternSign t j)).card : ℝ) /
            (2 * m : ℝ) := by
  classical
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties hn
  have hstable := coordinate_l1_stability hn
  intro hm s t θ v hdom
  have hs := hstable hm s t θ v hdom
  have hq := hprops hm s θ v hdom
  have hr := hprops hm t θ v hdom
  have he := center_difference_energy_le hm _ _ v hq.antiperiodic hr.antiperiodic
    hq.norm_le hr.norm_le
  apply he.trans
  calc
    _ ≤ 320 * (20 * ((Finset.univ.filter
        (fun j => FiniteBox.patternSign s j ≠ FiniteBox.patternSign t j)).card : ℝ)) /
          (2 * m : ℝ) := by gcongr
    _ = _ := by ring


theorem hamming_stability {m : ℕ} (hn : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s t : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      (∑ j, |coordinate (by omega) s θ v j - coordinate (by omega) t θ v j|) ≤
          40 * (hamming s t : ℝ) ∧
      (∀ j, |EdgeCoordinates.J (coordinate (by omega) s θ v) j -
        EdgeCoordinates.J (coordinate (by omega) t θ v) j| ≤
          80 * (hamming s t : ℝ) / (2 * m : ℝ)) ∧
      pairEnergy (by omega)
        (center (coordinate (by omega) s θ v) v - center (coordinate (by omega) t θ v) v) ≤
          12800 * (hamming s t : ℝ) / (2 * m : ℝ) := by
  classical
  have hq := coordinate_l1_stability hn
  have hJ := J_pointwise_stability hn
  have hC := center_energy_stability hn
  intro hm s t θ v hdom
  have hcard : ((Finset.univ.filter (fun j => patternSign s j ≠ patternSign t j)).card : ℝ) =
      2 * (hamming s t : ℝ) := by
    exact_mod_cast fullChangedSupport_card s t
  have hq' := hq hm s t θ v hdom
  have hJ' := hJ hm s t θ v hdom
  have hC' := hC hm s t θ v hdom
  rw [hcard] at hq' hC'
  refine ⟨by nlinarith, ?_, ?_⟩
  · intro j
    have h := hJ' j
    rw [hcard] at h
    convert h using 1; ring
  · convert hC' using 1; ring



theorem angleAverage_inv {m : ℕ} (hn : ExplicitHessianThreshold.orderThreshold ≤ 2 * m)
    (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain hm θ v) (j : Fin (2 * m)) :
    |CommonClosureEnergy.angleAverage (by omega) θ j| ≤ 1 / (2 * m : ℝ) := by
  have hm2 : 2 ≤ m := by have := ExplicitHessianThreshold.two_fifty_six_le_order hn; omega
  have h := (ExplicitComparisonScalars.inner_angle_sup hn hm2 θ v hdom).1 j
  apply h.trans
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)

theorem rotated_stability {m : ℕ} (hn : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s t : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → ∀ j,
      |rotatedP (by omega) v (coordinate (by omega) s θ v) j -
        rotatedP (by omega) v (coordinate (by omega) t θ v) j| ≤
        80 * (hamming s t : ℝ) / (2 * m : ℝ) ∧
      |rotatedS (by omega) θ v (coordinate (by omega) s θ v) j -
        rotatedS (by omega) θ v (coordinate (by omega) t θ v) j| ≤
        (80 * (hamming s t : ℝ) + 10) / (2 * m : ℝ) := by
  have hstab := hamming_stability hn
  have hb := angleAverage_inv hn
  have hprop := ExplicitHessianThresholdFixedSchur.coordinate_properties hn
  intro hm s t θ v hdom j
  have hp := (hstab hm s t θ v hdom).2.1 j
  have hp' : |rotatedP (by omega) v (coordinate (by omega) s θ v) j -
      rotatedP (by omega) v (coordinate (by omega) t θ v) j| ≤
      80 * (hamming s t : ℝ) / (2 * m : ℝ) := by
    simpa only [rotatedP, Pi.add_apply, add_sub_add_right_eq_sub] using hp
  refine ⟨hp', ?_⟩
  have hq (w : SignPattern (show 0 < m by omega)) : |coordinate (by omega) w θ v j| ≤ 5 := by
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (coordinate (by omega) w θ v) j).trans (hprop hm w θ v hdom).norm_le
  have hqdiff : |coordinate (by omega) s θ v j - coordinate (by omega) t θ v j| ≤ 10 :=
    (abs_sub _ _).trans (by linarith [hq s, hq t])
  have hbound := tangential_difference_le (angleAverage (by omega) θ j)
    (coordinate (by omega) s θ v j) (coordinate (by omega) t θ v j)
    (rotatedP (by omega) v (coordinate (by omega) s θ v) j)
    (rotatedP (by omega) v (coordinate (by omega) t θ v) j)
  apply hbound.trans
  calc
    _ ≤ 80 * (hamming s t : ℝ) / (2 * m : ℝ) + 10 * (1 / (2 * m : ℝ)) :=
      add_le_add hp' (mul_le_mul hqdiff (hb (by omega) θ v hdom j) (abs_nonneg _) (by norm_num))
    _ = _ := by ring



end
end StructuralNote.ExplicitComparisonStability

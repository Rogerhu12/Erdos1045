import StructuralNote.FixedSchurChart
import StructuralNote.FixedSchurContraction
import StructuralNote.FixedSchurHarmonicBounds

/-! Stability of the actual normalized Schur coordinates under a change of sign
pattern.  The estimate is stated on the full `Fin (2 * m)` grid; no half-period
counting or auxiliary Lipschitz hypothesis is used by the eventual conclusions.
-/

namespace StructuralNote.FixedSchurWordStability

open scoped BigOperators Topology

open Complex Filter
open Erdos1045 Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.FiniteFourierLift
open Erdos1045.EventualExact.SchurLift
open Erdos1045.EventualExact.SchurSpectrum
open CommonDomainClosure EdgeCoordinates FixedSchurData FixedSchurLinear
open FixedSchurChart FixedSchurContraction FixedSchurDomainSmallness
open FixedSchurEquations FixedSchurHarmonicBounds FixedSchurScalarRoot

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

theorem eventual_coordinate_l1_stability :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (s t : SignPattern (by omega))
        (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
        ∑ j : Fin (2 * m),
            |coordinate (by omega) s θ v j - coordinate (by omega) t θ v j| ≤
          20 * ((Finset.univ.filter
            (fun j => patternSign s j ≠ patternSign t j)).card : ℝ) := by
  filter_upwards [eventual_domain_smallness, eventual_coordinate_properties] with m hsmall hprops
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

theorem eventual_J_pointwise_stability :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (s t : SignPattern (by omega))
        (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
        ∀ j : Fin (2 * m),
          |J (coordinate (by omega) s θ v) j -
              J (coordinate (by omega) t θ v) j| ≤
            40 * ((Finset.univ.filter
              (fun i => patternSign s i ≠ patternSign t i)).card : ℝ) /
              (2 * m : ℝ) := by
  filter_upwards [eventual_coordinate_l1_stability] with m hstable
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

end
end StructuralNote.FixedSchurWordStability

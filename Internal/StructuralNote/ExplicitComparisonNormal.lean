import StructuralNote.ExplicitComparisonGeometry
import StructuralNote.ExplicitComparisonRotated
import StructuralNote.ExplicitComparisonStability
import StructuralNote.FixedSchurLocalQuadratic

/-! Explicit inner normal-error and quadratic comparison estimates. -/
namespace StructuralNote.ExplicitComparisonNormal
open scoped BigOperators Topology
open Complex Erdos1045 Erdos1045.EventualExact
open FiniteBox FourierMultiplier SchurSpectrum SchurLiftBounds
open CommonClosureEnergy CommonDomainClosure FixedSchurData FixedSchurChart
open FixedSchurNormalExpansion FixedSchurNormalInnerBound FixedSchurInnerAngles
open FixedSchurNormalScalarDifference FixedSchurNormalDifferenceSum FixedSchurRotatedStability
open FixedSchurDomainBounds FixedSchurDomainSmallness SolWordHamming SignPatternSymmetry
open FixedSchurNormalInnerEnergy FixedSchurNormalInnerDifference FixedSchurQuadraticExpansion
open FixedSchurWordExpansionBounds FixedSchurNearWordAngular FixedSchurLocalQuadratic
noncomputable section

def orderThreshold (B : ℝ) : ℕ := max ExplicitHessianThreshold.orderThreshold
  (max 2048 ⌈8 * normalSConstant B + 1⌉₊)

theorem thresholds {m : ℕ} {B : ℝ} (hN : orderThreshold B ≤ 2 * m) :
    ExplicitHessianThreshold.orderThreshold ≤ 2 * m ∧ 2048 ≤ 2 * m ∧
    8 * normalSConstant B + 1 ≤ (2 * m : ℝ) := by
  simp only [orderThreshold, max_le_iff] at hN
  refine ⟨hN.1, hN.2.1, ?_⟩
  exact (Nat.le_ceil _).trans (by exact_mod_cast hN.2.2)

theorem normal_error_meanSquare (B : ℝ) (hB : 0 ≤ B) {m : ℕ} (hN : orderThreshold B ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 →
      meanSquare (normalError (by omega) θ (coordinate (by omega) s θ v) (patternSign s)) ≤
        normalEnergyConstant B ^ 2 / (2 * m : ℝ) ^ 4 := by
  have hinner := ExplicitComparisonGeometry.normal_inner_local_bounds B hB (thresholds hN).1
  have hexp := ExplicitComparisonRotated.normalError_rotated_expansion (thresholds hN).1
  clear hN
  intro hm s θ v hdom henergy
  have hh := hinner hm s θ v hdom henergy
  have hA := angularSupConstant_nonneg hB
  have hP := normalPConstant_nonneg hB
  have hS := normalSConstant_nonneg hB
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hε := epsilon_pos (show 2 ≤ 2 * m by omega)
  have hsign (j : Fin (2 * m)) : |patternSign s j| = 1 := by
    rcases patternSign_is_sign s j with hs | hs <;> simp only [hs] <;> norm_num
  let f : Fin (2 * m) → ℝ := fun j => patternSign s j * angularErrorCoefficient (by omega) θ j
  let g : Fin (2 * m) → ℝ := fun j => rotatedP (by omega) v (coordinate (by omega) s θ v) j *
    Real.tan (angleAverage (by omega) θ j)
  let r : Fin (2 * m) → ℝ := fun j => patternSign s j * epsilon (2 * m) *
    rotatedS (by omega) θ v (coordinate (by omega) s θ v) j ^ 2 /
    (Real.cos (angleAverage (by omega) θ j) * (2 + rotatedH (by omega) θ v (coordinate (by omega) s θ v) j))
  have heq : normalError (by omega) θ (coordinate (by omega) s θ v) (patternSign s) =
      fun j => f j - g j - r j := by
    funext j
    exact hexp hm s θ v hdom j
  have hfpoint (j : Fin (2 * m)) : |f j| ≤ angularSupConstant B / (2 * m : ℝ) ^ 2 := by
    simpa only [f, abs_mul, hsign, one_mul] using hh.1 j
  have hf := meanSquare_le_of_bound (show 0 < 2 * m by omega) f
    (by positivity : 0 ≤ angularSupConstant B / (2 * m : ℝ) ^ 2) hfpoint
  have hgpoint (j : Fin (2 * m)) : |g j| ≤
      (2 * normalPConstant B) * |angleAverage (by omega) θ j| := by
    dsimp only [g]
    rw [abs_mul]
    exact (mul_le_mul (hh.2.1 j) (tan_abs_le (hh.2.2.2 j)) (abs_nonneg _) hP).trans_eq (by ring)
  have hg := meanSquare_domination g (angleAverage (by omega) θ) (by positivity) hgpoint
  have hb := angleAverage_meanSquare_le_of_joint_energy (by omega) θ v hB hdom henergy
  have hg' : meanSquare g ≤ 32 * normalPConstant B ^ 2 * B ^ 2 / (2 * m : ℝ) ^ 4 := by
    apply hg.trans
    exact (mul_le_mul_of_nonneg_left hb (sq_nonneg (2 * normalPConstant B))).trans_eq (by ring)
  have hrpoint (j : Fin (2 * m)) : |r j| ≤ 8 * normalSConstant B ^ 2 / (2 * m : ℝ) ^ 2 := by
    have hc := hh.2.2.2 j
    have hH : 0 ≤ rotatedH (by omega) θ v (coordinate (by omega) s θ v) j := Real.sqrt_nonneg _
    have hden : 1 ≤ Real.cos (angleAverage (by omega) θ j) *
        (2 + rotatedH (by omega) θ v (coordinate (by omega) s θ v) j) := by nlinarith
    have hdenpos := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hden
    have hsq : rotatedS (by omega) θ v (coordinate (by omega) s θ v) j ^ 2 ≤ normalSConstant B ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) (hh.2.2.1 j) 2
      simpa only [sq_abs] using h
    have hep : epsilon (2 * m) ≤ 8 / (2 * m : ℝ) ^ 2 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using epsilon_le (show 2 ≤ 2 * m by omega)
    dsimp only [r]
    rw [abs_div, abs_mul, abs_mul, hsign, one_mul, abs_of_pos hε, abs_of_nonneg (sq_nonneg _),
      abs_of_pos hdenpos]
    calc
      _ ≤ epsilon (2 * m) * rotatedS (by omega) θ v (coordinate (by omega) s θ v) j ^ 2 :=
        div_le_self (by positivity) hden
      _ ≤ (8 / (2 * m : ℝ) ^ 2) * normalSConstant B ^ 2 :=
        mul_le_mul hep hsq (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have hr := meanSquare_le_of_bound (show 0 < 2 * m by omega) r
    (by positivity : 0 ≤ 8 * normalSConstant B ^ 2 / (2 * m : ℝ) ^ 2) hrpoint
  rw [heq]
  apply (meanSquare_sub_sub_bound f g r).trans
  have hbound := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 3))
    (mul_le_mul_of_nonneg_left hg' (by norm_num : (0 : ℝ) ≤ 3)))
    (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 3))
  apply hbound.trans_eq
  unfold normalEnergyConstant
  rw [Real.sq_sqrt (by positivity)]
  ring


theorem normal_error_l1_difference (B : ℝ) (hB : 0 ≤ B) (s₀ : ℕ) {m : ℕ} (hN : orderThreshold B ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s t : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 → hamming s t ≤ s₀ →
      (∑ j, |normalError (by omega) θ (coordinate (by omega) s θ v) (patternSign s) j -
        normalError (by omega) θ (coordinate (by omega) t θ v) (patternSign t) j|) /
        (2 * m : ℝ) ≤ differenceConstant B (s₀ : ℝ) / (2 * m : ℝ) ^ 3 := by
  classical
  have hinner := ExplicitComparisonGeometry.normal_inner_local_bounds B hB (thresholds hN).1
  have hexp := ExplicitComparisonRotated.normalError_rotated_expansion (thresholds hN).1
  have hstable := ExplicitComparisonStability.rotated_stability (thresholds hN).1
  have hlarge := (thresholds hN).2.2
  clear hN
  intro hm s t θ v hdom henergy hham
  have hs := hinner hm s θ v hdom henergy
  have ht := hinner hm t θ v hdom henergy
  have hP := normalSConstant_nonneg hB
  have hA := angularSupConstant_nonneg hB
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hn1 : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hε := epsilon_pos (show 2 ≤ 2 * m by omega)
  have heps : epsilon (2 * m) ≤ 8 / (2 * m : ℝ) ^ 2 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using epsilon_le (show 2 ≤ 2 * m by omega)
  have heP : epsilon (2 * m) * normalSConstant B ≤ 1 := by
    apply (mul_le_mul_of_nonneg_right heps hP).trans
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hn)).2
    nlinarith
  have he_small (w : SignPattern (show 0 < m by omega))
      (hw : ∀ j, |rotatedS (by omega) θ v (coordinate (by omega) w θ v) j| ≤ normalSConstant B)
      (j : Fin (2 * m)) :
      |epsilon (2 * m) * rotatedS (by omega) θ v (coordinate (by omega) w θ v) j| ≤ 1 := by
    rw [abs_mul, abs_of_pos hε]
    exact (mul_le_mul_of_nonneg_left (hw j) hε.le).trans heP
  have hc (j : Fin (2 * m)) :
      |epsilon (2 * m) / Real.cos (angleAverage (by omega) θ j)| ≤ 16 / (2 * m : ℝ) ^ 2 := by
    have hcos := hs.2.2.2 j
    have hcospos := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hcos
    rw [abs_div, abs_of_pos hε, abs_of_pos hcospos]
    apply (div_le_iff₀ hcospos).2
    calc
      _ ≤ 8 / (2 * m : ℝ) ^ 2 := heps
      _ = (16 / (2 * m : ℝ) ^ 2) * (1 / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcos (by positivity)
  have hd : (hamming s t : ℝ) ≤ s₀ := by exact_mod_cast hham
  have hp (j : Fin (2 * m)) :
      |rotatedP (by omega) v (coordinate (by omega) s θ v) j -
        rotatedP (by omega) v (coordinate (by omega) t θ v) j| ≤ 80 * (s₀ : ℝ) / (2 * m : ℝ) :=
    (hstable hm s t θ v hdom j).1.trans (by gcongr)
  have hst (j : Fin (2 * m)) :
      |rotatedS (by omega) θ v (coordinate (by omega) s θ v) j -
        rotatedS (by omega) θ v (coordinate (by omega) t θ v) j| ≤
      (80 * (s₀ : ℝ) + 10) / (2 * m : ℝ) :=
    (hstable hm s t θ v hdom j).2.trans (by gcongr)
  have hsum := normalTerm_sum_difference (epsilon (2 * m)) hε.ne'
    (patternSign s) (patternSign t) (angularErrorCoefficient (by omega) θ)
    (rotatedP (by omega) v (coordinate (by omega) s θ v))
    (rotatedP (by omega) v (coordinate (by omega) t θ v)) (angleAverage (by omega) θ)
    (rotatedS (by omega) θ v (coordinate (by omega) s θ v))
    (rotatedS (by omega) θ v (coordinate (by omega) t θ v))
    (fun j => epsilon (2 * m) / Real.cos (angleAverage (by omega) θ j))
    (by positivity : 0 ≤ angularSupConstant B / (2 * m : ℝ) ^ 2)
    (by positivity : 0 ≤ 80 * (s₀ : ℝ) / (2 * m : ℝ)) hP
    (by positivity : 0 ≤ 16 / (2 * m : ℝ) ^ 2)
    (by positivity : 0 ≤ (80 * (s₀ : ℝ) + 10) / (2 * m : ℝ))
    (patternSign_is_sign s) (patternSign_is_sign t) hs.1 hp hc hs.2.2.1 ht.2.2.1
    (he_small s hs.2.2.1) (he_small t ht.2.2.1) hst
  have heq (w : SignPattern (show 0 < m by omega)) (j : Fin (2 * m)) :
      normalTerm (epsilon (2 * m)) (patternSign w j) (angularErrorCoefficient (by omega) θ j)
        (rotatedP (by omega) v (coordinate (by omega) w θ v) j) (angleAverage (by omega) θ j)
        (rotatedS (by omega) θ v (coordinate (by omega) w θ v) j)
        (epsilon (2 * m) / Real.cos (angleAverage (by omega) θ j)) =
      normalError (by omega) θ (coordinate (by omega) w θ v) (patternSign w) j := by
    simpa only [normalTerm_formula, rotatedH] using (hexp hm w θ v hdom j).symm
  simp only [heq, Nat.cast_mul, Nat.cast_ofNat] at hsum
  have hcard : ((Finset.univ.filter (fun j => patternSign s j ≠ patternSign t j)).card : ℝ) ≤
      2 * (s₀ : ℝ) := by
    have hh := fullChangedSupport_card s t
    change (Finset.univ.filter (fun j => patternSign s j ≠ patternSign t j)).card = 2 * hamming s t at hh
    rw [hh, Nat.cast_mul, Nat.cast_ofNat]
    gcongr
  have hsum' := hsum.trans (show _ ≤
      2 * (angularSupConstant B / (2 * m : ℝ) ^ 2) * (2 * (s₀ : ℝ)) +
      (80 * (s₀ : ℝ) / (2 * m : ℝ)) * (∑ j, |Real.tan (angleAverage (by omega) θ j)|) +
      (16 / (2 * m : ℝ) ^ 2) *
        (normalSConstant B * ((80 * (s₀ : ℝ) + 10) / (2 * m : ℝ)) * (2 * m : ℝ) +
          normalSConstant B ^ 2 * (2 * (s₀ : ℝ))) by gcongr)
  have htan := normalized_tan_angleAverage_le_of_joint_energy (by omega) θ v hB hdom henergy hs.2.2.2
  have hbound := scaled_budget hn (by positivity : 0 ≤ 80 * (s₀ : ℝ)) hsum' htan
  apply hbound.trans_eq
  unfold differenceConstant
  ring


theorem actual_quadratic_comparison (B : ℝ) (hB : 0 ≤ B) (s₀ : ℕ) {m : ℕ} (hN : orderThreshold B ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s t : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 → hamming s t ≤ s₀ →
      |(normalizedBoxEnergy (operator (2 * m)) (coordinate (by omega) s θ v) -
          normalizedBoxEnergy (operator (2 * m)) (coordinate (by omega) t θ v)) -
        (normalizedBoxEnergy (operator (2 * m)) (baseWord (patternSign s)) -
          normalizedBoxEnergy (operator (2 * m)) (baseWord (patternSign t))) -
        (∑ j, (signedPotential s j - signedPotential t j) * angleDifference (by omega) θ j) / 2| ≤
        quadraticConstant B (s₀ : ℝ) / (2 * m : ℝ) ^ 3 := by
  have he := normal_error_meanSquare B hB hN
  have herr := normal_error_l1_difference B hB s₀ hN
  have hmN : 1024 ≤ m := by have := (thresholds hN).2.1; omega
  clear hN
  intro hm s t θ v hdom henergy hham
  have hs := he hm s θ v hdom henergy
  have ht := he hm t θ v hdom henergy
  have hd := herr hm s t θ v hdom henergy hham
  have hangle := angleDifference_meanSquare_le_of_joint_energy (by omega) θ v hB hdom henergy
  have hh : (hamming s t : ℝ) ≤ s₀ := by exact_mod_cast hham
  have h := scalar_word_comparison (show 2048 ≤ 2 * m by omega) s t
    (angleDifference (by omega) θ)
    (normalError (by omega) θ (coordinate (by omega) s θ v) (patternSign s))
    (normalError (by omega) θ (coordinate (by omega) t θ v) (patternSign t))
    (normalEnergyConstant_nonneg B) (Nat.cast_nonneg s₀) hh hangle hs ht hd
  rw [normal_expansion_reconstruction, normal_expansion_reconstruction] at h
  apply h.trans_eq
  congr 1
  unfold quadraticConstant
  ring



end
end StructuralNote.ExplicitComparisonNormal

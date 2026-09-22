import StructuralNote.FixedSchurNormalInnerBound
import StructuralNote.FixedSchurNormalDifferenceSum
import StructuralNote.FixedSchurRotatedStability

/-! The actual normalized L1 normal-error difference at the fixed inner scale. -/

namespace StructuralNote.FixedSchurNormalInnerDifference

open Filter Complex Erdos1045.EventualExact FiniteBox SchurSpectrum
open CommonClosureEnergy CommonDomainClosure FixedSchurData FixedSchurChart
open FixedSchurNormalExpansion FixedSchurNormalInnerBound FixedSchurInnerAngles
open FixedSchurNormalScalarDifference FixedSchurNormalDifferenceSum FixedSchurRotatedStability
open FixedSchurDomainBounds SolWordHamming SignPatternSymmetry
open scoped BigOperators Topology

noncomputable section

def differenceConstant (B S : ℝ) : ℝ :=
  4 * angularSupConstant B * S + 480 * B * S +
    16 * normalSConstant B * (80 * S + 10) + 32 * normalSConstant B ^ 2 * S

theorem differenceConstant_nonneg {B S : ℝ} (hB : 0 ≤ B) (hS : 0 ≤ S) :
    0 ≤ differenceConstant B S := by
  unfold differenceConstant
  have hA := angularSupConstant_nonneg hB
  have hP := normalSConstant_nonneg hB
  positivity

theorem normalTerm_formula (ε σ a p b s : ℝ) :
    normalTerm ε σ a p b s (ε / Real.cos b) =
      σ * a - p * Real.tan b -
        σ * ε * s ^ 2 / (Real.cos b * (2 + Real.sqrt (4 - (ε * s) ^ 2))) := by
  unfold normalTerm rootCorrection rootHeight
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem eventual_normal_error_l1_difference (B : ℝ) (hB : 0 ≤ B) (s₀ : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s t : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 → hamming s t ≤ s₀ →
      (∑ j, |normalError (by omega) θ (coordinate (by omega) s θ v) (patternSign s) j -
        normalError (by omega) θ (coordinate (by omega) t θ v) (patternSign t) j|) /
        (2 * m : ℝ) ≤ differenceConstant B (s₀ : ℝ) / (2 * m : ℝ) ^ 3 := by
  classical
  have hreal : Tendsto (fun m : ℕ => (2 * m : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  filter_upwards [eventual_normal_inner_local_bounds B hB,
    eventual_normalError_rotated_expansion, eventual_rotated_stability,
    hreal.eventually_ge_atTop (8 * normalSConstant B + 1)] with m hinner hexp hstable hlarge
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

end
end StructuralNote.FixedSchurNormalInnerDifference

import StructuralNote.FixedSchurOperatorL1
import StructuralNote.FixedSchurDomainSmallness
import StructuralNote.SignPatternSymmetry

/-! Sparse word changes give order 1/n changes in the L2 Schur potential. -/

namespace StructuralNote.FixedSchurWordPotential

open Complex Filter Erdos1045.EventualExact
open FourierMultiplier FiniteBox SchurLiftBounds SchurOperatorBounds
open FixedSchurDomainSmallness FixedSchurOperatorL1 SignPatternSymmetry SolWordHamming
open scoped BigOperators Topology

noncomputable section

theorem baseWord_l1_difference {m : ℕ} {hm : 0 < m} (s t : SignPattern hm) :
    (∑ j, |baseWord (patternSign s) j - baseWord (patternSign t) j|) ≤
      16 * (hamming s t : ℝ) := by
  classical
  have hb (w : SignPattern hm) (j : Fin (2 * m)) : |baseWord (patternSign w) j| ≤ 4 := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (baseWord (patternSign w)) j).trans
      (baseWord_norm_le_four (show 2 ≤ 2 * m by omega) (patternSign_is_sign w))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    show |baseWord (patternSign s) j - baseWord (patternSign t) j| ≤
      if patternSign s j ≠ patternSign t j then (8 : ℝ) else 0 from by
      split_ifs with h
      · exact (abs_sub _ _).trans (by linarith [hb s j, hb t j])
      · have he : patternSign s j = patternSign t j := not_ne_iff.mp h
        simp only [baseWord, he, sub_self, abs_zero, le_refl])
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul] at hs
  have hc := fullChangedSupport_card s t
  change (Finset.univ.filter (fun j => patternSign s j ≠ patternSign t j)).card =
    2 * hamming s t at hc
  rw [hc, Nat.cast_mul, Nat.cast_ofNat] at hs
  nlinarith

theorem potential_meanSquare_difference {m : ℕ} (hm : 2048 ≤ 2 * m)
    (s t : SignPattern (by omega)) :
    meanSquare (operator (2 * m) (baseWord (patternSign s)) -
      operator (2 * m) (baseWord (patternSign t))) ≤
        128 * (hamming s t : ℝ) ^ 2 / (2 * m : ℝ) ^ 2 := by
  rw [← map_sub]
  have h := even_operator_l1_bound hm (baseWord (patternSign s) - baseWord (patternSign t))
  have hs := baseWord_l1_difference s t
  simp only [Pi.sub_apply] at h
  apply h.trans
  calc
    _ ≤ ((16 * (hamming s t : ℝ)) / (2 * m : ℝ)) ^ 2 / 2 := by gcongr
    _ = _ := by ring

theorem potential_l2_difference {m : ℕ} (hm : 2048 ≤ 2 * m)
    (s t : SignPattern (by omega)) :
    Real.sqrt (meanSquare (operator (2 * m) (baseWord (patternSign s)) -
      operator (2 * m) (baseWord (patternSign t)))) ≤
        12 * (hamming s t : ℝ) / (2 * m : ℝ) := by
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, (potential_meanSquare_difference hm s t).trans ?_⟩
  calc
    _ ≤ 144 * (hamming s t : ℝ) ^ 2 / (2 * m : ℝ) ^ 2 := by gcongr; norm_num
    _ = _ := by ring

theorem potential_abs_le_three {m : ℕ} (hm : 2048 ≤ 2 * m)
    (s : SignPattern (by omega)) (j : Fin (2 * m)) :
    |operator (2 * m) (baseWord (patternSign s)) j| ≤ 3 := by
  have hq := baseWord_norm_le_four (show 2 ≤ 2 * m by omega) (patternSign_is_sign s)
  have hms : meanSquare (baseWord (patternSign s)) ≤ 16 := by
    have h := meanSquare_le_of_bound (show 0 < 2 * m by omega) (baseWord (patternSign s))
      (by norm_num : (0 : ℝ) ≤ 4) (fun k => by
        simpa only [Real.norm_eq_abs] using (norm_le_pi_norm _ k).trans hq)
    norm_num at h
    exact h
  have h := operator_pointwise_sq_le (show 0 < 2 * m by omega) (baseWord (patternSign s)) j
  have hw := SchurWeights.weight_square_sum_lt_half hm
  have hprod := mul_le_mul hw.le hms (meanSquare_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hsq := h.trans hprod
  nlinarith [sq_abs (operator (2 * m) (baseWord (patternSign s)) j),
    abs_nonneg (operator (2 * m) (baseWord (patternSign s)) j)]

end
end StructuralNote.FixedSchurWordPotential

import StructuralNote.FixedSchurNormalInnerBound
import StructuralNote.FixedSchurNormalScalarDifference

/-! The L2 normal-error bound follows from actual local coefficients and
angle moments. The constant is explicit and independent of the word. -/

namespace StructuralNote.FixedSchurNormalInnerEnergy

open Filter Complex Erdos1045.EventualExact FiniteBox SchurSpectrum SchurLiftBounds
open CommonClosureEnergy CommonDomainClosure FixedSchurData FixedSchurChart
open FixedSchurNormalExpansion FixedSchurNormalInnerBound FixedSchurInnerAngles
open FixedSchurNormalScalarDifference FixedSchurDomainBounds
open scoped BigOperators Topology

noncomputable section

def normalEnergyConstant (B : ℝ) : ℝ :=
  Real.sqrt (3 * angularSupConstant B ^ 2 +
    96 * normalPConstant B ^ 2 * B ^ 2 + 192 * normalSConstant B ^ 4)

theorem normalEnergyConstant_nonneg (B : ℝ) : 0 ≤ normalEnergyConstant B := Real.sqrt_nonneg _

theorem meanSquare_sub_sub_bound {n : ℕ} (f g h : Fin n → ℝ) :
    meanSquare (fun j => f j - g j - h j) ≤
      3 * meanSquare f + 3 * meanSquare g + 3 * meanSquare h := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    show (f j - g j - h j) ^ 2 ≤ 3 * f j ^ 2 + 3 * g j ^ 2 + 3 * h j ^ 2 by
      nlinarith [sq_nonneg (f j + g j), sq_nonneg (f j + h j), sq_nonneg (g j - h j)])
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  exact (div_le_div_of_nonneg_right hs (Nat.cast_nonneg n : (0 : ℝ) ≤ n)).trans_eq (by
    unfold meanSquare
    ring)

theorem meanSquare_domination {n : ℕ} (f g : Fin n → ℝ) {K : ℝ} (_hK : 0 ≤ K)
    (h : ∀ j, |f j| ≤ K * |g j|) : meanSquare f ≤ K ^ 2 * meanSquare g := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    show f j ^ 2 ≤ K ^ 2 * g j ^ 2 from by
      have hj := pow_le_pow_left₀ (abs_nonneg _) (h j) 2
      simpa only [mul_pow, sq_abs] using hj)
  rw [← Finset.mul_sum] at hs
  exact (div_le_div_of_nonneg_right hs (Nat.cast_nonneg n : (0 : ℝ) ≤ n)).trans_eq (by
    unfold meanSquare
    ring)

theorem tan_abs_le {b : ℝ} (hc : (1 / 2 : ℝ) ≤ Real.cos b) :
    |Real.tan b| ≤ 2 * |b| := by
  have hc0 : 0 < Real.cos b := by linarith
  rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_pos hc0]
  apply (div_le_iff₀ hc0).2
  have hs := Real.abs_sin_le_abs (x := b)
  have hm := mul_le_mul_of_nonneg_left hc (abs_nonneg b)
  nlinarith only [hs, hm]

theorem eventual_normal_error_meanSquare (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ), InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 →
      meanSquare (normalError (by omega) θ (coordinate (by omega) s θ v) (patternSign s)) ≤
        normalEnergyConstant B ^ 2 / (2 * m : ℝ) ^ 4 := by
  filter_upwards [eventual_normal_inner_local_bounds B hB,
    eventual_normalError_rotated_expansion] with m hinner hexp
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

end
end StructuralNote.FixedSchurNormalInnerEnergy

import EventualExact.FiniteBoxMaximum
import StructuralNote.FixedDualClassificationArc

/-! A single wrong sign at a potential bounded away from zero costs order 1/n
for the actual finite Schur operator and its attained box maximum. -/

namespace StructuralNote.FixedDualClassificationFinite

open Real Set Erdos1045.EventualExact Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.FiniteBox
open FixedDualClassificationFunctional FixedDualClassificationArc
noncomputable section

theorem amplitude_ge_one {n : ℕ} (hn : 2 ≤ n) : 1 ≤ amplitude n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  have ht := le_tan (by positivity : 0 ≤ Real.pi / (2 * n))
    (by apply (div_lt_iff₀ (by positivity : 0 < (2 * n : ℝ))).mpr; nlinarith [pi_pos])
  have h := mul_le_mul_of_nonneg_left ht hnp.le
  have he : (n : ℝ) * (Real.pi / (2 * n)) = Real.pi / 2 := by field_simp
  rw [he] at h
  change 1 ≤ (n : ℝ) * tan (Real.pi / (2 * n))
  linarith [pi_gt_three]

def deficit {m : ℕ} (hm : 0 < m) (s : SignPattern hm) : ℝ :=
  B hm - normalizedBoxEnergy (operator (2 * m)) (vertex (amplitude (2 * m)) s)

def potential {m : ℕ} {hm : 0 < m} (s : SignPattern hm) : Fin (2 * m) → ℝ :=
  operator (2 * m) (vertex (amplitude (2 * m)) s)

theorem single_wrong_sign_cost {m : ℕ} (hm : 0 < m) (s : SignPattern hm)
    (j : Fin (2 * m)) (hwrong : patternSign s j * potential s j < 0) :
    2 * amplitude (2 * m) * |potential s j| ≤ (2 * m : ℕ) * deficit hm s := by
  classical
  have hA := amplitude_pos (n := 2 * m) (by omega)
  have hn : (0 : ℝ) < (2 * m : ℕ) := by positivity
  have hb := (rounding_defect hm s).1
  change badSignMass (patternSign s) (potential s) / (2 * m : ℕ) ≤
    deficit hm s / (2 * amplitude (2 * m)) at hb
  have hj := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.univ) => badSignWeight_nonneg (patternSign s i) (potential s i))
    (Finset.mem_univ j)
  change badSignWeight (patternSign s j) (potential s j) ≤ badSignMass (patternSign s) (potential s) at hj
  rw [badSignWeight, if_pos hwrong] at hj
  have h := (div_le_div_iff₀ hn (by positivity : 0 < 2 * amplitude (2 * m))).mp hb
  nlinarith

/-- At deficit C/n², every site with |potential|≥1/100 has the correct sign once n>50C. -/
theorem near_maximum_alignment {m : ℕ} (hm : 0 < m) (s : SignPattern hm) {C : ℝ}
    (hdef : deficit hm s ≤ C / (2 * m : ℕ) ^ 2) (hnC : 50 * C < (2 * m : ℕ))
    (j : Fin (2 * m)) (hg : (1 : ℝ) / 100 ≤ |potential s j|) :
    patternSign s j * potential s j = |potential s j| := by
  have hn : (0 : ℝ) < (2 * m : ℕ) := by positivity
  have hA := amplitude_ge_one (n := 2 * m) (by omega)
  have hc : (2 * m : ℕ) * deficit hm s ≤ C / (2 * m : ℕ) := by
    have h := (le_div_iff₀ (sq_pos_of_pos hn)).mp hdef
    apply (le_div_iff₀ hn).mpr
    nlinarith only [h]
  have hC : C / (2 * m : ℕ) < 1 / 50 := by
    apply (div_lt_iff₀ hn).mpr
    linarith
  have hnonneg : 0 ≤ patternSign s j * potential s j := by
    by_contra! hwrong
    have h := single_wrong_sign_cost hm s j hwrong
    have he : 2 * amplitude (2 * m) * |potential s j| ≥ (1 : ℝ) / 50 := by
      nlinarith [abs_nonneg (potential s j)]
    linarith
  have h := sign_mul_abs (patternSign_is_sign s j) (x := potential s j)
  rwa [abs_of_nonneg hnonneg] at h

theorem near_maximum_positive {m : ℕ} (hm : 0 < m) (s : SignPattern hm) {C : ℝ}
    (hdef : deficit hm s ≤ C / (2 * m : ℕ) ^ 2) (hnC : 50 * C < (2 * m : ℕ))
    (j : Fin (2 * m)) (hg : (1 : ℝ) / 100 < potential s j) : patternSign s j = 1 := by
  have hg0 : 0 < potential s j := by linarith
  have h := near_maximum_alignment hm s hdef hnC j (by rw [abs_of_pos hg0]; exact hg.le)
  rw [abs_of_pos hg0] at h
  rcases patternSign_is_sign s j with hs | hs
  · exact hs
  · rw [hs] at h
    nlinarith

theorem near_maximum_negative {m : ℕ} (hm : 0 < m) (s : SignPattern hm) {C : ℝ}
    (hdef : deficit hm s ≤ C / (2 * m : ℕ) ^ 2) (hnC : 50 * C < (2 * m : ℕ))
    (j : Fin (2 * m)) (hg : potential s j < -(1 / 100 : ℝ)) : patternSign s j = -1 := by
  have hg0 : potential s j < 0 := by linarith
  have h := near_maximum_alignment hm s hdef hnC j (by rw [abs_of_neg hg0]; linarith)
  rw [abs_of_neg hg0] at h
  rcases patternSign_is_sign s j with hs | hs
  · rw [hs] at h
    nlinarith
  · exact hs

/-- The exact remaining interface is a pointwise comparison of the actual finite and integral potentials. -/
theorem positive_arc_site {m : ℕ} (hm : 0 < m) (s : SignPattern hm) {C : ℝ}
    (hdef : deficit hm s ≤ C / (2 * m : ℕ) ^ 2) (hnC : 50 * C < (2 * m : ℕ))
    (j : Fin (2 * m)) {f : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ u ∈ Icc 0 Real.pi, |f u| ≤ Real.pi / 2) {r x : ℝ}
    (hr : (24 : ℝ) / 25 ≤ r) (hx : x ∈ Icc 0 (Real.pi / 2 - 3 / 8))
    (hc : cosineMoment f = r * cos x) (hs : |sineMoment f| = r * sin x)
    (hcompare : |potential s j - kernelPotential f| ≤ 1 / 100) : patternSign s j = 1 := by
  apply near_maximum_positive hm s hdef hnC j
  have h := profile_positive_arc hf hbox hr hx hc hs
  have he := abs_le.mp hcompare
  linarith [he.1]

end
end StructuralNote.FixedDualClassificationFinite

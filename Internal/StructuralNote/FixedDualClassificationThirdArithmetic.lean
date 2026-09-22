import StructuralNote.FixedDualClassificationThirdCoarse

/-! Exact arithmetic for the fine third-harmonic test. Positivity of the
degree-six certificate is proved by a rational Bernstein expansion. -/

namespace StructuralNote.FixedDualClassificationThirdArithmetic

open Real
noncomputable section

def upperEnergy (B δ b : ℝ) : ℝ :=
  B / 10 + (3 / 20) * (1 - δ) ^ 2 - b ^ 2 / 120 + (11 / 30) * b * δ + (11 / 30) * δ ^ 2

def finePolynomial (x : ℝ) : ℝ :=
  -(781 / 98000) + (37 / 120) * x ^ 2 - (7 / 15) * x ^ 3 -
    (71 / 180) * x ^ 4 + (31 / 90) * x ^ 5 - (31 / 540) * x ^ 6

theorem finePolynomial_bernstein (x : ℝ) : finePolynomial x =
    (548059375 / 987614208) * (11 / 25 - x) ^ 6 +
    (12404711875 / 164602368) * (x - 1 / 5) * (11 / 25 - x) ^ 5 +
    (117322386875 / 329204736) * (x - 1 / 5) ^ 2 * (11 / 25 - x) ^ 4 +
    (156962627375 / 246903552) * (x - 1 / 5) ^ 3 * (11 / 25 - x) ^ 3 +
    (168787498475 / 329204736) * (x - 1 / 5) ^ 4 * (11 / 25 - x) ^ 2 +
    (28220505379 / 164602368) * (x - 1 / 5) ^ 5 * (11 / 25 - x) +
    (63337006139 / 4938071040) * (x - 1 / 5) ^ 6 := by
  unfold finePolynomial
  ring

theorem finePolynomial_pos {x : ℝ} (hx : x ∈ Set.Icc (1 / 5) (11 / 25)) :
    0 < finePolynomial x := by
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h]
    norm_num [finePolynomial]
  · rw [finePolynomial_bernstein]
    have hleft : 0 < x - 1 / 5 := sub_pos.mpr h
    have hright : 0 ≤ 11 / 25 - x := sub_nonneg.mpr hx.2
    positivity

theorem finePolynomial_identity (x : ℝ) :
    (531 : ℝ) / 2000 - upperEnergy (121 / 98) (x ^ 2 - x ^ 3 / 3) x = finePolynomial x := by
  unfold upperEnergy finePolynomial
  ring

theorem upperEnergy_monotone_b {B δ b x : ℝ} (hδ : (1 : ℝ) / 25 ≤ δ)
    (hbx : b ≤ x) (hx : x ≤ 11 / 25) :
    upperEnergy B δ b ≤ upperEnergy B δ x := by
  have hh : 0 ≤ (11 / 30) * δ - (x + b) / 120 := by linarith
  have h := mul_nonneg (sub_nonneg.mpr hbx) hh
  unfold upperEnergy
  nlinarith

theorem fine_scalar_test {B δ b x : ℝ} (hB : B ≤ 121 / 98)
    (hδ : (1 : ℝ) / 25 ≤ δ) (hbx : b ≤ x)
    (hx : x ∈ Set.Icc (1 / 5) (11 / 25)) (he : δ = x ^ 2 - x ^ 3 / 3) :
    upperEnergy B δ b < 531 / 2000 := by
  have hm := upperEnergy_monotone_b (B := B) hδ hbx hx.2
  have hB' : upperEnergy B δ x ≤ upperEnergy (121 / 98) δ x := by
    unfold upperEnergy
    linarith
  have hpoly := finePolynomial_pos hx
  rw [← finePolynomial_identity] at hpoly
  rw [← he] at hpoly
  linarith

def cubicDefect (x : ℝ) : ℝ := x ^ 2 - x ^ 3 / 3

theorem cubicDefect_strictMono : StrictMonoOn cubicDefect (Set.Icc 0 1) := by
  intro a ha b hb hab
  have ha1 : a ^ 2 ≤ a := by nlinarith [ha.1, ha.2]
  have hb1 : b ^ 2 ≤ b := by nlinarith [hb.1, hb.2]
  have hab1 : a * b ≤ a := mul_le_of_le_one_right ha.1 hb.2
  have hb0 : 0 < b := lt_of_le_of_lt ha.1 hab
  have hp : 0 < a + b - (a ^ 2 + a * b + b ^ 2) / 3 := by linarith [ha.1]
  have h := mul_pos (sub_pos.mpr hab) hp
  unfold cubicDefect
  nlinarith

theorem cubicDefect_inverse {δ : ℝ} (hδ : δ ∈ Set.Icc (1 / 25) (4 / 25)) :
    ∃ x ∈ Set.Icc (1 / 5 : ℝ) (11 / 25), cubicDefect x = δ := by
  have hc : Continuous cubicDefect := by unfold cubicDefect; fun_prop
  apply intermediate_value_Icc (by norm_num : (1 / 5 : ℝ) ≤ 11 / 25) hc.continuousOn
  constructor <;> norm_num [cubicDefect] <;> linarith [hδ.1, hδ.2]

/-- The scalar fine interval closes once the actual coefficient coupling and energy bound are available. -/
theorem fine_test_from_cubic {B δ b : ℝ} (hB : B ≤ 121 / 98)
    (hδ : δ ∈ Set.Icc (1 / 25) (4 / 25)) (hb : b ∈ Set.Icc 0 1)
    (hc : cubicDefect b ≤ δ) : upperEnergy B δ b < 531 / 2000 := by
  obtain ⟨x, hx, he⟩ := cubicDefect_inverse hδ
  have hx01 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hbx : b ≤ x := by
    by_contra! h
    have hlt := cubicDefect_strictMono hx01 hb h
    linarith
  exact fine_scalar_test hB hδ.1 hbx hx he.symm

end
end StructuralNote.FixedDualClassificationThirdArithmetic

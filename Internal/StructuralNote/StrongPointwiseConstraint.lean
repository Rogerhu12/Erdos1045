import StructuralNote.StrongBudgetConsequences

/-! The unweighted crossing estimate at the strong-budget scale. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.StrongPointwiseConstraint

open Erdos1045 Erdos1045.EventualExact Complex GapRigidity
open SignedCrossingPressure SignedPressureRemainder

theorem unweighted_constraint {a η b₀ b₁ ρ : ℝ} {c₀ c₁ : ℂ}
    (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) (hη : |η| ≤ 1) (hρ : ρ ≤ 1)
    (hc₀ : ‖c₀‖ ≤ ρ) (hc₁ : ‖c₁‖ ≤ ρ)
    (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁) (hb : b₀ + b₁ ≤ 1 / 2)
    (hφ : |a + η / 2| ≤ 1 / 2)
    (hp : ‖radialSum a η b₀ b₁ + centerStep η c₀ c₁‖ ≤ 2)
    (hm : ‖radialSum a η b₀ b₁ - centerStep η c₀ c₁‖ ≤ 2) :
    |(c₁ - c₀).re| ≤ 2 * (1 - Real.cos a) +
      4 * (b₀ + b₁) + a * |η| + ρ * |η| + 2 * η ^ 2 + 9 * a ^ 4 := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg c₀).trans hc₀
  have hY : |(c₁ + c₀).im| ≤ 2 * ρ :=
    (abs_im_le_norm _).trans ((norm_add_le _ _).trans (by linarith))
  have hangular : |(c₁ + c₀).im * η / 2| ≤ ρ * |η| := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hh := mul_le_mul_of_nonneg_right hY (abs_nonneg η)
    linarith
  have hrad := mul_le_mul_of_nonneg_left (le_abs_self η) ha0
  have herr (g : ℝ) (hg : |g| ≤ 1) : remainder a η b₀ b₁ g c₀ c₁ ≤
      2 * η ^ 2 + 9 * a ^ 4 + 3 * (b₀ + b₁) := by
    have hh := remainder_le ha0 ha hη hρ hc₀ hc₁ (add_nonneg hb₀ hb₁) hb hg
    have hx := mul_le_mul_of_nonneg_right (show 1 / 2 + 2 * ρ ≤ (3 : ℝ) by linarith)
      (add_nonneg hb₀ hb₁)
    linarith only [hh, hx]
  have hpos := pointwise_signed_constraint hb₀ hb₁ hb hφ c₀ c₁ hp hm 1
  have hneg := pointwise_signed_constraint hb₀ hb₁ hb hφ c₀ c₁ hp hm (-1)
  have hepos := herr 1 (by norm_num)
  have heneg := herr (-1) (by norm_num)
  norm_num only [abs_one, abs_neg, one_mul, mul_one, neg_mul] at hpos hneg
  rcases abs_le.mp hangular with ⟨hlo, hup⟩
  apply abs_le.mpr
  constructor <;> linarith only [hpos, hneg, hepos, heneg, hlo, hup, hrad]

def errorConstant (B T C : ℝ) : ℝ := 8 * B + Real.pi * T + C * T + 2 * T ^ 2 + 9 * Real.pi ^ 4

theorem error_scale {n B T C b η ρ : ℝ} (hn : 1 ≤ n)
    (hC : 0 ≤ C)
    (hb : b ≤ 2 * B / n ^ 3) (hη : |η| ≤ T / n ^ 2) (hρ : ρ ≤ C / n) :
    4 * b + (Real.pi / n) * |η| + ρ * |η| + 2 * η ^ 2 + 9 * (Real.pi / n) ^ 4 ≤
      errorConstant B T C / n ^ 3 := by
  have hn0 : 0 < n := by linarith
  have hη2 : η ^ 2 ≤ T ^ 2 / n ^ 4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg η) hη 2
    simpa only [sq_abs, div_pow, ← pow_mul] using hh
  have htwo : 2 * η ^ 2 ≤ 2 * T ^ 2 / n ^ 3 := by
    have hh : n ^ 3 ≤ n ^ 4 := by nlinarith [mul_nonneg (pow_nonneg hn0.le 3) (sub_nonneg.mpr hn)]
    have hdiv := div_le_div_of_nonneg_left (sq_nonneg T) (pow_pos hn0 3) hh
    simp only [div_eq_mul_inv] at hη2 hdiv ⊢
    linarith only [hη2, hdiv]
  have hfour : 9 * (Real.pi / n) ^ 4 ≤ 9 * Real.pi ^ 4 / n ^ 3 := by
    rw [div_pow]
    have hh : n ^ 3 ≤ n ^ 4 := by nlinarith [mul_nonneg (pow_nonneg hn0.le 3) (sub_nonneg.mpr hn)]
    have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ Real.pi ^ 4) (pow_pos hn0 3) hh
    simp only [div_eq_mul_inv] at hdiv ⊢
    linarith only [hdiv]
  have ha := mul_le_mul_of_nonneg_left hη (show 0 ≤ Real.pi / n by positivity)
  have hc := mul_le_mul hρ hη (abs_nonneg η) (by positivity : 0 ≤ C / n)
  have hbase : 4 * b + (Real.pi / n) * |η| + ρ * |η| + 2 * η ^ 2 + 9 * (Real.pi / n) ^ 4 ≤
      4 * (2 * B / n ^ 3) + (Real.pi / n) * (T / n ^ 2) + (C / n) * (T / n ^ 2) +
        2 * T ^ 2 / n ^ 3 + 9 * Real.pi ^ 4 / n ^ 3 := by linarith only [hb, ha, hc, htwo, hfour]
  calc
    _ ≤ _ := hbase
    _ = _ := by unfold errorConstant; ring

theorem normal_bound {n : ℕ} (hn : 16 ≤ n) {B T C b₀ b₁ η : ℝ} {c₀ c₁ : ℂ}
    (hB : 0 ≤ B) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hsmallB : 2 * B / (n : ℝ) ^ 3 ≤ 1 / 2)
    (hsmallT : T / (n : ℝ) ^ 2 ≤ 1 / 2) (hsmallC : C / n ≤ 1)
    (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁)
    (hb : b₀ + b₁ ≤ 2 * B / (n : ℝ) ^ 3) (hη : |η| ≤ T / (n : ℝ) ^ 2)
    (hc₀ : ‖c₀‖ ≤ C / n) (hc₁ : ‖c₁‖ ≤ C / n)
    (hp : ‖radialSum (Real.pi / n) η b₀ b₁ + centerStep η c₀ c₁‖ ≤ 2)
    (hm : ‖radialSum (Real.pi / n) η b₀ b₁ - centerStep η c₀ c₁‖ ≤ 2) :
    |normalComponent n (Real.pi / n) c₀ c₁| ≤
      FiniteBox.amplitude n + errorConstant B T C / (4 * n) := by
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ha : Real.pi / n ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ hn0).2
    nlinarith [Real.pi_lt_four]
  have hφ : |Real.pi / n + η / 2| ≤ 1 / 2 := by
    calc
      _ ≤ |Real.pi / n| + |η / 2| := abs_add_le _ _
      _ = Real.pi / n + |η| / 2 := by rw [abs_of_pos (by positivity), abs_div]; norm_num
      _ ≤ _ := by linarith
  have hu := unweighted_constraint (by positivity) ha (hη.trans (by linarith)) hsmallC
    hc₀ hc₁ hb₀ hb₁ (hb.trans hsmallB) hφ hp hm
  have he := error_scale (show (1 : ℝ) ≤ n by linarith) hC hb hη le_rfl
  have hs := reciprocal_sine_le (show 2 ≤ n by omega)
  have hfactor : (n : ℝ) / (2 * Real.sin (Real.pi / n)) ≤ (n : ℝ) ^ 2 / 4 := by
    have hh := mul_le_mul_of_nonneg_left hs.2 hn0.le
    simpa only [div_eq_mul_inv, one_mul, pow_two, mul_assoc] using hh
  have hspos : 0 < Real.sin (Real.pi / n) := hs.1
  have hK : 0 ≤ errorConstant B T C := by unfold errorConstant; positivity
  have hh := mul_le_mul_of_nonneg_left (show |(c₁ - c₀).re| ≤
      2 * (1 - Real.cos (Real.pi / n)) + errorConstant B T C / (n : ℝ) ^ 3 by linarith only [hu, he])
    (show 0 ≤ (n : ℝ) / (2 * Real.sin (Real.pi / n)) by positivity)
  rw [normalComponent, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) / (2 * Real.sin (Real.pi / n)))]
  have hmain : (n : ℝ) / (2 * Real.sin (Real.pi / n)) * (2 * (1 - Real.cos (Real.pi / n))) =
      FiniteBox.amplitude n := by rw [amplitude_identity (show 2 ≤ n by omega)]; ring
  have herror := mul_le_mul_of_nonneg_right hfactor (div_nonneg hK (pow_nonneg hn0.le 3))
  have hcancel : (n : ℝ) ^ 2 / 4 * (errorConstant B T C / (n : ℝ) ^ 3) =
      errorConstant B T C / (4 * n) := by field_simp
  rw [hcancel] at herror
  rw [mul_add, hmain] at hh
  linarith only [hh, herror]

end StructuralNote.StrongPointwiseConstraint

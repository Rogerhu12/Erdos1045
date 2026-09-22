import StructuralNote.ExplicitThresholdScalar

/-! Symbolic threshold functions. No evaluation of their natural-number values is needed. -/

namespace Erdos1045.ExplicitThreshold

noncomputable section

/-- A canonical positive integral upper bound for an arbitrary real coefficient. -/
def majorant (C : ℝ) : ℕ := ⌈|C|⌉₊ + 1

theorem majorant_pos (C : ℝ) : 0 < majorant C := by
  unfold majorant
  omega

theorem abs_lt_majorant (C : ℝ) : |C| < (majorant C : ℝ) := by
  have hh := Nat.le_ceil |C|
  simp only [majorant, Nat.cast_add, Nat.cast_one]
  linarith only [hh]

theorem le_majorant (C : ℝ) : C ≤ (majorant C : ℝ) :=
  (le_abs_self C).trans (abs_lt_majorant C).le

/-- Sufficient order for every logarithmic monomial of degree at most ten
and decay exponent at least one quarter. -/
def decayThreshold (C ε : ℝ) : ℕ :=
  max 2 ((2 * majorant C * 81 ^ 10 * majorant (1 / ε)) ^ 8)

/-- Sufficient order for a strictly positive logarithmic margin. -/
def growthThreshold (T : ℝ) : ℕ := 2 ^ (2 * majorant T + 1)

theorem logBudget_le_small_power {x : ℝ} (hx : 1 ≤ x) :
    logBudget x ≤ 81 * x ^ (1 / 80 : ℝ) := by
  have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 1).trans hx
  have hl := Real.log_le_rpow_div hx0 (by norm_num : (0 : ℝ) < 1 / 80)
  have hp := Real.one_le_rpow hx (by norm_num : (0 : ℝ) ≤ 1 / 80)
  unfold logBudget
  norm_num only [div_eq_mul_inv, inv_div, one_mul] at hl
  linarith only [hl, hp]

theorem logBudget_tenth_bound {x : ℝ} (hx : 1 ≤ x) :
    logBudget x ^ 10 * x ^ (-(1 / 4 : ℝ)) ≤
      81 ^ 10 * x ^ (-(1 / 8 : ℝ)) := by
  have hx0 : 0 < x := (by norm_num : (0 : ℝ) < 1).trans_le hx
  have hH0 : 0 ≤ logBudget x := by
    dsimp [logBudget]
    linarith only [Real.log_nonneg hx]
  have hb := pow_le_pow_left₀ hH0 (logBudget_le_small_power hx) 10
  have hm := mul_le_mul_of_nonneg_right hb
    (Real.rpow_nonneg hx0.le (-(1 / 4 : ℝ)))
  rw [mul_pow, ← Real.rpow_natCast (x ^ (1 / 80 : ℝ)) 10,
    ← Real.rpow_mul hx0.le, mul_assoc, ← Real.rpow_add hx0] at hm
  convert hm using 1
  congr 2
  norm_num

theorem decayThreshold_two_le (C ε : ℝ) : 2 ≤ decayThreshold C ε := le_max_left _ _

theorem decay_small {n : ℕ} {C ε : ℝ} (hε : 0 < ε)
    (hn : decayThreshold C ε ≤ n) :
    C * logBudget (n : ℝ) ^ 10 * (n : ℝ) ^ (-(1 / 4 : ℝ)) < ε := by
  have hn2 : 2 ≤ n := (decayThreshold_two_le C ε).trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let A : ℝ := (majorant C : ℝ)
  let B : ℝ := (majorant (1 / ε) : ℝ)
  let R : ℝ := 2 * A * 81 ^ 10 * B
  have hA : 0 < A := by dsimp [A]; exact_mod_cast majorant_pos C
  have hB : 0 < B := by dsimp [B]; exact_mod_cast majorant_pos (1 / ε)
  have hR : 0 < R := by dsimp [R]; positivity
  have hsize : R ^ 8 ≤ (n : ℝ) := by
    have hh := (le_max_right 2 ((2 * majorant C * 81 ^ 10 * majorant (1 / ε)) ^ 8)).trans hn
    dsimp [R, A, B]
    exact_mod_cast hh
  have hroot : R ≤ (n : ℝ) ^ (1 / 8 : ℝ) := by
    have hh := Real.rpow_le_rpow (pow_nonneg hR.le 8) hsize (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [← Real.rpow_natCast R 8, ← Real.rpow_mul hR.le] at hh
    norm_num only [Nat.cast_ofNat, mul_one_div_cancel, Real.rpow_one] at hh
    exact hh
  have hCB : 1 / ε ≤ B := le_majorant (1 / ε)
  have hBeps : 1 ≤ B * ε := (div_le_iff₀ hε).mp hCB
  have hcoef : A * 81 ^ 10 ≤ (ε / 2) * R := by
    have hm := mul_le_mul_of_nonneg_left hBeps (show 0 ≤ A * 81 ^ 10 by positivity)
    dsimp [R]
    nlinarith only [hm]
  have hmain : A * 81 ^ 10 * (n : ℝ) ^ (-(1 / 8 : ℝ)) ≤ ε / 2 := by
    rw [Real.rpow_neg hn0.le]
    change A * 81 ^ 10 / (n : ℝ) ^ (1 / 8 : ℝ) ≤ ε / 2
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hn0 _)).mpr
    exact hcoef.trans (mul_le_mul_of_nonneg_left hroot (by positivity))
  have hH0 : 0 ≤ logBudget (n : ℝ) := by
    dsimp [logBudget]
    linarith only [Real.log_nonneg hn1]
  have hC : C ≤ A := le_majorant C
  calc
    _ ≤ A * (logBudget (n : ℝ) ^ 10 * (n : ℝ) ^ (-(1 / 4 : ℝ))) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC (pow_nonneg hH0 _)) (by positivity)
    _ ≤ A * (81 ^ 10 * (n : ℝ) ^ (-(1 / 8 : ℝ))) :=
      mul_le_mul_of_nonneg_left (logBudget_tenth_bound hn1) hA.le
    _ = A * 81 ^ 10 * (n : ℝ) ^ (-(1 / 8 : ℝ)) := by ring
    _ ≤ ε / 2 := hmain
    _ < ε := by linarith only [hε]

theorem growth_log_gt {n : ℕ} {T : ℝ} (hn : growthThreshold T ≤ n) :
    T < Real.log (n : ℝ) := by
  have hg : (0 : ℝ) < (2 : ℝ) ^ (2 * majorant T + 1) := by positivity
  have hcast : (2 : ℝ) ^ (2 * majorant T + 1) ≤ n := by
    exact_mod_cast hn
  have hl := Real.log_le_log hg hcast
  rw [Real.log_pow] at hl
  have hM : 0 ≤ (majorant T : ℝ) := Nat.cast_nonneg _
  have hm := abs_lt_majorant T
  have htwo := log_two_lower
  push_cast at hl
  nlinarith only [hl, hM, hm, le_abs_self T, htwo]

/-- The full family of smaller logarithmic monomials shares a symbolic threshold. -/
theorem monomial_small {n j : ℕ} {C ε α : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hj : j ≤ 10) (hα : (1 / 4 : ℝ) ≤ α) (hn : decayThreshold C ε ≤ n) :
    C * logBudget (n : ℝ) ^ j * (n : ℝ) ^ (-α) < ε := by
  have hn2 : 2 ≤ n := (decayThreshold_two_le C ε).trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hH : 1 ≤ logBudget (n : ℝ) := by
    dsimp [logBudget]
    linarith only [Real.log_nonneg hn1]
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH hj) hC
  have hr := Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hα)
  have hb := mul_le_mul hp hr (by positivity)
    (mul_nonneg hC (pow_nonneg (by linarith only [hH]) _))
  exact hb.trans_lt (decay_small hε hn)

def inverseSqrtThreshold (C ε : ℝ) : ℕ := max 2 (⌈(C / ε) ^ 2⌉₊ + 1)

theorem inverse_sqrt_small {n : ℕ} {C ε : ℝ} (hε : 0 < ε)
    (hn : inverseSqrtThreshold C ε ≤ n) : C / Real.sqrt (n : ℝ) < ε := by
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc := Nat.le_ceil ((C / ε) ^ 2)
  have hs : (⌈(C / ε) ^ 2⌉₊ : ℝ) + 1 ≤ n := by
    exact_mod_cast (le_max_right 2 (⌈(C / ε) ^ 2⌉₊ + 1)).trans hn
  have hsq : (C / ε) ^ 2 < (n : ℝ) := by linarith only [hc, hs]
  have hr := Real.sqrt_lt_sqrt (sq_nonneg (C / ε)) hsq
  rw [Real.sqrt_sq_eq_abs] at hr
  have hratio := (le_abs_self (C / ε)).trans_lt hr
  apply (div_lt_iff₀ (Real.sqrt_pos.mpr hn0)).mpr
  have hh := (div_lt_iff₀ hε).mp hratio
  linarith only [hh]

theorem comparison_error_small {n : ℕ} {C ε : ℝ} (hε : 0 < ε)
    (hn : inverseSqrtThreshold C ε ≤ n) :
    C / ((n : ℝ) ^ 2 * Real.sqrt n) < ε / (n : ℝ) ^ 2 := by
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh := div_lt_div_of_pos_right (inverse_sqrt_small hε hn) (sq_pos_of_pos hp)
  calc
    C / ((n : ℝ) ^ 2 * Real.sqrt n) = (C / Real.sqrt n) / (n : ℝ) ^ 2 := by ring
    _ < ε / (n : ℝ) ^ 2 := hh

theorem sqrt_monomial_small {n j : ℕ} {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hj : j ≤ 10) (hn : decayThreshold C ε ≤ n) :
    C * logBudget (n : ℝ) ^ j / Real.sqrt n < ε := by
  rw [div_eq_mul_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg n)]
  exact monomial_small hC hε hj (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) hn

def linearGrowthThreshold (A B D : ℝ) : ℕ :=
  growthThreshold (max (4 * |D| * |A| + 4) (32 * (|D| * |B|) ^ 2 + 4))

/-- A symbolic logarithmic bound absorbs a square-root logarithmic loss. -/
theorem log_dominates_sqrt {n : ℕ} {A B D : ℝ} (hD : 0 < D)
    (hn : linearGrowthThreshold A B D ≤ n) :
    A + B * Real.sqrt (1 + Real.log (n : ℝ)) < Real.log (n : ℝ) / D := by
  have hl := growth_log_gt hn
  change max (4 * |D| * |A| + 4) (32 * (|D| * |B|) ^ 2 + 4) < Real.log (n : ℝ) at hl
  have h₁ := lt_of_le_of_lt (le_max_left _ _) hl
  have h₂ := lt_of_le_of_lt (le_max_right _ _) hl
  rw [abs_of_pos hD] at h₁ h₂
  have ht : 4 < Real.log (n : ℝ) := by
    nlinarith only [h₁, abs_nonneg A, hD]
  have hs := Real.sq_sqrt (show 0 ≤ 1 + Real.log (n : ℝ) by linarith only [ht])
  have hs0 := Real.sqrt_nonneg (1 + Real.log (n : ℝ))
  have hB := mul_le_mul_of_nonneg_right (le_abs_self B) hs0
  have hDb : 0 ≤ D * |B| := mul_nonneg hD.le (abs_nonneg B)
  have hroot : D * |B| * Real.sqrt (1 + Real.log (n : ℝ)) < Real.log (n : ℝ) / 2 := by
    have hm := mul_lt_mul_of_pos_right h₂ (show 0 < 1 + Real.log (n : ℝ) by linarith only [ht])
    nlinarith only [hm, hs, hs0, hDb, ht,
      sq_nonneg (Real.log (n : ℝ)), sq_nonneg (D * |B|)]
  have hA := le_abs_self A
  have hDA := mul_le_mul_of_nonneg_left hA hD.le
  have hDB := mul_le_mul_of_nonneg_left hB hD.le
  apply (lt_div_iff₀ hD).mpr
  nlinarith only [h₁, hroot, hDA, hDB, ht]

def inverseThreshold (C ε : ℝ) : ℕ := max 2 (⌈C / ε⌉₊ + 1)

theorem inverse_small {n : ℕ} {C ε : ℝ} (hε : 0 < ε)
    (hn : inverseThreshold C ε ≤ n) : C / (n : ℝ) < ε := by
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc := Nat.le_ceil (C / ε)
  have hs : (⌈C / ε⌉₊ : ℝ) + 1 ≤ n := by
    exact_mod_cast (le_max_right 2 (⌈C / ε⌉₊ + 1)).trans hn
  have hr : C / ε < (n : ℝ) := by linarith only [hc, hs]
  have hh := (div_lt_iff₀ hε).mp hr
  apply (div_lt_iff₀ hn0).mpr
  linarith only [hh]

end
end Erdos1045.ExplicitThreshold

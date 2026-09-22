import EventualExact.BoxLensLift
import EventualExact.QuadraticStability

/-! A uniform error bound for the actual logarithmic objective on the whole box. -/

noncomputable section

open scoped BigOperators

namespace Erdos1045.EventualExact.WholeBoxObjective

open Complex FourierMultiplier FiniteFourierLift SchurLift SchurLiftBounds SchurSpectrum
open BoxLensLift QuadraticStability LocalObjective

theorem amplitude_le_four {n : ℕ} (hn : 2 ≤ n) : FiniteBox.amplitude n ≤ 4 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  let x := Real.pi / (2 * n)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < 2 * n)).2
    linarith [Real.pi_lt_four]
  have hc : (1 / 2 : ℝ) ≤ Real.cos x := by
    have h := Real.one_sub_sq_div_two_le_cos (x := x)
    nlinarith
  have ht : Real.tan x ≤ 2 * x := by
    rw [Real.tan_eq_sin_div_cos]
    apply (div_le_iff₀ (by linarith : 0 < Real.cos x)).2
    have hs := Real.sin_le hx
    nlinarith [mul_nonneg hx (show 0 ≤ Real.cos x - 1 / 2 by linarith)]
  calc
    _ = (n : ℝ) * Real.tan x := rfl
    _ ≤ (n : ℝ) * (2 * x) := mul_le_mul_of_nonneg_left ht hn0.le
    _ = Real.pi := by dsimp [x]; field_simp
    _ ≤ 4 := Real.pi_lt_four.le

theorem box_meanSquare_le {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q hm) : meanSquare q ≤ 16 := by
  have hb (j : Fin (2 * m)) : |q j| ≤ 4 := (hq.2 j).trans (amplitude_le_four (by omega))
  have he := meanSquare_le_of_bound (by omega) q (by norm_num : (0 : ℝ) ≤ 4) hb
  norm_num at he
  exact he

theorem canonical_energy_le {m : ℕ} (hm : 2 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) : pairEnergy (by omega) (canonicalLift q) ≤ 512 := by
  have he := canonicalLift_pairEnergy_le hm q hq.1
  have hq2 := box_meanSquare_le (by omega) q hq
  linarith

theorem periodize_difference {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (j : ℕ) :
    periodize hn c (j + 1) - periodize hn c j =
      difference hn c ⟨j % n, Nat.mod_lt _ hn⟩ := by
  simp only [periodize, difference, successor, Nat.mod_add_mod]

theorem correction_energy_le {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    pairEnergy (by omega) (liftedCenter hm q hq - canonicalLift q) ≤
      524288 / ((2 * m : ℕ) : ℝ) ^ 4 := by
  have he := energyA_le_step (by omega : 4 ≤ 2 * m)
    (periodize (by omega) (liftedCenter hm q hq - canonicalLift q)) (periodize_periodic _ _)
    (ε := 2048 / ((2 * m : ℕ) : ℝ) ^ 4) (by positivity) (by
      intro j
      rw [periodize_difference]
      exact liftedCenter_difference_error hm q hq _)
  change pairEnergy (by omega) (liftedCenter hm q hq - canonicalLift q) ≤ _ at he
  have hn0 : (((2 * m : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (show 2 * m ≠ 0 by omega)
  calc
    _ ≤ ((2 * m : ℕ) : ℝ) ^ 4 * (2048 / ((2 * m : ℕ) : ℝ) ^ 4) ^ 2 / 8 := he
    _ = _ := by field_simp; ring

theorem correction_energy_le_half {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    pairEnergy (by omega) (liftedCenter hm q hq - canonicalLift q) ≤ 1 / 2 := by
  refine (correction_energy_le hm q hq).trans ?_
  have hnR : (32 : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast (show 32 ≤ 2 * m by omega)
  have hs : (1024 : ℝ) ≤ ((2 * m : ℕ) : ℝ) ^ 2 := by nlinarith
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((2 * m : ℕ) : ℝ) ^ 4)).2
  nlinarith [sq_nonneg (((2 * m : ℕ) : ℝ) ^ 2 - 1024)]

theorem lifted_energy_le {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) : pairEnergy (by omega) (liftedCenter hm q hq) ≤ 1025 := by
  have he := pairEnergy_add_le (by omega) (canonicalLift q) (liftedCenter hm q hq - canonicalLift q)
  rw [add_sub_cancel] at he
  have hc := canonical_energy_le (by omega) q hq
  have hd := correction_energy_le_half hm q hq
  linarith

theorem lifted_step_le {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) (j : Fin (2 * m)) :
    ‖difference (by omega) (liftedCenter hm q hq) j‖ ≤ 34 / ((2 * m : ℕ) : ℝ) ^ 2 := by
  have hnR : (32 : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast (show 32 ≤ 2 * m by omega)
  have hsin := radius_le_numeric (by omega : 0 < 2 * m)
  have hsqrt : Real.sqrt 3 ≤ 2 := (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  have hmul := mul_le_mul_of_nonneg_right hsqrt (radius_nonneg (2 * m))
  have hrem : 2048 / ((2 * m : ℕ) : ℝ) ^ 4 ≤ 2 / ((2 * m : ℕ) : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < ((2 * m : ℕ) : ℝ) ^ 4)
      (by positivity : (0 : ℝ) < ((2 * m : ℕ) : ℝ) ^ 2)).2
    have hs : (1024 : ℝ) ≤ ((2 * m : ℕ) : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg (((2 * m : ℕ) : ℝ)))
      (show 0 ≤ ((2 * m : ℕ) : ℝ) ^ 2 - 1024 by linarith)]
  have he := liftedCenter_increment_norm_le hm q hq j
  calc
    _ ≤ 2 * (16 / ((2 * m : ℕ) : ℝ) ^ 2) + 2 / ((2 * m : ℕ) : ℝ) ^ 2 := by
      linarith
    _ = _ := by ring

theorem lifted_relative_step {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) (j : ℕ) :
    ‖periodize (by omega) (liftedCenter hm q hq) (j + 1) -
      periodize (by omega) (liftedCenter hm q hq) j‖ ≤
      (9 / ((2 * m : ℕ) : ℝ)) * ‖LocalPhase.regularRoot (2 * m) - 1‖ := by
  have hnR : (0 : ℝ) < (2 * m : ℕ) := by exact_mod_cast (show 0 < 2 * m by omega)
  rw [periodize_difference]
  calc
    _ ≤ 34 / ((2 * m : ℕ) : ℝ) ^ 2 := lifted_step_le hm q hq _
    _ ≤ 36 / ((2 * m : ℕ) : ℝ) ^ 2 := by gcongr; norm_num
    _ = (9 / ((2 * m : ℕ) : ℝ)) * (4 / ((2 * m : ℕ) : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (GapRigidity.root_edge_lower (by omega)) (by positivity)

theorem lifted_log_remainder {m : ℕ} (hm : 32 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    |logDistanceProduct (2 * m) (perturbedVertices (2 * m) (periodize (by omega) (liftedCenter (by omega) q hq))) -
      logDistanceProduct (2 * m) (regularVertices (2 * m)) -
      pairPotential (by omega) (liftedCenter (by omega) q hq)| ≤
      332100 / ((2 * m : ℕ) : ℝ) ^ 2 := by
  have hnR : (64 : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast (show 64 ≤ 2 * m by omega)
  have hη : 9 / ((2 * m : ℕ) : ℝ) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < (2 * m : ℕ))).2
    linarith
  have he := AntipodalLog.geometric_log_error_le (by omega)
    (liftedCenter (by omega) q hq) (liftedCenter_halfTurn (by omega) q hq)
    (η := 9 / ((2 * m : ℕ) : ℝ)) (by positivity) hη (lifted_relative_step (by omega) q hq)
  calc
    _ ≤ 4 * (9 / ((2 * m : ℕ) : ℝ)) ^ 2 * pairEnergy (by omega) (liftedCenter (by omega) q hq) := he
    _ ≤ 4 * (9 / ((2 * m : ℕ) : ℝ)) ^ 2 * 1025 :=
      mul_le_mul_of_nonneg_left (lifted_energy_le (by omega) q hq) (by positivity)
    _ = _ := by ring

theorem lifted_potential_error {m : ℕ} (hm : 16 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    |pairPotential (by omega) (liftedCenter hm q hq) - normalizedBoxEnergy (operator (2 * m)) q| ≤
      66560 / ((2 * m : ℕ) : ℝ) ^ 2 := by
  let n := 2 * m
  let c := canonicalLift q
  let d := liftedCenter hm q hq - c
  have hnR : (32 : ℝ) ≤ n := by dsimp [n]; exact_mod_cast (show 32 ≤ 2 * m by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hc : Real.sqrt (pairEnergy (by omega) c) ≤ 32 := by
    apply Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩
    have h := canonical_energy_le (by omega) q hq
    norm_num
    exact h.trans (by norm_num)
  have hdA : pairEnergy (by omega) d ≤ 524288 / (n : ℝ) ^ 4 := correction_energy_le hm q hq
  have hd : Real.sqrt (pairEnergy (by omega) d) ≤ 1024 / (n : ℝ) ^ 2 := by
    apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    calc
      _ ≤ 524288 / (n : ℝ) ^ 4 := hdA
      _ ≤ 1048576 / (n : ℝ) ^ 4 := by gcongr; norm_num
      _ = _ := by ring
  have hdscale : pairEnergy (by omega) d ≤ 1024 / (n : ℝ) ^ 2 := by
    refine hdA.trans ?_
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 4)
      (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).2
    have hs : (1024 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (show 0 ≤ (n : ℝ) ^ 2 - 512 by linarith)]
  have hsum : c + d = liftedCenter hm q hq := by dsimp [c, d]; abel
  have he := potential_difference_le (by omega) c d
  rw [hsum] at he
  have hP : pairPotential (by omega) c = normalizedBoxEnergy (operator (2 * m)) q :=
    pairPotential_canonicalLift (by omega) q hq.1
  rw [hP] at he
  calc
    _ ≤ 2 * Real.sqrt (pairEnergy (by omega) c) * Real.sqrt (pairEnergy (by omega) d) +
        pairEnergy (by omega) d := he
    _ ≤ 2 * 32 * (1024 / (n : ℝ) ^ 2) + 1024 / (n : ℝ) ^ 2 := by
      gcongr
    _ = 66560 / (n : ℝ) ^ 2 := by ring

/-- Manuscript (4.9), for the actual lifted vertices and actual log-distance sum,
with an explicit absolute error constant. No objective approximation is assumed. -/
theorem whole_box_objective {m : ℕ} (hm : 32 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    |logDistanceProduct (2 * m) (perturbedVertices (2 * m) (periodize (by omega) (liftedCenter (by omega) q hq))) -
      logDistanceProduct (2 * m) (regularVertices (2 * m)) -
      normalizedBoxEnergy (operator (2 * m)) q| ≤
      1000000 / ((2 * m : ℕ) : ℝ) ^ 2 := by
  have hlog := lifted_log_remainder hm q hq
  have hP := lifted_potential_error (by omega) q hq
  have ht := abs_add_le
    (logDistanceProduct (2 * m) (perturbedVertices (2 * m) (periodize (by omega) (liftedCenter (by omega) q hq))) -
      logDistanceProduct (2 * m) (regularVertices (2 * m)) -
      pairPotential (by omega) (liftedCenter (by omega) q hq))
    (pairPotential (by omega) (liftedCenter (by omega) q hq) - normalizedBoxEnergy (operator (2 * m)) q)
  rw [sub_add_sub_cancel] at ht
  calc
    _ ≤ 332100 / ((2 * m : ℕ) : ℝ) ^ 2 + 66560 / ((2 * m : ℕ) : ℝ) ^ 2 := by
      linarith
    _ = 398660 / ((2 * m : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ _ := by gcongr; norm_num

end Erdos1045.EventualExact.WholeBoxObjective

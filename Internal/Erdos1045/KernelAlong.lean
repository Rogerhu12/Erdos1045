import Erdos1045.KernelComparison
import Erdos1045.CircleGapQuantitative

open scoped BigOperators Topology
open Filter

namespace Erdos1045.KernelWeights

noncomputable section

theorem rowEnergy_difference_tendsto_along {N : ℕ → ℕ} (hN : ∀ j, 2 ≤ N j)
    {d e : ℕ → ℕ → ℝ}
    (hclose : Tendsto (fun j => rowDistance (N j) (d j) (e j)) atTop (𝓝 0)) :
    Tendsto (fun j => rowEnergy (N j) (d j) - rowEnergy (N j) (e j)) atTop (𝓝 0) := by
  apply tendsto_zero_of_cutoff_modulus hclose
  intro j _ M hM
  exact rowEnergy_difference_bound (hN j) hM (d j) (e j)

theorem triangularEnergy_difference_tendsto_along {N : ℕ → ℕ}
    (hN2 : ∀ j, 2 ≤ N j) (hN : Tendsto N atTop atTop)
    {d e : ℕ → ℕ → ℕ → ℝ} {A : ℝ} (hA : 0 < A)
    (hd : ∀ j, SeparatedRows (N j) (d j) A)
    (he : ∀ j, SeparatedRows (N j) (e j) A)
    (hclose : ∀ q, Tendsto (fun j => rowDistance (N j) (d j q) (e j q)) atTop (𝓝 0)) :
    Tendsto (fun j => triangularEnergy (N j) (d j) - triangularEnergy (N j) (e j)) atTop (𝓝 0) := by
  let B : ℕ → ℝ := fun q =>
    2 * ((2 + 3 * Real.pi ^ 2) / A ^ 2) * (1 / ((q : ℝ) + 1) ^ 2)
  let f : ℕ → ℕ → ℝ := fun j q => truncatedRow (N j) (d j) q - truncatedRow (N j) (e j) q
  have hz : Summable (fun q : ℕ => 1 / ((q : ℝ) + 1) ^ 2) := by
    have h : Summable (fun q : ℕ => (1 : ℝ) / (q : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)
    simpa using (summable_nat_add_iff 1).mpr h
  have hB : Summable B := hz.mul_left _
  have hpoint (q : ℕ) : Tendsto (fun j => f j q) atTop (𝓝 0) := by
    have heq : (fun j => f j q) =ᶠ[atTop]
        (fun j => rowEnergy (N j) (d j q) - rowEnergy (N j) (e j q)) := by
      filter_upwards [hN.eventually (eventually_ge_atTop (2 * (q + 1) + 1))] with j hj
      simp [f, truncatedRow, show 2 * (q + 1) < N j by omega]
    exact (tendsto_congr' heq).mpr (rowEnergy_difference_tendsto_along hN2 (hclose q))
  have hbound : ∀ᶠ j in atTop, ∀ q, ‖f j q‖ ≤ B q := by
    apply Eventually.of_forall
    intro j q
    by_cases hq : 2 * (q + 1) < N j
    · have h₁ := separated_row_bound (hN2 j) hA (hd j) q hq
      have h₂ := separated_row_bound (hN2 j) hA (he j) q hq
      simp only [f, truncatedRow, if_pos hq, Real.norm_eq_abs]
      have htri := abs_sub (rowEnergy (N j) (d j q)) (rowEnergy (N j) (e j q))
      dsimp [B]
      linarith
    · simp only [f, truncatedRow, if_neg hq, sub_self, norm_zero]
      dsimp [B]
      positivity
  have hlim := tendsto_tsum_of_dominated_convergence hB hpoint hbound
  have heq (j : ℕ) : (∑' q, f j q) =
      triangularEnergy (N j) (d j) - triangularEnergy (N j) (e j) := by
    exact (summable_truncatedRow (N j) (d j)).tsum_sub (summable_truncatedRow (N j) (e j))
  simpa only [heq, tsum_zero] using hlim

open CyclicAngles

def angleRows {n : ℕ} (a : Angles n) : ℕ → ℕ → ℝ :=
  fun q i => (n : ℝ) * window a (q + 1) i

theorem window_complement {n m : ℕ} (a : Angles n) (hm : m ≤ n) (i : ℕ) :
    window a (n - m) (i + m) = 2 * Real.pi - window a m i := by
  have hidx : ((i + m : ℕ) : ℤ) + (n - m : ℕ) = (i : ℤ) + n := by
    rw [Nat.cast_add, Nat.cast_sub hm]
    ring
  unfold window
  rw [hidx, a.period]
  push_cast
  ring

theorem angleRows_wrapped {n : ℕ} (a : Angles n) (hn : 3 ≤ n) {C : ℝ}
    (hC : energy a ≤ C) :
    WrappedSeparatedRows n (angleRows a) (2 * Real.pi * Real.exp (-C / 2 - 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlo (i : ℕ) := (gap_bounds_of_energy_le a hn hC i).1
  have hhi (i : ℕ) := (gap_bounds_of_energy_le a hn hC i).2
  constructor
  · intro q hq i hi
    have hp := window_pos a (show 0 < q + 1 by omega) i
    have hu := window_lt_two_pi a (show q + 1 < n by omega) i
    dsimp [angleRows]
    constructor <;> nlinarith
  · intro q hq i hi
    have h := (window_bounds_of_gap_bounds a (by omega) hlo hhi (q + 1) i).1
    have hm := mul_le_mul_of_nonneg_left h hn0.le
    dsimp [angleRows]
    push_cast at hm
    field_simp at hm
    rw [show (-C - 2) / 2 = -C / 2 - 1 by ring] at hm
    nlinarith
  · intro q hq i hi
    have h := (window_bounds_of_gap_bounds a (by omega) hlo hhi (n - (q + 1)) (i + (q + 1))).1
    rw [window_complement a (by omega)] at h
    have hm := mul_le_mul_of_nonneg_left h hn0.le
    have hcast : ((n - (q + 1) : ℕ) : ℝ) = (n : ℝ) - ((q : ℝ) + 1) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      rfl
    rw [hcast] at hm
    field_simp at hm
    rw [show (-C - 2) / 2 = -C / 2 - 1 by ring] at hm
    have hqn : 2 * ((q : ℝ) + 1) ≤ n := by exact_mod_cast hq.le
    have hmul := mul_nonneg (show 0 ≤ 2 * Real.pi * Real.exp (-C / 2 - 1) by positivity)
      (show 0 ≤ (n : ℝ) - 2 * ((q : ℝ) + 1) by linarith)
    dsimp [angleRows]
    nlinarith

theorem rowDistance_angleRows_tendsto {N : ℕ → ℕ} (hN3 : ∀ j, 3 ≤ N j)
    (hN : Tendsto N atTop atTop) (a : ∀ j, Angles (N j))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ j, energy (a j) ≤ C) (q : ℕ) :
    Tendsto (fun j => rowDistance (N j) (angleRows (a j) q) (regularRows q)) atTop (𝓝 0) := by
  let D := (2 * C + 6) * C / 2
  let err := fun j => rowDistance (N j) (angleRows (a j) q) (regularRows q)
  have hbound (j : ℕ) : (err j) ^ 2 ≤
      (4 * Real.pi ^ 2 * ((q : ℝ) + 1) ^ 2 * D) / (N j : ℝ) := by
    have h := mean_window_error_sq (a j) (by have := hN3 j; omega) (q + 1)
    have hD := gap_deviation_of_energy_le (a j) (hN3 j) hC0 (hC j)
    have hm := mul_le_mul_of_nonneg_left hD
      (show 0 ≤ 4 * Real.pi ^ 2 * (q + 1 : ℕ) ^ 2 / (N j : ℝ) by positivity)
    dsimp [err, rowDistance, angleRows, regularRows, D]
    push_cast at h hm
    convert h.trans hm using 1 <;> first | rfl | ring
  have hzero : Tendsto (fun j => (err j) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun j => sq_nonneg _) hbound
    exact (tendsto_const_div_atTop_nhds_zero_nat
      (4 * Real.pi ^ 2 * ((q : ℝ) + 1) ^ 2 * D)).comp hN
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hzero
  have hsq (j : ℕ) : Real.sqrt ((err j) ^ 2) = err j :=
    Real.sqrt_sq (rowDistance_nonneg _ _ _)
  simpa only [Function.comp_def, hsq, Real.sqrt_zero] using hsqrt

theorem angleRows_regular_comparison {N : ℕ → ℕ} (hN3 : ∀ j, 3 ≤ N j)
    (hN : Tendsto N atTop atTop) (a : ∀ j, Angles (N j))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ j, energy (a j) ≤ C) :
    Tendsto (fun j => triangularEnergy (N j) (angleRows (a j)) -
      triangularEnergy (N j) regularRows) atTop (𝓝 0) := by
  let A := 2 * Real.pi * Real.exp (-C / 2 - 1)
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hAπ : A ≤ 2 * Real.pi := by
    have hexp : Real.exp (-C / 2 - 1) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    dsimp [A]
    nlinarith [Real.pi_pos]
  have hd (j : ℕ) : SeparatedRows (N j) (foldedRows (N j) (angleRows (a j))) A :=
    (angleRows_wrapped (a j) (hN3 j) (hC j)).folded (by have := hN3 j; omega)
  have hclose (q : ℕ) : Tendsto
      (fun j => rowDistance (N j) (foldedRows (N j) (angleRows (a j)) q) (regularRows q)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun j => rowDistance_nonneg _ _ _))
    · filter_upwards [hN.eventually (eventually_ge_atTop (2 * (q + 1) + 1))] with j hj
      exact rowDistance_folded_le _ _ (regular_reference_le_half (by omega))
    · exact rowDistance_angleRows_tendsto hN3 hN a hC0 hC q
  have hlim := triangularEnergy_difference_tendsto_along
    (fun j => by have := hN3 j; omega) hN hA0 hd
    (fun j => regularRows_separated (by have := hN3 j; omega) hAπ) hclose
  have heq : (fun j => triangularEnergy (N j) (foldedRows (N j) (angleRows (a j))) -
      triangularEnergy (N j) regularRows) =
      (fun j => triangularEnergy (N j) (angleRows (a j)) - triangularEnergy (N j) regularRows) := by
    funext j
    rw [triangularEnergy_folded (by have := hN3 j; omega)]
  rw [heq] at hlim
  exact hlim

end

end Erdos1045.KernelWeights

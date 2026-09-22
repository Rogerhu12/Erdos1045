import Erdos1045.ClosedCosine

/-! The unpaired antipodal row in even dimension is a vanishing kernel tail. -/

namespace Erdos1045.EventualExact.AllOrderFourier

open Erdos1045.KernelWeights Erdos1045.CyclicAngles Filter
open scoped BigOperators Topology
noncomputable section

theorem sum_fold_even (f : ℕ → ℝ) {m : ℕ} (hm : 0 < m)
    (hs : ∀ k, k ≤ 2 * m → f (2 * m - k) = f k) :
    (∑ k ∈ Finset.range (2 * m), f k) =
      f 0 + 2 * ∑ k ∈ Finset.range (m - 1), f (k + 1) + f m := by
  have htail : (∑ k ∈ Finset.range (m - 1), f (m + (k + 1))) =
      ∑ k ∈ Finset.range (m - 1), f (k + 1) := by
    calc
      _ = ∑ k ∈ Finset.range (m - 1), f ((m - 1) - 1 - k + 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        simpa only [show 2 * m - ((m - 1) - 1 - k + 1) = m + (k + 1) by omega] using
          hs ((m - 1) - 1 - k + 1) (by omega)
      _ = _ := Finset.sum_range_reflect (fun k => f (k + 1)) (m - 1)
  have hfirst : (∑ k ∈ Finset.range m, f k) =
      (∑ k ∈ Finset.range (m - 1), f (k + 1)) + f 0 := by
    simpa only [show m - 1 + 1 = m by omega] using Finset.sum_range_succ' f (m - 1)
  have hsecond : (∑ k ∈ Finset.range m, f (m + k)) =
      (∑ k ∈ Finset.range (m - 1), f (m + (k + 1))) + f m := by
    simpa only [show m - 1 + 1 = m by omega, Nat.add_zero] using
      Finset.sum_range_succ' (fun k => f (m + k)) (m - 1)
  rw [show 2 * m = m + m by omega, Finset.sum_range_add, hfirst, hsecond, htail]
  ring

theorem triangularEnergy_even (m : ℕ) (d : ℕ → ℕ → ℝ) :
    triangularEnergy (2 * m) d =
      ∑ q ∈ Finset.range (m - 1), rowEnergy (2 * m) (d q) := by
  unfold triangularEnergy
  rw [tsum_eq_sum (s := Finset.range (m - 1)) (fun q hq => by
    have hqm : m - 1 ≤ q := by simpa using hq
    simp [truncatedRow, show ¬2 * (q + 1) < 2 * m by omega])]
  apply Finset.sum_congr rfl
  intro q hq
  have hqm := Finset.mem_range.mp hq
  simp [truncatedRow, show 2 * (q + 1) < 2 * m by omega]

def antipodalEnergy {n : ℕ} (a : Angles n) : ℝ :=
  if Even n then lagKernelEnergy a (n / 2) else 0

def antipodalGrid (n : ℕ) : ℝ := if Even n then kernel n Real.pi / n else 0

theorem angularKernelEnergy_all {n : ℕ} (hn : 0 < n) (a : Angles n) :
    angularKernelEnergy a = kernel n 0 / n +
      2 * triangularEnergy n (angleRows a) + antipodalEnergy a := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, hm⟩ := he
    have hn' : n = 2 * m := by omega
    clear hm
    subst n
    rw [angularKernelEnergy, sum_fold_even _ (by omega : 0 < m)
      (fun k hk => lagKernelEnergy_complement a hk), lagKernelEnergy_zero a hn,
      triangularEnergy_even]
    have hrows : (∑ k ∈ Finset.range (m - 1), lagKernelEnergy a (k + 1)) =
        ∑ k ∈ Finset.range (m - 1), rowEnergy (2 * m) (angleRows a k) := by
      exact Finset.sum_congr rfl (fun k _ => lagKernelEnergy_succ a hn k)
    rw [hrows]
    simp [antipodalEnergy]
  · rw [angularKernelEnergy_of_odd ho]
    rw [antipodalEnergy, if_neg (Nat.not_even_iff_odd.mpr ho), add_zero]

theorem regularGridEnergy_all {n : ℕ} (hn : 0 < n) :
    regularGridEnergy n = kernel n 0 / n +
      2 * triangularEnergy n regularRows + antipodalGrid n := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, hm⟩ := he
    have hn' : n = 2 * m := by omega
    clear hm
    subst n
    have hn0 : ((2 * m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    let f : ℕ → ℝ := fun k => kernel (2 * m) (2 * Real.pi * k / (2 * m : ℕ)) / (2 * m : ℕ)
    have hsym (k : ℕ) (hk : k ≤ 2 * m) : f (2 * m - k) = f k := by
      dsimp [f]
      have harg : 2 * Real.pi * ((2 * m - k : ℕ) : ℝ) / (2 * m : ℕ) =
          2 * Real.pi - 2 * Real.pi * k / (2 * m : ℕ) := by
        rw [Nat.cast_sub hk]
        field_simp
      rw [harg, kernel_reflection]
    unfold regularGridEnergy
    rw [Finset.sum_div]
    change (∑ k ∈ Finset.range (2 * m), f k) = _
    rw [sum_fold_even f (by omega) hsym, triangularEnergy_even]
    have hrows : (∑ k ∈ Finset.range (m - 1), f (k + 1)) =
        ∑ k ∈ Finset.range (m - 1), rowEnergy (2 * m) (regularRows k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [show regularRows k = (fun _ => 2 * Real.pi * ((k : ℝ) + 1)) by rfl,
        rowEnergy_constant hn]
      simp [f, normalizedKernel]
    rw [hrows]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have harg : 2 * Real.pi * (m : ℝ) / (2 * m : ℕ) = Real.pi := by
      push_cast
      field_simp
    have heven : Even (2 * m) := ⟨m, by omega⟩
    simp only [f, Nat.cast_zero, mul_zero, zero_div, harg, antipodalGrid, if_pos heven]
  · rw [regularGridEnergy_of_odd ho]
    rw [antipodalGrid, if_neg (Nat.not_even_iff_odd.mpr ho), add_zero]

theorem lagKernelEnergy_abs_le {n m : ℕ} (a : Angles n) (hn : 2 ≤ n)
    (hm : 0 < m) (hmn : m < n) {δ : ℝ} (hδ : 0 < δ)
    (hl : ∀ i, δ ≤ window a m i) (hr : ∀ i, δ ≤ 2 * Real.pi - window a m i) :
    |lagKernelEnergy a m| ≤ ((2 + 3 * Real.pi ^ 2) / δ ^ 2) / (n : ℝ) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let d (i : ℕ) := (n : ℝ) * window a m i
  have he : lagKernelEnergy a m = rowEnergy n d := by
    unfold lagKernelEnergy rowEnergy normalizedKernel d
    simp only [mul_div_cancel_left₀ _ hn0.ne']
    rw [← Finset.sum_div, div_div, pow_two]
  rw [he, ← rowEnergy_folded (show 0 < n by omega) d]
  have hb := rowEnergy_abs_bound hn (fun i => foldScaled n (d i))
    (A := (n : ℝ) * δ) (by positivity) (fun i _ =>
      foldScaled_principal (by omega) (mul_nonneg hn0.le (window_pos a hm i).le)
        (by dsimp [d]; nlinarith [window_lt_two_pi a hmn i])) (by
      intro i _
      apply le_trans _ (le_abs_self _)
      dsimp [foldScaled, d]
      apply le_min <;> nlinarith [hl i, hr i])
  convert hb using 1
  ring

theorem half_window_lower {n : ℕ} (a : Angles n) (hn : 3 ≤ n) (he : Even n)
    {C : ℝ} (hC : energy a ≤ C) (i : ℕ) :
    Real.pi * Real.exp (-C / 2 - 1) ≤ window a (n / 2) i := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have heq : 2 * (n / 2) = n := by obtain ⟨m, hm⟩ := he; omega
  have heqR : (2 : ℝ) * (n / 2 : ℕ) = n := by exact_mod_cast heq
  have hs : (2 * Real.pi / n) * (n / 2 : ℕ) = Real.pi := by
    field_simp
    nlinarith
  have hb := (window_bounds_of_gap_bounds a (by omega)
    (fun k => (gap_bounds_of_energy_le a hn hC k).1)
    (fun k => (gap_bounds_of_energy_le a hn hC k).2) (n / 2) i).1
  rwa [hs] at hb

theorem antipodalEnergy_abs_le {n : ℕ} (a : Angles n) (hn : 3 ≤ n)
    {C : ℝ} (hC : energy a ≤ C) :
    |antipodalEnergy a| ≤
      ((2 + 3 * Real.pi ^ 2) / (Real.pi * Real.exp (-C / 2 - 1)) ^ 2) / (n : ℝ) ^ 2 := by
  unfold antipodalEnergy
  split_ifs with he
  · apply lagKernelEnergy_abs_le a (by omega) (by omega) (by omega) (by positivity)
      (half_window_lower a hn he hC)
    intro i
    have hhalf : n - n / 2 = n / 2 := by obtain ⟨m, hm⟩ := he; omega
    have hw := window_complement a (show n / 2 ≤ n by omega) i
    rw [hhalf] at hw
    rw [← hw]
    exact half_window_lower a hn he hC _
  · simp only [abs_zero]
    positivity

theorem antipodalGrid_abs_le {n : ℕ} (hn : 2 ≤ n) :
    |antipodalGrid n| ≤ ((2 + 3 * Real.pi ^ 2) / Real.pi ^ 2) / (n : ℝ) ^ 2 := by
  unfold antipodalGrid
  split_ifs
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hb := kernel_spatial_bound (t := Real.pi) hn (by rw [abs_of_pos Real.pi_pos])
    rw [abs_div, abs_of_pos hn0]
    apply (div_le_iff₀ hn0).2
    rw [show ((2 + 3 * Real.pi ^ 2) / Real.pi ^ 2) / (n : ℝ) ^ 2 * n =
      (2 + 3 * Real.pi ^ 2) / ((n : ℝ) * Real.pi ^ 2) by field_simp]
    apply (le_div_iff₀ (mul_pos hn0 (sq_pos_of_pos Real.pi_pos))).2
    apply (mul_le_mul_iff_left₀ hn0).mp
    nlinarith [abs_nonneg (kernel n Real.pi)]
  · simp only [abs_zero]
    positivity

theorem tendsto_zero_of_inverse_square_bound {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {f : ℕ → ℝ} {K : ℝ} (hb : ∀ j, |f j| ≤ K / (N j : ℝ) ^ 2) :
    Tendsto f atTop (𝓝 0) := by
  have hNr : Tendsto (fun j => (N j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hu : Tendsto (fun j => K / (N j : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, inv_pow] using ((tendsto_inv_atTop_zero.comp hNr).pow 2).const_mul K
  apply squeeze_zero_norm (fun j => ?_) hu
  simpa only [Real.norm_eq_abs] using hb j

theorem fourierSquareSum_tendsto {N : ℕ → ℕ} (hN3 : ∀ j, 3 ≤ N j)
    (hN : Tendsto N atTop atTop) (a : ∀ j, Angles (N j))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ j, energy (a j) ≤ C) :
    Tendsto (fun j => fourierSquareSum (a j)) atTop (𝓝 (Real.pi ^ 2 / 6)) := by
  have ha := tendsto_zero_of_inverse_square_bound hN
    (fun j => antipodalEnergy_abs_le (a j) (hN3 j) (hC j))
  have hr := tendsto_zero_of_inverse_square_bound hN
    (fun j => antipodalGrid_abs_le (show 2 ≤ N j by have := hN3 j; omega))
  have ht := angleRows_regular_comparison hN3 hN a hC0 hC
  have hreg := regularEnergy_tendsto.comp hN
  have heq (j : ℕ) :
      2 * (triangularEnergy (N j) (angleRows (a j)) - triangularEnergy (N j) regularRows) +
        regularEnergy (N j) + (antipodalEnergy (a j) - antipodalGrid (N j)) =
      fourierSquareSum (a j) := by
    rw [fourierSquareSum_eq_angularKernelEnergy classicalCosineFourier (a j)
      (by have := hN3 j; omega), ← regularGridEnergy_eq_regularEnergy classicalCosineFourier
        (by have := hN3 j; omega), angularKernelEnergy_all (by have := hN3 j; omega),
      regularGridEnergy_all (by have := hN3 j; omega)]
    ring
  simpa only [Function.comp_def, mul_zero, zero_add, sub_zero, add_zero, heq] using
    ((ht.const_mul 2).add hreg).add (ha.sub hr)

theorem fourierSquareSum_tendsto_eventually {N : ℕ → ℕ} (hN3 : ∀ j, 3 ≤ N j)
    (hN : Tendsto N atTop atTop) (a : ∀ j, Angles (N j)) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ᶠ j in atTop, energy (a j) ≤ C) :
    Tendsto (fun j => fourierSquareSum (a j)) atTop (𝓝 (Real.pi ^ 2 / 6)) := by
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp hC
  apply (tendsto_add_atTop_iff_nat J).mp
  exact fourierSquareSum_tendsto (fun j => hN3 (j + J))
    (hN.comp (tendsto_add_atTop_nat J)) (fun j => a (j + J)) hC0
    (fun j => hJ (j + J) (by omega))

end
end Erdos1045.EventualExact.AllOrderFourier

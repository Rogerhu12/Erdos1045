import EventualExact.ForwardMaximalL2
import EventualExact.GeometricLogRemainder
import EventualExact.SchurLiftBounds
import Erdos1045.GapRigidity
import Mathlib.Algebra.Order.Chebyshev

/-! A uniform quartic estimate from the square sum of cyclic increments. -/

noncomputable section
open scoped BigOperators

namespace Erdos1045.EventualExact.QuarticWindowBound

open ForwardMaximal SchurSpectrum

theorem scalar_telescope {S B x : ℝ} (hS : 0 < S) (hB : 0 ≤ B)
    (hx : x ^ 2 ≤ B) (k : ℕ) (hk : ((k : ℝ) + 1) * x ^ 2 ≤ S) :
    x ^ 4 ≤ 4 * S * B *
      (S / (S + (k : ℝ) * B) - S / (S + ((k : ℝ) + 1) * B)) := by
  have hd : 0 < S + (k : ℝ) * B := by positivity
  have he : 0 < S + ((k : ℝ) + 1) * B := by positivity
  have hlin : (S + ((k : ℝ) + 1) * B) * x ^ 2 ≤ 2 * S * B := by
    have h₁ := mul_le_mul_of_nonneg_left hx hS.le
    have h₂ := mul_le_mul_of_nonneg_left hk hB
    nlinarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤
    (S + ((k : ℝ) + 1) * B) * x ^ 2) hlin 2
  have hprod : x ^ 4 * ((S + (k : ℝ) * B) * (S + ((k : ℝ) + 1) * B)) ≤
      x ^ 4 * (S + ((k : ℝ) + 1) * B) ^ 2 := by
    gcongr
    nlinarith
  have hid : 4 * S * B *
      (S / (S + (k : ℝ) * B) - S / (S + ((k : ℝ) + 1) * B)) =
      (4 * S ^ 2 * B ^ 2) /
        ((S + (k : ℝ) * B) * (S + ((k : ℝ) + 1) * B)) := by
    field_simp
    ring
  rw [hid]
  apply (le_div_iff₀ (mul_pos hd he)).mpr
  nlinarith

theorem sum_fourth_le {N : ℕ} (a : ℕ → ℝ) {S B : ℝ} (hS : 0 ≤ S) (hB : 0 ≤ B)
    (ha : ∀ k < N, a k ^ 2 ≤ B)
    (haS : ∀ k < N, ((k : ℝ) + 1) * a k ^ 2 ≤ S) :
    (∑ k ∈ Finset.range N, a k ^ 4) ≤ 4 * S * B := by
  rcases hS.eq_or_lt with hS | hS
  · have hz (k : ℕ) (hk : k ∈ Finset.range N) : a k = 0 := by
      have hh := haS k (Finset.mem_range.mp hk)
      have hc : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
      nlinarith [sq_nonneg (a k)]
    simp only [← hS, mul_zero, zero_mul]
    exact le_of_eq (Finset.sum_eq_zero (fun k hk => by rw [hz k hk]; norm_num))
  · let H (k : ℕ) := S / (S + (k : ℝ) * B)
    have ht := Finset.sum_le_sum (s := Finset.range N) (fun k hk =>
      scalar_telescope hS hB (ha k (Finset.mem_range.mp hk)) k
        (haS k (Finset.mem_range.mp hk)))
    have he : (∑ k ∈ Finset.range N, 4 * S * B *
        (S / (S + (k : ℝ) * B) - S / (S + ((k : ℝ) + 1) * B))) =
        4 * S * B * (1 - H N) := by
      rw [← Finset.mul_sum]
      have hs : (∑ k ∈ Finset.range N,
          (S / (S + (k : ℝ) * B) - S / (S + ((k : ℝ) + 1) * B))) = H 0 - H N := by
        simpa only [H, Nat.cast_add, Nat.cast_one] using Finset.sum_range_sub' H N
      rw [hs]
      simp [H, hS.ne']
    rw [he] at ht
    have hH : 0 ≤ H N := by dsimp [H]; positivity
    exact ht.trans (by nlinarith [mul_nonneg (by positivity : 0 ≤ 4 * S * B) hH])

theorem periodic_sum_shift {n : ℕ} (f : ℕ → ℝ) (hf : Function.Periodic f n) (j : ℕ) :
    (∑ r ∈ Finset.range n, f (j + r)) = ∑ r ∈ Finset.range n, f r := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h₁ := Finset.sum_range_succ (fun r => f (j + r)) n
    have h₂ := Finset.sum_range_succ' (fun r => f (j + r)) n
    rw [hf j] at h₁
    simp only [Nat.add_zero] at h₂
    have he : (∑ r ∈ Finset.range n, f (j + (r + 1))) =
        ∑ r ∈ Finset.range n, f (j + 1 + r) := by
      apply Finset.sum_congr rfl
      intro r _
      congr 1
      omega
    rw [he] at h₂
    change (∑ r ∈ Finset.range n, f (j + 1 + r)) = _
    linarith

theorem average_eq (f : ℕ → ℝ) (j k : ℕ) :
    average f j k = (∑ r ∈ Finset.range k, f (j + r)) / k := by
  simp only [average, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

theorem average_nonneg (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) (j k : ℕ) :
    0 ≤ average f j k := by
  rw [average_eq]
  exact div_nonneg (Finset.sum_nonneg (fun r _ => hf _)) (Nat.cast_nonneg _)

theorem average_periodic {n : ℕ} (f : ℕ → ℝ) (hf : Function.Periodic f n) (k : ℕ) :
    Function.Periodic (fun j => average f j k) n := by
  intro j
  simp only [average_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [show j + n + r = j + r + n by omega, hf]

theorem average_square_le {n : ℕ} (f : ℕ → ℝ) (hf : Function.Periodic f n)
    (j : ℕ) {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    (k : ℝ) * average f j k ^ 2 ≤ ∑ r ∈ Finset.range n, f r ^ 2 := by
  have hc := sq_sum_le_card_mul_sum_sq (s := Finset.range k) (f := fun r => f (j + r))
  simp only [Finset.card_range] at hc
  have hs : (∑ r ∈ Finset.range k, f (j + r) ^ 2) ≤
      ∑ r ∈ Finset.range n, f r ^ 2 := by
    calc
      _ ≤ ∑ r ∈ Finset.range n, f (j + r) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkn) (fun r _ _ => sq_nonneg _)
      _ = _ := periodic_sum_shift (n := n) (fun r => f r ^ 2)
        (fun r => congrArg (fun x : ℝ => x ^ 2) (hf r)) j
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [average_eq]
  have he : (k : ℝ) * ((∑ r ∈ Finset.range k, f (j + r)) / k) ^ 2 =
      (∑ r ∈ Finset.range k, f (j + r)) ^ 2 / k := by field_simp
  rw [he]
  exact ((div_le_iff₀ hkR).mpr (by nlinarith)).trans hs

theorem window_fourth_sum_le {n : ℕ} (hn : 0 < n) (f : ℕ → ℝ)
    (hperiod : Function.Periodic f n) (hf : ∀ j, 0 ≤ f j) (j : ℕ) :
    (∑ k ∈ Finset.range n, average f j (k + 1) ^ 4) ≤
      4 * (∑ r ∈ Finset.range n, f r ^ 2) * maximal hn f j ^ 2 := by
  apply sum_fourth_le _ (Finset.sum_nonneg (fun r _ => sq_nonneg _)) (sq_nonneg _)
  · intro k hk
    exact pow_le_pow_left₀ (average_nonneg f hf j _) (average_le_maximal hn f j (by omega) (by omega)) 2
  · intro k hk
    simpa only [Nat.cast_add, Nat.cast_one] using
      average_square_le f hperiod j (show 0 < k + 1 by omega) (show k + 1 ≤ n by omega)

theorem all_window_fourth_sum_le {n : ℕ} (hn : 0 < n) (f : ℕ → ℝ)
    (hperiod : Function.Periodic f n) (hf : ∀ j, 0 ≤ f j) :
    (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, average f j (k + 1) ^ 4) ≤
      64 * (∑ r ∈ Finset.range n, f r ^ 2) ^ 2 := by
  have hw := Finset.sum_le_sum (s := Finset.range n) (fun j _ => window_fourth_sum_le hn f hperiod hf j)
  rw [← Finset.mul_sum] at hw
  have hm := mul_le_mul_of_nonneg_left (square_sum_le hn f hperiod hf)
    (by positivity : 0 ≤ 4 * ∑ r ∈ Finset.range n, f r ^ 2)
  calc
    _ ≤ _ := hw.trans hm
    _ = _ := by ring

def incrementNorm (u : ℕ → ℂ) (j : ℕ) : ℝ := ‖u (j + 1) - u j‖

theorem incrementNorm_nonneg (u : ℕ → ℂ) (j : ℕ) : 0 ≤ incrementNorm u j := norm_nonneg _

theorem incrementNorm_periodic {n : ℕ} (u : ℕ → ℂ) (hu : Function.Periodic u n) :
    Function.Periodic (incrementNorm u) n := by
  intro j
  dsimp [incrementNorm]
  rw [show j + n + 1 = j + 1 + n by omega, hu, hu]

theorem norm_chain_sum (u : ℕ → ℂ) (j k : ℕ) :
    ‖u (j + k) - u j‖ ≤ ∑ r ∈ Finset.range k, incrementNorm u (j + r) := by
  have he := Finset.sum_range_sub (fun r => u (j + r)) k
  simp only [Nat.add_zero] at he
  rw [← he]
  exact (norm_sum_le _ _).trans_eq (by
    apply Finset.sum_congr rfl
    intro r _
    simp only [incrementNorm, Nat.add_assoc])

theorem short_chord_lower {n k : ℕ} (hn : 0 < n) (hk : 2 * k ≤ n) (j : ℕ) :
    4 * (k : ℝ) / n ≤ ‖LocalPhase.regularRoot n ^ (j + k) - LocalPhase.regularRoot n ^ j‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : 2 * (k : ℝ) ≤ n := by exact_mod_cast hk
  have hs := LocalTrigonometry.scaled_sine_lower hnR (Nat.cast_nonneg k) hkR
  have hsin : 0 ≤ Real.sin ((k : ℝ) * Real.pi / n) := le_trans (by positivity) hs
  have he : LocalPhase.regularRoot n ^ (j + k) - LocalPhase.regularRoot n ^ j =
      LocalPhase.regularRoot n ^ j * (LocalPhase.regularRoot n ^ k - 1) := by
    rw [pow_add]
    ring
  rw [he, norm_mul, norm_pow, LocalChord.root_norm, one_pow, one_mul,
    GapRigidity.root_power_eq_circle]
  unfold GapRigidity.circle
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  have ha : (2 * Real.pi / (n : ℝ) * k) / 2 = (k : ℝ) * Real.pi / n := by ring
  rw [ha, abs_of_nonneg (mul_nonneg (by norm_num) hsin)]
  calc
    4 * (k : ℝ) / n = 2 * (2 * k / n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by norm_num)

theorem short_pairRatio_bound {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hshort : 2 * k ≤ n)
    (u : ℕ → ℂ) (j : ℕ) :
    ‖LocalDFT.pairRatio n u j k‖ ≤ (n : ℝ) / 4 * average (incrementNorm u) j k := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hl := short_chord_lower hn hshort j
  have hden : 0 < ‖LocalPhase.regularRoot n ^ (j + k) - LocalPhase.regularRoot n ^ j‖ :=
    lt_of_lt_of_le (by positivity) hl
  have ha := average_nonneg (incrementNorm u) (incrementNorm_nonneg u) j k
  have havg : (∑ r ∈ Finset.range k, incrementNorm u (j + r)) =
      (k : ℝ) * average (incrementNorm u) j k := by
    rw [average_eq]
    field_simp
  have hnum := norm_chain_sum u j k
  rw [havg] at hnum
  rw [LocalDFT.pairRatio, norm_div]
  apply (div_le_iff₀ hden).mpr
  have hh := mul_le_mul_of_nonneg_left hl (mul_nonneg (by positivity : 0 ≤ (n : ℝ) / 4) ha)
  have he : ((n : ℝ) / 4 * average (incrementNorm u) j k) * (4 * k / n) =
      (k : ℝ) * average (incrementNorm u) j k := by field_simp
  rw [he] at hh
  exact hnum.trans hh

theorem pairRatio_reverse {n h : ℕ} (hn : 0 < n) (hh : h ≤ n)
    (u : ℕ → ℂ) (hu : Function.Periodic u n) (j : ℕ) :
    LocalDFT.pairRatio n u (j + h) (n - h) = LocalDFT.pairRatio n u j h := by
  dsimp [LocalDFT.pairRatio]
  rw [show j + h + (n - h) = j + n by omega, hu j,
    pow_add, LocalDFT.regularRoot_pow hn, mul_one]
  rw [show u j - u (j + h) = -(u (j + h) - u j) by ring,
    show LocalPhase.regularRoot n ^ j - LocalPhase.regularRoot n ^ (j + h) =
      -(LocalPhase.regularRoot n ^ (j + h) - LocalPhase.regularRoot n ^ j) by ring,
    neg_div_neg_eq]

theorem offset_sum_reverse {n h : ℕ} (hn : 0 < n) (hh : h ≤ n)
    (u : ℕ → ℂ) (hu : Function.Periodic u n) :
    (∑ j ∈ Finset.range n, ‖LocalDFT.pairRatio n u j h‖ ^ 4) =
      ∑ j ∈ Finset.range n, ‖LocalDFT.pairRatio n u j (n - h)‖ ^ 4 := by
  have hp := AntipodalLog.pairRatio_periodic hn u hu (n - h)
  calc
    _ = ∑ j ∈ Finset.range n, ‖LocalDFT.pairRatio n u (h + j) (n - h)‖ ^ 4 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.add_comm h j, pairRatio_reverse hn hh u hu j]
    _ = _ := periodic_sum_shift (n := n) (fun j => ‖LocalDFT.pairRatio n u j (n - h)‖ ^ 4)
      (fun j => congrArg (fun x : ℂ => ‖x‖ ^ 4) (hp j)) h

theorem fourthEnergy_le_increment_square {n : ℕ} (hn : 0 < n)
    (u : ℕ → ℂ) (hu : Function.Periodic u n) :
    AntipodalLog.fourthEnergy n u ≤
      (n : ℝ) ^ 4 / 4 * (∑ j ∈ Finset.range n, incrementNorm u j ^ 2) ^ 2 := by
  let f := incrementNorm u
  let G (h : ℕ) := ∑ j ∈ Finset.range n, ‖LocalDFT.pairRatio n u j h‖ ^ 4
  let B (h : ℕ) := (n : ℝ) ^ 4 / 256 * ∑ j ∈ Finset.range n, average f j h ^ 4
  have hB (h : ℕ) : 0 ≤ B h := by dsimp [B]; positivity
  have hshort (h : ℕ) (hh : 0 < h) (hs : 2 * h ≤ n) : G h ≤ B h := by
    have hb := Finset.sum_le_sum (s := Finset.range n) (fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (short_pairRatio_bound hn hh hs u j) 4)
    have he : (∑ j ∈ Finset.range n,
        ((n : ℝ) / 4 * average (incrementNorm u) j h) ^ 4) = B h := by
      simp only [mul_pow]
      rw [← Finset.mul_sum]
      dsimp [B, f]
      congr 1
      ring
    exact hb.trans_eq he
  have hpair (h : ℕ) (hh : h ∈ Finset.Ico 1 n) : G h ≤ B h + B (n - h) := by
    obtain ⟨hl, hu'⟩ := Finset.mem_Ico.mp hh
    by_cases hs : 2 * h ≤ n
    · exact (hshort h (by omega) hs).trans (le_add_of_nonneg_right (hB _))
    · have hr := hshort (n - h) (by omega) (by omega)
      have he : G h = G (n - h) := offset_sum_reverse hn (by omega) u hu
      rw [he]
      exact hr.trans (le_add_of_nonneg_left (hB _))
  have hreflect : (∑ h ∈ Finset.Ico 1 n, B (n - h)) = ∑ h ∈ Finset.Ico 1 n, B h := by
    have he := Finset.sum_Ico_reflect B 1 (m := n) (n := n) (by omega)
    simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel] using he
  have hall := Finset.sum_le_sum hpair
  rw [Finset.sum_add_distrib, hreflect] at hall
  have herase : (Finset.range n).erase 0 = Finset.Ico 1 n := by
    ext h
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
    omega
  have hQ : AntipodalLog.fourthEnergy n u ≤ ∑ h ∈ Finset.Ico 1 n, B h := by
    dsimp [AntipodalLog.fourthEnergy]
    rw [herase]
    change (∑ h ∈ Finset.Ico 1 n, G h) / 2 ≤ _
    linarith
  have hext : (∑ h ∈ Finset.Ico 1 n, B h) ≤ ∑ h ∈ Finset.Ico 1 (n + 1), B h :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega))
      (fun h _ _ => hB h)
  have hfull : (∑ h ∈ Finset.Ico 1 (n + 1), B h) =
      (n : ℝ) ^ 4 / 256 *
        ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, average f j (k + 1) ^ 4 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    dsimp [B]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.add_comm 1 k]
  have hw := all_window_fourth_sum_le hn f (incrementNorm_periodic u hu) (incrementNorm_nonneg u)
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ (n : ℝ) ^ 4 / 256)
  calc
    _ ≤ _ := hQ.trans hext
    _ = _ := hfull
    _ ≤ _ := hm
    _ = _ := by dsimp [f]; ring

theorem periodize_increment_square {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    (∑ j ∈ Finset.range n, incrementNorm (periodize hn c) j ^ 2) =
      ∑ j, Complex.normSq (FiniteFourierLift.difference hn c j) := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => incrementNorm (periodize hn c) j ^ 2) n]
  apply Finset.sum_congr rfl
  intro j _
  simp only [incrementNorm, periodize, FiniteFourierLift.difference,
    FiniteFourierLift.successor, Nat.mod_eq_of_lt j.isLt, Complex.normSq_eq_norm_sq]

/-- The actual ordered-pair quartic energy is controlled by the cyclic square energy.
The factor one half in `fourthEnergy` is retained. -/
theorem fourthEnergy_le_difference_square {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    AntipodalLog.fourthEnergy n (periodize hn c) ≤
      (n : ℝ) ^ 4 / 4 * (∑ j, Complex.normSq (FiniteFourierLift.difference hn c j)) ^ 2 := by
  simpa only [periodize_increment_square] using
    fourthEnergy_le_increment_square hn (periodize hn c) (periodize_periodic hn c)

/-- For the actual Schur lift, the quartic energy has the required order n⁻². -/
theorem canonicalLift_fourthEnergy_le {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ) :
    AntipodalLog.fourthEnergy n (periodize (by omega) (SchurLift.canonicalLift q)) ≤
      16 * Real.pi ^ 4 / (n : ℝ) ^ 2 * SchurLiftBounds.meanSquare q ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hs := SchurLiftBounds.difference_energy_le hn q
  have hS : 0 ≤ ∑ j, Complex.normSq
      (FiniteFourierLift.difference (show 0 < n by omega) (SchurLift.canonicalLift q) j) :=
    Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)
  have hpow := pow_le_pow_left₀ hS hs 2
  have hm := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (n : ℝ) ^ 4 / 4)
  calc
    _ ≤ _ := (fourthEnergy_le_difference_square (by omega) (SchurLift.canonicalLift q)).trans hm
    _ = _ := by field_simp; ring

theorem canonicalLift_fourthEnergy_le_of_bound {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ)
    {A : ℝ} (hA : 0 ≤ A) (hq : ∀ j, |q j| ≤ A) :
    AntipodalLog.fourthEnergy n (periodize (by omega) (SchurLift.canonicalLift q)) ≤
      16 * Real.pi ^ 4 / (n : ℝ) ^ 2 * A ^ 4 := by
  have hs := SchurLiftBounds.meanSquare_le_of_bound (by omega) q hA hq
  have hb := pow_le_pow_left₀ (SchurLiftBounds.meanSquare_nonneg q) hs 2
  have hm := mul_le_mul_of_nonneg_left hb
    (by positivity : 0 ≤ 16 * Real.pi ^ 4 / (n : ℝ) ^ 2)
  calc
    _ ≤ _ := (canonicalLift_fourthEnergy_le hn q).trans hm
    _ = _ := by ring

end Erdos1045.EventualExact.QuarticWindowBound

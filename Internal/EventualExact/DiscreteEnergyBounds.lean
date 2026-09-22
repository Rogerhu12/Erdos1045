import EventualExact.SchurOperatorBounds
import EventualExact.QuarticWindowBound

/-! Exact unshifted spectra and uniform estimates for the actual pair energy. -/

noncomputable section
open scoped BigOperators

namespace Erdos1045.EventualExact.DiscreteEnergy

open Complex FourierMultiplier FiniteFourierLift SchurSpectrum
local notation "conj" => (starRingEnd ℂ)

def weight (n p : ℕ) : ℝ := (p : ℝ) * ((n : ℝ) - p)

theorem weight_nonneg {n p : ℕ} (hp : p ≤ n) : 0 ≤ weight n p := by
  unfold weight
  exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hp))

theorem weight_pos {n p : ℕ} (hp : 0 < p) (hpn : p < n) : 0 < weight n p := by
  unfold weight
  exact mul_pos (by exact_mod_cast hp) (sub_pos.mpr (by exact_mod_cast hpn))

theorem pairEnergy_spectrum {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    pairEnergy hn c = (n : ℝ) / 2 * ∑ p : Fin n, weight n p * normSq (coefficient c p) := by
  let F (p : ℕ) := weight n p * normSq (coefficient c ⟨p % n, Nat.mod_lt _ hn⟩)
  have hF0 : F 0 = 0 := by simp [F, weight]
  have hFn : F n = 0 := by simp [F, weight]
  have hshift : (∑ p ∈ Finset.range n, F (p + 1)) = ∑ p ∈ Finset.range n, F p := by
    have h₁ := Finset.sum_range_succ F n
    have h₂ := Finset.sum_range_succ' F n
    rw [hFn, add_zero] at h₁
    rw [hF0, add_zero] at h₂
    exact h₂.symm.trans h₁
  have hterm (p : ℕ) (hp : p < n) :
      ((p : ℝ) + 1) * ((n : ℝ) - ((p : ℝ) + 1)) * normSq (centerCoefficient hn c p) =
        F (p + 1) := by
    by_cases he : p + 1 = n
    · have heR : (p : ℝ) + 1 = n := by exact_mod_cast he
      simp [heR, he, hFn]
    · have hlt : p + 1 < n := by omega
      have hc : centerCoefficient hn c p = coefficient c ⟨p + 1, hlt⟩ := by
        rw [centerCoefficient_eq]
        rfl
      simp only [F, weight, Nat.cast_add, Nat.cast_one, Nat.mod_eq_of_lt hlt, hc]
  have hA : pairEnergy hn c = LocalSpectrum.fullA n (centerCoefficient hn c) := by
    exact (LocalDFT.energyA_eq_fourier ClosedFourier.dftInversion hn _ (periodize_periodic hn c)).trans
      (LocalHessian.fullA_eq_geometric hn (ClosedFourier.orthogonality n hn) _).symm
  rw [hA]
  unfold LocalSpectrum.fullA
  rw [Finset.sum_congr rfl (fun p hp => hterm p (Finset.mem_range.mp hp)), hshift]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range F n]
  apply Finset.sum_congr rfl
  intro p _
  simp only [F, Nat.mod_eq_of_lt p.isLt]

theorem parseval {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    (∑ j, normSq (c j)) = (n : ℝ) * ∑ p, normSq (coefficient c p) := by
  have he := SchurOperatorBounds.synthesis_normSq hn (coefficient c)
  simpa only [synthesis_coefficient hn] using he

theorem synthesis_pairing {n : ℕ} (hn : 0 < n) (a b : Fin n → ℂ) :
    (∑ j, synthesis a j * conj (synthesis b j)) =
      (n : ℂ) * ∑ p, a p * conj (b p) := by
  simp only [synthesis, map_sum, map_mul]
  rw [LocalFourier.sum_bilinear]
  simp_rw [character_orthogonality hn]
  simp [Finset.mul_sum, mul_comm, mul_left_comm]

theorem pairing_parseval {n : ℕ} (hn : 0 < n) (c d : Fin n → ℂ) :
    (∑ j, c j * conj (d j)) =
      (n : ℂ) * ∑ p, coefficient c p * conj (coefficient d p) := by
  have he := synthesis_pairing hn (coefficient c) (coefficient d)
  simpa only [synthesis_coefficient hn] using he

theorem difference_spectrum {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    (∑ j, normSq (difference hn c j)) = (n : ℝ) *
      ∑ p : Fin n, normSq (differenceSymbol n p) * normSq (coefficient c p) := by
  rw [parseval hn]
  simp only [coefficient_difference hn, normSq_mul, mul_comm]

theorem symbol_norm_reflect {n p : ℕ} (hp : p ≤ n) (hn : 0 < n) :
    ‖differenceSymbol n (n - p)‖ = ‖differenceSymbol n p‖ := by
  have he : LocalPhase.regularRoot n ^ p * (LocalPhase.regularRoot n ^ (n - p) - 1) =
      -(LocalPhase.regularRoot n ^ p - 1) := by
    rw [mul_sub, ← pow_add, Nat.add_sub_of_le hp, LocalDFT.regularRoot_pow hn]
    ring
  have hh := congrArg norm he
  simpa only [norm_mul, norm_pow, ClosedFourier.root_norm, one_pow, one_mul,
    norm_neg, differenceSymbol] using hh

theorem symbol_norm_upper (n p : ℕ) :
    ‖differenceSymbol n p‖ ≤ 2 * Real.pi * p / n := by
  rw [differenceSymbol, GapRigidity.root_power_eq_circle]
  have he : GapRigidity.circle 0 = 1 := by simp [GapRigidity.circle]
  rw [← he]
  have hb := GapRigidity.circle_lipschitz ((2 * Real.pi / n) * p) 0
  rw [sub_zero, abs_of_nonneg (by positivity : 0 ≤ (2 * Real.pi / (n : ℝ)) * p)] at hb
  convert hb using 1
  ring

theorem symbol_norm_le_weight {n p : ℕ} (hn : 0 < n) (hp : p ≤ n) :
    ‖differenceSymbol n p‖ ≤ 4 * Real.pi / (n : ℝ) ^ 2 * weight n p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpR : (p : ℝ) ≤ n := by exact_mod_cast hp
  by_cases hs : 2 * p ≤ n
  · have hsR : 2 * (p : ℝ) ≤ n := by exact_mod_cast hs
    refine (symbol_norm_upper n p).trans ?_
    unfold weight
    apply (le_of_mul_le_mul_right ?_ (sq_pos_of_pos hnR))
    field_simp
    nlinarith [Real.pi_pos, mul_nonneg (Nat.cast_nonneg (α := ℝ) p) (by linarith : 0 ≤ (n : ℝ) - 2 * p)]
  · rw [← symbol_norm_reflect hp hn]
    refine (symbol_norm_upper n (n - p)).trans ?_
    rw [Nat.cast_sub hp]
    unfold weight
    apply (le_of_mul_le_mul_right ?_ (sq_pos_of_pos hnR))
    field_simp
    have hsR : (n : ℝ) ≤ 2 * p := by exact_mod_cast (show n ≤ 2 * p by omega)
    nlinarith [Real.pi_pos, mul_nonneg (sub_nonneg.mpr hpR) (by linarith : 0 ≤ 2 * (p : ℝ) - n)]

def rootWeight (n p : ℕ) : ℝ := Real.sqrt ((n : ℝ) / 2 * weight n p)

theorem rootWeight_nonneg (n p : ℕ) : 0 ≤ rootWeight n p := Real.sqrt_nonneg _

theorem rootWeight_sq {n p : ℕ} (hp : p ≤ n) :
    rootWeight n p ^ 2 = (n : ℝ) / 2 * weight n p :=
  Real.sq_sqrt (mul_nonneg (by positivity) (weight_nonneg hp))

theorem pairEnergy_squares {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    pairEnergy hn c = ∑ p : Fin n, (rootWeight n p * ‖coefficient c p‖) ^ 2 := by
  rw [pairEnergy_spectrum hn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [mul_pow, rootWeight_sq p.isLt.le, normSq_eq_norm_sq]
  ring

/-- A complex form of (3.14), valid without the half-period restriction. -/
theorem difference_pairing_le {n : ℕ} (hn : 0 < n) (c d : Fin n → ℂ) :
    ‖∑ j, c j * conj (difference hn d j)‖ ≤
      8 * Real.pi / (n : ℝ) ^ 2 * Real.sqrt (pairEnergy hn c) * Real.sqrt (pairEnergy hn d) := by
  let x (p : Fin n) := rootWeight n p * ‖coefficient c p‖
  let y (p : Fin n) := rootWeight n p * ‖coefficient d p‖
  have hpoint (p : Fin n) : (n : ℝ) *
      ‖coefficient c p * conj (coefficient (difference hn d) p)‖ ≤
      (8 * Real.pi / (n : ℝ) ^ 2) * (x p * y p) := by
    rw [coefficient_difference hn, norm_mul, norm_conj, norm_mul]
    have hs := mul_le_mul_of_nonneg_left (symbol_norm_le_weight hn p.isLt.le)
      (by positivity : 0 ≤ (n : ℝ) * ‖coefficient c p‖ * ‖coefficient d p‖)
    have hxy : x p * y p = (n : ℝ) / 2 * weight n p *
        ‖coefficient c p‖ * ‖coefficient d p‖ := by
      dsimp [x, y]
      rw [show rootWeight n p * ‖coefficient c p‖ * (rootWeight n p * ‖coefficient d p‖) =
        rootWeight n p ^ 2 * ‖coefficient c p‖ * ‖coefficient d p‖ by ring, rootWeight_sq p.isLt.le]
    rw [hxy]
    calc
      _ = (n : ℝ) * ‖coefficient c p‖ * ‖coefficient d p‖ * ‖differenceSymbol n p‖ := by ring
      _ ≤ _ := hs
      _ = _ := by ring
  have hsum : ‖∑ j, c j * conj (difference hn d j)‖ ≤
      (8 * Real.pi / (n : ℝ) ^ 2) * ∑ p : Fin n, x p * y p := by
    rw [pairing_parseval hn, norm_mul, Complex.norm_natCast]
    calc
      _ ≤ (n : ℝ) * ∑ p : Fin n,
          ‖coefficient c p * conj (coefficient (difference hn d) p)‖ := by
        gcongr
        exact norm_sum_le _ _
      _ ≤ _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_le_sum (fun p _ => hpoint p)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ x y
  have hx : (∑ p, x p ^ 2) = pairEnergy hn c := (pairEnergy_squares hn c).symm
  have hy : (∑ p, y p ^ 2) = pairEnergy hn d := (pairEnergy_squares hn d).symm
  rw [hx, hy] at hcs
  calc
    _ ≤ _ := hsum.trans (mul_le_mul_of_nonneg_left hcs (by positivity))
    _ = _ := by ring

def realEnergy {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) : ℝ :=
  pairEnergy hn (fun j => (f j : ℂ))

theorem real_difference_pairing_le {n : ℕ} (hn : 0 < n) (f θ : Fin n → ℝ) :
    |∑ j, f j * (θ (successor hn j) - θ j)| ≤
      8 * Real.pi / (n : ℝ) ^ 2 * Real.sqrt (realEnergy hn f) * Real.sqrt (realEnergy hn θ) := by
  have h := difference_pairing_le hn (fun j => (f j : ℂ)) (fun j => (θ j : ℂ))
  have he : (∑ j, (f j : ℂ) * conj (difference hn (fun j => (θ j : ℂ)) j)) =
      ((∑ j, f j * (θ (successor hn j) - θ j) : ℝ) : ℂ) := by
    simp [difference]
  rw [he, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

theorem symbol_normSq_le_weight {n p : ℕ} (hn : 0 < n) (hp : p ≤ n) :
    normSq (differenceSymbol n p) ≤ 4 * Real.pi ^ 2 / (n : ℝ) ^ 2 * weight n p := by
  have h₁ := symbol_norm_upper n p
  have h₂ := symbol_norm_upper n (n - p)
  rw [symbol_norm_reflect hp hn, Nat.cast_sub hp] at h₂
  have hm := mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity : 0 ≤ 2 * Real.pi * p / n)
  rw [normSq_eq_norm_sq]
  calc
    _ ≤ _ := by simpa only [pow_two] using hm
    _ = _ := by unfold weight; ring

theorem weight_reflect {n p : ℕ} (hp : p ≤ n) : weight n (n - p) = weight n p := by
  simp only [weight, Nat.cast_sub hp]
  ring

theorem weight_le_symbol_normSq_short {n p : ℕ} (hn : 0 < n) (hp : 2 * p ≤ n) :
    weight n p ≤ (n : ℝ) ^ 3 / 16 * normSq (differenceSymbol n p) := by
  by_cases hp0 : p = 0
  · simp [hp0, weight, differenceSymbol]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hlo := QuarticWindowBound.short_chord_lower hn hp 0
  simp only [Nat.zero_add, pow_zero] at hlo
  change 4 * (p : ℝ) / n ≤ ‖differenceSymbol n p‖ at hlo
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * (p : ℝ) / n) hlo 2
  have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg (n : ℝ))
  have he : (n : ℝ) ^ 2 * (4 * (p : ℝ) / n) ^ 2 = 16 * (p : ℝ) ^ 2 := by field_simp; norm_num
  rw [he, ← normSq_eq_norm_sq] at hmul
  have hm := mul_le_mul_of_nonneg_left hmul hnR.le
  unfold weight
  nlinarith [mul_nonneg hnR.le (by nlinarith : 0 ≤ (p : ℝ) ^ 2 - p)]

theorem weight_le_symbol_normSq {n p : ℕ} (hn : 0 < n) (hp : p ≤ n) :
    weight n p ≤ (n : ℝ) ^ 3 / 16 * normSq (differenceSymbol n p) := by
  by_cases hs : 2 * p ≤ n
  · exact weight_le_symbol_normSq_short hn hs
  · have h := weight_le_symbol_normSq_short hn (show 2 * (n - p) ≤ n by omega)
    rwa [weight_reflect hp, normSq_eq_norm_sq, symbol_norm_reflect hp hn, ← normSq_eq_norm_sq] at h

theorem difference_energy_le {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    (n : ℝ) ^ 2 * (∑ j, normSq (difference hn c j)) ≤ 8 * Real.pi ^ 2 * pairEnergy hn c := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun p (_ : p ∈ (Finset.univ : Finset (Fin n))) =>
    mul_le_mul_of_nonneg_right (symbol_normSq_le_weight hn p.isLt.le) (normSq_nonneg (coefficient c p)))
  have hm := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ (n : ℝ) ^ 3)
  rw [difference_spectrum hn, pairEnergy_spectrum hn]
  calc
    _ = (n : ℝ) ^ 3 * ∑ p : Fin n, normSq (differenceSymbol n p) * normSq (coefficient c p) := by ring
    _ ≤ _ := hm
    _ = _ := by
      simp only [mul_assoc, ← Finset.mul_sum]
      field_simp
      ring

theorem pairEnergy_le_difference {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    pairEnergy hn c ≤ (n : ℝ) ^ 3 / 32 * ∑ j, normSq (difference hn c j) := by
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun p (_ : p ∈ (Finset.univ : Finset (Fin n))) =>
    mul_le_mul_of_nonneg_right (weight_le_symbol_normSq hn p.isLt.le) (normSq_nonneg (coefficient c p)))
  have hm := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ (n : ℝ) / 2)
  rw [difference_spectrum hn, pairEnergy_spectrum hn]
  calc
    _ ≤ _ := hm
    _ = _ := by simp only [mul_assoc, ← Finset.mul_sum]; ring

theorem halfPeriodic_coefficient_odd_zero {m : ℕ} (hm : 0 < m) (c : Fin (2 * m) → ℂ)
    (hc : HalfPeriodic hm c) (p : Fin (2 * m)) (hp : Odd p.val) : coefficient c p = 0 := by
  have hpmod := Nat.odd_iff.mp hp
  have hp1 : 1 ≤ p.val := by omega
  have heven : Even (p.val - 1) := Nat.even_iff.mpr (by omega)
  have hz := centerCoefficient_even_zero hm c hc (p.val - 1) heven
  rw [centerCoefficient_eq, Nat.sub_add_cancel hp1] at hz
  exact hz

theorem halfPeriodic_poincare {m : ℕ} (hm : 0 < m) (c : Fin (2 * m) → ℂ)
    (hc : HalfPeriodic hm c) (hmean : ∑ j, c j = 0) :
    ((2 * m : ℕ) - 2 : ℝ) * (∑ j, normSq (c j)) ≤ pairEnergy (by omega) c := by
  let : NeZero (2 * m) := ⟨by omega⟩
  have hzero : coefficient c 0 = 0 := by rw [coefficient_zero, hmean, zero_div]
  have hp (p : Fin (2 * m)) :
      2 * ((2 * m : ℕ) - 2 : ℝ) * normSq (coefficient c p) ≤
        weight (2 * m) p * normSq (coefficient c p) := by
    by_cases hp0 : p = 0
    · simp [hp0, hzero]
    by_cases hodd : Odd p.val
    · simp [halfPeriodic_coefficient_odd_zero hm c hc p hodd]
    have hpv : p.val ≠ 0 := Fin.val_ne_zero_iff.mpr hp0
    have hodd' : p.val % 2 ≠ 1 := fun h => hodd (Nat.odd_iff.mpr h)
    have hmod : p.val % 2 = 0 := by have := Nat.mod_lt p.val (by omega : 0 < 2); omega
    have hlo : 2 ≤ p.val := by omega
    have hhi : p.val + 2 ≤ 2 * m := by omega
    have hloR : (2 : ℝ) ≤ p := by exact_mod_cast hlo
    have hhiR : (p : ℝ) + 2 ≤ (2 * m : ℕ) := by exact_mod_cast hhi
    have hw : 2 * ((2 * m : ℕ) - 2 : ℝ) ≤ weight (2 * m) p := by
      unfold weight
      nlinarith [mul_nonneg (sub_nonneg.mpr hloR) (by linarith : 0 ≤ ((2 * m : ℕ) : ℝ) - p - 2)]
    exact mul_le_mul_of_nonneg_right hw (normSq_nonneg _)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hp p)
  have hm' := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ ((2 * m : ℕ) : ℝ) / 2)
  rw [pairEnergy_spectrum, parseval (by omega)]
  calc
    _ = ((2 * m : ℕ) : ℝ) / 2 * ∑ p : Fin (2 * m),
        2 * ((2 * m : ℕ) - 2 : ℝ) * normSq (coefficient c p) := by rw [← Finset.mul_sum]; ring
    _ ≤ _ := hm'

end Erdos1045.EventualExact.DiscreteEnergy

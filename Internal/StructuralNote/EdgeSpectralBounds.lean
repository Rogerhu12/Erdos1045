import StructuralNote.EdgeWeights
import EventualExact.SchurWeightBounds
import Mathlib.Analysis.Convex.Deriv

/-! Uniform bounds for the full edge spectrum, including frequency two. -/

noncomputable section

namespace StructuralNote.EdgeSpectralBounds

open Set EdgeWeights

def logSinc (t : ℝ) : ℝ := Real.log (Real.sin t) - Real.log t

def logSincFirst (t : ℝ) : ℝ := Real.cos t / Real.sin t - 1 / t

def logSincSecond (t : ℝ) : ℝ := 1 / t ^ 2 - 1 / Real.sin t ^ 2

theorem logSinc_hasDerivAt {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    HasDerivAt logSinc (logSincFirst t) t := by
  unfold logSinc logSincFirst
  apply HasDerivAt.sub
  · exact (Real.hasDerivAt_sin t).log (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
  · simpa only [one_div] using Real.hasDerivAt_log ht.1.ne'

theorem logSincFirst_hasDerivAt {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    HasDerivAt logSincFirst (logSincSecond t) t := by
  have hs := (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
  have h := ((Real.hasDerivAt_cos t).div (Real.hasDerivAt_sin t) hs).sub
    ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht.1.ne')
  apply h.congr_deriv
  dsimp [logSincSecond]
  field_simp [ht.1.ne']
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem logSincSecond_nonpos {t : ℝ} (ht : t ∈ Ioo 0 Real.pi) :
    logSincSecond t ≤ 0 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hb := (sq_le_sq₀ hs.le ht.1.le).2 (Real.sin_le ht.1.le)
  exact sub_nonpos.mpr (one_div_le_one_div_of_le (sq_pos_of_pos hs) hb)

theorem logSinc_concave : ConcaveOn ℝ (Ioo 0 Real.pi) logSinc := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := logSincFirst) (f'' := logSincSecond)
    (convex_Ioo 0 Real.pi)
  · exact fun t ht => (logSinc_hasDerivAt ht).continuousAt.continuousWithinAt
  · exact fun t ht => (logSinc_hasDerivAt (interior_subset ht)).hasDerivWithinAt
  · exact fun t ht => (logSincFirst_hasDerivAt (interior_subset ht)).hasDerivWithinAt
  · exact fun t ht => logSincSecond_nonpos (interior_subset ht)

/-- Balancing two arguments with fixed sum increases their sinc product. -/
theorem sinc_product_balancing {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < Real.pi) (hax : a ≤ x) (hxb : x ≤ b) :
    (Real.sin a / a) * (Real.sin b / b) ≤
      (Real.sin x / x) * (Real.sin (a + b - x) / (a + b - x)) := by
  rcases hab.eq_or_lt with he | hab
  · have hx : x = a := by linarith
    subst b
    subst x
    simp
  have hba : 0 < b - a := sub_pos.mpr hab
  let A := (b - x) / (b - a)
  let B := (x - a) / (b - a)
  have hA : 0 ≤ A := div_nonneg (sub_nonneg.mpr hxb) hba.le
  have hB : 0 ≤ B := div_nonneg (sub_nonneg.mpr hax) hba.le
  have hAB : A + B = 1 := by dsimp [A, B]; field_simp; ring
  have hx : A * a + B * b = x := by dsimp [A, B]; field_simp; ring
  have hy : B * a + A * b = a + b - x := by dsimp [A, B]; field_simp; ring
  have h1 := logSinc_concave.2 (show a ∈ Ioo 0 Real.pi by constructor <;> linarith)
    (show b ∈ Ioo 0 Real.pi by constructor <;> linarith) hA hB hAB
  have h2 := logSinc_concave.2 (show a ∈ Ioo 0 Real.pi by constructor <;> linarith)
    (show b ∈ Ioo 0 Real.pi by constructor <;> linarith) hB hA (by linarith)
  simp only [smul_eq_mul, hx, hy] at h1 h2
  have hlog : logSinc a + logSinc b ≤ logSinc x + logSinc (a + b - x) := by
    nlinarith [congrArg (fun z => z * logSinc a) hAB,
      congrArg (fun z => z * logSinc b) hAB]
  have hp (t : ℝ) (ht : t ∈ Ioo 0 Real.pi) : 0 < Real.sin t / t :=
    div_pos (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2) ht.1
  have pa := hp a ⟨ha, by linarith⟩
  have pb := hp b ⟨by linarith, hb⟩
  have px := hp x ⟨by linarith, by linarith⟩
  have py := hp (a + b - x) ⟨by linarith, by linarith⟩
  apply (Real.log_le_log_iff (mul_pos pa pb) (mul_pos px py)).mp
  have he (t : ℝ) (ht : t ∈ Ioo 0 Real.pi) :
      Real.log (Real.sin t / t) = logSinc t :=
    Real.log_div (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne' ht.1.ne'
  rw [Real.log_mul pa.ne' pb.ne', Real.log_mul px.ne' py.ne',
    he a ⟨ha, by linarith⟩, he b ⟨by linarith, hb⟩,
    he x ⟨by linarith, by linarith⟩, he (a + b - x) ⟨by linarith, by linarith⟩]
  exact hlog

def endpointBudget (x : ℝ) : ℝ := (x - 1) * Real.sin (Real.pi / x) ^ 2

def endpointBudgetFirst (x : ℝ) : ℝ :=
  Real.sin (Real.pi / x) ^ 2 -
    2 * Real.pi * (x - 1) / x ^ 2 * Real.sin (Real.pi / x) * Real.cos (Real.pi / x)

theorem endpointBudget_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt endpointBudget (endpointBudgetFirst x) x := by
  have h := ((hasDerivAt_id x).sub_const 1).mul
    ((((hasDerivAt_const x Real.pi).div (hasDerivAt_id x) hx).sin).pow 2)
  apply h.congr_deriv
  dsimp [endpointBudgetFirst]
  field_simp
  ring

theorem endpointBudgetFirst_nonpos {x : ℝ} (hx : 4 ≤ x) : endpointBudgetFirst x ≤ 0 := by
  have hx0 : 0 < x := by linarith
  let a := Real.pi / x
  have ha : 0 < a := div_pos Real.pi_pos hx0
  have hap : a ≤ Real.pi / 4 := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hx
  have ha2 : a ^ 2 ≤ 2 / 3 := by
    calc
      _ ≤ (Real.pi / 4) ^ 2 := (sq_le_sq₀ ha.le (by positivity)).2 hap
      _ ≤ _ := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hc : (2 / 3 : ℝ) ≤ Real.cos a := by
    have h := Real.one_sub_sq_div_two_le_cos (x := a)
    linarith
  have hb : (3 / 2 : ℝ) ≤ 2 * (x - 1) / x := by
    apply (le_div_iff₀ hx0).2
    linarith
  have hprod : 1 ≤ (2 * (x - 1) / x) * Real.cos a := by
    have h := mul_le_mul hb hc (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (by linarith : 0 ≤ 2 * (x - 1) / x)
    norm_num at h
    exact h
  have hsin := Real.sin_le ha.le
  have hs : 0 ≤ Real.sin a := (Real.sin_pos_of_pos_of_lt_pi ha (by linarith [Real.pi_pos])).le
  have hm := mul_le_mul_of_nonneg_left hprod ha.le
  have hinside : Real.sin a - a * (2 * (x - 1) / x) * Real.cos a ≤ 0 := by
    nlinarith
  have he : endpointBudgetFirst x = Real.sin a *
      (Real.sin a - a * (2 * (x - 1) / x) * Real.cos a) := by
    dsimp [endpointBudgetFirst, a]
    field_simp
  rw [he]
  exact mul_nonpos_of_nonneg_of_nonpos hs hinside

theorem endpointBudget_antitone : AntitoneOn endpointBudget (Ici 4) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := endpointBudgetFirst) (convex_Ici 4)
  · intro x hx
    have hx4 : 4 ≤ x := hx
    exact (endpointBudget_hasDerivAt (by linarith)).continuousAt.continuousWithinAt
  · intro x hx
    have hx4 : 4 ≤ x := interior_subset hx
    exact (endpointBudget_hasDerivAt (by linarith)).hasDerivWithinAt
  · exact fun x hx => endpointBudgetFirst_nonpos (interior_subset hx)

theorem endpointBudget_le {x : ℝ} (hx : 4 ≤ x) :
    (x - 1) * Real.sin (Real.pi / x) ^ 2 ≤ 3 / 2 := by
  have h := endpointBudget_antitone (by simp) hx hx
  have h4 : endpointBudget 4 = 3 / 2 := by
    rw [endpointBudget, Real.sin_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  exact h.trans_eq h4

theorem endpoint_denominator_pos {n : ℕ} (hn : 4 ≤ n) :
    0 < 3 - 4 * Real.sin (Real.pi / n) ^ 2 := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have h := endpointBudget_le hnR
  have hm := mul_nonneg (show 0 ≤ (n : ℝ) - 4 by linarith)
    (sq_nonneg (Real.sin (Real.pi / n)))
  nlinarith

theorem sine_triple (a : ℝ) :
    Real.sin (3 * a) = Real.sin a * (3 - 4 * Real.sin a ^ 2) := by
  rw [show 3 * a = 2 * a + a by ring, Real.sin_add, Real.sin_two_mul, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq a,
    congrArg (fun t => t * Real.sin a) (Real.sin_sq_add_cos_sq a)]

theorem weight_two_quotient {n : ℕ} (hn : 4 ≤ n) :
    weight n 2 = ((n : ℝ) - 3) / n *
      Real.sin (Real.pi / n) / Real.sin (3 * Real.pi / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : Real.sin (Real.pi / n) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    apply (div_lt_iff₀ hnR).2
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  rw [weight, if_pos (show Active n 2 from ⟨by omega, by omega⟩)]
  norm_num only [Nat.cast_ofNat]
  field_simp
  ring

/-- The exact extremal-frequency value in Lemma 4.2. -/
theorem weight_two_eq {n : ℕ} (hn : 4 ≤ n) :
    weight n 2 = ((n : ℝ) - 3) /
      ((n : ℝ) * (3 - 4 * Real.sin (Real.pi / n) ^ 2)) := by
  rw [weight_two_quotient hn, show 3 * Real.pi / (n : ℝ) = 3 * (Real.pi / n) by ring,
    sine_triple]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : Real.sin (Real.pi / n) ≠ 0 := by
    apply (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
    apply (div_lt_iff₀ hnR).2
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  field_simp

theorem weight_two_le {n : ℕ} (hn : 4 ≤ n) :
    weight n 2 ≤ ((n : ℝ) - 1) / (3 * n) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hbudget := endpointBudget_le hnR
  have hd := endpoint_denominator_pos hn
  rw [weight_two_eq hn]
  apply (div_le_div_iff₀ (mul_pos (by linarith : (0 : ℝ) < n) hd) (by positivity)).2
  have h := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ (n : ℝ) by positivity)
  nlinarith

theorem weight_le_two {n p : ℕ} (hp : Active n p) : weight n p ≤ weight n 2 := by
  have hn4 : 4 ≤ n := by have := hp.1; have := hp.2; omega
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.1
  have hpnR : (p : ℝ) + 2 ≤ n := by exact_mod_cast hp.2
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  let a := Real.pi / n
  have ha : 0 < a := div_pos Real.pi_pos (by linarith)
  have hna : (n : ℝ) * a = Real.pi := by dsimp [a]; field_simp
  have ha3 : 0 < Real.sin (3 * a) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    nlinarith
  have hs : 0 < Real.sin a := by
    apply Real.sin_pos_of_pos_of_lt_pi ha
    nlinarith
  have hsm : 0 < Real.sin (((p : ℝ) - 1) * a) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by nlinarith)
    nlinarith
  have hsp : 0 < Real.sin (((p : ℝ) + 1) * a) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by nlinarith)
    nlinarith
  have hcomp := sinc_product_balancing ha
    (show a ≤ ((n : ℝ) - 3) * a by nlinarith)
    (show ((n : ℝ) - 3) * a < Real.pi by nlinarith)
    (show a ≤ ((p : ℝ) - 1) * a by nlinarith)
    (show ((p : ℝ) - 1) * a ≤ ((n : ℝ) - 3) * a by nlinarith)
  have hsinb : Real.sin (((n : ℝ) - 3) * a) = Real.sin (3 * a) := by
    rw [show ((n : ℝ) - 3) * a = Real.pi - 3 * a by nlinarith]
    exact Real.sin_pi_sub _
  have hsiny : Real.sin (((n : ℝ) - p - 1) * a) = Real.sin (((p : ℝ) + 1) * a) := by
    rw [show ((n : ℝ) - p - 1) * a = Real.pi - ((p : ℝ) + 1) * a by nlinarith]
    exact Real.sin_pi_sub _
  rw [show a + ((n : ℝ) - 3) * a - ((p : ℝ) - 1) * a =
    ((n : ℝ) - p - 1) * a by ring, hsinb, hsiny, div_mul_div_comm, div_mul_div_comm] at hcomp
  have hcross := (div_le_div_iff₀
    (show 0 < a * (((n : ℝ) - 3) * a) by
      exact mul_pos ha (mul_pos (by linarith) ha))
    (show 0 < (((p : ℝ) - 1) * a) * (((n : ℝ) - p - 1) * a) by
      apply mul_pos <;> apply mul_pos <;> linarith)).mp hcomp
  have hproduct : ((p : ℝ) - 1) * ((n : ℝ) - p - 1) * Real.sin a * Real.sin (3 * a) ≤
      ((n : ℝ) - 3) * Real.sin (((p : ℝ) - 1) * a) * Real.sin (((p : ℝ) + 1) * a) := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos ha)).mp
    convert hcross using 1 <;> ring
  rw [weight_two_quotient hn4, weight, if_pos hp]
  rw [show ((p : ℝ) - 1) * Real.pi / n = ((p : ℝ) - 1) * a by dsimp [a]; ring,
    show ((p : ℝ) + 1) * Real.pi / n = ((p : ℝ) + 1) * a by dsimp [a]; ring,
    show 3 * Real.pi / (n : ℝ) = 3 * a by dsimp [a]; ring]
  change (((p : ℝ) - 1) * ((n : ℝ) - p - 1) / n) * Real.sin a ^ 2 /
      (Real.sin (((p : ℝ) - 1) * a) * Real.sin (((p : ℝ) + 1) * a)) ≤
    ((n : ℝ) - 3) / n * Real.sin a / Real.sin (3 * a)
  apply (div_le_div_iff₀ (mul_pos hsm hsp) ha3).2
  have hm := mul_le_mul_of_nonneg_right hproduct (show 0 ≤ Real.sin a / n by positivity)
  convert hm using 1 <;> ring

/-- The sharp uniform bound in (4.12), for every full-spectrum frequency. -/
theorem weight_le_s_over_three {n : ℕ} (hn : 3 ≤ n) (p : ℕ) :
    weight n p ≤ (((n : ℝ) - 1) / n) / 3 := by
  by_cases hp : Active n p
  · have hn4 : 4 ≤ n := by have := hp.1; have := hp.2; omega
    have h := (weight_le_two hp).trans (weight_two_le hn4)
    simpa only [div_div, mul_comm (n : ℝ) 3] using h
  · rw [weight_eq_zero hp]
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg (div_nonneg (by linarith) (by linarith)) (by norm_num)

theorem weight_le_rational {n p : ℕ} (hp : Active n p) :
    weight n p ≤ (n : ℝ) / (((p : ℝ) + 1) * ((n : ℝ) - p + 1)) := by
  rcases active_bounds hp with ⟨hn, hp1, hpn, hnp⟩
  have hleft : 0 < (n : ℝ) - (p - 1) := by linarith
  have hright : 0 < (n : ℝ) - (p + 1) := by linarith
  have hplus : 0 < (n : ℝ) - p + 1 := by linarith
  have hnN : 0 < n := by exact_mod_cast hn
  have hden1 := Erdos1045.EventualExact.SchurWeights.sin_grid_lower hnN hp1.le
    (by linarith : (p : ℝ) - 1 ≤ n)
  have hden2 := Erdos1045.EventualExact.SchurWeights.sin_grid_lower hnN
    (by linarith : (0 : ℝ) ≤ p + 1) hpn.le
  have hprod := mul_le_mul hden1 hden2
    (by positivity : 0 ≤ ((p : ℝ) + 1) * ((n : ℝ) - (p + 1)) * Real.pi / (n : ℝ) ^ 2)
    (le_trans (by positivity) hden1)
  have hs1 : 0 < Real.sin (((p : ℝ) - 1) * Real.pi / n) :=
    lt_of_lt_of_le (by positivity) hden1
  have hs2 : 0 < Real.sin (((p : ℝ) + 1) * Real.pi / n) :=
    lt_of_lt_of_le (by positivity) hden2
  have hsq := Real.sin_sq_le_sq (x := Real.pi / n)
  rw [weight, if_pos hp]
  apply (div_le_iff₀ (mul_pos hs1 hs2)).2
  calc
    _ ≤ (((p : ℝ) - 1) * ((n : ℝ) - p - 1) / n) * (Real.pi / n) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (n : ℝ) / (((p : ℝ) + 1) * ((n : ℝ) - p + 1)) *
        ((((p : ℝ) - 1) * ((n : ℝ) - (p - 1)) * Real.pi / (n : ℝ) ^ 2) *
        (((p : ℝ) + 1) * ((n : ℝ) - (p + 1)) * Real.pi / (n : ℝ) ^ 2)) := by
      field_simp [hn.ne', hplus.ne']
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)

theorem weight_le_endpoint_sum {n p : ℕ} (hp : p ≤ n) :
    weight n p ≤ 1 / ((p : ℝ) + 1) + 1 / ((n - p : ℕ) + 1 : ℝ) := by
  by_cases ha : Active n p
  · rcases active_bounds ha with ⟨hn, _, _, hnp⟩
    have hplus : 0 < (n : ℝ) - p + 1 := by linarith
    rw [Nat.cast_sub hp]
    refine (weight_le_rational ha).trans ?_
    calc
      _ ≤ ((n : ℝ) + 2) / (((p : ℝ) + 1) * ((n : ℝ) - p + 1)) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp [hplus.ne']; ring
  · rw [weight_eq_zero ha]
    positivity

/-- A uniform endpoint tail bound, with no parity hypothesis on n or p. -/
theorem weight_le_two_div_min {n p : ℕ} (hp : p ≤ n) :
    weight n p ≤ 2 / ((min p (n - p) : ℕ) + 1 : ℝ) := by
  have hmin1 : ((min p (n - p) : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.min_le_left p (n - p)
  have hmin2 : ((min p (n - p) : ℕ) : ℝ) ≤ (n - p : ℕ) := by
    exact_mod_cast Nat.min_le_right p (n - p)
  have hmpos : 0 < ((min p (n - p) : ℕ) : ℝ) + 1 := by positivity
  have h1 := one_div_le_one_div_of_le hmpos (by linarith :
    ((min p (n - p) : ℕ) : ℝ) + 1 ≤ (p : ℝ) + 1)
  have h2 := one_div_le_one_div_of_le hmpos (by linarith :
    ((min p (n - p) : ℕ) : ℝ) + 1 ≤ (n - p : ℕ) + 1)
  have h := (weight_le_endpoint_sum hp).trans (add_le_add h1 h2)
  calc
    _ ≤ 1 / (((min p (n - p) : ℕ) : ℝ) + 1) +
        1 / (((min p (n - p) : ℕ) : ℝ) + 1) := h
    _ = _ := by ring

end StructuralNote.EdgeSpectralBounds

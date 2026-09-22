import Erdos1045.ClosedGenerating

/-!
The differentiated Laurent difference quotient follows from a recurrence for
the coefficient tails. Two shifts of absolutely convergent geometric series
avoid any interchange of a conditionally convergent double sum.
-/

namespace Erdos1045.ExteriorClassical

open scoped BigOperators
open ExteriorBoundary FaberFourier
noncomputable section

private theorem bounded_geometric_summable {T : ℕ → ℂ} {A : ℝ} {x : ℂ}
    (hx : ‖x‖ < 1) (hT : ∀ k, ‖T k‖ ≤ A) :
    Summable (fun k => x ^ k * T k) := by
  have hs := (summable_geometric_of_norm_lt_one (by simpa using hx : ‖‖x‖‖ < 1)).mul_right A
  apply Summable.of_norm
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  simpa only [norm_mul, norm_pow] using
    mul_le_mul_of_nonneg_left (hT k) (pow_nonneg (norm_nonneg x) k)

private theorem bounded_weighted_geometric_summable {T : ℕ → ℂ} {A : ℝ} {x : ℂ}
    (hx : ‖x‖ < 1) (hT : ∀ k, ‖T k‖ ≤ A) :
    Summable (fun k : ℕ => (k : ℂ) * x ^ k * T k) := by
  have hs := (summable_pow_mul_geometric_of_norm_lt_one 1
    (by simpa using hx : ‖‖x‖‖ < 1)).mul_right A
  apply Summable.of_norm
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  simpa only [norm_mul, norm_pow, Complex.norm_natCast, pow_one] using
    mul_le_mul_of_nonneg_left (hT k)
      (show (0 : ℝ) ≤ (k : ℝ) * ‖x‖ ^ k by positivity)

private theorem tail_series_norm_le {a : ℕ → ℂ} (ha : Summable (fun m => ‖a m‖))
    (θ : ℝ) (k : ℕ) :
    ‖series (tailCoefficients a k) θ‖ ≤ ∑' m, ‖a m‖ := by
  have ht : Summable (fun m => ‖a (m + k)‖) :=
    ha.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hs : Summable (fun m => ‖a (m + k) * character m θ‖) := by
    simpa only [norm_mul, norm_character, mul_one] using ht
  have hb := norm_tsum_le_tsum_norm hs
  simp only [norm_mul, norm_character, mul_one] at hb
  have he := ha.sum_add_tsum_nat_add k
  have hn : 0 ≤ ∑ m ∈ Finset.range k, ‖a m‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  exact hb.trans (by linarith)

private theorem tail_series_succ {a : ℕ → ℂ} (ha : Summable (fun m => ‖a m‖))
    (θ : ℝ) (k : ℕ) :
    series (tailCoefficients a (k + 1)) θ =
      unit θ * (series (tailCoefficients a k) θ - a k) := by
  have hu : unit θ ≠ 0 := by
    intro h
    have hn := norm_unit θ
    rw [h, norm_zero] at hn
    norm_num at hn
  have ht : Summable (fun m => ‖a (m + k)‖) :=
    ha.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hs : Summable (fun m => a (m + k) * character m θ) := by
    apply Summable.of_norm
    simpa only [norm_mul, norm_character, mul_one] using ht
  have he := hs.tsum_eq_zero_add
  simp only [Nat.zero_add, show character 0 θ = 1 by
    rw [character_eq_unit_inv_pow, pow_zero], mul_one] at he
  have htshift : (∑' m, a (m + 1 + k) * character (m + 1) θ) =
      (unit θ)⁻¹ * series (tailCoefficients a (k + 1)) θ := by
    simp only [series, tailCoefficients, character_eq_unit_inv_pow, pow_succ]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    rw [Nat.add_assoc]
    ring
  rw [htshift] at he
  change series (tailCoefficients a k) θ = _ at he
  rw [he]
  simp [hu]

private theorem weighted_tsum_recurrence {T a : ℕ → ℂ} {u x : ℂ}
    (hF : Summable (fun k => x ^ k * T k))
    (hS : Summable (fun k : ℕ => (k : ℂ) * x ^ k * T k))
    (hL : Summable (fun k => x ^ k * a k))
    (hD : Summable (fun k : ℕ => (k : ℂ) * x ^ k * a k))
    (hrec : ∀ k, T (k + 1) = u * (T k - a k)) :
    (1 - u * x) ^ 2 * (∑' k : ℕ, (k : ℂ) * x ^ k * T k) =
      u * x * (T 0 - (∑' k, x ^ k * a k) -
        (1 - u * x) * (∑' k : ℕ, (k : ℂ) * x ^ k * a k)) := by
  let F := ∑' k, x ^ k * T k
  let S := ∑' k : ℕ, (k : ℂ) * x ^ k * T k
  let L := ∑' k, x ^ k * a k
  let D := ∑' k : ℕ, (k : ℂ) * x ^ k * a k
  have hFid : F = T 0 + u * x * (F - L) := by
    calc
      F = T 0 + ∑' k, x ^ (k + 1) * T (k + 1) := by
        simpa only [pow_zero, one_mul] using hF.tsum_eq_zero_add
      _ = T 0 + ∑' k, u * x * (x ^ k * T k - x ^ k * a k) := by
        congr 1
        apply tsum_congr
        intro k
        rw [hrec, pow_succ]
        ring
      _ = T 0 + u * x * (F - L) := by
        rw [tsum_mul_left, hF.tsum_sub hL]
  have hSid : S = u * x * (S + F - (D + L)) := by
    calc
      S = ∑' k : ℕ, ((k : ℂ) + 1) * x ^ (k + 1) * T (k + 1) := by
        simpa only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_add, Nat.cast_one]
          using hS.tsum_eq_zero_add
      _ = ∑' k : ℕ, u * x * (((k : ℂ) * x ^ k * T k + x ^ k * T k) -
          ((k : ℂ) * x ^ k * a k + x ^ k * a k)) := by
        apply tsum_congr
        intro k
        rw [hrec, pow_succ]
        ring
      _ = u * x * (S + F - (D + L)) := by
        rw [tsum_mul_left, (hS.add hF).tsum_sub (hD.add hL),
          hS.tsum_add hF, hD.tsum_add hL]
  change (1 - u * x) ^ 2 * S = u * x * (T 0 - L - (1 - u * x) * D)
  linear_combination (u * x) * hFid + (1 - u * x) * hSid

/-- The Laurent difference quotient identity, with no analytic input beyond
absolute summability of the Laurent coefficients. -/
theorem divided_difference_derivative_proved (a : ℕ → ℂ) (ha : SobolevCoefficients a)
    (c : ℝ) (hc : 0 < c) (r : ℝ) (hr : 1 < r) (θ t : ℝ) :
    series (radialCoefficients (1 / r)
      (firstOrder (coefficient c a (fun _ : Fin 1 => θ) 0))) t =
      let v := (r : ℂ) * unit t
      v * (laurentDerivative a v * (v - unit θ) - (laurent a v - laurent a (unit θ))) /
        ((c : ℂ) * (v - unit θ) ^ 2) := by
  let v : ℂ := (r : ℂ) * unit t
  let u : ℂ := unit θ
  let x : ℂ := v⁻¹
  let T : ℕ → ℂ := fun k => series (tailCoefficients a k) θ
  let A : ℝ := ∑' k, ‖a k‖
  let D : ℂ := ∑' k : ℕ, (k : ℂ) * x ^ k * a k
  let S : ℂ := ∑' k : ℕ, (k : ℂ) * x ^ k * T k
  have hvnorm : ‖v‖ = r := radial_norm (by linarith) t
  have hv : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hvnorm
    linarith
  have hu : u ≠ 0 := by
    intro h
    have hn : ‖u‖ = 1 := norm_unit θ
    rw [h, norm_zero] at hn
    norm_num at hn
  have hx : ‖x‖ < 1 := by
    dsimp [x]
    rw [norm_inv, hvnorm]
    exact (inv_lt_one₀ (by linarith)).2 hr
  have habs := ClosedSeries.laurent_absolute a ha
  have ha_bound (k : ℕ) : ‖a k‖ ≤ A :=
    habs.le_tsum k (fun _ _ => norm_nonneg _)
  have hT_bound (k : ℕ) : ‖T k‖ ≤ A := tail_series_norm_le habs θ k
  have hF := bounded_geometric_summable hx hT_bound
  have hS := bounded_weighted_geometric_summable hx hT_bound
  have hL := bounded_geometric_summable hx ha_bound
  have hD := bounded_weighted_geometric_summable hx ha_bound
  have hrec (k : ℕ) : T (k + 1) = u * (T k - a k) := tail_series_succ habs θ k
  have he := weighted_tsum_recurrence hF hS hL hD hrec
  have hTzero : T 0 = laurent a u := by
    simp only [T, series, tailCoefficients, Nat.add_zero, character_eq_unit_inv_pow,
      laurent, u]
  have hLval : (∑' k, x ^ k * a k) = laurent a v := by
    simp only [laurent, x, mul_comm]
  have hder : laurentDerivative a v = -x * D := by
    unfold laurentDerivative
    dsimp [D]
    rw [← tsum_mul_left, ← tsum_neg]
    apply tsum_congr
    intro k
    dsimp [x]
    rw [pow_succ]
    ring
  have hxp (k : ℕ) : ((1 / r : ℝ) : ℂ) ^ k * character k t = x ^ k := by
    rw [character_eq_unit_inv_pow, ← mul_pow]
    congr 1
    simp [x, v, one_div, mul_comm]
  have hsource : series (radialCoefficients (1 / r)
      (firstOrder (coefficient c a (fun _ : Fin 1 => θ) 0))) t =
        (c : ℂ)⁻¹ * u⁻¹ * S := by
    unfold series
    dsimp only [radialCoefficients, firstOrder, coefficient, S, T]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [character_eq_unit_inv_pow 1 θ, pow_one]
    change _ = (c : ℂ)⁻¹ * u⁻¹ * ((k : ℂ) * x ^ k * series (tailCoefficients a k) θ)
    rw [← hxp]
    dsimp [u]
    ring
  rw [hTzero, hLval] at he
  change (1 - u * x) ^ 2 * S = u * x *
    (laurent a u - laurent a v - (1 - u * x) * D) at he
  change _ = v * (laurentDerivative a v * (v - u) - (laurent a v - laurent a u)) /
    ((c : ℂ) * (v - u) ^ 2)
  rw [hsource, hder]
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hdiff : v - u ≠ 0 := radial_difference_ne_zero hr θ t
  dsimp only [x] at he ⊢
  field_simp at he ⊢
  linear_combination he

/-- All four classical Laurent-series fields are now theorems. -/
theorem classicalLaurentSeries : ClassicalLaurentSeries where
  geometric_summable := geometric_summable_proved
  geometric_identity := geometric_identity_proved
  derivative_summable := derivative_summable_proved
  divided_difference_derivative := divided_difference_derivative_proved

end
end Erdos1045.ExteriorClassical

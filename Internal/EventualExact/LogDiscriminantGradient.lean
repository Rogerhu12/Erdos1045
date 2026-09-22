import EventualExact.LocalGradientBound

/-! Identification with the real derivative and the exact regular reference. -/

namespace Erdos1045.EventualExact.LocalGradient

open Complex Configuration ExteriorClassical CircleMatrix MatrixDefect
open scoped BigOperators ComplexConjugate
noncomputable section

theorem discriminant_update {n : ℕ} {z : Points n} (hz : Function.Injective z)
    (i : Fin n) (w : ℂ) :
    discriminant (Function.update z i w) =
      ‖(Lagrange.basis Finset.univ z i).eval w‖ ^ 2 * discriminant z := by
  rw [← vandermonde_detSq, ← vandermonde_detSq, detSq,
    vandermonde_replace_det z hz i w, map_mul]
  rw [Complex.normSq_eq_norm_sq]
  rfl

theorem realGradient_inner {n : ℕ} (z : Points n) (i : Fin n) (v : ℂ) :
    inner ℝ (realGradient z i) v =
      2 * (conj (FeketeStationarity.nodeGradient z i) * v).re := by
  simp [Complex.inner, realGradient, Complex.mul_re]
  ring

/-- This is the derivative of the original discriminant, with only coordinate `i` moving. -/
theorem hasDerivAt_log_discriminant {n : ℕ} {z : Points n}
    (hz : Function.Injective z) (i : Fin n) {p : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (hp : HasDerivAt p v t) (hpt : p t = z i) :
    HasDerivAt (fun s => Real.log (discriminant (Function.update z i (p s))))
      (inner ℝ (realGradient z i) v) t := by
  have hb : (Lagrange.basis Finset.univ z i).eval (p t) = 1 := by
    rw [hpt, Lagrange.eval_basis_self hz.injOn (Finset.mem_univ i)]
  have hd : HasDerivAt (fun s => (Lagrange.basis Finset.univ z i).eval (p s))
      (conj (FeketeStationarity.nodeGradient z i) * v) t := by
    have he := (FeketeStationarity.basis_hasDerivAt hz i).hasFDerivAt.restrictScalars ℝ
    rw [← hpt] at he
    simpa [Function.comp_def, mul_comm] using he.comp_hasDerivAt t hp
  have hD := (discriminant_pos z hz).ne'
  have hne : ‖(Lagrange.basis Finset.univ z i).eval (p t)‖ ^ 2 * discriminant z ≠ 0 := by
    simpa only [hb, norm_one, one_pow, one_mul] using hD
  have hl := (hd.norm_sq.mul_const (discriminant z)).log hne
  simp only [hb, norm_one, one_pow, one_mul, Complex.inner, map_one, mul_one,
    mul_div_cancel_right₀ _ hD] at hl
  rw [realGradient_inner]
  convert hl using 1
  ext s
  rw [discriminant_update hz]

theorem inverse_complement_pair {x y : ℂ} (hx : x ≠ 1) (hxy : x * y = 1) :
    (1 - x)⁻¹ + (1 - y)⁻¹ = 1 := by
  have hy : y ≠ 1 := by intro h; rw [h, mul_one] at hxy; exact hx hxy
  have hxe : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hye : 1 - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  field_simp
  linear_combination -hxy

theorem regular_reciprocal_sum {n : ℕ} (hn : 0 < n) :
    (∑ h ∈ Finset.Ico 1 n, (1 - LocalPhase.regularRoot n ^ h)⁻¹) =
      ((n : ℂ) - 1) / 2 := by
  let w := LocalPhase.regularRoot n
  let f (h : ℕ) := (1 - w ^ h)⁻¹
  have hs := sum_Ico_reflect n f
  have hp : (∑ h ∈ Finset.Ico 1 n, (f h + f (n - h))) = ((n : ℂ) - 1) := by
    have he : (∑ h ∈ Finset.Ico 1 n, (f h + f (n - h))) = ∑ _h ∈ Finset.Ico 1 n, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro h hh
      have ht := Finset.mem_Ico.mp hh
      apply inverse_complement_pair (LocalDFT.regularRoot_power_ne_one hn (by omega) ht.2)
      rw [← pow_add, Nat.add_sub_of_le (by omega : h ≤ n)]
      exact LocalDFT.regularRoot_pow hn
    rw [he]
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [Finset.sum_add_distrib, hs] at hp
  change (∑ h ∈ Finset.Ico 1 n, f h) = _
  linear_combination hp / 2

theorem realGradient_regular {n : ℕ} (hn : 0 < n) (i : Fin n) :
    realGradient (fun j : Fin n => LocalPhase.regularRoot n ^ (j : ℕ)) i =
      ((n : ℂ) - 1) * LocalPhase.regularRoot n ^ (i : ℕ) := by
  let w := LocalPhase.regularRoot n
  have hw : Function.Periodic (fun j : ℕ => w ^ j) n := by
    intro j
    dsimp only
    rw [pow_add, LocalDFT.regularRoot_pow hn, mul_one]
  have hnorm : Complex.normSq (w ^ (i : ℕ)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow, LocalChord.root_norm, one_pow, one_pow]
  have hconj : conj ((w ^ (i : ℕ))⁻¹) = w ^ (i : ℕ) := by
    rw [Complex.inv_def, hnorm]
    simp
  have he (h : ℕ) : (w ^ (i : ℕ) - w ^ ((i : ℕ) + h))⁻¹ =
      (w ^ (i : ℕ))⁻¹ * (1 - w ^ h)⁻¹ := by
    rw [pow_add, show w ^ (i : ℕ) - w ^ (i : ℕ) * w ^ h =
      w ^ (i : ℕ) * (1 - w ^ h) by ring, mul_inv_rev, mul_comm]
  rw [realGradient, nodeGradient_eq_lags hn _ hw]
  simp only [he, ← Finset.mul_sum, map_mul, hconj]
  dsimp only [w]
  rw [regular_reciprocal_sum hn]
  simp only [map_div₀, map_sub, map_natCast, map_one, map_ofNat]
  ring

end
end Erdos1045.EventualExact.LocalGradient

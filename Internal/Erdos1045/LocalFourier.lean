import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-!
# Finite Fourier calculations for the local Hessian

The only external input in this file is the standard orthogonality formula for
powers of a primitive root of unity. Its statement is independent of polygon
perturbations, quadratic forms, and the manuscript's identities (6.6)--(6.8).
The geometric sums and their two quadratic moments are proved below.
-/

namespace Erdos1045.LocalFourier

open Complex
open scoped BigOperators
noncomputable section

/-- The classical finite character orthogonality formulas. For the application
`ω = exp (2 * π * I / n)` and `n > 0`. These formulas are the only classical
Fourier input: none mentions a perturbation or the manuscript's energies. -/
structure ClassicalOrthogonality (n : ℕ) (ω : ℂ) : Prop where
  sum_pow : ∀ m : ℕ, (∑ h ∈ Finset.range n, ω ^ (h * m)) =
    if n ∣ m then (n : ℂ) else 0
  sum_mul_conj : ∀ r s : ℕ,
    (∑ h ∈ Finset.range n, ω ^ (h * r) * (starRingEnd ℂ) (ω ^ (h * s))) =
      if r % n = s % n then (n : ℂ) else 0

/-- The polynomial `(z^k - 1)/(z-1)`, defined also at `z=1`. -/
def geom (k : ℕ) (z : ℂ) : ℂ := ∑ r ∈ Finset.range k, z ^ r

@[simp] theorem geom_at_one (k : ℕ) : geom k 1 = k := by
  simp [geom]

theorem geom_mul_sub_one (k : ℕ) (z : ℂ) :
    geom k z * (z - 1) = z ^ k - 1 := by
  exact geom_sum_mul z k

theorem geom_eq_div {z : ℂ} (hz : z ≠ 1) (k : ℕ) :
    geom k z = (z ^ k - 1) / (z - 1) := by
  apply (eq_div_iff (sub_ne_zero.mpr hz)).2
  exact geom_mul_sub_one k z

/-- Reordering a finite bilinear Fourier calculation. -/
theorem sum_bilinear {ι κ τ : Type*} (s : Finset ι) (t : Finset κ)
    (u : Finset τ) (a : ι → ℂ) (b : κ → ℂ)
    (φ : τ → ι → ℂ) (ψ : τ → κ → ℂ) :
    (∑ j ∈ u, (∑ k ∈ s, a k * φ j k) * (∑ l ∈ t, b l * ψ j l)) =
      ∑ k ∈ s, ∑ l ∈ t, (a k * b l) * (∑ j ∈ u, φ j k * ψ j l) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A finite Parseval calculation expressed in terms of the explicit characters. -/
theorem synthesis_normSq {n : ℕ} {ω : ℂ} (H : ClassicalOrthogonality n ω)
    (s : Finset ℕ) (hs : ∀ k ∈ s, k < n) (a : ℕ → ℂ) :
    (∑ j ∈ Finset.range n, normSq (∑ k ∈ s, a k * ω ^ (j * k))) =
      (n : ℝ) * ∑ k ∈ s, normSq (a k) := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  simp_rw [← Complex.mul_conj, map_sum, map_mul]
  rw [sum_bilinear]
  simp_rw [H.sum_mul_conj]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hmod (l : ℕ) (hl : l ∈ s) : k % n = l % n ↔ k = l := by
    rw [Nat.mod_eq_of_lt (hs k hk), Nat.mod_eq_of_lt (hs l hl)]
  calc
    (∑ l ∈ s, (a k * star (a l)) *
        (if k % n = l % n then (n : ℂ) else 0)) =
        ∑ l ∈ s, if k = l then (n : ℂ) * (a k * star (a k)) else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      simp only [hmod l hl]
      split_ifs with heq
      · subst l
        ring
      · ring
    _ = (n : ℂ) * (a k * star (a k)) := by simp [hk]

/-- The full-circle geometric-sum energy is `n*k`, by Parseval. -/
theorem geom_normSq_sum {n k : ℕ} {ω : ℂ}
    (H : ClassicalOrthogonality n ω) (hk : k ≤ n) :
    (∑ h ∈ Finset.range n, normSq (geom k (ω ^ h))) = (n : ℝ) * k := by
  have h := synthesis_normSq H (Finset.range k)
    (fun i hi => (Finset.mem_range.mp hi).trans_le hk) (fun _ => 1)
  simpa [geom, pow_mul] using h

/-- Removing the diagonal sample gives the coefficient `k*(n-k)` in (6.6). -/
theorem geom_normSq_sum_off_zero {n k : ℕ} {ω : ℂ}
    (H : ClassicalOrthogonality n ω) (hn : 0 < n) (hk : k ≤ n) :
    (∑ h ∈ (Finset.range n).erase 0, normSq (geom k (ω ^ h))) =
      (k : ℝ) * ((n : ℝ) - k) := by
  have hfull := geom_normSq_sum H hk
  have hsplit := Finset.sum_erase_add (Finset.range n)
    (fun h => normSq (geom k (ω ^ h))) (Finset.mem_range.mpr hn)
  simp only [pow_zero, geom_at_one, normSq_natCast] at hsplit
  rw [hfull] at hsplit
  nlinarith

/-- The non-conjugated product uses the divisibility, not Hermitian, orthogonality. -/
theorem geom_product_sum {n k l : ℕ} {ω : ℂ}
    (H : ClassicalOrthogonality n ω) :
    (∑ h ∈ Finset.range n, geom k (ω ^ h) * geom l (ω ^ h)) =
      ∑ r ∈ Finset.range k, ∑ s ∈ Finset.range l,
        if n ∣ r + s then (n : ℂ) else 0 := by
  have h := sum_bilinear (Finset.range k) (Finset.range l) (Finset.range n)
    (fun _ => 1) (fun _ => 1) (fun h r => ω ^ (h * r)) (fun h s => ω ^ (h * s))
  simp only [one_mul, mul_one] at h
  simp only [← pow_add, ← Nat.mul_add, H.sum_pow] at h
  simpa only [geom, ← pow_mul] using h

/-- At total degree `n`, divisibility can occur only at the two endpoints. -/
theorem paired_divisibility {n k l r s : ℕ} (_hn : 0 < n)
    (hkl : k + l = n + 2) (hr : r < k) (hs : s < l) :
    n ∣ r + s ↔ (r = 0 ∧ s = 0) ∨ (r = k - 1 ∧ s = l - 1) := by
  have hbound : r + s ≤ n := by omega
  have hdiv : n ∣ r + s ↔ r + s = 0 ∨ r + s = n := by
    constructor
    · intro hd
      rcases Nat.eq_zero_or_pos (r + s) with hz | hp
      · exact Or.inl hz
      · exact Or.inr (le_antisymm hbound (Nat.le_of_dvd hp hd))
    · rintro (hz | hz) <;> simp [hz]
  rw [hdiv]
  omega

/-- The two endpoint coefficients of `D_k D_l` both equal one. -/
theorem geom_product_sum_paired {n k l : ℕ} {ω : ℂ}
    (H : ClassicalOrthogonality n ω) (hn : 0 < n)
    (hk : 2 ≤ k) (hl : 2 ≤ l) (hkl : k + l = n + 2) :
    (∑ h ∈ Finset.range n, geom k (ω ^ h) * geom l (ω ^ h)) = 2 * n := by
  rw [geom_product_sum H]
  have hterm (r s : ℕ) (hr : r < k) (hs : s < l) :
      (if n ∣ r + s then (n : ℂ) else 0) =
        (if r = 0 then if s = 0 then (n : ℂ) else 0 else 0) +
        (if r = k - 1 then if s = l - 1 then (n : ℂ) else 0 else 0) := by
    simp only [paired_divisibility hn hkl hr hs]
    split_ifs <;> simp_all
    omega
  simp_rw [Finset.sum_congr rfl fun r hr =>
    Finset.sum_congr rfl fun s hs => hterm r s (Finset.mem_range.mp hr)
      (Finset.mem_range.mp hs)]
  simp [Finset.sum_add_distrib, show 0 < k by omega, show 0 < l by omega,
    show k - 1 < k by omega, show l - 1 < l by omega]
  ring

/-- Removing the diagonal sample gives `2*n-k*l`, including its negative sign. -/
theorem geom_product_sum_off_zero {n k l : ℕ} {ω : ℂ}
    (H : ClassicalOrthogonality n ω) (hn : 0 < n)
    (hk : 2 ≤ k) (hl : 2 ≤ l) (hkl : k + l = n + 2) :
    (∑ h ∈ (Finset.range n).erase 0, geom k (ω ^ h) * geom l (ω ^ h)) =
      (2 : ℂ) * n - k * l := by
  have hfull := geom_product_sum_paired H hn hk hl hkl
  have hsplit := Finset.sum_erase_add (Finset.range n)
    (fun h => geom k (ω ^ h) * geom l (ω ^ h)) (Finset.mem_range.mpr hn)
  simp only [pow_zero, geom_at_one] at hsplit
  rw [hfull] at hsplit
  linear_combination hsplit

/-- The frequency paired with `r` by a non-conjugated Fourier product. -/
def partner (n r : ℕ) : ℕ := if r = 0 then 0 else n - r

theorem partner_lt {n r : ℕ} (hn : 0 < n) (hr : r < n) : partner n r < n := by
  unfold partner
  split_ifs <;> omega

theorem divisibility_iff_partner {n r s : ℕ} (_hn : 0 < n)
    (hr : r < n) (hs : s < n) : n ∣ r + s ↔ s = partner n r := by
  have hsum : r + s < 2 * n := by omega
  have hd : n ∣ r + s ↔ r + s = 0 ∨ r + s = n := by
    constructor
    · rintro ⟨m, hm⟩
      have hm2 : m < 2 := by nlinarith
      interval_cases m <;> simp_all
    · rintro (h | h) <;> simp [h]
  rw [hd]
  unfold partner
  split_ifs <;> omega

/-- Non-Hermitian Parseval pairs opposite frequencies, with no conjugation. -/
theorem synthesis_product {n : ℕ} {ω : ℂ} (H : ClassicalOrthogonality n ω)
    (hn : 0 < n) (a b : ℕ → ℂ) :
    (∑ j ∈ Finset.range n,
      (∑ r ∈ Finset.range n, a r * ω ^ (j * r)) *
      (∑ s ∈ Finset.range n, b s * ω ^ (j * s))) =
      (n : ℂ) * ∑ r ∈ Finset.range n, a r * b (partner n r) := by
  rw [sum_bilinear]
  simp_rw [← pow_add, ← Nat.mul_add, H.sum_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    (∑ s ∈ Finset.range n, (a r * b s) * (if n ∣ r + s then (n : ℂ) else 0)) =
        ∑ s ∈ Finset.range n, if s = partner n r then (n : ℂ) * (a r * b s) else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      simp only [divisibility_iff_partner hn (Finset.mem_range.mp hr)
        (Finset.mem_range.mp hs)]
      split_ifs <;> ring
    _ = (n : ℂ) * (a r * b (partner n r)) := by
      simp [partner_lt hn (Finset.mem_range.mp hr)]

/-- Shifted coefficients use frequency `r=k-1` for the pair ratios. -/
def ratioFourier (n : ℕ) (ω : ℂ) (b : ℕ → ℂ) (j h : ℕ) : ℂ :=
  ∑ r ∈ Finset.range n, (b r * geom (r + 1) (ω ^ h)) * ω ^ (j * r)

/-- Exact ordered-pair version of (6.6); division by two counts each pair once.
The Fourier coefficient denoted `b r` here is the manuscript's `b_(r+1)`. -/
theorem ratio_energy {n : ℕ} {ω : ℂ} (H : ClassicalOrthogonality n ω)
    (hn : 0 < n) (b : ℕ → ℂ) :
    (∑ h ∈ (Finset.range n).erase 0,
      ∑ j ∈ Finset.range n, normSq (ratioFourier n ω b j h)) / 2 =
      (n : ℝ) / 2 * ∑ r ∈ Finset.range n,
        (r + 1 : ℝ) * ((n : ℝ) - (r + 1)) * normSq (b r) := by
  have hinner (h : ℕ) :
      (∑ j ∈ Finset.range n, normSq (ratioFourier n ω b j h)) =
        (n : ℝ) * ∑ r ∈ Finset.range n,
          normSq (b r) * normSq (geom (r + 1) (ω ^ h)) := by
    simpa [ratioFourier, normSq_mul] using synthesis_normSq H (Finset.range n)
      (fun r hr => Finset.mem_range.mp hr) (fun r => b r * geom (r + 1) (ω ^ h))
  simp_rw [hinner]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hsum : (∑ r ∈ Finset.range n,
      ∑ h ∈ (Finset.range n).erase 0, normSq (b r) * normSq (geom (r + 1) (ω ^ h))) =
      ∑ r ∈ Finset.range n, (r + 1 : ℝ) * ((n : ℝ) - (r + 1)) * normSq (b r) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [← Finset.mul_sum, geom_normSq_sum_off_zero H hn
      (show r + 1 ≤ n by have := Finset.mem_range.mp hr; omega)]
    push_cast
    ring
  rw [hsum]
  ring

theorem imaginary_sq (z : ℂ) : z.im ^ 2 = (normSq z - (z * z).re) / 2 := by
  simp only [normSq_apply, mul_re]
  ring

/-- Exact imaginary-part energy for arbitrary Fourier coefficients. Applied to
`a r = b r * D_(r+1)(ω)`, this is the unconverted geometric-sum form of (6.8). -/
theorem imaginary_synthesis_energy {n : ℕ} {ω : ℂ}
    (H : ClassicalOrthogonality n ω) (hn : 0 < n) (a : ℕ → ℂ) :
    (∑ j ∈ Finset.range n, (∑ r ∈ Finset.range n, a r * ω ^ (j * r)).im ^ 2) =
      (n : ℝ) / 2 * ((∑ r ∈ Finset.range n, normSq (a r)) -
        (∑ r ∈ Finset.range n, a r * a (partner n r)).re) := by
  simp_rw [imaginary_sq]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [synthesis_normSq H (Finset.range n) (fun r hr => Finset.mem_range.mp hr)]
  rw [← Complex.re_sum, synthesis_product H hn a a]
  simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
  ring

/-- The constant Fourier coefficient is the average; this proves the linear
cancellations used by the nonlinear estimates once the first mode is removed. -/
theorem synthesis_sum {n : ℕ} {ω : ℂ} (H : ClassicalOrthogonality n ω)
    (hn : 0 < n) (a : ℕ → ℂ) :
    (∑ j ∈ Finset.range n, ∑ r ∈ Finset.range n, a r * ω ^ (j * r)) =
      (n : ℂ) * a 0 := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, H.sum_pow]
  calc
    (∑ r ∈ Finset.range n, a r * (if n ∣ r then (n : ℂ) else 0)) =
        ∑ r ∈ Finset.range n, if r = 0 then (n : ℂ) * a 0 else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      have hd : n ∣ r ↔ r = 0 := by
        rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
      simp only [hd]
      split_ifs with hz
      · subst r
        ring
      · ring
    _ = (n : ℂ) * a 0 := by simp [hn]

theorem ratio_sum_zero {n : ℕ} {ω : ℂ} (H : ClassicalOrthogonality n ω)
    (hn : 0 < n) (b : ℕ → ℂ) (hb : b 0 = 0) (h : ℕ) :
    (∑ j ∈ Finset.range n, ratioFourier n ω b j h) = 0 := by
  simpa [ratioFourier, hb] using synthesis_sum H hn
    (fun r => b r * geom (r + 1) (ω ^ h))

/-- Exact non-conjugated pair-square identity (6.7), with shifted indexing.
Only the first Fourier mode is removed; the translation mode has zero factor. -/
theorem ratio_square_sum {n : ℕ} {ω : ℂ} (H : ClassicalOrthogonality n ω)
    (hn : 0 < n) (b : ℕ → ℂ) (hb : b 0 = 0) :
    (∑ h ∈ (Finset.range n).erase 0,
      ∑ j ∈ Finset.range n, ratioFourier n ω b j h * ratioFourier n ω b j h) / 2 =
      -(n : ℂ) / 2 * ∑ r ∈ Finset.range n,
        ((r : ℂ) - 1) * ((n : ℂ) - (r + 1)) * b r * b (partner n r) := by
  have hinner (h : ℕ) :
      (∑ j ∈ Finset.range n, ratioFourier n ω b j h * ratioFourier n ω b j h) =
        (n : ℂ) * ∑ r ∈ Finset.range n,
          (b r * b (partner n r)) *
            (geom (r + 1) (ω ^ h) * geom (partner n r + 1) (ω ^ h)) := by
    have heq := synthesis_product H hn
      (fun r => b r * geom (r + 1) (ω ^ h))
      (fun r => b r * geom (r + 1) (ω ^ h))
    simpa only [ratioFourier, mul_mul_mul_comm] using heq
  simp_rw [hinner]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hsum :
      (∑ r ∈ Finset.range n, ∑ h ∈ (Finset.range n).erase 0,
        (b r * b (partner n r)) *
          (geom (r + 1) (ω ^ h) * geom (partner n r + 1) (ω ^ h))) =
      -(∑ r ∈ Finset.range n,
        ((r : ℂ) - 1) * ((n : ℂ) - (r + 1)) * b r * b (partner n r)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hr0 : r = 0
    · simp [hr0, hb]
    · have hrn := Finset.mem_range.mp hr
      have hp : partner n r = n - r := by simp [partner, hr0]
      have hpcast : (partner n r : ℂ) = (n : ℂ) - r := by
        rw [hp, Nat.cast_sub hrn.le]
      rw [← Finset.mul_sum, geom_product_sum_off_zero H hn
        (show 2 ≤ r + 1 by omega) (show 2 ≤ partner n r + 1 by rw [hp]; omega)
        (show (r + 1) + (partner n r + 1) = n + 2 by rw [hp]; omega)]
      push_cast
      rw [hpcast]
      ring
  rw [hsum]
  ring

/-- The actual perturbation of vertices `ω^j`, using shifted Fourier indices. -/
def displacement (n : ℕ) (ω : ℂ) (b : ℕ → ℂ) (j : ℕ) : ℂ :=
  ∑ r ∈ Finset.range n, b r * ω ^ (j * (r + 1))

theorem displacement_periodic {n : ℕ} {ω : ℂ} (hω : ω ^ n = 1)
    (b : ℕ → ℂ) (j : ℕ) :
    displacement n ω b (j + n) = displacement n ω b j := by
  simp [displacement, Nat.add_mul, pow_add, pow_mul, hω]

/-- The finite geometric sum turns the Fourier expression into a genuine
vertex difference. No nonzero-denominator assumption is needed for this identity. -/
theorem ratio_mul_vertex_difference (n : ℕ) (ω : ℂ) (b : ℕ → ℂ) (j h : ℕ) :
    ratioFourier n ω b j h * (ω ^ (j + h) - ω ^ j) =
      displacement n ω b (j + h) - displacement n ω b j := by
  unfold ratioFourier displacement
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    (b r * geom (r + 1) (ω ^ h) * ω ^ (j * r)) * (ω ^ (j + h) - ω ^ j) =
        b r * ω ^ (j * (r + 1)) * (geom (r + 1) (ω ^ h) * (ω ^ h - 1)) := by
      rw [Nat.mul_add, Nat.mul_one, pow_add, pow_add]
      ring
    _ = b r * ω ^ (j * (r + 1)) * ((ω ^ h) ^ (r + 1) - 1) := by
      rw [geom_mul_sub_one]
    _ = b r * ω ^ ((j + h) * (r + 1)) - b r * ω ^ (j * (r + 1)) := by
      rw [Nat.add_mul, pow_add, pow_mul]
      ring

/-- Identification with the geometric pair ratio, not merely a formal series. -/
theorem ratio_eq_difference_quotient (n : ℕ) (ω : ℂ) (b : ℕ → ℂ) (j h : ℕ)
    (hden : ω ^ (j + h) - ω ^ j ≠ 0) :
    ratioFourier n ω b j h =
      (displacement n ω b (j + h) - displacement n ω b j) /
        (ω ^ (j + h) - ω ^ j) := by
  exact (eq_div_iff hden).2 (ratio_mul_vertex_difference n ω b j h)

/-- The perturbation is identically zero when its finite coefficient list is zero. -/
theorem displacement_zero_of_coefficients_zero {n : ℕ} (ω : ℂ) (b : ℕ → ℂ)
    (hb : ∀ r < n, b r = 0) (j : ℕ) : displacement n ω b j = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  simp [hb r (Finset.mem_range.mp hr)]

/-- The only zero-energy Fourier coefficient is the translation mode, which is
the last shifted index. This is the rigidity needed after nonlinear absorption. -/
theorem zero_pair_energy_forces_coefficients_zero {n : ℕ} {ω : ℂ}
    (H : ClassicalOrthogonality n ω) (hn : 0 < n) (b : ℕ → ℂ)
    (hlast : b (n - 1) = 0)
    (hzero : (∑ h ∈ (Finset.range n).erase 0,
      ∑ j ∈ Finset.range n, normSq (ratioFourier n ω b j h)) = 0) :
    ∀ r < n, b r = 0 := by
  have he := ratio_energy H hn b
  rw [hzero, zero_div] at he
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (∑ r ∈ Finset.range n,
      (r + 1 : ℝ) * ((n : ℝ) - (r + 1)) * normSq (b r)) = 0 := by
    have hne : (n : ℝ) / 2 ≠ 0 := by positivity
    exact (mul_eq_zero.mp he.symm).resolve_left hne
  have hnonneg (r : ℕ) (hr : r ∈ Finset.range n) :
      0 ≤ (r + 1 : ℝ) * ((n : ℝ) - (r + 1)) * normSq (b r) := by
    have hrn : (r : ℝ) + 1 ≤ n := by
      exact_mod_cast (show r + 1 ≤ n by have := Finset.mem_range.mp hr; omega)
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (normSq_nonneg _)
  intro r hr
  by_cases hlastindex : r = n - 1
  · simpa [hlastindex] using hlast
  · have hrn : (r : ℝ) + 1 < n := by
      exact_mod_cast (show r + 1 < n by omega)
    have hterm := Finset.single_le_sum hnonneg (Finset.mem_range.mpr hr)
    rw [hsum] at hterm
    have hcoef : 0 < (r + 1 : ℝ) * ((n : ℝ) - (r + 1)) := by positivity
    have hnorm : normSq (b r) = 0 := by nlinarith [normSq_nonneg (b r)]
    exact normSq_eq_zero.mp hnorm

end

end Erdos1045.LocalFourier

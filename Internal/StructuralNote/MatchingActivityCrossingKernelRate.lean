import StructuralNote.MatchingActivityCrossingVariationPressure
import StructuralNote.SolMidpointPressure
import EventualExact.SchurWeightLimit
import Mathlib.NumberTheory.Harmonic.Bounds

/-! A quantitative version of diagonal Schur-kernel growth.  Keeping a
linearly growing block of low odd frequencies retains the harmonic rate that
is lost by the fixed-head convergence argument. -/

namespace StructuralNote.MatchingActivityCrossingKernelRate

open Real Finset Erdos1045.EventualExact
open FixedDualClassificationKernel
open SolScalarGap SolMidpointPressure
open scoped BigOperators
noncomputable section

/-- On the lower half of the spectrum, every active odd Schur weight is at
least a fixed multiple of its limiting reciprocal weight. -/
theorem low_odd_weight_lower {n p : ℕ} (hpodd : Odd p) (hp3 : 3 ≤ p)
    (hhalf : 2 * (p + 1) ≤ n) :
    1 / (8 * ((p : ℝ) + 1)) ≤ SchurWeights.weight n p := by
  have hn : 4 ≤ n := by omega
  have hactive : SchurWeights.Active n p := ⟨hpodd, hp3, by omega⟩
  have hnR : (0 : ℝ) < n := by positivity
  have hpR : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hhalfR : 2 * ((p : ℝ) + 1) ≤ n := by exact_mod_cast hhalf
  let xzero : ℝ := Real.pi / n
  let xminus : ℝ := ((p : ℝ) - 1) * Real.pi / n
  let xplus : ℝ := ((p : ℝ) + 1) * Real.pi / n
  have hxzero0 : 0 ≤ xzero := by positivity
  have hxzeropi : xzero ≤ Real.pi / 2 := by
    dsimp [xzero]
    apply (div_le_iff₀ hnR).2
    nlinarith [Real.pi_pos]
  have hszeroraw := Real.mul_le_sin hxzero0 hxzeropi
  have hxzerone : xzero ≠ 0 := by positivity
  have hszero : (1 / 2 : ℝ) ≤ Real.sinc xzero := by
    rw [Real.sinc_of_ne_zero hxzerone]
    have he : (2 / Real.pi) * xzero = 2 / (n : ℝ) := by
      dsimp [xzero]
      field_simp [Real.pi_ne_zero, ne_of_gt hnR]
    rw [he] at hszeroraw
    have hx : xzero = Real.pi / n := rfl
    rw [hx]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < Real.pi / n)).2
    have hcomp : (1 / 2 : ℝ) * (Real.pi / n) ≤ 2 / n := by
      rw [show (1 / 2 : ℝ) * (Real.pi / n) = (Real.pi / 2) / n by ring]
      apply (div_le_div_iff_of_pos_right hnR).2
      nlinarith [Real.pi_lt_four]
    exact hcomp.trans (by simpa [xzero] using hszeroraw)
  have hxminus0 : 0 < xminus := by
    dsimp [xminus]
    have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    exact div_pos (mul_pos (by linarith) Real.pi_pos) hnR
  have hxminuspi : xminus < Real.pi := by
    dsimp [xminus]
    apply (div_lt_iff₀ hnR).2
    have hpcast : (p : ℝ) + 1 ≤ n / 2 := by linarith
    nlinarith [Real.pi_pos]
  have hxplus0 : 0 < xplus := by
    dsimp [xplus]
    positivity
  have hxpluspi : xplus < Real.pi := by
    dsimp [xplus]
    apply (div_lt_iff₀ hnR).2
    nlinarith [Real.pi_pos]
  have hsminuspos : 0 < Real.sinc xminus := by
    rw [Real.sinc_of_ne_zero hxminus0.ne']
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hxminus0 hxminuspi) hxminus0
  have hspluspos : 0 < Real.sinc xplus := by
    rw [Real.sinc_of_ne_zero hxplus0.ne']
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hxplus0 hxpluspi) hxplus0
  have hdenpos : 0 < Real.sinc xminus * Real.sinc xplus := mul_pos hsminuspos hspluspos
  have hdenle : Real.sinc xminus * Real.sinc xplus ≤ 1 := by
    nlinarith [Real.sinc_le_one xminus, Real.sinc_le_one xplus]
  have hfac : 1 / (2 * ((p : ℝ) + 1)) ≤
      (1 - ((p : ℝ) + 1) / n) / ((p : ℝ) + 1) := by
    rw [show 1 / (2 * ((p : ℝ) + 1)) = (1 / 2) / ((p : ℝ) + 1) by
      field_simp [ne_of_gt hpR]]
    apply (div_le_div_iff_of_pos_right hpR).2
    have hratio : ((p : ℝ) + 1) / n ≤ 1 / 2 := by
      apply (div_le_iff₀ hnR).2
      nlinarith
    linarith
  have hszerosq : (1 / 4 : ℝ) ≤ Real.sinc xzero ^ 2 := by nlinarith
  rw [SchurWeights.weight_eq_sinc hactive]
  change 1 / (8 * ((p : ℝ) + 1)) ≤
    (1 - ((p : ℝ) + 1) / n) / ((p : ℝ) + 1) *
      Real.sinc xzero ^ 2 / (Real.sinc xminus * Real.sinc xplus)
  apply (le_div_iff₀ hdenpos).2
  have hfac0 : 0 ≤ 1 / (2 * ((p : ℝ) + 1)) := by positivity
  have hfacrhs0 : 0 ≤
      (1 - ((p : ℝ) + 1) / n) / ((p : ℝ) + 1) := hfac0.trans hfac
  have hmain := mul_le_mul hfac hszerosq (by norm_num : (0 : ℝ) ≤ 1 / 4) hfacrhs0
  have hleft : 1 / (8 * ((p : ℝ) + 1)) *
      (Real.sinc xminus * Real.sinc xplus) ≤ 1 / (8 * ((p : ℝ) + 1)) := by
    exact mul_le_of_le_one_right (by positivity) hdenle
  calc
    _ ≤ 1 / (8 * ((p : ℝ) + 1)) := hleft
    _ = 1 / (2 * ((p : ℝ) + 1)) * (1 / 4) := by
      field_simp [ne_of_gt hpR]
      norm_num
    _ ≤ _ := hmain

/-- The reciprocal mass in the first `P` odd modes, with the inactive mode
`p = 1` deleted. -/
def lowOddMass (P : ℕ) : ℝ :=
  ∑ k : Fin P, if k.val = 0 then 0 else 1 / (16 * ((k : ℝ) + 1))

theorem lowOddMass_eq_harmonic {P : ℕ} (hP : 0 < P) :
    lowOddMass P = (((harmonic P : ℚ) : ℝ) - 1) / 16 := by
  have hcast : ((harmonic P : ℚ) : ℝ) =
      ∑ k ∈ range P, 1 / ((k : ℝ) + 1) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    apply sum_congr rfl
    intro k hk
    norm_num [div_eq_mul_inv]
  have hdelete : (∑ k ∈ range P, if k = 0 then 0 else 1 / ((k : ℝ) + 1)) =
      (∑ k ∈ range P, 1 / ((k : ℝ) + 1)) - 1 := by
    simp_rw [show ∀ k : ℕ, (if k = 0 then 0 else 1 / ((k : ℝ) + 1)) =
        1 / ((k : ℝ) + 1) - if k = 0 then 1 / ((k : ℝ) + 1) else 0 by
      intro k
      split <;> simp_all]
    rw [sum_sub_distrib]
    simp [hP]
  unfold lowOddMass
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => if k = 0 then 0 else 1 / (16 * ((k : ℝ) + 1))) P]
  have hscale : (∑ k ∈ range P, if k = 0 then 0 else
      1 / (16 * ((k : ℝ) + 1))) =
      (1 / 16 : ℝ) *
        ∑ k ∈ range P, if k = 0 then 0 else 1 / ((k : ℝ) + 1) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    split <;> simp_all
    ring
  rw [hscale, hdelete, ← hcast]
  ring

/-- A growing block of actual finite weights gives a quantitative harmonic
lower bound for the diagonal kernel. -/
theorem diagonal_kernel_harmonic_lower {n P : ℕ} (hP : 0 < P)
    (hsize : 4 * P ≤ n) :
    (((harmonic P : ℚ) : ℝ) - 1) / 32 ≤ finiteKernel n 0 := by
  let e : Fin P ↪ Fin n :=
    { toFun := fun k => ⟨2 * k.val + 1, by omega⟩
      inj' := by
        intro a b hab
        apply Fin.ext
        have hv := congrArg Fin.val hab
        dsimp at hv
        omega }
  have hterm (k : Fin P) :
      (if k.val = 0 then 0 else 1 / (16 * ((k : ℝ) + 1))) ≤
        SchurWeights.weight n (e k) := by
    by_cases hk : k.val = 0
    · simp [hk, SchurWeights.weight_nonneg]
    · rw [if_neg hk]
      have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
      have hlower := low_odd_weight_lower
        (n := n) (p := 2 * k.val + 1) ⟨k.val, by omega⟩ (by omega) (by omega)
      change 1 / (16 * ((k : ℝ) + 1)) ≤
        SchurWeights.weight n (2 * k.val + 1)
      convert hlower using 1
      field_simp
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
  have hterms : lowOddMass P ≤ ∑ k : Fin P, SchurWeights.weight n (e k) := by
    unfold lowOddMass
    exact sum_le_sum fun k hk => hterm k
  have hsubset :
      (∑ p ∈ univ.map e, SchurWeights.weight n p) ≤
        ∑ p : Fin n, SchurWeights.weight n p := by
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p hp hnot =>
      SchurWeights.weight_nonneg n p
  have hpartial : (∑ k : Fin P, SchurWeights.weight n (e k)) ≤
      ∑ p : Fin n, SchurWeights.weight n p := by
    simpa using hsubset
  rw [lowOddMass_eq_harmonic hP] at hterms
  unfold finiteKernel
  simp only [mul_zero, cos_zero, mul_one]
  nlinarith [hterms.trans hpartial]

/-- The diagonal kernel has an explicit logarithmic lower bound. -/
theorem diagonal_kernel_log_lower {n : ℕ} (hn : 4 ≤ n) :
    (Real.log (((n / 4 : ℕ) : ℝ) + 1) - 1) / 32 ≤ finiteKernel n 0 := by
  have hP : 0 < n / 4 := by omega
  have hsize : 4 * (n / 4) ≤ n := Nat.mul_div_le n 4
  have hk := diagonal_kernel_harmonic_lower hP hsize
  have hh := log_add_one_le_harmonic (n / 4)
  simp only [Nat.cast_add, Nat.cast_one] at hh
  nlinarith

theorem diagonal_kernel_nonneg (n : ℕ) : 0 ≤ finiteKernel n 0 := by
  unfold finiteKernel
  simp only [mul_zero, cos_zero, mul_one]
  exact mul_nonneg (by norm_num) (sum_nonneg fun p hp => SchurWeights.weight_nonneg n p)

/-- Quantitative midpoint pressure before inserting the logarithmic kernel
bound.  This is the rate-preserving form of `scaled_potential_eventually`. -/
theorem scaled_potential_kernel_lower {m : ℕ} (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hG : G hm q ≤ C₀ / (2 * m : ℝ) ^ 2) (i : Fin (2 * m)) :
    2 * finiteKernel (2 * m) 0 - C₀ / 2 ≤
      (2 * m : ℝ) * |FourierMultiplier.operator (2 * m) q i| := by
  let A := FiniteBox.amplitude (2 * m)
  let K := finiteKernel (2 * m) 0
  let N : ℝ := 2 * m
  have hA := FixedDualClassificationFinite.amplitude_ge_one (n := 2 * m) (by omega)
  have hApos : 0 < A := by dsimp [A]; positivity
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hK : 0 ≤ K := diagonal_kernel_nonneg _
  have hpress := midpoint_pressure hm q i
  have hscaled : N ^ 2 * G hm q ≤ C₀ := by
    calc
      _ ≤ N ^ 2 * (C₀ / N ^ 2) := mul_le_mul_of_nonneg_left hG (sq_nonneg N)
      _ = C₀ := by field_simp [ne_of_gt hNpos]
  have hCA : C₀ ≤ C₀ * A := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hA hC₀
  have hrem : N ^ 2 * G hm q / (2 * A) ≤ C₀ / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * A)).2
    have := hscaled.trans hCA
    nlinarith
  have hAK : K ≤ A * K := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA hK
  change 2 * A * K / N - N * G hm q / (2 * A) ≤
    |FourierMultiplier.operator (2 * m) q i| at hpress
  have hpressN := mul_le_mul_of_nonneg_left hpress hNpos.le
  have heq : N * (2 * A * K / N - N * G hm q / (2 * A)) =
      2 * A * K - N ^ 2 * G hm q / (2 * A) := by
    field_simp [ne_of_gt hNpos, ne_of_gt hApos]
  rw [heq] at hpressN
  change 2 * K - C₀ / 2 ≤ N * |FourierMultiplier.operator (2 * m) q i|
  nlinarith

/-- An `O(m⁻²)` scalar gap forces every scaled pressure to grow at the
explicit logarithmic rate retained by the diagonal kernel. -/
theorem scaled_potential_log_lower {m : ℕ} (hm : 2 ≤ m)
    (q : Fin (2 * m) → ℝ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hG : G (by omega) q ≤ C₀ / (2 * m : ℝ) ^ 2) (i : Fin (2 * m)) :
    (Real.log ((((2 * m) / 4 : ℕ) : ℝ) + 1) - 1) / 16 - C₀ / 2 ≤
      (2 * m : ℝ) * |FourierMultiplier.operator (2 * m) q i| := by
  have hk := diagonal_kernel_log_lower (n := 2 * m) (by omega)
  have hp := scaled_potential_kernel_lower (m := m) (by omega) q hC₀ hG i
  nlinarith

end
end StructuralNote.MatchingActivityCrossingKernelRate

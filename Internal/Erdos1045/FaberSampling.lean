import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic

/-!
# The two-regime weighted estimate behind Faber sampling

The input is a nonnegative radial weight whose second moment is bounded by
`K n³`.  All frequency/sampling interactions, including the two regimes
`m ≤ n` and `n ≤ m`, are proved here.  Frequencies are indexed by `k+1`.
-/

namespace Erdos1045.FaberSampling

open scoped BigOperators
noncomputable section

def moment (w : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) ^ 2 * w (k + 1)

def coupling (n : ℕ) (w : ℕ → ℝ) (k m : ℕ) : ℝ :=
  if k + 1 ≤ m then ((k + 1 : ℕ) : ℝ) ^ 2 * w (k + 1) *
    ((n : ℝ) + ((m - (k + 1) : ℕ) : ℝ) ^ 2 / n) else 0

def samplingKernel (n k m : ℕ) : ℝ :=
  if k + 1 ≤ m then ((n : ℝ) + ((m - (k + 1) : ℕ) : ℝ) ^ 2 / n) else 0

theorem coupling_eq (n k m : ℕ) (w : ℕ → ℝ) :
    coupling n w k m = ((k + 1 : ℕ) : ℝ) ^ 2 * w (k + 1) * samplingKernel n k m := by
  unfold coupling samplingKernel
  split_ifs <;> simp

theorem coupling_nonneg {n k m : ℕ} {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) :
    0 ≤ coupling n w k m := by
  have hwk := hw (k + 1)
  unfold coupling
  split_ifs <;> positivity

theorem coupling_eq_zero_of_ge {n k m : ℕ} {w : ℕ → ℝ} (h : m ≤ k) :
    coupling n w k m = 0 := by
  simp [coupling, show ¬k + 1 ≤ m by omega]

theorem moment_le_cube {w : ℕ → ℝ} (hw : ∀ j, w j ≤ 1) (m : ℕ) :
    moment w m ≤ (m : ℝ) ^ 3 := by
  calc
    moment w m ≤ ∑ k ∈ Finset.range m, (m : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hkm : ((k + 1 : ℕ) : ℝ) ≤ m := by
        exact_mod_cast (show k + 1 ≤ m by simpa using Finset.mem_range.mp hk)
      have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)) hkm 2
      have hm := mul_le_mul_of_nonneg_left (hw (k + 1))
        (sq_nonneg (((k + 1 : ℕ) : ℝ)))
      exact (by simpa using hm : ((k + 1 : ℕ) : ℝ) ^ 2 * w (k + 1) ≤
        ((k + 1 : ℕ) : ℝ) ^ 2).trans hs
    _ = (m : ℝ) ^ 3 := by simp; ring

/-- The purely real two-regime comparison. -/
theorem two_regime_bound {N M U K : ℝ} (hN : 0 < N) (hM : 0 ≤ M)
    (hU : 0 ≤ U) (hK : 1 ≤ K) (hsmall : U ≤ M ^ 3) (hlarge : U ≤ K * N ^ 3) :
    (N + M ^ 2 / N) * U ≤ 2 * K * N ^ 2 * M ^ 2 := by
  by_cases hMN : M ≤ N
  · have hs : M ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hM hMN 2
    have hf : N + M ^ 2 / N ≤ 2 * N := by
      have hd : M ^ 2 / N ≤ N := (div_le_iff₀ hN).2 (by nlinarith)
      linarith
    have hc : M ^ 3 ≤ N * M ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hMN (sq_nonneg M)]
    calc
      (N + M ^ 2 / N) * U ≤ 2 * N * U := mul_le_mul_of_nonneg_right hf hU
      _ ≤ 2 * N * (N * M ^ 2) := mul_le_mul_of_nonneg_left (hsmall.trans hc) (by positivity)
      _ ≤ 2 * K * N ^ 2 * M ^ 2 := by
        have hk := mul_le_mul_of_nonneg_right hK (show 0 ≤ 2 * N ^ 2 * M ^ 2 by positivity)
        nlinarith
  · have hNM : N ≤ M := le_of_lt (lt_of_not_ge hMN)
    have hs : N ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hN.le hNM 2
    have hf : N + M ^ 2 / N ≤ 2 * M ^ 2 / N := by
      apply (le_div_iff₀ hN).2
      have hid : (N + M ^ 2 / N) * N = N ^ 2 + M ^ 2 := by field_simp
      rw [hid]
      linarith
    calc
      (N + M ^ 2 / N) * U ≤ (2 * M ^ 2 / N) * U :=
        mul_le_mul_of_nonneg_right hf hU
      _ ≤ (2 * M ^ 2 / N) * (K * N ^ 3) :=
        mul_le_mul_of_nonneg_left hlarge (by positivity)
      _ = 2 * K * N ^ 2 * M ^ 2 := by field_simp

theorem inner_sum_le {n : ℕ} (hn : 0 < n) {w : ℕ → ℝ}
    (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∀ j, w j ≤ 1)
    {K : ℝ} (hK : 1 ≤ K) (hglobal : ∀ m, moment w m ≤ K * (n : ℝ) ^ 3)
    (m : ℕ) :
    (∑ k ∈ Finset.range m, coupling n w k m) ≤ 2 * K * (n : ℝ) ^ 2 * (m : ℝ) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hreduce : (∑ k ∈ Finset.range m, coupling n w k m) ≤
      ((n : ℝ) + (m : ℝ) ^ 2 / n) * moment w m := by
    unfold moment
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkm : k + 1 ≤ m := by simpa using Finset.mem_range.mp hk
    have hd : ((m - (k + 1) : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m (k + 1)
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((m - (k + 1) : ℕ) : ℝ)) hd 2
    have hquot := div_le_div_of_nonneg_right hs hn'.le
    have hm := mul_le_mul_of_nonneg_left (add_le_add (le_refl (n : ℝ)) hquot)
      (mul_nonneg (sq_nonneg (((k + 1 : ℕ) : ℝ))) (hw0 (k + 1)))
    simpa [coupling, hkm, mul_comm] using hm
  exact hreduce.trans (two_regime_bound hn' (by positivity)
    (Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (hw0 (k + 1)))
    hK (moment_le_cube hw1 m) (hglobal m))

theorem inner_tsum_eq (n m : ℕ) (w : ℕ → ℝ) :
    (∑' k, coupling n w k m) = ∑ k ∈ Finset.range m, coupling n w k m := by
  apply tsum_eq_sum
  intro k hk
  exact coupling_eq_zero_of_ge (Nat.le_of_not_gt (by simpa using hk))

theorem inner_summable (n m : ℕ) (w : ℕ → ℝ) : Summable (fun k => coupling n w k m) := by
  apply summable_of_ne_finset_zero (s := Finset.range m)
  intro k hk
  exact coupling_eq_zero_of_ge (Nat.le_of_not_gt (by simpa using hk))

/-- Infinite summation is justified by domination before exchanging the sums. -/
theorem weighted_double_sum_bound {n : ℕ} (hn : 0 < n) {w : ℕ → ℝ}
    (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∀ j, w j ≤ 1)
    {K : ℝ} (hK : 1 ≤ K) (hglobal : ∀ m, moment w m ≤ K * (n : ℝ) ^ 3)
    {e : ℕ → ℝ} (he : ∀ m, 0 ≤ e m)
    (henergy : Summable (fun m : ℕ => (m : ℝ) ^ 2 * e m)) :
    Summable (fun k => ∑' m, coupling n w k m * e m) ∧
      (∑' k, ∑' m, coupling n w k m * e m) ≤
        2 * K * (n : ℝ) ^ 2 * (∑' m : ℕ, (m : ℝ) ^ 2 * e m) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hrow (m : ℕ) : Summable (fun k => coupling n w k m * e m) :=
    (inner_summable n m w).mul_right (e m)
  have hroweq (m : ℕ) : (∑' k, coupling n w k m * e m) =
      (∑ k ∈ Finset.range m, coupling n w k m) * e m := by
    rw [tsum_mul_right, inner_tsum_eq]
  have hrowbound (m : ℕ) : (∑' k, coupling n w k m * e m) ≤
      (2 * K * (n : ℝ) ^ 2) * ((m : ℝ) ^ 2 * e m) := by
    rw [hroweq]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right
      (inner_sum_le hn hw0 hw1 hK hglobal m) (he m)
  have hrowsum : Summable (fun m => ∑' k, coupling n w k m * e m) :=
    Summable.of_nonneg_of_le (fun m => tsum_nonneg fun k =>
      mul_nonneg (coupling_nonneg hw0) (he m)) hrowbound
      (henergy.mul_left (2 * K * (n : ℝ) ^ 2))
  have hprod : Summable (fun p : ℕ × ℕ => coupling n w p.2 p.1 * e p.1) :=
    (summable_prod_of_nonneg (fun p => mul_nonneg (coupling_nonneg hw0) (he p.1))).2
      ⟨hrow, hrowsum⟩
  have hswapped := hprod.prod_symm
  have hcolsum := (summable_prod_of_nonneg
    (fun p : ℕ × ℕ => mul_nonneg (coupling_nonneg hw0) (he p.2))).1 hswapped
  refine ⟨hcolsum.2, ?_⟩
  have hcomm : (∑' k, ∑' m, coupling n w k m * e m) =
      ∑' m, ∑' k, coupling n w k m * e m := hprod.tsum_comm
  rw [hcomm]
  calc
    (∑' m, ∑' k, coupling n w k m * e m) ≤
        ∑' m : ℕ, (2 * K * (n : ℝ) ^ 2) * ((m : ℝ) ^ 2 * e m) :=
      Summable.tsum_le_tsum hrowbound hrowsum (henergy.mul_left _)
    _ = 2 * K * (n : ℝ) ^ 2 * (∑' m : ℕ, (m : ℝ) ^ 2 * e m) := tsum_mul_left

/-- The sampled coefficient inequality (4.3), once proved, feeds into this
fully proved weighted summation step (4.4). -/
theorem weighted_sample_bound {n : ℕ} (hn : 0 < n) {w : ℕ → ℝ}
    (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∀ j, w j ≤ 1)
    {K : ℝ} (hK : 1 ≤ K) (hglobal : ∀ m, moment w m ≤ K * (n : ℝ) ^ 3)
    {e v : ℕ → ℝ} (he : ∀ m, 0 ≤ e m) (hv : ∀ k, 0 ≤ v k)
    (henergy : Summable (fun m : ℕ => (m : ℝ) ^ 2 * e m))
    {S : ℝ} (hS : 0 ≤ S)
    (hcolumn : ∀ k, v k ≤ S * (∑' m, samplingKernel n k m * e m)) :
    Summable (fun k => ((k + 1 : ℕ) : ℝ) ^ 2 * w (k + 1) * v k) ∧
    (∑' k, ((k + 1 : ℕ) : ℝ) ^ 2 * w (k + 1) * v k) ≤
      S * (2 * K * (n : ℝ) ^ 2 * (∑' m : ℕ, (m : ℝ) ^ 2 * e m)) := by
  have hdouble := weighted_double_sum_bound hn hw0 hw1 hK hglobal he henergy
  have hmajor (k : ℕ) : ((k + 1 : ℕ) : ℝ) ^ 2 * w (k + 1) * v k ≤
      S * (∑' m, coupling n w k m * e m) := by
    have hweight : 0 ≤ ((k + 1 : ℕ) : ℝ) ^ 2 * w (k + 1) :=
      mul_nonneg (sq_nonneg _) (hw0 (k + 1))
    have h := mul_le_mul_of_nonneg_left (hcolumn k) hweight
    have heq : (∑' m, coupling n w k m * e m) =
        (((k + 1 : ℕ) : ℝ) ^ 2 * w (k + 1)) *
          (∑' m, samplingKernel n k m * e m) := by
      simp_rw [coupling_eq, mul_assoc]
      rw [tsum_mul_left, tsum_mul_left]
    rw [heq]
    convert h using 1 <;> first | rfl | ring
  have hvsum : Summable (fun k => ((k + 1 : ℕ) : ℝ) ^ 2 * w (k + 1) * v k) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (mul_nonneg (sq_nonneg _) (hw0 (k + 1))) (hv k))
      hmajor (hdouble.1.mul_left S)
  refine ⟨hvsum, ?_⟩
  calc
    _ ≤ ∑' k, S * (∑' m, coupling n w k m * e m) :=
      Summable.tsum_le_tsum hmajor hvsum (hdouble.1.mul_left S)
    _ = S * (∑' k, ∑' m, coupling n w k m * e m) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hdouble.2 hS

end

end Erdos1045.FaberSampling

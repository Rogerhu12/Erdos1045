import Erdos1045.KernelAnalytic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries

open scoped BigOperators Topology
open Filter

namespace Erdos1045.KernelWeights

noncomputable section

def rowEnergy (n : ℕ) (d : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, normalizedKernel n (d i)) / n

def rowDistance (n : ℕ) (d e : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, |d i - e i|) / n

theorem rowDistance_nonneg (n : ℕ) (d e : ℕ → ℝ) : 0 ≤ rowDistance n d e := by
  unfold rowDistance
  positivity

theorem rowEnergy_constant {n : ℕ} (hn : 0 < n) (c : ℝ) :
    rowEnergy n (fun _ => c) = normalizedKernel n c := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [rowEnergy, hn0]

/-- The local comparison is an average estimate, not a pointwise proximity assumption. -/
theorem rowEnergy_difference_bound {n M : ℕ} (hn : 2 ≤ n) (hM : 2 ≤ M)
    (d e : ℕ → ℝ) :
    |rowEnergy n d - rowEnergy n e| ≤
      (M : ℝ) ^ 2 * rowDistance n d e + 4 / (M : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold rowEnergy rowDistance
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hn0]
  calc
    |∑ i ∈ Finset.range n, (normalizedKernel n (d i) - normalizedKernel n (e i))| / n ≤
        (∑ i ∈ Finset.range n, |normalizedKernel n (d i) - normalizedKernel n (e i)|) / n := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ i ∈ Finset.range n, ((M : ℝ) ^ 2 * |d i - e i| + 4 / (M : ℝ))) / n := by
      gcongr with i hi
      exact normalizedKernel_modulus hn hM (d i) (e i)
    _ = (M : ℝ) ^ 2 * ((∑ i ∈ Finset.range n, |d i - e i|) / n) + 4 / (M : ℝ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

theorem rowEnergy_abs_bound {n : ℕ} (hn : 2 ≤ n) (d : ℕ → ℝ) {A : ℝ} (hA : 0 < A)
    (hprincipal : ∀ i ∈ Finset.range n, |d i / n| ≤ Real.pi)
    (hsep : ∀ i ∈ Finset.range n, A ≤ |d i|) :
    |rowEnergy n d| ≤ (2 + 3 * Real.pi ^ 2) / A ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpoint (i : ℕ) (hi : i ∈ Finset.range n) :
      |normalizedKernel n (d i)| ≤ (2 + 3 * Real.pi ^ 2) / A ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hA)).mpr
    have h := normalizedKernel_spatial_bound hn (hprincipal i hi)
    have hsq : A ^ 2 ≤ (d i) ^ 2 := by nlinarith [hsep i hi, sq_abs (d i)]
    have hmul := mul_le_mul_of_nonneg_left hsq (abs_nonneg (normalizedKernel n (d i)))
    nlinarith [abs_nonneg (normalizedKernel n (d i))]
  unfold rowEnergy
  rw [abs_div, abs_of_pos hn0]
  calc
    |∑ i ∈ Finset.range n, normalizedKernel n (d i)| / n ≤
        (∑ i ∈ Finset.range n, |normalizedKernel n (d i)|) / n := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ _i ∈ Finset.range n, (2 + 3 * Real.pi ^ 2) / A ^ 2) / n := by
      gcongr with i hi
      exact hpoint i hi
    _ = (2 + 3 * Real.pi ^ 2) / A ^ 2 := by
      simp [ne_of_gt hn0]

/-- A quantitative modulus with arbitrary cutoff yields convergence from mean
closeness alone. This is the epsilon step used for each fixed point-order offset. -/
theorem tendsto_zero_of_cutoff_modulus {f δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0))
    (hbound : ∀ n, 2 ≤ n → ∀ M : ℕ, 2 ≤ M → |f n| ≤ (M : ℝ) ^ 2 * δ n + 4 / (M : ℝ)) :
    Tendsto f atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (max (2 : ℝ) (8 / ε))
  have hMreal : (2 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hM2 : 2 ≤ M := by exact_mod_cast hMreal.le
  have hM0 : (0 : ℝ) < M := by linarith
  have hMε : 8 < (M : ℝ) * ε :=
    (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hM)
  have hsmall : 4 / (M : ℝ) < ε / 2 := by
    apply (div_lt_iff₀ hM0).mpr
    nlinarith
  have htol : 0 < (ε / 2) / (M : ℝ) ^ 2 := by positivity
  have hlocal := Metric.tendsto_nhds.mp hδ _ htol
  filter_upwards [hlocal, eventually_ge_atTop 2] with n hn hn2
  have hδn : δ n < (ε / 2) / (M : ℝ) ^ 2 := by
    have hab : |δ n| < (ε / 2) / (M : ℝ) ^ 2 := by simpa [Real.dist_eq] using hn
    exact (le_abs_self _).trans_lt hab
  have hprod : (M : ℝ) ^ 2 * δ n < ε / 2 := by
    have h := (lt_div_iff₀ (sq_pos_of_pos hM0)).mp hδn
    nlinarith
  have h := hbound n hn2 M hM2
  simpa [Real.dist_eq] using (h.trans_lt (by linarith : (M : ℝ) ^ 2 * δ n + 4 / (M : ℝ) < ε))

theorem rowEnergy_difference_tendsto {d e : ℕ → ℕ → ℝ}
    (hclose : Tendsto (fun n => rowDistance n (d n) (e n)) atTop (𝓝 0)) :
    Tendsto (fun n => rowEnergy n (d n) - rowEnergy n (e n)) atTop (𝓝 0) := by
  apply tendsto_zero_of_cutoff_modulus hclose
  intro n hn M hM
  exact rowEnergy_difference_bound hn hM (d n) (e n)

def truncatedRow (n : ℕ) (d : ℕ → ℕ → ℝ) (q : ℕ) : ℝ :=
  if 2 * (q + 1) < n then rowEnergy n (d q) else 0

def triangularEnergy (n : ℕ) (d : ℕ → ℕ → ℝ) : ℝ := ∑' q, truncatedRow n d q

theorem summable_truncatedRow (n : ℕ) (d : ℕ → ℕ → ℝ) : Summable (truncatedRow n d) := by
  apply summable_of_ne_finset_zero (s := Finset.range n)
  intro q hq
  have hqn : n ≤ q := by simpa using hq
  simp [truncatedRow, show ¬2 * (q + 1) < n by omega]

theorem triangularEnergy_odd (m : ℕ) (d : ℕ → ℕ → ℝ) :
    triangularEnergy (2 * m + 1) d =
      ∑ q ∈ Finset.range m, rowEnergy (2 * m + 1) (d q) := by
  unfold triangularEnergy
  rw [tsum_eq_sum (s := Finset.range m) (fun q hq => by
    have hqm : m ≤ q := by simpa using hq
    simp [truncatedRow, show ¬2 * (q + 1) < 2 * m + 1 by omega])]
  apply Finset.sum_congr rfl
  intro q hq
  have hqm := Finset.mem_range.mp hq
  simp [truncatedRow, show 2 * (q + 1) < 2 * m + 1 by omega]

/-- Geometric input for the kernel estimate. These are actual scaled angular
separations; no kernel bound is included as an assumption. -/
structure SeparatedRows (n : ℕ) (d : ℕ → ℕ → ℝ) (A : ℝ) : Prop where
  principal : ∀ q, 2 * (q + 1) < n → ∀ i ∈ Finset.range n, |d q i / n| ≤ Real.pi
  separation : ∀ q, 2 * (q + 1) < n → ∀ i ∈ Finset.range n, A * ((q : ℝ) + 1) ≤ |d q i|

theorem separated_row_bound {n : ℕ} (hn : 2 ≤ n) {A : ℝ} (hA : 0 < A)
    {d : ℕ → ℕ → ℝ} (hd : SeparatedRows n d A) (q : ℕ) (hq : 2 * (q + 1) < n) :
    |rowEnergy n (d q)| ≤ ((2 + 3 * Real.pi ^ 2) / A ^ 2) * (1 / ((q : ℝ) + 1) ^ 2) := by
  have h := rowEnergy_abs_bound hn (d q) (A := A * ((q : ℝ) + 1))
    (by positivity) (hd.principal q hq) (hd.separation q hq)
  calc
    |rowEnergy n (d q)| ≤ (2 + 3 * Real.pi ^ 2) / (A * ((q : ℝ) + 1)) ^ 2 := h
    _ = ((2 + 3 * Real.pi ^ 2) / A ^ 2) * (1 / ((q : ℝ) + 1) ^ 2) := by
      rw [mul_pow, div_mul_eq_div_div]
      ring

/-- Removing the offset cutoff by summable domination. The proof uses only the
actual weight bounds and mean angular closeness, not a continuous limiting kernel. -/
theorem triangularEnergy_difference_tendsto {d e : ℕ → ℕ → ℕ → ℝ} {A : ℝ} (hA : 0 < A)
    (hd : ∀ n, 2 ≤ n → SeparatedRows n (d n) A)
    (he : ∀ n, 2 ≤ n → SeparatedRows n (e n) A)
    (hclose : ∀ q, Tendsto (fun n => rowDistance n (d n q) (e n q)) atTop (𝓝 0)) :
    Tendsto (fun n => triangularEnergy n (d n) - triangularEnergy n (e n)) atTop (𝓝 0) := by
  let B : ℕ → ℝ := fun q =>
    2 * ((2 + 3 * Real.pi ^ 2) / A ^ 2) * (1 / ((q : ℝ) + 1) ^ 2)
  let f : ℕ → ℕ → ℝ := fun n q => truncatedRow n (d n) q - truncatedRow n (e n) q
  have hz : Summable (fun q : ℕ => 1 / ((q : ℝ) + 1) ^ 2) := by
    have h : Summable (fun q : ℕ => (1 : ℝ) / (q : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)
    simpa using (summable_nat_add_iff 1).mpr h
  have hB : Summable B := hz.mul_left _
  have hpoint (q : ℕ) : Tendsto (fun n => f n q) atTop (𝓝 0) := by
    have heq : (fun n => f n q) =ᶠ[atTop]
        (fun n => rowEnergy n (d n q) - rowEnergy n (e n q)) := by
      filter_upwards [eventually_ge_atTop (2 * (q + 1) + 1)] with n hn
      simp [f, truncatedRow, show 2 * (q + 1) < n by omega]
    exact (tendsto_congr' heq).mpr (rowEnergy_difference_tendsto (hclose q))
  have hbound : ∀ᶠ n in atTop, ∀ q, ‖f n q‖ ≤ B q := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    intro q
    by_cases hq : 2 * (q + 1) < n
    · have h₁ := separated_row_bound hn hA (hd n hn) q hq
      have h₂ := separated_row_bound hn hA (he n hn) q hq
      simp only [f, truncatedRow, if_pos hq, Real.norm_eq_abs]
      have htri := abs_sub (rowEnergy n (d n q)) (rowEnergy n (e n q))
      dsimp [B]
      linarith
    · simp only [f, truncatedRow, if_neg hq, sub_self, norm_zero]
      dsimp [B]
      positivity
  have hlim := tendsto_tsum_of_dominated_convergence hB hpoint hbound
  have heq (n : ℕ) : (∑' q, f n q) = triangularEnergy n (d n) - triangularEnergy n (e n) := by
    exact (summable_truncatedRow n (d n)).tsum_sub (summable_truncatedRow n (e n))
  simpa only [heq, tsum_zero] using hlim

def foldScaled (n : ℕ) (s : ℝ) : ℝ := min s (2 * Real.pi * n - s)

theorem normalizedKernel_foldScaled {n : ℕ} (hn : 0 < n) (s : ℝ) :
    normalizedKernel n (foldScaled n s) = normalizedKernel n s := by
  unfold foldScaled
  rcases le_total s (2 * Real.pi * n - s) with hs | hs
  · rw [min_eq_left hs]
  · rw [min_eq_right hs, normalizedKernel_reflection hn]

theorem foldScaled_principal {n : ℕ} (hn : 0 < n) {s : ℝ}
    (hs0 : 0 ≤ s) (hs2 : s ≤ 2 * Real.pi * n) :
    |foldScaled n s / n| ≤ Real.pi := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnonneg : 0 ≤ foldScaled n s := by exact le_min hs0 (by linarith)
  rw [abs_of_nonneg (div_nonneg hnonneg hn0.le)]
  apply (div_le_iff₀ hn0).mpr
  unfold foldScaled
  rcases le_total s (2 * Real.pi * n - s) with hs | hs
  · rw [min_eq_left hs]
    linarith
  · rw [min_eq_right hs]
    linarith

/-- Folding across the antipodal angle never increases distance to a reference
angle in the first semicircle. -/
theorem foldScaled_distance_le {n : ℕ} {s c : ℝ} (hc : c ≤ Real.pi * n) :
    |foldScaled n s - c| ≤ |s - c| := by
  unfold foldScaled
  rcases le_total s (2 * Real.pi * n - s) with hs | hs
  · rw [min_eq_left hs]
  · rw [min_eq_right hs]
    have hsc : 0 ≤ s - c := by linarith
    rw [abs_of_nonneg hsc]
    apply abs_le.mpr
    constructor <;> linarith

def foldedRows (n : ℕ) (d : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun q i => foldScaled n (d q i)

theorem rowEnergy_folded {n : ℕ} (hn : 0 < n) (d : ℕ → ℝ) :
    rowEnergy n (fun i => foldScaled n (d i)) = rowEnergy n d := by
  simp only [rowEnergy, normalizedKernel_foldScaled hn]

theorem rowDistance_folded_le (n : ℕ) (d : ℕ → ℝ) {c : ℝ} (hc : c ≤ Real.pi * n) :
    rowDistance n (fun i => foldScaled n (d i)) (fun _ => c) ≤
      rowDistance n d (fun _ => c) := by
  unfold rowDistance
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact Finset.sum_le_sum (fun i _ => foldScaled_distance_le (s := d i) hc)

structure WrappedSeparatedRows (n : ℕ) (d : ℕ → ℕ → ℝ) (A : ℝ) : Prop where
  inArc : ∀ q, 2 * (q + 1) < n → ∀ i ∈ Finset.range n, 0 ≤ d q i ∧ d q i ≤ 2 * Real.pi * n
  forward : ∀ q, 2 * (q + 1) < n → ∀ i ∈ Finset.range n, A * ((q : ℝ) + 1) ≤ d q i
  backward : ∀ q, 2 * (q + 1) < n → ∀ i ∈ Finset.range n, A * ((q : ℝ) + 1) ≤ 2 * Real.pi * n - d q i

theorem WrappedSeparatedRows.folded {n : ℕ} (hn : 0 < n) {d : ℕ → ℕ → ℝ} {A : ℝ}
    (hd : WrappedSeparatedRows n d A) : SeparatedRows n (foldedRows n d) A := by
  constructor
  · intro q hq i hi
    exact foldScaled_principal hn (hd.inArc q hq i hi).1 (hd.inArc q hq i hi).2
  · intro q hq i hi
    exact (le_min (hd.forward q hq i hi) (hd.backward q hq i hi)).trans (le_abs_self _)

def regularRows : ℕ → ℕ → ℝ := fun q _ => 2 * Real.pi * ((q : ℝ) + 1)

theorem regular_reference_le_half {n q : ℕ} (hq : 2 * (q + 1) < n) :
    2 * Real.pi * ((q : ℝ) + 1) ≤ Real.pi * n := by
  have hq' : 2 * ((q : ℝ) + 1) ≤ n := by exact_mod_cast hq.le
  nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hq')]

theorem regularRows_separated {n : ℕ} (hn : 2 ≤ n) {A : ℝ} (hA : A ≤ 2 * Real.pi) :
    SeparatedRows n regularRows A := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  constructor
  · intro q hq i hi
    dsimp [regularRows]
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_iff₀ hn0).mpr (regular_reference_le_half hq)
  · intro q hq i hi
    dsimp [regularRows]
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right hA (by positivity)

theorem triangularEnergy_folded {n : ℕ} (hn : 0 < n) (d : ℕ → ℕ → ℝ) :
    triangularEnergy n (foldedRows n d) = triangularEnergy n d := by
  unfold triangularEnergy
  apply tsum_congr
  intro q
  unfold truncatedRow
  split_ifs
  · exact rowEnergy_folded hn (d q)
  · rfl

/-- Uniform row comparison in the exact form needed by increasing periodic
angle lifts: both forward and complementary arcs have a linear gap lower bound. -/
theorem triangularEnergy_regular_comparison {d : ℕ → ℕ → ℕ → ℝ} {A : ℝ}
    (hA0 : 0 < A) (hAπ : A ≤ 2 * Real.pi)
    (hd : ∀ n, 2 ≤ n → WrappedSeparatedRows n (d n) A)
    (hclose : ∀ q, Tendsto (fun n => rowDistance n (d n q) (regularRows q)) atTop (𝓝 0)) :
    Tendsto (fun n => triangularEnergy n (d n) - triangularEnergy n regularRows) atTop (𝓝 0) := by
  have hfoldclose (q : ℕ) : Tendsto
      (fun n => rowDistance n (foldedRows n (d n) q) (regularRows q)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => rowDistance_nonneg n _ _))
    · filter_upwards [eventually_ge_atTop (2 * (q + 1) + 1)] with n hn
      exact rowDistance_folded_le n (d n q) (regular_reference_le_half (by omega))
    · exact hclose q
  have hlim := triangularEnergy_difference_tendsto hA0
    (fun n hn => (hd n hn).folded (by omega))
    (fun n hn => regularRows_separated hn hAπ) hfoldclose
  have heq : (fun n => triangularEnergy n (foldedRows n (d n)) - triangularEnergy n regularRows) =ᶠ[atTop]
      (fun n => triangularEnergy n (d n) - triangularEnergy n regularRows) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [triangularEnergy_folded (by omega)]
  exact (tendsto_congr' heq).mp hlim

end

end Erdos1045.KernelWeights

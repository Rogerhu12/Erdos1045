import StructuralNote.SolDiagonalKernelGrowth

namespace StructuralNote.SolNearMaximumSigns

open Real Filter Erdos1045.EventualExact FourierMultiplier FiniteBox
open FixedDualClassificationFinite SolScalarGap SolDiagonalKernelGrowth
open scoped Topology
noncomputable section

/-- Uniform Corollary 7.2: the threshold depends only on `C₀`, and at every
site every near-maximizing actual vertex has nonzero potential and the correct
sign. -/
theorem near_maximum_signs_eventually (C₀ : ℝ) :
    ∀ᶠ m in Filter.atTop, ∀ (hm : 0 < m) (s : SignPattern hm),
      deficit hm s ≤ C₀ / (2 * m : ℝ) ^ 2 → ∀ i : Fin (2 * m),
        potential s i ≠ 0 ∧ patternSign s i * potential s i = |potential s i| := by
  filter_upwards [scaled_potential_eventually C₀ (|C₀| + 1),
    Filter.eventually_ge_atTop 1] with m hlarge hmN
  intro hm s hdef i
  have hG : G hm (vertex (amplitude (2 * m)) s) ≤ C₀ / (2 * m : ℝ) ^ 2 :=
    (vertex_gap_le_deficit hm s).trans hdef
  have hpot := hlarge hm (vertex (amplitude (2 * m)) s) hG i
  change |C₀| + 1 < (2 * m : ℝ) * |potential s i| at hpot
  have hn : (0 : ℝ) < (2 * m : ℕ) := by positivity
  have hn' : (0 : ℝ) < 2 * (m : ℝ) := by positivity
  have hnonzero : potential s i ≠ 0 := by
    intro hz
    rw [hz, abs_zero, mul_zero] at hpot
    linarith [abs_nonneg C₀]
  refine ⟨hnonzero, ?_⟩
  have hnonneg : 0 ≤ patternSign s i * potential s i := by
    by_contra hneg
    have hneg' : patternSign s i * potential s i < 0 := lt_of_not_ge hneg
    have hcost := single_wrong_sign_cost hm s i hneg'
    have hscaled : (2 * m : ℝ) * deficit hm s ≤ C₀ / (2 * m : ℝ) := by
      calc
        _ ≤ (2 * m : ℝ) * (C₀ / (2 * m : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hdef hn'.le
        _ = _ := by field_simp
    have hA := amplitude_ge_one (n := 2 * m) (by omega)
    have hC := le_abs_self C₀
    have hAn := mul_le_mul_of_nonneg_right hA
      (mul_nonneg hn.le (abs_nonneg (potential s i)))
    have hscaled' := (le_div_iff₀ hn').mp hscaled
    have hcostn := mul_le_mul_of_nonneg_left hcost hn.le
    ring_nf at hpot hAn hscaled' hcostn
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hAn hcostn
    ring_nf at hAn hcostn
    nlinarith [abs_nonneg (potential s i)]
  have hs := sign_mul_abs (patternSign_is_sign s i) (x := potential s i)
  rwa [abs_of_nonneg hnonneg] at hs

end
end StructuralNote.SolNearMaximumSigns

import StructuralNote.FixedDualClassificationKernelUniformDivergence
import StructuralNote.SolMidpointPressure
import StructuralNote.FixedDualClassificationFinite

namespace StructuralNote.SolDiagonalKernelGrowth

open Real Finset Filter Erdos1045.EventualExact Erdos1045.EventualExact.FourierMultiplier
open FixedDualClassificationKernel FixedDualClassificationKernelUniformDivergence
open FixedDualClassificationFinite SolScalarGap SolMidpointPressure
open scoped Topology BigOperators
noncomputable section

theorem kernel_le_diagonal (n : ℕ) (t : ℝ) : finiteKernel n t ≤ finiteKernel n 0 := by
  unfold finiteKernel
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply sum_le_sum
  intro p _
  have hw := SchurWeights.weight_nonneg n p
  have hc := Real.cos_le_one (p * t)
  simpa using mul_le_mul_of_nonneg_left hc hw

theorem diagonal_ge_first_grid (m : ℕ) :
    finiteKernel (2 * m) (Real.pi / m) ≤ finiteKernel (2 * m) 0 :=
  kernel_le_diagonal _ _

theorem diagonal_tendsto_atTop :
    Tendsto (fun m : ℕ => finiteKernel (2 * m) 0) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [first_grid_tendsto_atTop.eventually (eventually_ge_atTop b)] with m hm
  exact hm.trans (diagonal_ge_first_grid m)

/-- An `O(n⁻²)` scalar gap forces every actual potential to be uniformly
large after multiplication by `n`; this is the min-potential conclusion of
Lemma 7.1. -/
theorem scaled_potential_eventually (C₀ M : ℝ)
    : ∀ᶠ m in atTop, ∀ (hm : 0 < m) (q : Fin (2 * m) → ℝ),
      G hm q ≤ C₀ / (2 * m : ℝ) ^ 2 → ∀ i : Fin (2 * m),
        M < (2 * m : ℝ) * |operator (2 * m) q i| := by
  have hdiag := diagonal_tendsto_atTop.eventually
    (eventually_gt_atTop ((|M| + |C₀| + 1) / 2))
  filter_upwards [hdiag, eventually_ge_atTop 1] with m hK hm
  intro hm0 q hG i
  have hA := amplitude_ge_one (n := 2 * m) (by omega)
  have hApos : 0 < FiniteBox.amplitude (2 * m) := by linarith
  have hpress := midpoint_pressure hm0 q i
  have hn : (0 : ℝ) < (2 * m : ℕ) := by positivity
  have hscaled : (2 * m : ℝ) ^ 2 * G hm0 q ≤ C₀ := by
    calc
      _ ≤ (2 * m : ℝ) ^ 2 * (C₀ / (2 * m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hG (sq_nonneg _)
      _ = C₀ := by field_simp
  have hC : C₀ ≤ |C₀| := le_abs_self C₀
  have hM : M ≤ |M| := le_abs_self M
  have hKpos : 0 < finiteKernel (2 * m) 0 := by
    linarith [abs_nonneg C₀, abs_nonneg M]
  field_simp at hpress
  have hGm : 4 * (m : ℝ) ^ 2 * G hm0 q ≤ |C₀| := by nlinarith
  have hCA : |C₀| ≤ FiniteBox.amplitude (2 * m) * |C₀| := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA (abs_nonneg C₀)
  have hAK : FiniteBox.amplitude (2 * m) * finiteKernel (2 * m) 0 ≤
      FiniteBox.amplitude (2 * m) ^ 2 * finiteKernel (2 * m) 0 := by
    have := mul_le_mul_of_nonneg_right hA hKpos.le
    nlinarith
  have hboundA : FiniteBox.amplitude (2 * m) * finiteKernel (2 * m) 0 ≤
      FiniteBox.amplitude (2 * m) *
        ((m : ℝ) * |operator (2 * m) q i| + |C₀| / 4) := by
    nlinarith
  have hbound : finiteKernel (2 * m) 0 ≤
      (m : ℝ) * |operator (2 * m) q i| + |C₀| / 4 :=
    le_of_mul_le_mul_left hboundA hApos
  nlinarith [abs_nonneg C₀, abs_nonneg M]

end
end StructuralNote.SolDiagonalKernelGrowth

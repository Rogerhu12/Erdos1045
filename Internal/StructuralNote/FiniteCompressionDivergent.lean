import StructuralNote.FiniteCompressionActual
import StructuralNote.FixedDualClassificationKernelUniformDivergence
import StructuralNote.FixedDualClassificationFinite

/-! Divergence of the first grid kernel value is enough for one-pass rigidity;
no logarithmic asymptotic or rate of divergence is assumed. -/

namespace StructuralNote.FiniteCompressionDivergent

open Erdos1045.EventualExact FourierMultiplier Filter
open FiniteCompressionEnergy FiniteCompressionRanked FiniteCompressionActual
open FixedDualClassificationKernel FixedDualClassificationKernelUniformBounds
open FixedDualClassificationKernelUniformDivergence FixedDualClassificationFinite
open scoped BigOperators Topology
noncomputable section

theorem first_grid_eq (m : ℕ) :
    gridKernel (2 * m) 1 = finiteKernel (2 * m) (Real.pi / m) := by
  unfold gridKernel
  congr 1
  push_cast
  ring

theorem eventual_gain (C₀ M : ℝ) : ∀ᶠ m : ℕ in atTop, ∀ ℓ : ℕ,
    gridKernel (2 * m) ℓ ≤ M →
    C₀ < 32 * FiniteBox.amplitude (2 * m) ^ 2 *
      (gridKernel (2 * m) 1 - gridKernel (2 * m) ℓ) := by
  filter_upwards [first_grid_tendsto_atTop.eventually (eventually_gt_atTop (M + max C₀ 0 + 1)),
    eventually_ge_atTop 1] with m hfirst hm ℓ hℓ
  rw [← first_grid_eq] at hfirst
  have hA := amplitude_ge_one (n := 2 * m) (by omega)
  have hA2 : 1 ≤ FiniteBox.amplitude (2 * m) ^ 2 := by nlinarith
  have hd : 0 < gridKernel (2 * m) 1 - gridKernel (2 * m) ℓ := by
    linarith [le_max_right C₀ 0]
  have hmul := mul_le_mul_of_nonneg_right hA2 hd.le
  nlinarith [le_max_left C₀ 0]

/-- Local background monotonicity and the two buffer consequences suffice
for actual box rigidity, uniformly for every fixed normalized deficit. -/
theorem eventual_prefix_of_sine_bound (C₀ η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 0 < m) (ℓ L R N : ℕ) (e : ℕ → ℕ)
      (b : Fin (2 * m) → ℝ),
    R < 2 * m → StrictMonoOn e (Set.Iio ℓ) → e 0 = L → e (ℓ - 1) ≤ R →
    e (ℓ - 1) - e 0 ≤ N → b ∈ FiniteBox.Q hm →
    (∀ k ∈ Set.Icc L R, b (site hm k) = -FiniteBox.amplitude (2 * m)) →
    AntitoneOn (gridKernel (2 * m)) (Set.Icc 1 N) →
    AntitoneOn (fun k => operator (2 * m) b (site hm k)) (Set.Icc L R) →
    η ≤ |Real.sin (2 * Real.pi * ℓ / (2 * m : ℝ))| →
    FiniteBox.B hm - normalizedBoxEnergy (operator (2 * m))
      (b + patch hm (FiniteBox.amplitude (2 * m)) (sites hm ℓ e)) ≤ C₀ / (2 * m : ℝ) ^ 2 →
    ∀ j < ℓ, e j = L + j := by
  filter_upwards [eventual_gain C₀ (1 / (2 * η)), eventually_ge_atTop 2] with m hgain hm2
  intro hm ℓ L R N e b hR he hfirst hlast hspan hb hbase hK hbackground hsin hdeficit
  have hgrid : (2 * m : ℕ) * (2 * Real.pi * ℓ / (2 * m : ℝ)) =
      (ℓ : ℝ) * (2 * Real.pi) := by
    have hn : (2 * m : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hbound := grid_kernel_bound_uniform (m := m) (r := ℓ) hm2 hgrid hη hsin
  apply prefix_of_near_max hm hR (FiniteBox.amplitude_pos (by omega)).le e he hfirst hlast hspan
    b hb hbase hK hbackground hdeficit
  apply hgain ℓ
  apply (le_abs_self _).trans
  simpa only [gridKernel, Nat.cast_mul, Nat.cast_ofNat] using hbound

end
end StructuralNote.FiniteCompressionDivergent

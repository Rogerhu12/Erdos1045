import StructuralNote.FixedDualClassificationKernelSignsEnlarged
import StructuralNote.SolIntegratedKernel
import StructuralNote.FixedDualClassificationFinite

/-! Uniform strong convexity of the actual integrated kernel on the enlarged
three-block interval. The negative kernel margin is proved, not assumed. -/

namespace StructuralNote.ThreeBlockKernelMargin

open Real Filter Set Erdos1045.EventualExact FiniteBox
open FixedDualClassificationKernel FixedDualClassificationKernelSignsPropagation
open FixedDualClassificationKernelSignsEnlarged FixedDualClassificationFinite
open SolIntegratedKernel DiscreteConvexBalance
open scoped Topology
noncomputable section

def angle (m : ℕ) (r : ℤ) : ℝ := (r : ℝ) * (2 * Real.pi / (2 * m : ℕ))

theorem angle_mono (m : ℕ) : Monotone (angle m) := by
  intro r s hrs
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hrs) (by positivity)

theorem angle_pos_index {m : ℕ} {α : ℝ} (hα : 0 < α) {r : ℤ}
    (hr : α ≤ angle m r) : 0 ≤ r := by
  by_contra hn
  have hrR : (r : ℝ) ≤ 0 := by exact_mod_cast (show r ≤ 0 by omega)
  have hh : angle m r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hrR (by positivity)
  linarith

theorem integer_kernel_margin {m : ℕ} {α β c : ℝ} (hα : 0 < α)
    (h : ∀ r : ℕ, α ≤ angle m r → angle m r ≤ β → gridKernel m r ≤ -c)
    {r : ℤ} (hr : angle m r ∈ Icc α β) :
    finiteKernel (2 * m) (2 * Real.pi * (r : ℝ) / (2 * m : ℕ)) ≤ -c := by
  have hr0 := angle_pos_index hα hr.1
  have he : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr0
  have hh := h r.toNat (by simpa only [he] using hr.1) (by simpa only [he] using hr.2)
  have heR : (r.toNat : ℝ) = (r : ℝ) := by exact_mod_cast he
  have heangle : (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) =
      2 * Real.pi * (r : ℝ) / (2 * m : ℕ) := by ring
  simpa only [gridKernel, heR, heangle] using hh

theorem strong_convexity_of_margin {m : ℕ} (hm : 0 < m) {c : ℝ} (hc : 0 ≤ c)
    {r : ℤ}
    (hK : finiteKernel (2 * m) (2 * Real.pi * (r : ℝ) / (2 * m : ℕ)) ≤ -c) :
    16 * c / (2 * m : ℕ) ^ 2 ≤ secondDifference (S (2 * m)) r := by
  rw [secondDifference_S]
  have hA := amplitude_ge_one (show 2 ≤ 2 * m by omega)
  have hA2 : 1 ≤ amplitude (2 * m) ^ 2 := by nlinarith
  have hn : (0 : ℝ) < (2 * m : ℕ) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hK
    (show 0 ≤ 16 * amplitude (2 * m) ^ 2 / (2 * m : ℕ) ^ 2 by positivity)
  have hcoeff : 16 * c / (2 * m : ℕ) ^ 2 ≤
      16 * amplitude (2 * m) ^ 2 / (2 * m : ℕ) ^ 2 * c := by
    apply (div_le_iff₀ hn).2
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hA2 hc]
  calc
    _ ≤ 16 * amplitude (2 * m) ^ 2 / (2 * m : ℕ) ^ 2 * c := hcoeff
    _ = -(16 * amplitude (2 * m) ^ 2 / (2 * m : ℕ) ^ 2 * -c) := by ring
    _ ≤ -(16 * amplitude (2 * m) ^ 2 / (2 * m : ℕ) ^ 2 *
        finiteKernel (2 * m) (2 * Real.pi * (r : ℝ) / (2 * m : ℕ))) := neg_le_neg hmul
    _ = _ := by ring

/-- A single interval and a single positive constant work for every sufficiently
large order and every integer grid point in the interval. -/
theorem exists_uniform_strong_convexity :
    ∃ α β κ : ℝ, 0 < α ∧ α < Real.pi / 4 ∧
      5 * Real.pi / 12 < β ∧ β < Real.pi / 2 ∧ 0 < κ ∧
      ∀ᶠ m : ℕ in atTop, ∀ r : ℤ, angle m r ∈ Icc α β →
        κ / (2 * m : ℕ) ^ 2 ≤ secondDifference (S (2 * m)) r := by
  obtain ⟨θ, α, β, c, _, _, hα, hαlo, hβlo, hβhi, hc, hevent⟩ :=
    exists_enlarged_compression_intervals
  refine ⟨α, β, 16 * c, hα, hαlo, hβlo, hβhi, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop 0, hevent] with m hm h r hr
  exact strong_convexity_of_margin hm hc.le (integer_kernel_margin hα h.2.2.1 hr)

theorem strong_convexity_on_span {m : ℕ} {α β κ : ℝ} {l u : ℤ}
    (h : ∀ r : ℤ, angle m r ∈ Icc α β →
      κ ≤ secondDifference (S (2 * m)) r)
    (hl : α ≤ angle m l) (hu : angle m u ≤ β) :
    ∀ r, l < r → r < u → κ ≤ secondDifference (S (2 * m)) r := by
  intro r hrl hru
  exact h r ⟨hl.trans (angle_mono m hrl.le), (angle_mono m hru.le).trans hu⟩

end
end StructuralNote.ThreeBlockKernelMargin

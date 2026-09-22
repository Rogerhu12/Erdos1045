import StructuralNote.FixedDualClassificationKernelSignsMargins
import StructuralNote.KernelSignsEndpoints

/-! Unconditional finite-kernel signs and monotonicity on the actual compression intervals. -/

namespace StructuralNote.FixedDualClassificationKernelSignsFinal

open Real Filter Set Erdos1045.EventualExact
open FixedDualPrimitive FixedDualClassificationKernelSignsPropagation
open FixedDualClassificationKernelSignsTransfer FixedDualClassificationKernelSignsMargins
open KernelSignsEndpoints
open scoped Topology
noncomputable section

def CompressionKernelSigns (m : ℕ) : Prop :=
  (∀ r : ℕ, (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ Real.pi / 12 → 0 < gridKernel m r) ∧
  (∀ r : ℕ, ((r + 1 : ℕ) : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ Real.pi / 12 →
    gridKernel m (r + 1) < gridKernel m r) ∧
  (∀ r : ℕ, Real.pi / 4 ≤ (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) →
    (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ 5 * Real.pi / 12 → gridKernel m r < 0) ∧
  (∀ r : ℕ, Real.pi / 4 ≤ (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) →
    ((r + 1 : ℕ) : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ 5 * Real.pi / 12 →
      gridKernel m r < gridKernel m (r + 1))

theorem eventually_compressionKernelSigns : ∀ᶠ m : ℕ in atTop, CompressionKernelSigns m := by
  have hpos := eventually_positive_decreasing_interval
    (show Real.pi / 12 ∈ Set.Ioo 0 (Real.pi / 2) by constructor <;> linarith [pi_pos])
    kernel_pi_div_twelve_pos
  obtain ⟨a, b, ha, hab, hb, hsec, hneg⟩ := exists_negative_increasing_pair_pos
  have hneg' := eventually_negative_increasing_interval (α := Real.pi / 4) (β := 5 * Real.pi / 12)
    ha hab hb (by linarith [pi_pos]) (by linarith [pi_pos]) hsec hneg
  filter_upwards [hpos, hneg'] with m hp hn
  exact ⟨hp.1, hp.2, hn.1, hn.2⟩

theorem eventually_cross_negative_margin : ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
    ∀ r : ℕ, Real.pi / 4 ≤ (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) →
      (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ 5 * Real.pi / 12 → gridKernel m r ≤ -c := by
  obtain ⟨a, b, ha, hab, hb, hsec, hneg⟩ := exists_negative_increasing_pair_pos
  exact eventually_negative_margin_on_interval (θ := a) (α := Real.pi / 4) (β := 5 * Real.pi / 12)
    ha (hab.trans hb) (by linarith [pi_pos]) (by linarith [pi_pos]) (hsec.trans hneg)

theorem near_antitone {m r s : ℕ} (h : CompressionKernelSigns m) (hrs : r ≤ s)
    (hs : (s : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ Real.pi / 12) :
    gridKernel m s ≤ gridKernel m r := by
  revert hs
  induction s, hrs using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ s hrs ih =>
    intro hs
    have hstep := h.2.1 s hs
    apply hstep.le.trans (ih ?_)
    have hb : 0 ≤ 2 * Real.pi / (2 * m : ℕ) := by positivity
    simp only [Nat.cast_add, Nat.cast_one] at hs
    nlinarith

end
end StructuralNote.FixedDualClassificationKernelSignsFinal

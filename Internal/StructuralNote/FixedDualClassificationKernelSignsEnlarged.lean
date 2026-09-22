import StructuralNote.FixedDualClassificationKernelSignsFinal
import StructuralNote.KernelSignsEndpointExtension

/-! Fixed open margins in the finite-kernel intervals, including exterior grid neighbors. -/

namespace StructuralNote.FixedDualClassificationKernelSignsEnlarged

open Real Filter Erdos1045.EventualExact
open FixedDualPrimitive FixedDualClassificationKernelSignsPropagation
open FixedDualClassificationKernelSignsTransfer FixedDualClassificationKernelSignsMargins
open KernelSignsEndpoints KernelSignsEndpointExtension
open scoped Topology
noncomputable section

theorem exists_enlarged_compression_intervals :
    ∃ θ α β c : ℝ, Real.pi / 12 < θ ∧ θ < Real.pi / 2 ∧
      0 < α ∧ α < Real.pi / 4 ∧ 5 * Real.pi / 12 < β ∧ β < Real.pi / 2 ∧ 0 < c ∧
      ∀ᶠ m : ℕ in atTop,
        (∀ r : ℕ, (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ θ → 0 < gridKernel m r) ∧
        (∀ r : ℕ, ((r + 1 : ℕ) : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ θ →
          gridKernel m (r + 1) < gridKernel m r) ∧
        (∀ r : ℕ, α ≤ (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) →
          (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ β → gridKernel m r ≤ -c) ∧
        (∀ r : ℕ, α ≤ (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) →
          ((r + 1 : ℕ) : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ β →
            gridKernel m r < gridKernel m (r + 1)) := by
  obtain ⟨θ, hθlo, hθhi, hθK⟩ := exists_positive_point_above_twelfth
  obtain ⟨a, b, ha, hab, hb, hsec, hneg⟩ := exists_negative_increasing_pair_pos
  let α := (b + Real.pi / 4) / 2
  let β := 11 * Real.pi / 24
  have hα0 : 0 < α := by dsimp [α]; linarith [pi_pos]
  have hbα : b < α := by dsimp [α]; linarith
  have hαπ : α < Real.pi / 4 := by dsimp [α]; linarith
  have hβlo : 5 * Real.pi / 12 < β := by dsimp [β]; linarith [pi_pos]
  have hβhi : β < Real.pi / 2 := by dsimp [β]; linarith [pi_pos]
  have hαβ : α ≤ β := by linarith [pi_pos]
  obtain ⟨c, hc, hmargin⟩ := eventually_negative_margin_on_interval
    ha (hab.trans hbα) hαβ hβhi (hsec.trans hneg)
  refine ⟨θ, α, β, c, hθlo, hθhi, hα0, hαπ, hβlo, hβhi, hc, ?_⟩
  have hpos := eventually_positive_decreasing_interval
    (show θ ∈ Set.Ioo 0 (Real.pi / 2) from ⟨by linarith [pi_pos], hθhi⟩) hθK
  have hcross := eventually_negative_increasing_interval ha hab hbα hαβ hβhi hsec hneg
  filter_upwards [hpos, hcross, hmargin] with m hp hn hc
  exact ⟨hp.1, hp.2, hc, hn.2⟩

end
end StructuralNote.FixedDualClassificationKernelSignsEnlarged

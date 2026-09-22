import EventualExact.ExtremalEnergyBound
import EventualExact.CoercivityRefinement

/-! The sharp asymptotic bound on the local edge energy of actual diameter extremizers. -/

namespace Erdos1045.EventualExact.ExtremalEnergyBound

open Filter Configuration HullGeometry CommonLocalization
open scoped Topology
noncomputable section

def edgeBudget (n : ℕ) (η : ℝ) : ℝ :=
  12 * diameterBudget n + 1536 * Real.pi ^ 2 * η + 32 * Real.pi ^ 2 / n

theorem edgeBudget_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun j => edgeBudget (N j) (η j)) atTop (𝓝 (3 * Real.pi ^ 2 / 2)) := by
  have h1 := (diameterBudget_tendsto hN).const_mul 12
  have h2 := hη.const_mul (1536 * Real.pi ^ 2)
  have hinv : Tendsto (fun j => (N j : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
  have h3 : Tendsto (fun j => 32 * Real.pi ^ 2 / N j) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (32 * Real.pi ^ 2)
  convert (h1.add h2).add h3 using 1
  · rfl
  · congr 1
    ring

theorem model_edge_bound {n : ℕ} {z : Points n} {σ : Equiv.Perm (Fin n)}
    {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hn : 4 ≤ n)
    (hE : totalEnergy n u ≤ 32 * Real.pi ^ 2)
    (hQ : LocalDFT.positiveQuadratic n u ≤ diameterBudget n + 128 * Real.pi ^ 2 * η) :
    (n : ℝ) * LocalDFT.energyB n u ≤ edgeBudget n η := by
  have hc := CoercivityRefinement.normalized_B_coercivity hn u h.periodic h.mean_zero h.similarity_zero
  have hA := LocalMaximum.energyA_nonneg n u
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hB : LocalDFT.energyB n u ≤ 32 * Real.pi ^ 2 / n := by
    apply (le_div_iff₀ hnR).2
    unfold totalEnergy at hE
    nlinarith
  unfold edgeBudget
  nlinarith

/-- The quantitative form of (3.10), retaining all actual local coordinates and
proving the energy bound from genuine diameter maximality. -/
theorem diameter_sequence_edge_energy {N : ℕ → ℕ} (hN4 : ∀ j, 4 ≤ N j)
    (hN : Tendsto N atTop atTop) (z : ∀ j, Points (N j))
    (hz : ∀ j, ExtremalNormalization.DiameterExtremal (z j)) :
    ∃ (σ : ∀ j, Equiv.Perm (Fin (N j))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ),
      Tendsto η atTop (𝓝 0) ∧
      (∀ᶠ j in atTop,
        NormalizedRelativeEdgeModel (z j) (σ j) (α j) (β j) (u j) (η j) ∧
        boundaryLength (z j ∘ σ j) ≤ hullPerimeter (z j) ∧
        totalEnergy (N j) (u j) ≤ 32 * Real.pi ^ 2 ∧
        LocalDFT.positiveQuadratic (N j) (u j) ≤ diameterBudget (N j) + 128 * Real.pi ^ 2 * η j ∧
        (N j : ℝ) * LocalDFT.energyB (N j) (u j) ≤ edgeBudget (N j) (η j)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
        (N j : ℝ) * LocalDFT.energyB (N j) (u j) ≤ 3 * Real.pi ^ 2 / 2 + ε) := by
  obtain ⟨σ, α, β, u, η, hη, hm⟩ := diameter_sequence_energy hN4 hN z hz
  have hbound : ∀ᶠ j in atTop, (N j : ℝ) * LocalDFT.energyB (N j) (u j) ≤ edgeBudget (N j) (η j) := by
    filter_upwards [hm] with j hj
    exact model_edge_bound hj.1 (hN4 j) hj.2.2.2.1 hj.2.2.2.2
  refine ⟨σ, α, β, u, η, hη, ?_, ?_⟩
  · filter_upwards [hm, hbound] with j hj hb
    exact ⟨hj.1, hj.2.1, hj.2.2.2.1, hj.2.2.2.2, hb⟩
  · intro ε hε
    filter_upwards [hbound, (edgeBudget_tendsto hN hη).eventually
      (gt_mem_nhds (lt_add_of_pos_right (3 * Real.pi ^ 2 / 2) hε))] with j hj he
    exact hj.trans he.le

end
end Erdos1045.EventualExact.ExtremalEnergyBound

import EventualExact.CommonLocalization
import EventualExact.NormalizedExtremalFekete

/-! Common localization for actual diameter and perimeter extremal sequences. -/

namespace Erdos1045.EventualExact.CommonLocalization

open Filter Configuration ExteriorClassical ExteriorBoundary ExteriorSupport HullGeometry
open CoarseFekete
open scoped Topology
noncomputable section

theorem NormalizedRelativeEdgeModel.relabel {n : ℕ} {z : Points n}
    {τ σ : Equiv.Perm (Fin n)} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel (z ∘ τ) σ α β u η) :
    NormalizedRelativeEdgeModel z (σ.trans τ) α β u η := by
  exact ⟨⟨h.periodic, h.scale_ne_zero, h.coordinates, h.error_nonneg, h.relative_edges⟩,
    h.mean_zero, h.similarity_zero⟩

theorem NormalizedRelativeEdgeModel.unscale {n : ℕ} {z : Points n}
    {σ : Equiv.Perm (Fin n)} {α β c : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel (fun i => c * z i) σ α β u η) (hc : c ≠ 0) :
    NormalizedRelativeEdgeModel z σ (α / c) (β / c) u η := by
  refine ⟨⟨h.periodic, div_ne_zero h.scale_ne_zero hc, ?_, h.error_nonneg,
    h.relative_edges⟩, h.mean_zero, h.similarity_zero⟩
  intro i
  rw [show α / c + β / c * (LocalPhase.regularRoot n ^ (i : ℕ) + u i) =
    (α + β * (LocalPhase.regularRoot n ^ (i : ℕ) + u i)) / c by ring]
  exact (eq_div_iff hc).2 (by simpa only [mul_comm] using h.coordinates i)

/-- No exterior model is an input to this endpoint. -/
theorem normalized_fekete_localization {N : ℕ → ℕ}
    (hN4 : ∀ j, 4 ≤ N j) (hN : Tendsto N atTop atTop) (z : ∀ j, Points (N j))
    (hinj : ∀ j, Function.Injective (z j))
    (hP : ∀ j, hullPerimeter (z j) = 2 * Real.pi)
    (hF : ∀ j, Fekete (z j)) (hΔ : ∀ j, (N j : ℝ) ^ N j ≤ discriminant (z j)) :
    ∃ (σ : ∀ j, Equiv.Perm (Fin (N j))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ),
      Tendsto η atTop (𝓝 0) ∧ ∀ᶠ j in atTop,
        NormalizedRelativeEdgeModel (z j) (σ j) (α j) (β j) (u j) (η j) := by
  obtain ⟨τ, d, HF, _⟩ := normalized_fekete_inverse_square_energy hN4 hN z hinj hP hF hΔ
  let s : Family :=
    { size := N
      size_ge := hN4
      size_tendsto := hN
      points := fun j => z j ∘ τ j
      injective := fun j => (hinj j).comp (τ j).injective
      fekete := fun j => fekete_perm (hF j) (τ j)
      discriminant_ge := fun j => by rw [discriminant_perm]; exact hΔ j
      data := d
      identities := HF }
  obtain ⟨σ, α, β, u, η, hη, hm⟩ := s.normalized_relative_edge_localization
  exact ⟨fun j => (σ j).trans (τ j), α, β, u, η, hη, hm.mono fun _ h => h.relabel⟩

/-- Every growing sequence of genuine diameter or perimeter maximizers admits
the common normalized local coordinates, with relative edge error tending to zero. -/
theorem extremal_sequence_localization {N : ℕ → ℕ}
    (hN4 : ∀ j, 4 ≤ N j) (hN : Tendsto N atTop atTop) (z : ∀ j, Points (N j))
    (hz : ∀ j, ExtremalNormalization.DiameterExtremal (z j) ∨ PerimeterExtremal (N j) (z j)) :
    ∃ (σ : ∀ j, Equiv.Perm (Fin (N j))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ),
      Tendsto η atTop (𝓝 0) ∧ ∀ᶠ j in atTop,
        NormalizedRelativeEdgeModel (z j) (σ j) (α j) (β j) (u j) (η j) := by
  have h (j : ℕ) := ExtremalNormalization.extremal_normalized (hN4 j) (hz j)
  obtain ⟨σ, α, β, u, η, hη, hm⟩ := normalized_fekete_localization hN4 hN
    (fun j => ExtremalNormalization.normalize (z j))
    (fun j => (h j).injective) (fun j => (h j).perimeter_eq)
    (fun j => (h j).fekete) (fun j => (h j).discriminant_ge)
  let c (j : ℕ) : ℂ := ((2 * Real.pi / hullPerimeter (z j) : ℝ) : ℂ)
  have hc (j : ℕ) : c j ≠ 0 := by
    have hn : (0 : ℝ) < N j := by exact_mod_cast (show 0 < N j by have := hN4 j; omega)
    have hD : 0 < discriminant (z j) := by
      rcases hz j with hd | hp
      · exact (pow_pos hn _).trans_le (hd.discriminant_ge (by have := hN4 j; omega))
      · exact (pow_pos hn _).trans_le
          (ExtremalNormalization.perimeterExtremal_normalized (hN4 j) hp).discriminant_ge
    have hP := ExtremalNormalization.perimeter_pos_of_discriminant_pos
      (by have := hN4 j; omega) hD
    exact Complex.ofReal_ne_zero.mpr (div_pos (by positivity) hP).ne'
  refine ⟨σ, (fun j => α j / c j), (fun j => β j / c j), u, η, hη, ?_⟩
  filter_upwards [hm] with j hj
  exact hj.unscale (hc j)

end
end Erdos1045.EventualExact.CommonLocalization

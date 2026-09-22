import EventualExact.PhysicalBoundaryOrder
import EventualExact.ExteriorArbitrarySampling
import EventualExact.ExtremalLocalization

/-! Common localization retaining the actual convex-hull perimeter bound.
The physical sorting is discharged by ordered boundary preimages. -/

namespace Erdos1045.EventualExact.PhysicalBoundaryOrder

open Configuration ExteriorClassical ExteriorBoundary CyclicAngles HullGeometry
noncomputable section

theorem physical_boundaryLength_le {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hn : 2 ≤ n)
    (he : ExteriorSupport.errorRadius d < d.capacity)
    (σ : Equiv.Perm (Fin n)) (a : Angles n)
    (hpolar : ∀ i : Fin n, z (σ i) - ExteriorSupport.center d =
      (‖z (σ i) - ExteriorSupport.center d‖ : ℂ) * unit (a.angle i)) :
    boundaryLength (fun i => z (σ i)) ≤ hullPerimeter z := by
  obtain ⟨b, hb⟩ := physical_ordered_preimages d HF (by omega) he σ a hpolar
  simpa only [hb] using ExteriorArbitrarySampling.boundary_sampling_le d HF hn b

end
end Erdos1045.EventualExact.PhysicalBoundaryOrder

namespace Erdos1045.EventualExact.CoarseFekete

open Filter Configuration ExteriorClassical ExteriorBoundary ExteriorSupport CyclicAngles
open CommonLocalization CanonicalPolarEdges HullGeometry
open scoped Topology
noncomputable section

theorem Family.relative_edge_localization_with_perimeter (s : Family) :
    ∃ (σ : ∀ j, Equiv.Perm (Fin (s.size j))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ),
      Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ j in atTop, RelativeEdgeModel (s.points j) (σ j) (α j) (β j) (u j) (η j) ∧
        boundaryLength (fun i => s.points j (σ j i)) ≤ hullPerimeter (s.points j) := by
  obtain ⟨σ, a, hgeometry, hgap⟩ := s.physical_polar_rigidity
  obtain ⟨K, _, henergy⟩ := s.inverse_square_energy_bounded
  have hρ := errorRadius_tendsto_zero s.data s.size_tendsto henergy
  have hη := RadialEdges.edgeError_tendsto_zero a hgap hρ
  have hn (j : ℕ) : 0 < s.size j := by have := s.size_ge j; omega
  let u (j : ℕ) := RadialEdges.perturbation (a j)
    (radii (s.data j) (σ j) (hn j)) (s.data j).capacity
  refine ⟨σ, (fun j => center (s.data j)),
    (fun j => ((s.data j).capacity : ℂ) * unit ((a j).angle 0)), u,
    (fun j => RadialEdges.edgeError (a j) (errorRadius (s.data j))), hη, ?_⟩
  obtain ⟨_, _, _, _, hgood⟩ := s.eventual_geometric_bounds
  filter_upwards [hgeometry, hgood] with j hj hg
  refine ⟨?_, PhysicalBoundaryOrder.physical_boundaryLength_le (s.data j) (s.identities j)
    (by have := s.size_ge j; omega) (by linarith [hg.1, hg.2.1]) (σ j) (a j) hj.polar⟩
  refine ⟨RadialEdges.perturbation_periodic (a j) (hn j) _
    (radii_periodic (s.data j) (σ j) (hn j)) _, ?_, ?_,
    RadialEdges.edgeError_nonneg (a j) (errorRadius_nonneg (s.data j)), ?_⟩
  · apply mul_ne_zero (Complex.ofReal_ne_zero.mpr (s.data j).capacity_pos.ne')
    exact norm_ne_zero_iff.mp (by rw [norm_unit]; norm_num)
  · intro i
    have hi : index (hn j) (i : ℕ) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    simpa only [hi] using actual_coordinates (s.data j) (σ j) (a j) (hn j) hj.polar i
  · exact relative_edges (s.data j) (s.identities j) (σ j) (a j)
      (by have := s.size_ge j; omega) hg.1 hg.2.1 hj.polar

/-- Proposition 2.2 in sequential form, with the actual translation and similarity
coefficients removed. Neither parity nor global perimeter maximality is used. -/
theorem Family.normalized_relative_edge_localization_with_perimeter (s : Family) :
    ∃ (σ : ∀ j, Equiv.Perm (Fin (s.size j))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ),
      Tendsto η atTop (𝓝 0) ∧ ∀ᶠ j in atTop,
        NormalizedRelativeEdgeModel (s.points j) (σ j) (α j) (β j) (u j) (η j) ∧
        boundaryLength (fun i => s.points j (σ j i)) ≤ hullPerimeter (s.points j) := by
  obtain ⟨σ, α, β, u, η, hη, hmodel⟩ := s.relative_edge_localization_with_perimeter
  refine ⟨σ, (fun j => α j + β j * LocalNormalization.mean (s.size j) (u j)),
    (fun j => β j * (1 + LocalNormalization.first (s.size j) (u j))),
    (fun j => LocalNormalization.normalized (s.size j) (u j)),
    (fun j => 2 * η j / (1 - η j)), ?_, ?_⟩
  · have hc : ContinuousAt (fun x : ℝ => 2 * x / (1 - x)) 0 := by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · norm_num
    simpa only [Function.comp_def, mul_zero, sub_zero, zero_div] using hc.tendsto.comp hη
  · filter_upwards [hmodel, hη.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with j hj hs
    exact ⟨hj.1.normalize (s.size_ge j) hs, hj.2⟩

end
end Erdos1045.EventualExact.CoarseFekete

namespace Erdos1045.EventualExact.CommonLocalization

open Filter Configuration ExteriorClassical ExteriorBoundary ExteriorSupport HullGeometry
open CoarseFekete
open scoped Topology
noncomputable section

/-- No exterior model is an input to this endpoint. -/
theorem normalized_fekete_localization_with_perimeter {N : ℕ → ℕ}
    (hN4 : ∀ j, 4 ≤ N j) (hN : Tendsto N atTop atTop) (z : ∀ j, Points (N j))
    (hinj : ∀ j, Function.Injective (z j))
    (hP : ∀ j, hullPerimeter (z j) = 2 * Real.pi)
    (hF : ∀ j, Fekete (z j)) (hΔ : ∀ j, (N j : ℝ) ^ N j ≤ discriminant (z j)) :
    ∃ (σ : ∀ j, Equiv.Perm (Fin (N j))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ),
      Tendsto η atTop (𝓝 0) ∧ ∀ᶠ j in atTop,
        NormalizedRelativeEdgeModel (z j) (σ j) (α j) (β j) (u j) (η j) ∧
        boundaryLength (fun i => z j (σ j i)) ≤ hullPerimeter (z j) := by
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
  obtain ⟨σ, α, β, u, η, hη, hm⟩ := s.normalized_relative_edge_localization_with_perimeter
  refine ⟨fun j => (σ j).trans (τ j), α, β, u, η, hη, ?_⟩
  filter_upwards [hm] with j hj
  refine ⟨hj.1.relabel, ?_⟩
  have hb := hj.2
  change boundaryLength (fun i => z j (τ j (σ j i))) ≤ hullPerimeter (z j ∘ τ j) at hb
  rw [hullPerimeter_perm_proved] at hb
  exact hb

/-- Every growing sequence of genuine diameter or perimeter maximizers admits
the common normalized local coordinates, with relative edge error tending to zero. -/
theorem extremal_sequence_localization_with_perimeter {N : ℕ → ℕ}
    (hN4 : ∀ j, 4 ≤ N j) (hN : Tendsto N atTop atTop) (z : ∀ j, Points (N j))
    (hz : ∀ j, ExtremalNormalization.DiameterExtremal (z j) ∨ PerimeterExtremal (N j) (z j)) :
    ∃ (σ : ∀ j, Equiv.Perm (Fin (N j))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ),
      Tendsto η atTop (𝓝 0) ∧ ∀ᶠ j in atTop,
        NormalizedRelativeEdgeModel (z j) (σ j) (α j) (β j) (u j) (η j) ∧
        boundaryLength (fun i => z j (σ j i)) ≤ hullPerimeter (z j) := by
  have h (j : ℕ) := ExtremalNormalization.extremal_normalized (hN4 j) (hz j)
  obtain ⟨σ, α, β, u, η, hη, hm⟩ := normalized_fekete_localization_with_perimeter hN4 hN
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
  refine ⟨hj.1.unscale (hc j), ?_⟩
  have hL := boundaryLength_affine (fun i => z j (σ j i)) 0 (c j)
  simp only [zero_add] at hL
  have hP := classicalBackground_proved.toClassicalAnalysis.geometry.affine (N j) (z j) 0 (c j)
  simp only [zero_add] at hP
  have hb := hj.2
  change boundaryLength (fun i => c j * z j (σ j i)) ≤
    hullPerimeter (fun i => c j * z j i) at hb
  rw [hL, hP] at hb
  have hcpos : 0 < ‖c j‖ := norm_pos_iff.mpr (hc j)
  nlinarith

end
end Erdos1045.EventualExact.CommonLocalization

import EventualExact.FamilyPolarRigidity
import EventualExact.CanonicalPolarEdges
import Erdos1045.LocalNormalization

/-! Common relative-edge localization and removal of the two similarity modes. -/

namespace Erdos1045.EventualExact.CommonLocalization

open Filter Configuration ExteriorClassical ExteriorBoundary ExteriorSupport CyclicAngles
open scoped Topology BigOperators
noncomputable section

/-- A similarity representation of the actual labeled points with small relative edge error. -/
structure RelativeEdgeModel {n : ℕ} (z : Points n) (σ : Equiv.Perm (Fin n))
    (α β : ℂ) (u : ℕ → ℂ) (η : ℝ) : Prop where
  periodic : Function.Periodic u n
  scale_ne_zero : β ≠ 0
  coordinates : ∀ i : Fin n, z (σ i) = α + β * (LocalPhase.regularRoot n ^ (i : ℕ) + u i)
  error_nonneg : 0 ≤ η
  relative_edges : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖

structure NormalizedRelativeEdgeModel {n : ℕ} (z : Points n) (σ : Equiv.Perm (Fin n))
    (α β : ℂ) (u : ℕ → ℂ) (η : ℝ) : Prop extends RelativeEdgeModel z σ α β u η where
  mean_zero : (∑ j ∈ Finset.range n, u j) = 0
  similarity_zero : (∑ j ∈ Finset.range n,
    u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0

theorem RelativeEdgeModel.normalize {n : ℕ} {z : Points n} {σ : Equiv.Perm (Fin n)}
    {α β : ℂ} {u : ℕ → ℂ} {η : ℝ} (h : RelativeEdgeModel z σ α β u η)
    (hn : 4 ≤ n) (hη : η < 1) :
    NormalizedRelativeEdgeModel z σ (α + β * LocalNormalization.mean n u)
      (β * (1 + LocalNormalization.first n u)) (LocalNormalization.normalized n u)
      (2 * η / (1 - η)) := by
  have HF := ClosedFourier.orthogonality n (show 0 < n by omega)
  have hf := LocalNormalization.first_norm_bound ClosedFourier.dftInversion hn HF u
    h.periodic h.relative_edges
  have hd := LocalNormalization.denominator_ne_zero hf hη
  refine ⟨⟨LocalNormalization.normalized_periodic (by omega) u h.periodic,
    mul_ne_zero h.scale_ne_zero hd, ?_, ?_, ?_⟩,
    LocalNormalization.normalized_mean_zero (by omega) HF u,
    LocalNormalization.normalized_similarity_zero (by omega) HF u⟩
  · intro i
    have he := LocalNormalization.normalized_affine u hd i
    change LocalPhase.regularRoot n ^ (i : ℕ) + u i =
      LocalNormalization.mean n u + (1 + LocalNormalization.first n u) *
        (LocalPhase.regularRoot n ^ (i : ℕ) + LocalNormalization.normalized n u i) at he
    rw [h.coordinates, he]
    ring
  · exact div_nonneg (mul_nonneg (by norm_num) h.error_nonneg) (by linarith)
  · exact LocalNormalization.normalized_step u h.error_nonneg hη hf h.relative_edges

end
end Erdos1045.EventualExact.CommonLocalization

namespace Erdos1045.EventualExact.CoarseFekete

open Filter Configuration ExteriorClassical ExteriorBoundary ExteriorSupport CyclicAngles
open CommonLocalization CanonicalPolarEdges
open scoped Topology
noncomputable section

theorem Family.relative_edge_localization (s : Family) :
    ∃ (σ : ∀ j, Equiv.Perm (Fin (s.size j))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ),
      Tendsto η atTop (𝓝 0) ∧
      ∀ᶠ j in atTop, RelativeEdgeModel (s.points j) (σ j) (α j) (β j) (u j) (η j) := by
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
theorem Family.normalized_relative_edge_localization (s : Family) :
    ∃ (σ : ∀ j, Equiv.Perm (Fin (s.size j))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ),
      Tendsto η atTop (𝓝 0) ∧ ∀ᶠ j in atTop,
        NormalizedRelativeEdgeModel (s.points j) (σ j) (α j) (β j) (u j) (η j) := by
  obtain ⟨σ, α, β, u, η, hη, hmodel⟩ := s.relative_edge_localization
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
    exact hj.normalize (s.size_ge j) hs

end
end Erdos1045.EventualExact.CoarseFekete

import EventualExact.ExteriorSupportBounds
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Sequences

/-! Every boundary point of a closed convex planar set admits a unit support
normal, including degenerate sets. Actual exterior nodes lie on that boundary. -/

namespace Erdos1045.EventualExact.BoundarySupport

open Filter Set Complex ExteriorClassical ExteriorBoundary Configuration
open scoped Topology ComplexConjugate
noncomputable section

theorem exists_unit_strict_separator {K : Set ℂ} (hK : Convex ℝ K) (hclosed : IsClosed K)
    (hne : K.Nonempty) {x : ℂ} (hx : x ∉ K) :
    ∃ ν : ℂ, ‖ν‖ = 1 ∧ ∀ y ∈ K, (conj ν * y).re < (conj ν * x).re := by
  obtain ⟨f, c, hfc, hcx⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hK hclosed hx
  have hmap (w : ℂ) : f w = f 1 * w := by
    simpa only [smul_eq_mul, mul_one, mul_comm] using f.map_smul w (1 : ℂ)
  have hf : f 1 ≠ 0 := by
    intro hzero
    obtain ⟨p, hp⟩ := hne
    have hh := (hfc p hp).trans hcx
    rw [hmap p, hmap x, hzero] at hh
    simp at hh
  have hnorm : 0 < ‖f 1‖ := norm_pos_iff.mpr hf
  let ν := conj (f 1) / (‖f 1‖ : ℂ)
  have heval (w : ℂ) : (conj ν * w).re = (f w).re / ‖f 1‖ := by
    simp only [ν, map_div₀, conj_conj, conj_ofReal, div_mul_eq_mul_div, ← hmap, div_ofReal_re]
  refine ⟨ν, ?_, ?_⟩
  · simp [ν, Complex.norm_real, hnorm.ne']
  · intro y hy
    rw [heval, heval]
    exact (div_lt_div_iff_of_pos_right hnorm).2 ((hfc y hy).trans hcx)

theorem exists_unit_separator {K : Set ℂ} (hK : Convex ℝ K) (hclosed : IsClosed K)
    (hne : K.Nonempty) {x : ℂ} (hx : x ∉ K) :
    ∃ ν : ℂ, ‖ν‖ = 1 ∧ ∀ y ∈ K, (conj ν * y).re ≤ (conj ν * x).re := by
  obtain ⟨ν, hν, hs⟩ := exists_unit_strict_separator hK hclosed hne hx
  exact ⟨ν, hν, fun y hy => (hs y hy).le⟩

theorem exists_unit_support_at_frontier {K : Set ℂ} (hK : Convex ℝ K)
    (hclosed : IsClosed K) {p : ℂ} (hp : p ∈ frontier K) :
    ∃ ν : ℂ, ‖ν‖ = 1 ∧ ∀ v ∈ K, (conj ν * v).re ≤ (conj ν * p).re := by
  have hpK := hclosed.frontier_subset hp
  have hpcomp : p ∈ closure Kᶜ := by
    rw [frontier_eq_closure_inter_closure] at hp
    exact hp.2
  obtain ⟨q, hq, hqlim⟩ := mem_closure_iff_seq_limit.mp hpcomp
  have hsep (j : ℕ) := exists_unit_separator hK hclosed ⟨p, hpK⟩ (hq j)
  choose ν hν hsep using hsep
  obtain ⟨v, hv, φ, hφ, hνlim⟩ := (isCompact_sphere (0 : ℂ) 1).tendsto_subseq
    (fun j => by simpa only [Metric.mem_sphere, dist_zero_right] using hν j)
  refine ⟨v, by simpa only [Metric.mem_sphere, dist_zero_right] using hv, ?_⟩
  intro y hy
  have hc := (Complex.continuous_conj.tendsto v).comp hνlim
  have hl := (Complex.continuous_re.tendsto (conj v * y)).comp (hc.mul_const y)
  have hr := (Complex.continuous_re.tendsto (conj v * p)).comp
    (hc.mul (hqlim.comp hφ.tendsto_atTop))
  exact le_of_tendsto_of_tendsto' hl hr (fun j => hsep (φ j) y hy)

theorem exists_unit_support_at_frontier_centered {K : Set ℂ} (hK : Convex ℝ K)
    (hclosed : IsClosed K) {p : ℂ} (hp : p ∈ frontier K) (center : ℂ) :
    ∃ ν : ℂ, ‖ν‖ = 1 ∧ ∀ v ∈ K,
      (conj ν * (v - center)).re ≤ (conj ν * (p - center)).re := by
  obtain ⟨ν, hν, hs⟩ := exists_unit_support_at_frontier hK hclosed hp
  refine ⟨ν, hν, ?_⟩
  intro v hv
  simp only [mul_sub, sub_re]
  exact sub_le_sub_right (hs v hv) _

theorem node_mem_frontier {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (i : Fin n) : z i ∈ frontier (hull z) := by
  rw [← HF.boundary_image]
  exact ⟨unit (d.angles.angle i), norm_unit _, (d.node_identity i).symm⟩

theorem exists_node_unit_support {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (i : Fin n) (center : ℂ) :
    ∃ ν : ℂ, ‖ν‖ = 1 ∧ ∀ v ∈ hull z,
      (conj ν * (v - center)).re ≤ (conj ν * (z i - center)).re :=
  exists_unit_support_at_frontier_centered (convex_convexHull ℝ _)
    ((Set.finite_range z).isClosed_convexHull ℝ) (node_mem_frontier d HF i) center

theorem exists_node_unit_normals {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (center : ℂ) :
    ∃ ν : Fin n → ℂ, (∀ i, ‖ν i‖ = 1) ∧ ∀ i, ∀ v ∈ hull z,
      (conj (ν i) * (v - center)).re ≤ (conj (ν i) * (z i - center)).re := by
  classical
  choose ν hν hs using fun i => exists_node_unit_support d HF i center
  exact ⟨ν, hν, hs⟩

theorem map_unit_direction_lower {n : ℕ} {z : Points n} (d : ExteriorData z)
    {ν : ℂ} (hν : ‖ν‖ = 1) :
    d.capacity - ExteriorSupport.errorRadius d ≤
      (conj ν * (d.map ν - ExteriorSupport.center d)).re := by
  have he := ExteriorSupport.map_error_le d hν
  have hre : |(conj ν * (d.map ν - ExteriorSupport.center d - (d.capacity : ℂ) * ν)).re| ≤
      ExteriorSupport.errorRadius d := by
    calc
      _ ≤ ‖conj ν * (d.map ν - ExteriorSupport.center d - (d.capacity : ℂ) * ν)‖ :=
        Complex.abs_re_le_norm _
      _ = ‖d.map ν - ExteriorSupport.center d - (d.capacity : ℂ) * ν‖ := by simp [hν]
      _ ≤ _ := he
  have hcn : conj ν * ν = 1 := by
    rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq, hν]
    norm_num
  have heq : (conj ν * (d.map ν - ExteriorSupport.center d - (d.capacity : ℂ) * ν)).re =
      (conj ν * (d.map ν - ExteriorSupport.center d)).re - d.capacity := by
    rw [mul_sub, show conj ν * ((d.capacity : ℂ) * ν) = (d.capacity : ℂ) by
      calc
        _ = (d.capacity : ℂ) * (conj ν * ν) := by ring
        _ = _ := by rw [hcn, mul_one]]
    simp
  rw [heq] at hre
  linarith [(abs_le.mp hre).1]

/-- Uniform boundary proximity fills the entire inner disk by convex separation. -/
theorem inner_disk_subset_hull {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) :
    Metric.closedBall (ExteriorSupport.center d) (d.capacity - ExteriorSupport.errorRadius d) ⊆
      hull z := by
  intro x hx
  by_contra hnot
  have hne : (hull z).Nonempty :=
    ⟨d.map 1, ExteriorSupport.map_mem_hull d HF (by simp)⟩
  obtain ⟨ν, hν, hs⟩ := exists_unit_strict_separator (convex_convexHull ℝ _)
    ((Set.finite_range z).isClosed_convexHull ℝ) hne hnot
  have hsep := hs (d.map ν) (ExteriorSupport.map_mem_hull d HF hν)
  have hlow := map_unit_direction_lower d hν
  have hupper : (conj ν * (x - ExteriorSupport.center d)).re ≤
      d.capacity - ExteriorSupport.errorRadius d := by
    calc
      _ ≤ ‖conj ν * (x - ExteriorSupport.center d)‖ := Complex.re_le_norm _
      _ = ‖x - ExteriorSupport.center d‖ := by simp [hν]
      _ ≤ _ := mem_closedBall_iff_norm.mp hx
  have hstrict : (conj ν * (d.map ν - ExteriorSupport.center d)).re <
      (conj ν * (x - ExteriorSupport.center d)).re := by
    simp only [mul_sub, sub_re]
    exact sub_lt_sub_right hsep _
  exact (not_lt_of_ge hupper) (hlow.trans_lt hstrict)

theorem center_mem_interior {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (he : ExteriorSupport.errorRadius d < d.capacity) :
    ExteriorSupport.center d ∈ interior (hull z) := by
  apply mem_interior_iff_mem_nhds.mpr
  exact mem_of_superset (Metric.closedBall_mem_nhds _ (sub_pos.mpr he)) (inner_disk_subset_hull d HF)

end
end Erdos1045.EventualExact.BoundarySupport

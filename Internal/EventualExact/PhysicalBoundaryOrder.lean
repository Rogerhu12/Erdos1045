import BoundaryPolygonLength
import EventualExact.OrderedLiftPreimages
import EventualExact.BoundarySupportNormal
import EventualExact.ExteriorRadialPairs

/-! The physical polar order is realized by ordered preimages of the actual
exterior boundary map. Only its continuity and near-circle estimate are used. -/

namespace Erdos1045.EventualExact.PhysicalBoundaryOrder

open Set Complex CyclicAngles ExteriorClassical ExteriorBoundary Configuration
open scoped Topology ComplexConjugate
noncomputable section

variable {n : ℕ} {z : Points n}

def rotatedBoundary (d : ExteriorData z) (t : ℝ) : ℂ :=
  (d.map (unit t) - ExteriorSupport.center d) * conj (unit t)

def physicalLift (d : ExteriorData z) (t : ℝ) : ℝ :=
  t + (rotatedBoundary d t).arg

theorem unit_mul_conj (t : ℝ) : unit t * conj (unit t) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_unit]
  norm_num

theorem rotatedBoundary_mul_unit (d : ExteriorData z) (t : ℝ) :
    rotatedBoundary d t * unit t = d.map (unit t) - ExteriorSupport.center d := by
  dsimp [rotatedBoundary]
  rw [mul_assoc, mul_comm (conj (unit t)), unit_mul_conj, mul_one]

theorem rotatedBoundary_re_pos (d : ExteriorData z)
    (he : ExteriorSupport.errorRadius d < d.capacity) (t : ℝ) :
    0 < (rotatedBoundary d t).re := by
  have h := BoundarySupport.map_unit_direction_lower d (norm_unit t)
  have hh : (conj (unit t) * (d.map (unit t) - ExteriorSupport.center d)).re =
      (rotatedBoundary d t).re := by simp only [rotatedBoundary, mul_comm]
  rw [hh] at h
  linarith

theorem rotatedBoundary_continuous (d : ExteriorData z) (HF : FaberIdentities d) :
    Continuous (rotatedBoundary d) := by
  have hu : Continuous unit := by unfold unit; fun_prop
  exact ((HF.map_continuous.comp_continuous hu (fun t => (norm_unit t).ge)).sub continuous_const).mul
    (Complex.continuous_conj.comp hu)

theorem physicalLift_continuous (d : ExteriorData z) (HF : FaberIdentities d)
    (he : ExteriorSupport.errorRadius d < d.capacity) : Continuous (physicalLift d) := by
  apply continuous_id.add
  exact continuous_iff_continuousAt.mpr fun t =>
    (Complex.continuousAt_arg (Or.inl (rotatedBoundary_re_pos d he t))).comp
      (rotatedBoundary_continuous d HF).continuousAt

theorem physicalLift_period (d : ExteriorData z) (t : ℝ) :
    physicalLift d (t + 2 * Real.pi) = physicalLift d t + 2 * Real.pi := by
  simp only [physicalLift, rotatedBoundary, ExteriorReduction.unit_two_pi_periodic t]
  ring

theorem physicalLift_surjective (d : ExteriorData z) (HF : FaberIdentities d)
    (he : ExteriorSupport.errorRadius d < d.capacity) :
    Function.Surjective (physicalLift d) := by
  intro y
  have hl : physicalLift d (y - 2 * Real.pi) ≤ y := by
    dsimp [physicalLift]
    linarith [Complex.arg_le_pi (rotatedBoundary d (y - 2 * Real.pi)), Real.pi_pos]
  have hr : y ≤ physicalLift d (y + 2 * Real.pi) := by
    dsimp [physicalLift]
    linarith [Complex.neg_pi_lt_arg (rotatedBoundary d (y + 2 * Real.pi)), Real.pi_pos]
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc
    (show y - 2 * Real.pi ≤ y + 2 * Real.pi by linarith [Real.pi_pos])
    (physicalLift_continuous d HF he).continuousOn ⟨hl, hr⟩
  exact ⟨t, ht⟩

theorem physicalLift_polar (d : ExteriorData z) (t : ℝ) :
    d.map (unit t) - ExteriorSupport.center d =
      (‖d.map (unit t) - ExteriorSupport.center d‖ : ℂ) * unit (physicalLift d t) := by
  have he := Complex.norm_mul_exp_arg_mul_I (rotatedBoundary d t)
  have hn : ‖rotatedBoundary d t‖ = ‖d.map (unit t) - ExteriorSupport.center d‖ := by
    simp [rotatedBoundary]
  calc
    _ = rotatedBoundary d t * unit t := (rotatedBoundary_mul_unit d t).symm
    _ = ((‖rotatedBoundary d t‖ : ℂ) * unit (rotatedBoundary d t).arg) * unit t := by
      congr 1
      exact he.symm
    _ = _ := by rw [physicalLift, ExteriorSupport.unit_add, hn]; ring

/-- Two boundary points on the same ray from the controlled interior center agree. -/
theorem frontier_same_ray (d : ExteriorData z) (HF : FaberIdentities d)
    (he : ExteriorSupport.errorRadius d < d.capacity)
    {p q : ℂ} (hp : p ∈ frontier (hull z)) (hq : q ∈ frontier (hull z))
    {R S θ : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hpR : p - ExteriorSupport.center d = (R : ℂ) * unit θ)
    (hqS : q - ExteriorSupport.center d = (S : ℂ) * unit θ) : p = q := by
  have hclosed : IsClosed (hull z) := (Set.finite_range z).isClosed_convexHull ℝ
  have hconv : Convex ℝ (hull z) := convex_convexHull ℝ _
  have hle {v w : ℂ} (hv : v ∈ frontier (hull z)) (hw : w ∈ hull z)
      {r s : ℝ} (hr : 0 ≤ r)
      (hvR : v - ExteriorSupport.center d = (r : ℂ) * unit θ)
      (hwS : w - ExteriorSupport.center d = (s : ℂ) * unit θ) : s ≤ r := by
    obtain ⟨ν, hν, hsupport⟩ := BoundarySupport.exists_unit_support_at_frontier_centered
      hconv hclosed hv (ExteriorSupport.center d)
    have hlow := ExteriorSupport.support_lower d HF hν hsupport
    have hsw := hsupport w hw
    have hm (u : ℝ) : (conj ν * ((u : ℂ) * unit θ)).re = u * (conj ν * unit θ).re := by
      rw [show conj ν * ((u : ℂ) * unit θ) = (u : ℂ) * (conj ν * unit θ) by ring]
      simp
    rw [hvR, hm] at hlow
    rw [hvR, hwS, hm, hm] at hsw
    have hk : 0 < (conj ν * unit θ).re := by
      by_contra hnot
      have hh := mul_nonpos_of_nonneg_of_nonpos hr (le_of_not_gt hnot)
      linarith
    exact (mul_le_mul_iff_left₀ hk).mp hsw
  have heq : R = S := le_antisymm (hle hq (hclosed.frontier_subset hp) hS hqS hpR)
    (hle hp (hclosed.frontier_subset hq) hR hpR hqS)
  have hh : p - ExteriorSupport.center d = q - ExteriorSupport.center d := by
    rw [hpR, hqS, heq]
  exact sub_left_injective hh

/-- Physical angle sorting yields genuinely ordered exterior preimages. -/
theorem physical_ordered_preimages (d : ExteriorData z) (HF : FaberIdentities d)
    (hn : 0 < n) (he : ExteriorSupport.errorRadius d < d.capacity)
    (σ : Equiv.Perm (Fin n)) (a : Angles n)
    (hpolar : ∀ i : Fin n, z (σ i) - ExteriorSupport.center d =
      (‖z (σ i) - ExteriorSupport.center d‖ : ℂ) * unit (a.angle i)) :
    ∃ b : Angles n, ∀ i : Fin n, d.map (unit (b.angle i)) = z (σ i) := by
  obtain ⟨b, hb⟩ := ordered_lift_preimages hn a (physicalLift_continuous d HF he)
    (physicalLift_surjective d HF he) (physicalLift_period d)
  refine ⟨b, fun i => ?_⟩
  have hmap : d.map (unit (b.angle i)) ∈ frontier (hull z) := by
    rw [← HF.boundary_image]
    exact ⟨unit (b.angle i), norm_unit _, rfl⟩
  apply frontier_same_ray d HF he hmap (BoundarySupport.node_mem_frontier d HF (σ i))
    (R := ‖d.map (unit (b.angle i)) - ExteriorSupport.center d‖)
    (S := ‖z (σ i) - ExteriorSupport.center d‖)
    (norm_nonneg _) (norm_nonneg _) _ (hpolar i)
  simpa only [hb] using physicalLift_polar d (b.angle i)

end
end Erdos1045.EventualExact.PhysicalBoundaryOrder


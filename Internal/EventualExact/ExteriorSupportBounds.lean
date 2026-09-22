import Erdos1045.ClosedHolder
import EventualExact.PolarTangentCone
import Mathlib.Analysis.Convex.Topology

/-! Actual exterior data give uniform hull and support estimates after translation. -/

namespace Erdos1045.EventualExact.ExteriorSupport

open Complex Set Metric ExteriorClassical ExteriorBoundary Configuration
open scoped ComplexConjugate
noncomputable section

def center {n : ℕ} {z : Points n} (d : ExteriorData z) : ℂ :=
  d.offset + laurent d.coefficient 1

def errorRadius {n : ℕ} {z : Points n} (d : ExteriorData z) : ℝ :=
  6 * Real.sqrt d.energySquared

theorem errorRadius_nonneg {n : ℕ} {z : Points n} (d : ExteriorData z) :
    0 ≤ errorRadius d := by unfold errorRadius; positivity

theorem map_error_le {n : ℕ} {z : Points n} (d : ExteriorData z)
    {u : ℂ} (hu : ‖u‖ = 1) :
    ‖d.map u - center d - (d.capacity : ℂ) * u‖ ≤ errorRadius d := by
  have h := ClosedSeries.laurent_holder_bound d.coefficient d.sobolev u 1
    hu.ge (by simp)
  rw [← d.parseval_identity] at h
  have hdist : ‖u - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖u‖ + ‖(1 : ℂ)‖ := norm_sub_le u 1
      _ = 2 := by rw [hu]; norm_num
  have hsqrt : Real.sqrt ‖u - 1‖ ≤ 3 / 2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith
  have he : d.map u - center d - (d.capacity : ℂ) * u =
      laurent d.coefficient u - laurent d.coefficient 1 := by
    unfold ExteriorData.map center
    ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hsqrt (by positivity :
    0 ≤ 4 * Real.sqrt d.energySquared)
  unfold errorRadius
  linarith

theorem map_mem_hull {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) {u : ℂ} (hu : ‖u‖ = 1) : d.map u ∈ hull z := by
  have hb : d.map u ∈ frontier (hull z) := by
    rw [← HF.boundary_image]
    exact ⟨u, hu, rfl⟩
  have hc : IsClosed (hull z) := (Set.finite_range z).isClosed_convexHull ℝ
  exact hc.frontier_subset hb

theorem node_norm_le {n : ℕ} {z : Points n} (d : ExteriorData z) (i : Fin n) :
    ‖z i - center d‖ ≤ d.capacity + errorRadius d := by
  have he := map_error_le d (norm_unit (d.angles.angle i))
  have hnode : d.map (unit (d.angles.angle i)) = z i := (d.node_identity i).symm
  rw [hnode] at he
  have hn : ‖(d.capacity : ℂ) * unit (d.angles.angle i)‖ = d.capacity := by
    simp [abs_of_pos d.capacity_pos]
  have ht := norm_add_le (z i - center d - (d.capacity : ℂ) * unit (d.angles.angle i))
    ((d.capacity : ℂ) * unit (d.angles.angle i))
  simp only [sub_add_cancel] at ht
  linarith

theorem hull_norm_le {n : ℕ} {z : Points n} (d : ExteriorData z)
    {w : ℂ} (hw : w ∈ hull z) : ‖w - center d‖ ≤ d.capacity + errorRadius d := by
  have hsub : hull z ⊆ closedBall (center d) (d.capacity + errorRadius d) := by
    apply convexHull_min _ (convex_closedBall _ _)
    rintro _ ⟨i, rfl⟩
    exact mem_closedBall_iff_norm.mpr (node_norm_le d i)
  exact mem_closedBall_iff_norm.mp (hsub hw)

theorem support_lower {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) {ν w : ℂ} (hν : ‖ν‖ = 1)
    (hsupport : ∀ v ∈ hull z, (conj ν * (v - center d)).re ≤
      (conj ν * (w - center d)).re) :
    d.capacity - errorRadius d ≤ (conj ν * (w - center d)).re := by
  have hs := hsupport (d.map ν) (map_mem_hull d HF hν)
  have he := map_error_le d hν
  have hre : |(conj ν * (d.map ν - center d - (d.capacity : ℂ) * ν)).re| ≤
      errorRadius d := by
    calc
      _ ≤ ‖conj ν * (d.map ν - center d - (d.capacity : ℂ) * ν)‖ :=
        Complex.abs_re_le_norm _
      _ = ‖d.map ν - center d - (d.capacity : ℂ) * ν‖ := by simp [hν]
      _ ≤ _ := he
  have hcn : conj ν * ν = 1 := by
    rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq, hν]
    norm_num
  have heq : (conj ν * (d.map ν - center d - (d.capacity : ℂ) * ν)).re =
      (conj ν * (d.map ν - center d)).re - d.capacity := by
    rw [mul_sub, show conj ν * ((d.capacity : ℂ) * ν) = (d.capacity : ℂ) by
      calc
        _ = (d.capacity : ℂ) * (conj ν * ν) := by ring
        _ = _ := by rw [hcn, mul_one]]
    simp
  rw [heq] at hre
  linarith [(abs_le.mp hre).1]

/-- The slope is controlled using the existing exterior energy, without an area formula. -/
theorem tangent_slope_le_error {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hc : 1 / 2 ≤ d.capacity)
    (he : errorRadius d ≤ 1 / 4) {ν w : ℂ} (hν : ‖ν‖ = 1)
    (hw : w ∈ hull z)
    (hsupport : ∀ v ∈ hull z, (conj ν * (v - center d)).re ≤
      (conj ν * (w - center d)).re) (speed : ℝ) :
    |PolarSlopeEnergy.polarSlope (w - center d) (I * (speed : ℂ) * ν)| ≤
      8 * Real.sqrt (errorRadius d) := by
  have hρ := errorRadius_nonneg d
  have hc1 := d.toBoundaryData.capacity_le_one
  have hr : 1 / 4 ≤ d.capacity - errorRadius d := by linarith
  have hr2 : 1 / 16 ≤ (d.capacity - errorRadius d) ^ 2 := by nlinarith
  have ho := hull_norm_le d hw
  have ho2 : ‖w - center d‖ ^ 2 ≤ (d.capacity + errorRadius d) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by linarith [d.capacity_pos])).mpr ho
  apply PolarSlopeEnergy.tangent_slope_le hν (by linarith : 0 < d.capacity - errorRadius d)
    (by positivity) (support_lower d HF hν hsupport)
  have hsqrt := Real.sq_sqrt hρ
  have hh : (8 * Real.sqrt (errorRadius d)) ^ 2 = 64 * errorRadius d := by nlinarith
  rw [hh]
  have hmul := mul_le_mul_of_nonneg_right hr2 (by positivity : 0 ≤ 64 * errorRadius d)
  have hcρ := mul_le_mul_of_nonneg_right hc1 hρ
  nlinarith

end
end Erdos1045.EventualExact.ExteriorSupport

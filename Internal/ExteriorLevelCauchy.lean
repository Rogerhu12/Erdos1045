import BernsteinWalshExterior
import ExteriorEnvelopeTopology
import LevelContainment

/-! Actual exterior sublevel geometry and the Cauchy--Bernstein--Walsh bound.
No Jordan theorem or assumed level-set Cauchy estimate is used. -/

namespace ExteriorReduction

open Complex Metric Set
open ExteriorEnvelope
noncomputable section

def exteriorSublevel (K : Set ℂ) (Φ : ℂ → ℂ) (r : ℝ) : Set ℂ :=
  {z | inverseNormEnvelope K Φ z ≤ r}

theorem frontier_exteriorSublevel_image {K : Set ℂ} {Ψ Φ : ℂ → ℂ}
    (hU : Continuous (inverseNormEnvelope K Φ))
    (hright : ∀ z ∈ Kᶜ, Ψ (Φ z) = z) {r : ℝ} (hr : 1 < r) :
    frontier (exteriorSublevel K Φ r) ⊆ Ψ '' sphere (0 : ℂ) r := by
  intro z hz
  have he : inverseNormEnvelope K Φ z = r :=
    frontier_le_subset_eq hU continuous_const hz
  have hzK : z ∉ K := by
    intro hzK
    rw [inverseNormEnvelope_eq_one hzK] at he
    linarith
  refine ⟨Φ z, ?_, hright z hzK⟩
  rw [mem_sphere_zero_iff_norm, ← inverseNormEnvelope_eq_norm hzK]
  exact he

/-- Separation from the frontier bounds distance from every point of the set.
The nearest-frontier point is taken in the complement, so no convexity is needed. -/
theorem separation_from_frontier_to_set {K : Set ℂ} (hK : K.Nonempty)
    {y : ℂ} (hy : y ∉ K) {h : ℝ}
    (hsep : ∀ v ∈ frontier K, h ≤ ‖y - v‖) : ∀ x ∈ K, h ≤ ‖y - x‖ := by
  have hproper : Kᶜ ≠ univ := by
    intro he
    obtain ⟨x, hx⟩ := hK
    have : x ∈ Kᶜ := by rw [he]; trivial
    exact this hx
  obtain ⟨v, hv, hd⟩ := exists_mem_frontier_infDist_compl_eq_dist hy hproper
  rw [frontier_compl] at hv
  simp only [compl_compl] at hd
  intro x hx
  calc
    h ≤ ‖y - v‖ := hsep v hv
    _ = infDist y K := by rw [hd, dist_eq_norm]
    _ ≤ ‖y - x‖ := by simpa only [dist_eq_norm] using (infDist_le_dist_of_mem (x := y) hx)

theorem exteriorSublevel_contains_disks {K : Set ℂ} {Ψ Φ : ℂ → ℂ}
    (hK : K.Nonempty) (hU : Continuous (inverseNormEnvelope K Φ))
    (hright : ∀ z ∈ Kᶜ, Ψ (Φ z) = z)
    (hboundary : ∀ v ∈ frontier K, ∃ u : ℂ, ‖u‖ = 1 ∧ Ψ u = v)
    {r h : ℝ} (hr : 1 < r)
    (hsep : ∀ u v : ℂ, ‖u‖ = r → ‖v‖ = 1 → h ≤ ‖Ψ u - Ψ v‖) :
    ∀ x ∈ K, ball x h ⊆ exteriorSublevel K Φ r := by
  apply disks_subset_of_frontier_separation
  · intro x hx
    change inverseNormEnvelope K Φ x ≤ r
    rw [inverseNormEnvelope_eq_one hx]
    exact hr.le
  · intro x hx z hz
    have he : inverseNormEnvelope K Φ z = r := frontier_le_subset_eq hU continuous_const hz
    have hzK : z ∉ K := by
      intro hzK
      rw [inverseNormEnvelope_eq_one hzK] at he
      linarith
    obtain ⟨u, hu, rfl⟩ := frontier_exteriorSublevel_image hU hright hr hz
    apply separation_from_frontier_to_set hK hzK _ x hx
    intro v hv
    obtain ⟨w, hw, rfl⟩ := hboundary v hv
    exact hsep u w (mem_sphere_zero_iff_norm.mp hu) hw

theorem polynomial_bound_on_exteriorSublevel (p : Polynomial ℂ) (A : ℂ)
    {K : Set ℂ} {q Ψ Φ : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1))
    (hΨ : ContinuousOn Ψ {w : ℂ | 1 ≤ ‖w‖})
    (hmatch : ∀ w ∈ exteriorDisk, Ψ w = A + w * q w⁻¹)
    (hboundary : ∀ w : ℂ, ‖w‖ = 1 → Ψ w ∈ K)
    (hΦmap : MapsTo Φ Kᶜ exteriorDisk) (hright : ∀ z ∈ Kᶜ, Ψ (Φ z) = z)
    (hp : ∀ x ∈ K, ‖p.eval x‖ ≤ 1) {r : ℝ} (hr : 1 < r) :
    ∀ x ∈ exteriorSublevel K Φ r, ‖p.eval x‖ ≤ r ^ p.natDegree := by
  intro x hx
  by_cases hxK : x ∈ K
  · exact (hp x hxK).trans (one_le_pow₀ hr.le)
  · have hb := polynomial_bernstein_walsh_exterior p A hq hΨ hmatch
      (fun w hw => hp (Ψ w) (hboundary w hw)) (hΦmap hxK)
    rw [hright x hxK] at hb
    have hnorm : ‖Φ x‖ ≤ r := by
      simpa only [exteriorSublevel, mem_ofPred_eq, inverseNormEnvelope_eq_norm hxK] using hx
    exact hb.trans (pow_le_pow_left₀ (norm_nonneg _) hnorm _)

/-- The concrete estimate replacing the former Cauchy--Bernstein--Walsh input.
All hypotheses describe ordinary maps, their boundary values and separation. -/
theorem cauchy_bernstein_walsh_actual (p : Polynomial ℂ) (A : ℂ)
    {K : Set ℂ} {q Ψ Φ : ℂ → ℂ} (hK : K.Nonempty)
    (hq : AnalyticOnNhd ℂ q (ball 0 1))
    (hΨ : ContinuousOn Ψ {w : ℂ | 1 ≤ ‖w‖})
    (hmatch : ∀ w ∈ exteriorDisk, Ψ w = A + w * q w⁻¹)
    (hboundaryMap : ∀ w : ℂ, ‖w‖ = 1 → Ψ w ∈ K)
    (hboundarySurj : ∀ v ∈ frontier K, ∃ u : ℂ, ‖u‖ = 1 ∧ Ψ u = v)
    (hΦmap : MapsTo Φ Kᶜ exteriorDisk) (hright : ∀ z ∈ Kᶜ, Ψ (Φ z) = z)
    (hU : Continuous (inverseNormEnvelope K Φ))
    {r h : ℝ} (hr : 1 < r) (hh : 0 < h)
    (hsep : ∀ u v : ℂ, ‖u‖ = r → ‖v‖ = 1 → h ≤ ‖Ψ u - Ψ v‖)
    (hp : ∀ x ∈ K, ‖p.eval x‖ ≤ 1) :
    ∀ x ∈ K, ‖p.derivative.eval x‖ ≤ 2 * r ^ p.natDegree / h := by
  have hdisks := exteriorSublevel_contains_disks hK hU hright hboundarySurj hr hsep
  have hbound := polynomial_bound_on_exteriorSublevel p A hq hΨ hmatch hboundaryMap hΦmap hright hp hr
  intro x hx
  exact polynomial_cauchy_of_ball_bound p hh (fun y hy => hbound y (hdisks x hx hy))

#print axioms frontier_exteriorSublevel_image
#print axioms exteriorSublevel_contains_disks
#print axioms cauchy_bernstein_walsh_actual

end
end ExteriorReduction

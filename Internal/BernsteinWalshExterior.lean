import BernsteinWalshDisk
import ExteriorExistence

/-! Bernstein--Walsh for an actual exterior map with a continuous boundary
extension. The interior auxiliary model is constructed, not assumed. -/

namespace ExteriorReduction

open Complex Metric Set Filter
open scoped Topology
noncomputable section

def filledInverseModel (q Ψ : ℂ → ℂ) (A z : ℂ) : ℂ :=
  if z = 0 then q 0 else z * (Ψ z⁻¹ - A)

theorem filledInverseModel_eq {q Ψ : ℂ → ℂ} {A : ℂ}
    (hmatch : ∀ w ∈ exteriorDisk, Ψ w = A + w * q w⁻¹)
    {z : ℂ} (hz : z ∈ ball 0 1) : filledInverseModel q Ψ A z = q z := by
  by_cases hz0 : z = 0
  · simp [filledInverseModel, hz0]
  · rw [filledInverseModel, if_neg hz0, hmatch z⁻¹ (inv_mem_exterior_of_disk hz hz0), inv_inv]
    field_simp
    ring

theorem filledInverseModel_quotient (q Ψ : ℂ → ℂ) (A : ℂ) {z : ℂ} (hz : z ≠ 0) :
    A + filledInverseModel q Ψ A z / z = Ψ z⁻¹ := by
  simp only [filledInverseModel, if_neg hz]
  field_simp
  ring

private theorem inverse_mem_closedExterior {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1)
    (hz0 : z ≠ 0) : 1 ≤ ‖z⁻¹‖ := by
  rw [norm_inv]
  exact (one_le_inv₀ (norm_pos_iff.mpr hz0)).mpr (mem_closedBall_zero_iff.mp hz)

theorem filledInverseModel_diffContOnCl {q Ψ : ℂ → ℂ} (A : ℂ)
    (hq : AnalyticOnNhd ℂ q (ball 0 1))
    (hΨ : ContinuousOn Ψ {w : ℂ | 1 ≤ ‖w‖})
    (hmatch : ∀ w ∈ exteriorDisk, Ψ w = A + w * q w⁻¹) :
    DiffContOnCl ℂ (filledInverseModel q Ψ A) (ball 0 1) := by
  constructor
  · exact hq.differentiableOn.congr (fun z hz => filledInverseModel_eq hmatch hz)
  · rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    intro z hz
    by_cases hz0 : z = 0
    · subst z
      have he : filledInverseModel q Ψ A =ᶠ[𝓝 (0 : ℂ)] q := by
        filter_upwards [ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
        exact filledInverseModel_eq hmatch hz
      exact ((hq 0 (by simp)).continuousAt.congr_of_eventuallyEq he).continuousWithinAt
    · have hinv : Tendsto (fun v : ℂ => v⁻¹) (𝓝[closedBall 0 1] z)
          (𝓝[{w : ℂ | 1 ≤ ‖w‖}] z⁻¹) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨(continuousAt_inv₀ hz0).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (eventually_ne_nhds hz0)] with v hv hv0
        exact inverse_mem_closedExterior hv hv0
      have hcomp : ContinuousWithinAt (fun v : ℂ => Ψ v⁻¹) (closedBall 0 1) z :=
        (hΨ z⁻¹ (inverse_mem_closedExterior hz hz0)).tendsto.comp hinv
      have hc := continuousWithinAt_id.mul (hcomp.sub_const A)
      apply hc.congr_of_eventuallyEq _ (by simp [filledInverseModel, hz0])
      filter_upwards [nhdsWithin_le_nhds (eventually_ne_nhds hz0)] with v hv
      simp [filledInverseModel, hv]

/-- The ordinary Bernstein--Walsh growth bound for the given exterior map.
Only its actual analytic model and continuous circle values are inputs. -/
theorem polynomial_bernstein_walsh_exterior (p : Polynomial ℂ) (A : ℂ)
    {q Ψ : ℂ → ℂ} (hq : AnalyticOnNhd ℂ q (ball 0 1))
    (hΨ : ContinuousOn Ψ {w : ℂ | 1 ≤ ‖w‖})
    (hmatch : ∀ w ∈ exteriorDisk, Ψ w = A + w * q w⁻¹)
    (hboundary : ∀ w : ℂ, ‖w‖ = 1 → ‖p.eval (Ψ w)‖ ≤ 1)
    {w : ℂ} (hw : w ∈ exteriorDisk) : ‖p.eval (Ψ w)‖ ≤ ‖w‖ ^ p.natDegree := by
  have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hw)
  have hd := filledInverseModel_diffContOnCl A hq hΨ hmatch
  have hb : ∀ z : ℂ, ‖z‖ = 1 →
      ‖p.eval (A + filledInverseModel q Ψ A z / z)‖ ≤ 1 := by
    intro z hz
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by simp [hz])
    rw [filledInverseModel_quotient q Ψ A hz0]
    exact hboundary z⁻¹ (by simp [norm_inv, hz])
  have he := polynomial_bernstein_walsh_disk p A hd hb (inv_ne_zero hw0)
    (ball_subset_closedBall (inv_mem_disk_of_exterior hw))
  simpa only [filledInverseModel_quotient q Ψ A (inv_ne_zero hw0), inv_inv,
    norm_inv] using he

#print axioms filledInverseModel_diffContOnCl
#print axioms polynomial_bernstein_walsh_exterior

end
end ExteriorReduction

import CanonicalExteriorModel
import OrderedBoundaryAngles
import FeketeBoundary
import Erdos1045.ExteriorClassical

/-! Assemble the main proof's data from one actual conformal model. The only
geometric facts still supplied here are radial length and finite chord bounds. -/

namespace ExteriorReduction.ConvexExteriorModel

open Complex Metric Set Filter
open Erdos1045 Erdos1045.Configuration Erdos1045.ExteriorBoundary
open Erdos1045.ExteriorClassical
open scoped Topology
noncomputable section

variable {K : Set ℂ} (m : ConvexExteriorModel K)

def toBoundaryData (hK : IsCompact K) (hconv : Convex ℝ K)
    (hL : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[<] 1,
      m.capacity * radialMeanNorm m.D r ≤ 1 + ε) : BoundaryData where
  capacity := m.capacity
  capacity_pos := m.capacity_pos
  model := m.q
  model_analytic := m.q_analytic
  model_zero := m.q_zero
  model_derivative_ne := fun _ hz => m.D_ne_zero hK hz
  model_criterion := fun _ hz => (m.criterion_pos hK hconv hz).le
  radial_perimeter := hL

def toExteriorData (hK : IsCompact K) (hconv : Convex ℝ K)
    (hL : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[<] 1,
      m.capacity * radialMeanNorm m.D r ≤ 1 + ε)
    {n : ℕ} (z : Points n) (a : CyclicAngles.Angles n)
    (har : ∀ i : Fin n, 0 ≤ a.angle i ∧ a.angle i < 2 * Real.pi)
    (hz : ∀ i : Fin n, z i = m.map (unit (a.angle i)))
    (hP : boundaryLength z ≤ HullGeometry.hullPerimeter z) : ExteriorData z where
  toBoundaryData := m.toBoundaryData hK hconv hL
  offset := m.offset
  angles := a
  angle_range := har
  model_node_identity := fun i => (hz i).trans (m.map_formula _)
  boundary_perimeter := hP

variable (hK : IsCompact K) (hconv : Convex ℝ K)
  (hL : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[<] 1,
    m.capacity * radialMeanNorm m.D r ≤ 1 + ε)
  {n : ℕ} (z : Points n) (a : CyclicAngles.Angles n)
  (har : ∀ i : Fin n, 0 ≤ a.angle i ∧ a.angle i < 2 * Real.pi)
  (hz : ∀ i : Fin n, z i = m.map (unit (a.angle i)))
  (hP : boundaryLength z ≤ HullGeometry.hullPerimeter z)

theorem toExteriorData_map : (m.toExteriorData hK hconv hL z a har hz hP).map = m.map := by
  funext w
  exact (m.map_formula w).symm

theorem toExteriorData_faber (k : ℕ) (x : ℂ) :
    (m.toExteriorData hK hconv hL z a har hz hP).faber k x = m.faber k x := by
  have hc : (fun j => m.coefficient j / (m.capacity : ℂ)) =
      FaberKernel.laurentCoefficients (FaberKernel.taylorCoefficients m.q) := by
    funext j
    rw [← m.q_zero]
    exact modelLaurentCoefficient_normalized m.q j
  change (FaberAlgebra.normalizedFaber (fun j => m.coefficient j / (m.capacity : ℂ)) k).eval
    ((x - m.offset) / (m.capacity : ℂ)) = _
  rw [hc]
  unfold faber modelFaberValue FaberKernel.value FaberKernel.laurentVariable
  simp only [FaberKernel.taylorCoefficients_zero, FaberKernel.taylorCoefficients_one, m.q_zero]
  congr 2
  dsimp [offset]
  ring

theorem toExteriorData_faberIdentities (hull_eq : hull z = K) :
    FaberIdentities (m.toExteriorData hK hconv hL z a har hz hP) := by
  let d := m.toExteriorData hK hconv hL z a har hz hP
  have hm : d.map = m.map := m.toExteriorData_map hK hconv hL z a har hz hP
  have hf : ∀ k x, d.faber k x = m.faber k x := m.toExteriorData_faber hK hconv hL z a har hz hP
  have hd (w : ℂ) (hw : 1 < ‖w‖) : deriv m.map w = d.derivative w := m.map_deriv hw
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm, hull_eq]
    exact m.map_bijective hK
  · rw [hm]
    exact m.map_continuous hK hconv
  · intro w hw
    rw [hm, ← hd w hw]
    exact (m.map_hasDerivAt hw).differentiableAt.hasDerivAt
  · rw [hm, hull_eq]
    have hs : sphere (0 : ℂ) 1 = {w : ℂ | ‖w‖ = 1} := by ext w; simp
    rw [← hs]
    exact m.boundary_image hK hconv
  · intro k _ x hx
    rw [hf]
    exact m.faber_bound hK hconv (hull_eq ▸ hx) k
  · intro x hx r hr t
    have hxK : x ∈ K := hull_eq ▸ hx
    have hw : (r : ℂ) * unit t ∈ exteriorDisk := by
      simpa [exteriorDisk, norm_mul, norm_unit, abs_of_pos (zero_lt_one.trans hr)] using hr
    have hg := model_faber_fourier_generating m.q_analytic m.center x
      (fun _ hv => m.kernel_denominator_ne_zero hxK hv) r hr t
    have hder : deriv (fun v => m.center + v * m.q v⁻¹) ((r : ℂ) * unit t) =
        d.derivative ((r : ℂ) * unit t) := by
      rw [(hasDerivAt_laurentExterior m.q_analytic m.center hw).deriv]
      have hh := (m.map_hasDerivAt hw).deriv
      rw [hd _ hw] at hh
      exact hh.symm
    change FaberFourier.series (fun k => ((1 / r : ℝ) : ℂ) ^ k * d.faber k x) t = _
    simp_rw [hf]
    rw [hm, m.map_eq_open hw]
    exact hg.trans (by rw [hder]; rfl)
  · intro x hx r hr
    change Summable (fun k => ‖((1 / r : ℝ) : ℂ) ^ k * d.faber k x‖)
    simp_rw [hf]
    exact m.faber_generating_summable (hull_eq ▸ hx) hr
  · intro w hw
    rw [hm, hull_eq]
    exact m.map_mapsTo hK hw

#print axioms toExteriorData_faberIdentities

end
end ExteriorReduction.ConvexExteriorModel

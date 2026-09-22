import PositiveNormalization
import ExteriorEnvelopeModel
import LaurentEnergyLimit
import LaurentBoundaryExtension
import ExteriorLevelCauchy
import FaberExteriorGenerating

/-!
# The exterior model constructed from compact convex geometry

The record stores only an ordinary normalized disk biholomorphism. Analytic
criteria, Sobolev coefficients, boundary values and Bernstein--Walsh estimates
are theorems about that record, not additional fields or assumptions.
-/

namespace ExteriorReduction

open Complex Metric Set Filter
open scoped Topology
noncomputable section

structure ConvexExteriorModel (K : Set ℂ) where
  center : ℂ
  center_mem : center ∈ K
  capacity : ℝ
  capacity_pos : 0 < capacity
  f : ℂ → ℂ
  g : ℂ → ℂ
  f_differentiable : DifferentiableOn ℂ f (invertedComplement K center)
  g_differentiable : DifferentiableOn ℂ g (ball 0 1)
  f_bijective : BijOn f (invertedComplement K center) (ball 0 1)
  g_mapsTo : MapsTo g (ball 0 1) (invertedComplement K center)
  inverse : InvOn g f (invertedComplement K center) (ball 0 1)
  f_zero : f 0 = 0
  g_zero : g 0 = 0
  g_deriv_zero : deriv g 0 = ((capacity⁻¹ : ℝ) : ℂ)

theorem exists_convexExteriorModel {K : Set ℂ} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hnt : K.Nontrivial) : Nonempty (ConvexExteriorModel K) := by
  obtain ⟨A, hA, y, hy, hAy⟩ := hnt
  obtain ⟨f, g, c, hc, hf, hg, hbij, hgmap, hinv, hf0, hg0, hdg⟩ :=
    exists_positive_inverted_biholomorphic hK hconv hA hy hAy.symm
  exact ⟨⟨A, hA, c, hc, f, g, hf, hg, hbij, hgmap, hinv, hf0, hg0, hdg⟩⟩

namespace ConvexExteriorModel

variable {K : Set ℂ} (d : ConvexExteriorModel K)

def q : ℂ → ℂ := laurentModel d.g
def D : ℂ → ℂ := modelDerivative d.q
def coefficient : ℕ → ℂ := modelLaurentCoefficient d.q
def offset : ℂ := d.center + deriv d.q 0
def openMap : ℂ → ℂ := exteriorFromModel d.q d.center
def map : ℂ → ℂ := laurentBoundaryMap d.q d.center
def inverseMap : ℂ → ℂ := exteriorInverseFromDisk d.f d.center
def envelope : ℂ → ℝ := ExteriorEnvelope.inverseNormEnvelope K d.inverseMap
def faber (k : ℕ) (x : ℂ) : ℂ := modelFaberValue d.q d.center x k

@[simp] theorem coefficient_zero : d.coefficient 0 = 0 := modelLaurentCoefficient_zero d.q

theorem map_formula (w : ℂ) : d.map w =
    (d.capacity : ℂ) * w + d.offset + Erdos1045.ExteriorClassical.laurent d.coefficient w := by
  change d.q 0 * w + d.offset + Erdos1045.ExteriorClassical.laurent d.coefficient w = _
  rw [q, laurentModel_zero, d.g_deriv_zero, ← Complex.ofReal_inv, inv_inv]

theorem g_deriv_ne_zero_zero : deriv d.g 0 ≠ 0 := by
  rw [d.g_deriv_zero]
  exact Complex.ofReal_ne_zero.mpr (inv_ne_zero d.capacity_pos.ne')

theorem g_value_ne_zero {z : ℂ} (hz : z ∈ ball 0 1) (hz0 : z ≠ 0) : d.g z ≠ 0 :=
  StarLike.value_ne_zero d.inverse.2 d.g_zero hz hz0

theorem q_analytic : AnalyticOnNhd ℂ d.q (ball 0 1) :=
  laurentModel_analytic d.g_differentiable d.g_zero d.g_deriv_ne_zero_zero
    (fun _ hz hz0 => d.g_value_ne_zero hz hz0)

@[simp] theorem q_zero : d.q 0 = (d.capacity : ℂ) := by
  rw [q, laurentModel_zero, d.g_deriv_zero, ← Complex.ofReal_inv, inv_inv]

theorem q_ne_zero {z : ℂ} (hz : z ∈ ball 0 1) : d.q z ≠ 0 :=
  laurentModel_ne_zero d.g_zero d.g_deriv_ne_zero_zero
    (fun _ hv hv0 => d.g_value_ne_zero hv hv0) hz

theorem q_zero_ne : d.q 0 ≠ 0 := d.q_ne_zero (by simp)

theorem D_analytic : AnalyticOnNhd ℂ d.D (ball 0 1) :=
  modelDerivative_analytic d.q_analytic d.q_zero_ne

@[simp] theorem D_zero : d.D 0 = 1 := modelDerivative_zero d.q_zero_ne

@[simp] theorem D_deriv_zero : deriv d.D 0 = 0 :=
  (modelDerivative_hasDerivAt_zero (d.q_analytic 0 (by simp))).deriv

theorem g_deriv_ne_zero (hK : IsCompact K) {z : ℂ} (hz : z ∈ ball 0 1) : deriv d.g z ≠ 0 :=
  RiemannBiholomorphic.deriv_ne_zero_of_biholomorphic
    isOpen_ball (invertedComplement_isOpen hK d.center) d.g_differentiable
    d.f_differentiable d.g_mapsTo d.inverse.2 hz

theorem D_ne_zero (hK : IsCompact K) {z : ℂ} (hz : z ∈ ball 0 1) : d.D z ≠ 0 :=
  modelDerivative_ne_zero d.g_differentiable d.g_zero
    (fun _ hv hv0 => d.g_value_ne_zero hv hv0) (fun _ hv => d.g_deriv_ne_zero hK hv) hz

theorem criterion_pos (hK : IsCompact K) (hconv : Convex ℝ K)
    {z : ℂ} (hz : z ∈ ball 0 1) : 0 < (derivativeCriterion d.D z).re :=
  ExteriorEnvelope.laurentModel_criterion_pos hK hconv d.center_mem
    d.f_differentiable d.g_differentiable d.f_bijective d.g_mapsTo d.inverse d.f_zero d.g_zero z hz

theorem derivative_bound (hK : IsCompact K) (hconv : Convex ℝ K)
    {z : ℂ} (hz : z ∈ ball 0 1) : ‖d.D z‖ ≤ 1 + ‖z‖ ^ 2 :=
  ExteriorEnvelope.laurentModel_derivative_bound hK hconv d.center_mem
    d.f_differentiable d.g_differentiable d.f_bijective d.g_mapsTo d.inverse d.f_zero d.g_zero z hz

theorem sobolev (hK : IsCompact K) (hconv : Convex ℝ K) :
    Erdos1045.ExteriorClassical.SobolevCoefficients d.coefficient :=
  model_laurent_sobolev_of_criterion d.q_analytic d.q_zero_ne
    (fun _ hz => d.D_ne_zero hK hz) (fun _ hz => (d.criterion_pos hK hconv hz).le)

theorem open_biholomorphic (hK : IsCompact K) :
    DifferentiableOn ℂ d.openMap exteriorDisk ∧
      DifferentiableOn ℂ d.inverseMap Kᶜ ∧ BijOn d.openMap exteriorDisk Kᶜ ∧
      MapsTo d.inverseMap Kᶜ exteriorDisk ∧ InvOn d.inverseMap d.openMap exteriorDisk Kᶜ ∧
      (∀ w ∈ exteriorDisk, deriv d.openMap w ≠ 0) :=
  laurentModel_exterior_biholomorphic hK d.center_mem
    d.f_differentiable d.g_differentiable d.f_bijective d.g_mapsTo d.inverse d.f_zero d.g_zero

theorem map_eq_open {w : ℂ} (hw : w ∈ exteriorDisk) : d.map w = d.openMap w :=
  laurentBoundaryMap_eq_exterior d.q_analytic d.center hw

theorem map_continuous (hK : IsCompact K) (hconv : Convex ℝ K) :
    ContinuousOn d.map closedExteriorDisk :=
  laurentBoundaryMap_continuousOn (d.sobolev hK hconv) d.center

theorem map_hasDerivAt {w : ℂ} (hw : w ∈ exteriorDisk) :
    HasDerivAt d.map (derivativeNumerator d.q w⁻¹) w := by
  apply (exteriorFromModel_hasDerivAt d.q_analytic d.center hw).congr_of_eventuallyEq
  filter_upwards [exteriorDisk_isOpen.mem_nhds hw] with v hv
  exact d.map_eq_open hv

theorem map_deriv {w : ℂ} (hw : w ∈ exteriorDisk) :
    deriv d.map w = (d.capacity : ℂ) * d.D w⁻¹ := by
  rw [(d.map_hasDerivAt hw).deriv]
  change derivativeNumerator d.q w⁻¹ = (d.capacity : ℂ) *
    (derivativeNumerator d.q w⁻¹ / d.q 0)
  rw [d.q_zero]
  field_simp [Complex.ofReal_ne_zero.mpr d.capacity_pos.ne']

theorem map_mapsTo (hK : IsCompact K) : MapsTo d.map exteriorDisk Kᶜ := by
  intro w hw
  rw [d.map_eq_open hw]
  exact (d.open_biholomorphic hK).2.2.1.mapsTo hw

theorem inverseMap_mapsTo (hK : IsCompact K) : MapsTo d.inverseMap Kᶜ exteriorDisk :=
  (d.open_biholomorphic hK).2.2.2.1

theorem left_inverse (hK : IsCompact K) {w : ℂ} (hw : w ∈ exteriorDisk) :
    d.inverseMap (d.map w) = w := by
  rw [d.map_eq_open hw]
  exact (d.open_biholomorphic hK).2.2.2.2.1.1 hw

theorem right_inverse (hK : IsCompact K) {z : ℂ} (hz : z ∈ Kᶜ) :
    d.map (d.inverseMap z) = z := by
  rw [d.map_eq_open (d.inverseMap_mapsTo hK hz)]
  exact (d.open_biholomorphic hK).2.2.2.2.1.2 hz

theorem map_bijective (hK : IsCompact K) : BijOn d.map exteriorDisk Kᶜ := by
  have hb := (d.open_biholomorphic hK).2.2.1
  exact hb.congr (fun _ hw => (d.map_eq_open hw).symm)

theorem envelope_continuous (hK : IsCompact K) : Continuous d.envelope := by
  obtain ⟨hΨ, hΦ, hΨbij, hΦmap, hinv, _⟩ := d.open_biholomorphic hK
  exact ExteriorEnvelope.continuous_inverseNormEnvelope hK.isClosed
    hΨ.continuousOn hΦ.continuousOn hΨbij.mapsTo hΦmap hinv.2
    (exteriorFromModel_norm_atTop (d.q_analytic 0 (by simp)).continuousAt d.q_zero_ne d.center)

theorem boundary_image (hK : IsCompact K) (hconv : Convex ℝ K) :
    d.map '' sphere (0 : ℂ) 1 = frontier K := by
  obtain ⟨_, _, hΨbij, hΦmap, hinv, _⟩ := d.open_biholomorphic hK
  exact boundary_image_eq_frontier hK.isClosed (d.map_continuous hK hconv)
    (fun _ hw => d.map_eq_open hw) hΨbij.mapsTo hΦmap hinv.1 hinv.2 (d.envelope_continuous hK)

theorem boundary_mapsTo (hK : IsCompact K) (hconv : Convex ℝ K)
    {w : ℂ} (hw : ‖w‖ = 1) : d.map w ∈ K := by
  apply hK.isClosed.frontier_subset
  rw [← d.boundary_image hK hconv]
  exact ⟨w, mem_sphere_zero_iff_norm.mpr hw, rfl⟩

theorem boundary_surjective (hK : IsCompact K) (hconv : Convex ℝ K)
    {x : ℂ} (hx : x ∈ frontier K) : ∃ u : ℂ, ‖u‖ = 1 ∧ d.map u = x := by
  rw [← d.boundary_image hK hconv] at hx
  obtain ⟨u, hu, he⟩ := hx
  exact ⟨u, mem_sphere_zero_iff_norm.mp hu, he⟩

theorem bernstein_walsh (hK : IsCompact K) (hconv : Convex ℝ K)
    (p : Polynomial ℂ) (hp : ∀ x ∈ K, ‖p.eval x‖ ≤ 1)
    {w : ℂ} (hw : w ∈ exteriorDisk) : ‖p.eval (d.map w)‖ ≤ ‖w‖ ^ p.natDegree :=
  polynomial_bernstein_walsh_exterior p d.center d.q_analytic (d.map_continuous hK hconv)
    (fun _ hv => d.map_eq_open hv) (fun _ hv => hp _ (d.boundary_mapsTo hK hconv hv)) hw

theorem faber_bound (hK : IsCompact K) (hconv : Convex ℝ K)
    {x : ℂ} (hx : x ∈ K) (k : ℕ) : ‖d.faber k x‖ ≤ 2 :=
  convex_faber_bound hK hconv d.center_mem hx d.g_differentiable d.f_differentiable
    d.g_mapsTo d.f_bijective.mapsTo d.inverse.2 d.g_zero k

theorem kernel_denominator_ne_zero {x z : ℂ} (hx : x ∈ K) (hz : z ∈ ball 0 1) :
    d.q z + (d.center - x) * z ≠ 0 :=
  modelDenominator_ne_zero hx d.g_mapsTo d.g_zero d.g_deriv_ne_zero_zero
    (fun _ hv hv0 => d.g_value_ne_zero hv hv0) hz

theorem faber_generating_hasSum {x : ℂ} (hx : x ∈ K) {w : ℂ} (hw : w ∈ exteriorDisk) :
    HasSum (fun k => d.faber k x * w⁻¹ ^ k)
      (w * deriv d.map w / (d.map w - x)) := by
  have hs := model_faber_generating_hasSum d.q_analytic d.center x
    (fun _ hz => d.kernel_denominator_ne_zero hx hz) hw
  have hd : deriv (fun v => d.center + v * d.q v⁻¹) w = deriv d.map w := by
    rw [(hasDerivAt_laurentExterior d.q_analytic d.center hw).deriv, (d.map_hasDerivAt hw).deriv]
  change HasSum (fun k => d.faber k x * w⁻¹ ^ k)
    (w * deriv (fun v => d.center + v * d.q v⁻¹) w / (d.openMap w - x)) at hs
  rwa [hd, ← d.map_eq_open hw] at hs

theorem faber_generating_summable {x : ℂ} (hx : x ∈ K) {r : ℝ} (hr : 1 < r) :
    Summable (fun k => ‖((1 / r : ℝ) : ℂ) ^ k * d.faber k x‖) :=
  model_faber_generating_summable d.q_analytic d.center x
    (fun _ hz => d.kernel_denominator_ne_zero hx hz) r hr

theorem cauchy_bernstein_walsh (hK : IsCompact K) (hconv : Convex ℝ K)
    {r h : ℝ} (hr : 1 < r) (hh : 0 < h)
    (hsep : ∀ u v : ℂ, ‖u‖ = r → ‖v‖ = 1 → h ≤ ‖d.map u - d.map v‖)
    (p : Polynomial ℂ) (hp : ∀ x ∈ K, ‖p.eval x‖ ≤ 1) :
    ∀ x ∈ K, ‖p.derivative.eval x‖ ≤ 2 * r ^ p.natDegree / h :=
  cauchy_bernstein_walsh_actual p d.center ⟨d.center, d.center_mem⟩
    d.q_analytic (d.map_continuous hK hconv) (fun _ hw => d.map_eq_open hw)
    (fun _ hw => d.boundary_mapsTo hK hconv hw) (fun _ hx => d.boundary_surjective hK hconv hx)
    (d.inverseMap_mapsTo hK) (fun _ hz => d.right_inverse hK hz) (d.envelope_continuous hK)
    hr hh hsep hp

#print axioms criterion_pos
#print axioms sobolev
#print axioms boundary_image
#print axioms cauchy_bernstein_walsh
#print axioms faber_bound
#print axioms faber_generating_hasSum

end ConvexExteriorModel

#print axioms exists_convexExteriorModel

end
end ExteriorReduction

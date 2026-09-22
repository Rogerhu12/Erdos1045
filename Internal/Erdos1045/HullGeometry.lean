import Erdos1045.Configuration
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Order.Compact

open scoped BigOperators

namespace Erdos1045.HullGeometry

open Configuration
noncomputable section

/-- The support function of the actual finite configuration, hence of its convex hull. -/
def support {n : ℕ} (z : Points n) (t : ℝ) : ℝ :=
  sSup (Set.range (fun i : Fin n => (z i * Complex.exp (-((t : ℂ) * Complex.I))).re))

/-- Cauchy's support-integral perimeter. It assigns twice the length to a segment. -/
def hullPerimeter {n : ℕ} (z : Points n) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * Real.pi), support z t

def circlePerimeter (n : ℕ) : ℝ := 2 * n * Real.sin (Real.pi / n)

def diameterPerimeterBound (n : ℕ) : ℝ := 2 * n * Real.sin (Real.pi / (2 * n))

/-- Classical convex geometry and the elementary regular-polygon formulas.
Every field refers to the concrete support integral or concrete point coordinates.
There is no extremality, stability, or manuscript-specific estimate in this interface. -/
structure ClassicalHullGeometry : Prop where
  nonneg : ∀ n (z : Points n), 0 ≤ hullPerimeter z
  continuous : ∀ n, Continuous (@hullPerimeter n)
  affine : ∀ n (z : Points n) (a b : ℂ),
    hullPerimeter (fun i => a + b * z i) = ‖b‖ * hullPerimeter z
  perm : ∀ n (z : Points n) (σ : Equiv.Perm (Fin n)), hullPerimeter (z ∘ σ) = hullPerimeter z
  monotone : ∀ n m (z : Points n) (w : Points m),
    Set.range z ⊆ convexHull ℝ (Set.range w) → hullPerimeter z ≤ hullPerimeter w
  distance_le_half : ∀ n (z : Points n) (i j : Fin n), ‖z i - z j‖ ≤ hullPerimeter z / 2
  regular_perimeter : ∀ n : ℕ, 3 ≤ n → hullPerimeter (regular n) = circlePerimeter n
  regular_discriminant : ∀ n : ℕ, 3 ≤ n → discriminant (regular n) = (n : ℝ) ^ n
  regular_diameter : ∀ n : ℕ, 3 ≤ n → Odd n →
    DiameterAtMost (2 * Real.cos (Real.pi / (2 * n))) (regular n)
  reinhardt : ∀ n, 3 ≤ n → ∀ z : Points n, DiameterAtMost 1 z →
    hullPerimeter z ≤ diameterPerimeterBound n

def PerimeterExtremal (n : ℕ) (z : Points n) : Prop :=
  hullPerimeter z ≤ 2 * Real.pi ∧
    ∀ w : Points n, hullPerimeter w ≤ 2 * Real.pi → discriminant w ≤ discriminant z

theorem continuous_discriminant (n : ℕ) : Continuous (@discriminant n) := by
  unfold discriminant
  fun_prop

theorem discriminant_perm {n : ℕ} (z : Points n) (σ : Equiv.Perm (Fin n)) :
    discriminant (z ∘ σ) = discriminant z := by
  have hinner (i : Fin n) :
      (∏ j ∈ Finset.univ.erase i, ‖z (σ i) - z (σ j)‖) =
        ∏ j ∈ Finset.univ.erase (σ i), ‖z (σ i) - z j‖ := by
    apply Finset.prod_equiv σ
    · intro j
      simp
    · intro j hj
      rfl
  unfold discriminant
  simp only [Function.comp_apply, hinner]
  exact Equiv.prod_comp σ (fun i : Fin n => ∏ j ∈ Finset.univ.erase i, ‖z i - z j‖)

theorem hullPerimeter_zero (H : ClassicalHullGeometry) (n : ℕ) :
    hullPerimeter (0 : Points n) = 0 := by
  change hullPerimeter (fun _ : Fin n => 0) = 0
  simpa using H.affine n (0 : Points n) 0 0

/-- Compactness after fixing the translation proves existence of a genuine
global perimeter-constrained maximizer. This is not included as an input. -/
theorem exists_perimeterExtremal (H : ClassicalHullGeometry) {n : ℕ} (hn : 0 < n) :
    ∃ z : Points n, PerimeterExtremal n z := by
  let i₀ : Fin n := ⟨0, hn⟩
  let s : Set (Points n) := {z | z i₀ = 0 ∧ hullPerimeter z ≤ 2 * Real.pi}
  have hsclosed : IsClosed s :=
    (isClosed_eq (continuous_apply i₀) continuous_const).inter
      (isClosed_le (H.continuous n) continuous_const)
  have hsub : s ⊆ Metric.closedBall (0 : Points n) Real.pi := by
    intro z hz
    apply Metric.mem_closedBall.mpr
    rw [dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr
    intro i
    have h := H.distance_le_half n z i i₀
    rw [hz.1, sub_zero] at h
    linarith [hz.2]
  have hscompact : IsCompact s :=
    (isCompact_closedBall (0 : Points n) Real.pi).of_isClosed_subset hsclosed hsub
  have hsnonempty : s.Nonempty := by
    refine ⟨0, rfl, ?_⟩
    rw [hullPerimeter_zero H n]
    positivity
  obtain ⟨z, hz, hmax⟩ := hscompact.exists_isMaxOn hsnonempty (continuous_discriminant n).continuousOn
  refine ⟨z, hz.2, ?_⟩
  intro w hw
  let v : Points n := fun i => -w i₀ + w i
  have hP : hullPerimeter v = hullPerimeter w := by
    simpa [v] using H.affine n w (-w i₀) 1
  have hD : discriminant v = discriminant w := by
    simpa [v] using discriminant_affine w (-w i₀) 1
  have hv : v ∈ s := by
    constructor
    · simp [v]
    · rw [hP]
      exact hw
  have h := hmax hv
  change discriminant v ≤ discriminant z at h
  rwa [hD] at h

theorem circlePerimeter_pos {n : ℕ} (hn : 3 ≤ n) : 0 < circlePerimeter n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hsin : 0 < Real.sin (Real.pi / n) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    apply (div_lt_iff₀ hn0).mpr
    nlinarith [Real.pi_pos]
  unfold circlePerimeter
  positivity

theorem regular_discriminant_from_perimeter (H : ClassicalHullGeometry) {n : ℕ}
    (hn : 3 ≤ n) {z : Points n} (hz : Configuration.IsRegular z) :
    discriminant z = (hullPerimeter z / circlePerimeter n) ^ exponent n * (n : ℝ) ^ n := by
  obtain ⟨a, b, hb, σ, hz⟩ := hz
  have hfun : z = fun i => a + b * (regular n ∘ σ) i := by funext i; exact hz i
  rw [hfun, discriminant_affine, H.affine, discriminant_perm, H.perm,
    H.regular_perimeter n hn, H.regular_discriminant n hn]
  rw [mul_div_cancel_right₀ _ (circlePerimeter_pos hn).ne']

end

end Erdos1045.HullGeometry

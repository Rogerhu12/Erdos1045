import Erdos1045.ExteriorClassical

/-!
# The actual differentiated Faber correction identity

Generic Laurent and geometric series identities are classical inputs. The
specialization to the exterior map and the division by `1+q` are proved here.
In particular the Faber error is never postulated to satisfy a coefficientwise
quotient identity.
-/

namespace Erdos1045.ExteriorClassical

open scoped BigOperators
open ExteriorBoundary Configuration FaberFourier FaberAlgebra
noncomputable section

structure ClassicalLaurentSeries : Prop where
  geometric_summable : ∀ r : ℝ, 1 < r → ∀ θ : ℝ,
    Summable (fun k => ‖((1 / r : ℝ) : ℂ) ^ k * unit θ ^ k‖)
  geometric_identity : ∀ r : ℝ, 1 < r → ∀ θ t : ℝ,
    series (fun k => ((1 / r : ℝ) : ℂ) ^ k * unit θ ^ k) t =
      ((r : ℂ) * unit t) / ((r : ℂ) * unit t - unit θ)
  derivative_summable : ∀ a, SobolevCoefficients a → ∀ c : ℝ, 0 < c →
    ∀ r : ℝ, 1 < r → ∀ θ : ℝ,
      Summable (fun k => ‖radialCoefficients (1 / r)
        (firstOrder (coefficient c a (fun _ : Fin 1 => θ) 0)) k‖)
  divided_difference_derivative : ∀ a, SobolevCoefficients a →
    ∀ c : ℝ, 0 < c → ∀ r : ℝ, 1 < r → ∀ θ t : ℝ,
      series (radialCoefficients (1 / r)
        (firstOrder (coefficient c a (fun _ : Fin 1 => θ) 0))) t =
      let v := (r : ℂ) * unit t
      v * (laurentDerivative a v * (v - unit θ) - (laurent a v - laurent a (unit θ))) /
        ((c : ℂ) * (v - unit θ) ^ 2)

theorem quotient_identity {c A B D v : ℂ} (hc : c ≠ 0) (hB : B ≠ 0)
    (hden : c * B + A ≠ 0) :
    v * (c + D) / (c * B + A) - v / B =
      correction (A / (c * B)) (v * (D * B - A) / (c * B ^ 2)) := by
  have hq : 1 + A / (c * B) ≠ 0 := by
    intro h
    apply hden
    have he : (1 + A / (c * B)) * (c * B) = c * B + A := by field_simp
    rw [← he, h, zero_mul]
  unfold correction
  field_simp
  ring

theorem radial_norm {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : ‖(r : ℂ) * unit t‖ = r := by
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

theorem radial_difference_ne_zero {r : ℝ} (hr : 1 < r) (θ t : ℝ) :
    (r : ℂ) * unit t - unit θ ≠ 0 := by
  intro h
  have heq := congrArg norm (sub_eq_zero.mp h)
  rw [radial_norm (by linarith), norm_unit] at heq
  linarith

theorem ExteriorData.map_sub_node {n : ℕ} {z : Points n} (d : ExteriorData z)
    (i : Fin n) (v : ℂ) :
    d.map v - z i = (d.capacity : ℂ) * (v - unit (d.angles.angle i)) +
      (laurent d.coefficient v - laurent d.coefficient (unit (d.angles.angle i))) := by
  rw [d.node_identity i]
  unfold ExteriorData.map
  ring

theorem ExteriorData.remainder_summable {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (HL : ClassicalLaurentSeries) {r : ℝ} (hr : 1 < r)
    (i : Fin n) : Summable (fun k => ‖radialCoefficients (1 / r) (d.remainder i) k‖) := by
  have hz : z i ∈ hull z := subset_convexHull ℝ (Set.range z) (Set.mem_range_self i)
  have h := norm_sub_summable (HF.generating_summable (z i) hz r hr)
    (HL.geometric_summable r hr (d.angles.angle i))
  simpa only [radialCoefficients, ExteriorData.remainder, mul_sub] using h

theorem ExteriorData.source_summable {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HL : ClassicalLaurentSeries) {r : ℝ} (hr : 1 < r) (i : Fin n) :
    Summable (fun k => ‖radialCoefficients (1 / r)
      (firstOrder (FaberFourier.coefficient d.capacity d.coefficient (fun j : Fin n => d.angles.angle j) i)) k‖) :=
  HL.derivative_summable d.coefficient d.sobolev d.capacity d.capacity_pos r hr (d.angles.angle i)

/-- The exact pointwise identity needed by the Parseval estimates of Section 4. -/
theorem ExteriorData.correction_identity {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (HL : ClassicalLaurentSeries) {r : ℝ} (hr : 1 < r)
    (i : Fin n) (t : ℝ) :
    series (radialCoefficients (1 / r) (d.remainder i)) t =
      correction (d.quotient i ((r : ℂ) * unit t))
        (series (radialCoefficients (1 / r)
          (firstOrder (FaberFourier.coefficient d.capacity d.coefficient
            (fun j : Fin n => d.angles.angle j) i))) t) := by
  let v : ℂ := (r : ℂ) * unit t
  have hv : 1 < ‖v‖ := by rw [show v = (r : ℂ) * unit t from rfl, radial_norm (by linarith)]; exact hr
  have hz : z i ∈ hull z := subset_convexHull ℝ (Set.range z) (Set.mem_range_self i)
  have hden : d.map v - z i ≠ 0 := by
    intro h
    exact HF.map_avoids_hull v hv (sub_eq_zero.mp h ▸ hz)
  have hc : (d.capacity : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr d.capacity_pos.ne'
  have hb := radial_difference_ne_zero hr (d.angles.angle i) t
  have hs := series_sub (HF.generating_summable (z i) hz r hr)
    (HL.geometric_summable r hr (d.angles.angle i)) t
  have hsource := HL.divided_difference_derivative d.coefficient d.sobolev
    d.capacity d.capacity_pos r hr (d.angles.angle i) t
  change series (radialCoefficients (1 / r)
    (firstOrder (FaberFourier.coefficient d.capacity d.coefficient
      (fun j : Fin n => d.angles.angle j) i))) t = _ at hsource
  change series (radialCoefficients (1 / r) (d.remainder i)) t =
    correction (d.quotient i v) _
  have hcoeff : radialCoefficients (1 / r) (d.remainder i) =
      fun k => ((1 / r : ℝ) : ℂ) ^ k * d.faber k (z i) -
        ((1 / r : ℝ) : ℂ) ^ k * unit (d.angles.angle i) ^ k := by
    funext k
    simp only [radialCoefficients, ExteriorData.remainder, mul_sub]
  rw [hcoeff, hs, HF.generating (z i) hz r hr t,
    HL.geometric_identity r hr (d.angles.angle i) t, hsource]
  change v * d.derivative v / (d.map v - z i) - v / (v - unit (d.angles.angle i)) = _
  rw [d.derivative_identity v hv, d.map_sub_node]
  unfold ExteriorData.quotient
  exact quotient_identity hc hb (by rwa [← d.map_sub_node])

end
end Erdos1045.ExteriorClassical


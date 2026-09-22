import Erdos1045.ExteriorClassical
import Erdos1045.HullExtremal
import Erdos1045.GapExterior

/-!
# The local rigidity endpoint for the actual exterior-map data

Only the upstream asymptotic conclusions (circle energy tending to zero and
bounded n^2 times Laurent energy) remain ordinary premises here. Extremal
objective comparison, Fourier normalization, and relative edge convergence
are proved from the concrete data and are not classical-package fields.
-/

namespace Erdos1045.ExteriorLocalBridge

open Complex ExteriorBoundary ExteriorClassical Configuration HullGeometry
open scoped BigOperators Topology
open Filter
noncomputable section

theorem regular_boundaryLength {n : ℕ} (hn : 3 ≤ n) :
    boundaryLength (regular n) = circlePerimeter n := by
  have hp : Function.Periodic (LocalObjective.regularVertices n) n := by
    intro j
    simp [LocalObjective.regularVertices, pow_add, LocalDFT.regularRoot_pow (by omega : 0 < n)]
  have he : (fun j : Fin n => LocalObjective.regularVertices n j) = regular n := by
    funext j
    exact LocalRigidity.root_power_eq_regular n j
  rw [← he, ← LocalConfiguration.perimeter_eq_boundaryLength (by omega) _ hp,
    LocalObjective.perimeter_regular]
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hs := LocalTrigonometry.base_sine_pos hnR
  have hd : ‖LocalPhase.regularRoot n - 1‖ = 2 * Real.sin (Real.pi / n) := by
    unfold LocalPhase.regularRoot
    rw [mul_comm _ I, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
    rw [show (2 * Real.pi / (n : ℝ)) / 2 = Real.pi / n by ring,
      abs_of_pos (mul_pos (by norm_num) hs)]
  rw [hd]
  unfold circlePerimeter
  ring

theorem perimeterExtremal_fekete (H : ClassicalHullGeometry) {n : ℕ}
    {z : Points n} (hz : PerimeterExtremal n z) : Fekete z := by
  intro w hw
  exact perimeterExtremal_dominates_hull H hz w hw

theorem boundaryLength_pos_of_injective {n : ℕ} (hn : 2 ≤ n) {z : Points n}
    (hz : Function.Injective z) : 0 < boundaryLength z := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold boundaryLength
  apply Finset.sum_pos'
  · intro i _
    exact norm_nonneg _
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    rw [finRotate_apply_zero]
    apply norm_pos_iff.mpr
    apply sub_ne_zero.mpr
    intro heq
    have hh := congrArg Fin.val (hz heq)
    norm_num at hh

theorem perimeterExtremal_objective (H : ClassicalHullGeometry) {n : ℕ}
    (hn : 3 ≤ n) {z : Points n} (hz : PerimeterExtremal n z)
    (hboundary : boundaryLength z ≤ hullPerimeter z) :
    objective (regular n) ≤ objective z := by
  let r : ℝ := 2 * Real.pi / circlePerimeter n
  let w : Points n := fun i => (r : ℂ) * regular n i
  have hr : 0 < r := div_pos (by positivity) (circlePerimeter_pos hn)
  have hP : hullPerimeter w = 2 * Real.pi := by
    have he := H.affine n (regular n) 0 (r : ℂ)
    simp only [zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      H.regular_perimeter n hn] at he
    change hullPerimeter w = _ at he
    rw [he]
    unfold r
    field_simp [(circlePerimeter_pos hn).ne']
  have hLw : boundaryLength w = 2 * Real.pi := by
    have he := boundaryLength_affine (regular n) 0 (r : ℂ)
    simp only [zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      regular_boundaryLength hn] at he
    change boundaryLength w = _ at he
    rw [he]
    unfold r
    field_simp [(circlePerimeter_pos hn).ne']
  have hLz : boundaryLength z ≤ 2 * Real.pi := by
    rwa [perimeterExtremal_perimeter_eq H hn hz] at hboundary
  have hDreg : 0 < discriminant (regular n) := by
    rw [H.regular_discriminant n hn]
    exact pow_pos (by exact_mod_cast (show 0 < n by omega)) _
  have hDw : 0 < discriminant w := by
    have he := discriminant_affine (regular n) 0 (r : ℂ)
    simp only [zero_add] at he
    change discriminant w = _ at he
    rw [he]
    exact mul_pos (pow_pos (norm_pos_iff.mpr (Complex.ofReal_ne_zero.mpr hr.ne')) _) hDreg
  have hlog := Real.log_le_log hDw (hz.2 w hP.le)
  have hlogL := Real.log_le_log
    (boundaryLength_pos_of_injective (by omega) (perimeterExtremal_injective H hn hz)) hLz
  have hmul := mul_le_mul_of_nonneg_left hlogL (Nat.cast_nonneg (exponent n) : (0 : ℝ) ≤ _)
  have hobj : objective w = objective (regular n) := by
    simpa [w] using objective_affine (regular n) 0 (r : ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')
      hDreg (by rw [regular_boundaryLength hn]; exact circlePerimeter_pos hn)
  rw [← hobj]
  unfold objective
  rw [hLw]
  linarith

def residual {n : ℕ} {z : Points n} (d : ExteriorData z) (j : ℕ) : ℂ :=
  laurent d.coefficient (unit (d.angles.angle j))

def scale {n : ℕ} {z : Points n} (d : ExteriorData z) : ℂ :=
  (d.capacity : ℂ) * unit (d.angles.angle 0)

theorem unit_period (t : ℝ) : unit (t + 2 * Real.pi) = unit t := by
  unfold unit
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem residual_periodic {n : ℕ} {z : Points n} (d : ExteriorData z) :
    Function.Periodic (residual d) n := by
  intro j
  simp only [residual, Nat.cast_add, d.angles.period, unit_period]

theorem scale_norm {n : ℕ} {z : Points n} (d : ExteriorData z) : ‖scale d‖ = d.capacity := by
  simp [scale, Complex.norm_real, Real.norm_eq_abs, abs_of_pos d.capacity_pos]

theorem residual_sobolev (HL : ClassicalLaurentAnalysis) {n : ℕ} {z : Points n}
    (d : ExteriorData z) (j : ℕ) :
    ‖residual d (j + 1) - residual d j‖ ≤
      Real.sqrt d.energySquared * Real.sqrt (CyclicAngles.window d.angles 1 j) := by
  have hs := HL.interval_sobolev d.coefficient d.sobolev
    (d.angles.angle (j : ℤ)) (d.angles.angle ((j + 1 : ℕ) : ℤ))
  rw [← d.parseval_identity] at hs
  have he : d.angles.angle ((j + 1 : ℕ) : ℤ) - d.angles.angle (j : ℤ) =
      CyclicAngles.window d.angles 1 j := by simp [CyclicAngles.window]
  rw [he, abs_of_pos (CyclicAngles.window_pos d.angles (by omega) j)] at hs
  exact hs

theorem originalPoints_eq {n : ℕ} {z : Points n} (d : ExteriorData z) :
    GapExterior.originalPoints d.angles (residual d) d.offset (scale d) = z := by
  funext j
  unfold GapExterior.originalPoints residual scale GapRigidity.circlePoints GapRigidity.circle
  rw [d.node_identity j]
  have he : unit (d.angles.angle 0) *
      Complex.exp (((d.angles.angle (j : ℕ) - d.angles.angle 0 : ℝ) : ℂ) * I) =
        unit (d.angles.angle j) := by
    unfold unit
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [mul_assoc, he]
  ring

/-- The final local implication, specialized to concrete exterior data.
The two asymptotic premises are the output obligations of the Faber/matrix
argument; they are deliberately not inserted into a classical structure. -/
theorem eventually_regular (H : ClassicalHullGeometry) (HL : ClassicalLaurentAnalysis)
    (HI : LocalDFT.ClassicalDFTInversion) (HS : LocalPhase.ClassicalGeometricSine)
    (HT : LocalNonlinear.ScalarLogTaylor) {N : ℕ → ℕ}
    (hN : ∀ k, 4 ≤ N k) (hNtop : Tendsto N atTop atTop)
    (z : ∀ k, Points (N k)) (hz : ∀ k, PerimeterExtremal (N k) (z k))
    (d : ∀ k, ExteriorData (z k))
    (HF : ∀ k, LocalFourier.ClassicalOrthogonality (N k) (LocalPhase.regularRoot (N k)))
    (hangle : Tendsto (fun k => CyclicAngles.energy (d k).angles) atTop (nhds 0))
    (hc : ∀ k, 1 / 2 ≤ (d k).capacity)
    (C : ℝ) (henergy : ∀ k, (N k : ℝ) ^ 2 * (d k).energySquared ≤ C) :
    ∀ᶠ k in atTop, Configuration.IsRegular (z k) := by
  have hmax (k : ℕ) : objective (regular (N k)) ≤
      objective (GapExterior.originalPoints (d k).angles (residual (d k)) (d k).offset (scale (d k))) := by
    rw [originalPoints_eq]
    exact perimeterExtremal_objective H (by have := hN k; omega) (hz k) (d k).boundary_perimeter
  have h := GapExterior.eventually_original_regular HI HS HT (fun k => (d k).angles)
    hN hNtop HF hangle (fun k => residual (d k)) (fun k => residual_periodic (d k))
    (fun k => (d k).offset) (fun k => scale (d k))
    (fun k => by rw [scale_norm]; exact hc k)
    (fun k => Real.sqrt (d k).energySquared) (fun k => Real.sqrt_nonneg _) C
    (fun k => by rw [Real.sq_sqrt (d k).energySquared_nonneg]; exact henergy k)
    (fun k j => residual_sobolev HL (d k) j) hmax
  simpa only [originalPoints_eq] using h

theorem eventually_regular_of_eventual_bounds
    (H : ClassicalHullGeometry) (HL : ClassicalLaurentAnalysis)
    (HI : LocalDFT.ClassicalDFTInversion) (HS : LocalPhase.ClassicalGeometricSine)
    (HT : LocalNonlinear.ScalarLogTaylor) {N : ℕ → ℕ}
    (hN : ∀ k, 4 ≤ N k) (hNtop : Tendsto N atTop atTop)
    (z : ∀ k, Points (N k)) (hz : ∀ k, PerimeterExtremal (N k) (z k))
    (d : ∀ k, ExteriorData (z k))
    (HF : ∀ k, LocalFourier.ClassicalOrthogonality (N k) (LocalPhase.regularRoot (N k)))
    (hangle : Tendsto (fun k => CyclicAngles.energy (d k).angles) atTop (nhds 0))
    (hc : ∀ᶠ k in atTop, 1 / 2 ≤ (d k).capacity)
    (C : ℝ) (henergy : ∀ᶠ k in atTop, (N k : ℝ) ^ 2 * (d k).energySquared ≤ C) :
    ∀ᶠ k in atTop, Configuration.IsRegular (z k) := by
  filter_upwards [GapExterior.eventually_small_edges (fun k => (d k).angles)
    (fun k => by have := hN k; omega) hNtop hangle C, hc, henergy] with k hsmall hcap hbound
  have hmax : objective (regular (N k)) ≤
      objective (GapExterior.originalPoints (d k).angles (residual (d k)) (d k).offset (scale (d k))) := by
    rw [originalPoints_eq]
    exact perimeterExtremal_objective H (by have := hN k; omega) (hz k) (d k).boundary_perimeter
  have h := GapExterior.original_regular_of_small_error HI HS HT (d k).angles (hN k) (HF k)
    (residual (d k)) (residual_periodic (d k)) (d k).offset (scale (d k))
    (by rw [scale_norm]; exact hcap)
    (Real.sqrt_nonneg (d k).energySquared)
    (by rw [Real.sq_sqrt (d k).energySquared_nonneg]; exact hbound)
    (fun j => residual_sobolev HL (d k) j) hsmall hmax
  simpa only [originalPoints_eq] using h

end
end Erdos1045.ExteriorLocalBridge

import Erdos1045.GapRigidity

/-!
# The exterior remainder and eventual exact rigidity

The residual edge estimate is the ordinary H1 Cauchy--Schwarz bound on an
arc. The finite quantitative passage to relative edge error and the eventual
application of the local maximum theorem are proved here.
-/

namespace Erdos1045.GapExterior

open Complex CyclicAngles GapRigidity
open scoped BigOperators Topology
open Filter
noncomputable section

def arcUpper {n : ℕ} (a : Angles n) : ℝ :=
  2 * Real.pi * (1 + gapError a) / n

def edgeError {n : ℕ} (a : Angles n) (C : ℝ) : ℝ :=
  circleEdgeError a + Real.sqrt C / 2 * Real.sqrt (arcUpper a)

def perturbation {n : ℕ} (a : Angles n) (f : ℕ → ℂ) (b : ℂ) (j : ℕ) : ℂ :=
  circlePerturbation a j + f j / b

def originalPoints {n : ℕ} (a : Angles n) (f : ℕ → ℂ) (offset b : ℂ) :
    Configuration.Points n := fun j => offset + b * circlePoints a j + f j

theorem originalPoints_affine {n : ℕ} (a : Angles n) (f : ℕ → ℂ)
    (offset b : ℂ) (hb : b ≠ 0) :
    originalPoints a f offset b = fun j : Fin n => offset + b *
      LocalObjective.perturbedVertices n (perturbation a f b) j := by
  funext j
  unfold originalPoints LocalObjective.perturbedVertices LocalObjective.regularVertices
    perturbation circlePerturbation
  field_simp
  ring

theorem arcUpper_nonneg {n : ℕ} (a : Angles n) : 0 ≤ arcUpper a := by
  have hg := gapError_nonneg a
  unfold arcUpper
  positivity

theorem edgeError_nonneg {n : ℕ} (a : Angles n) (C : ℝ) : 0 ≤ edgeError a C := by
  have hg := gapError_nonneg a
  unfold edgeError circleEdgeError
  positivity

theorem gap_le_arcUpper {n : ℕ} (a : Angles n) (hn : 0 < n) (j : ℕ) :
    window a 1 j ≤ arcUpper a := by
  have hb := gap_angle_bound a hn j
  have h := (le_abs_self (window a 1 j - 2 * Real.pi / n)).trans hb
  calc
    _ ≤ 2 * Real.pi / n + (2 * Real.pi / n) * gapError a := by linarith
    _ = _ := by unfold arcUpper; ring

theorem scaled_energy_bound {n : ℕ} {E C : ℝ}
    (hbound : (n : ℝ) ^ 2 * E ^ 2 ≤ C) : (n : ℝ) * E ≤ Real.sqrt C := by
  have hsq : ((n : ℝ) * E) ^ 2 ≤ C := by nlinarith
  exact (le_abs_self _).trans (Real.abs_le_sqrt hsq)

theorem residual_edge_bound {n : ℕ} (a : Angles n) (hn : 2 ≤ n)
    (f : ℕ → ℂ) (b : ℂ) (hb : 1 / 2 ≤ ‖b‖) {E C : ℝ} (hE : 0 ≤ E)
    (hbound : (n : ℝ) ^ 2 * E ^ 2 ≤ C)
    (hSobolev : ∀ j, ‖f (j + 1) - f j‖ ≤ E * Real.sqrt (window a 1 j)) (j : ℕ) :
    ‖f (j + 1) / b - f j / b‖ ≤
      (Real.sqrt C / 2 * Real.sqrt (arcUpper a)) * ‖LocalPhase.regularRoot n - 1‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb0 : 0 < ‖b‖ := by linarith
  have hg := Real.sqrt_le_sqrt (gap_le_arcUpper a (by omega) j)
  have hs := scaled_energy_bound hbound
  have hd : 4 ≤ (n : ℝ) * ‖LocalPhase.regularRoot n - 1‖ := by
    simpa [mul_comm] using (div_le_iff₀ hnR).mp (root_edge_lower hn)
  have hcoeff : 2 * E ≤ Real.sqrt C / 2 * ‖LocalPhase.regularRoot n - 1‖ := by
    have hmul := mul_le_mul_of_nonneg_right hd (Real.sqrt_nonneg C)
    have hmul2 := mul_le_mul_of_nonneg_right hs (norm_nonneg (LocalPhase.regularRoot n - 1))
    apply (mul_le_mul_iff_right₀ hnR).mp
    nlinarith
  rw [← sub_div, norm_div]
  calc
    _ ≤ (E * Real.sqrt (window a 1 j)) / ‖b‖ :=
      div_le_div_of_nonneg_right (hSobolev j) hb0.le
    _ ≤ (E * Real.sqrt (arcUpper a)) / ‖b‖ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg hE) hb0.le
    _ ≤ (E * Real.sqrt (arcUpper a)) / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hb
    _ = (2 * E) * Real.sqrt (arcUpper a) := by ring
    _ ≤ (Real.sqrt C / 2 * ‖LocalPhase.regularRoot n - 1‖) * Real.sqrt (arcUpper a) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem perturbation_periodic {n : ℕ} (a : Angles n) (hn : 0 < n)
    (f : ℕ → ℂ) (hf : Function.Periodic f n) (b : ℂ) :
    Function.Periodic (perturbation a f b) n := by
  intro j
  simp only [perturbation, circlePerturbation_periodic a hn j, hf j]

theorem total_edge_bound {n : ℕ} (a : Angles n) (hn : 2 ≤ n)
    (f : ℕ → ℂ) (b : ℂ) (hb : 1 / 2 ≤ ‖b‖) {E C : ℝ} (hE : 0 ≤ E)
    (hbound : (n : ℝ) ^ 2 * E ^ 2 ≤ C)
    (hSobolev : ∀ j, ‖f (j + 1) - f j‖ ≤ E * Real.sqrt (window a 1 j)) (j : ℕ) :
    ‖perturbation a f b (j + 1) - perturbation a f b j‖ ≤
      edgeError a C * ‖LocalPhase.regularRoot n - 1‖ := by
  have he : perturbation a f b (j + 1) - perturbation a f b j =
      (circlePerturbation a (j + 1) - circlePerturbation a j) +
        (f (j + 1) / b - f j / b) := by unfold perturbation; ring
  rw [he]
  have h := (norm_add_le _ _).trans (add_le_add (circle_edge_bound a hn j)
    (residual_edge_bound a hn f b hb hE hbound hSobolev j))
  simpa [edgeError, circleEdgeError, add_mul] using h

theorem arcUpper_tendsto_zero {N : ℕ → ℕ} (a : ∀ k, Angles (N k))
    (hN : ∀ k, 3 ≤ N k) (hNtop : Tendsto N atTop atTop)
    (hE : Tendsto (fun k => energy (a k)) atTop (nhds 0)) :
    Tendsto (fun k => arcUpper (a k)) atTop (nhds 0) := by
  have hg := gapError_tendsto_zero a hN hE
  have hinv : Tendsto (fun k => (N k : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hNtop)
  have hconst : Tendsto (fun _k : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have ht := ((hconst.add hg).const_mul (2 * Real.pi)).mul hinv
  simpa [arcUpper, div_eq_mul_inv] using ht

theorem edgeError_tendsto_zero {N : ℕ → ℕ} (a : ∀ k, Angles (N k))
    (hN : ∀ k, 3 ≤ N k) (hNtop : Tendsto N atTop atTop)
    (hE : Tendsto (fun k => energy (a k)) atTop (nhds 0)) (C : ℝ) :
    Tendsto (fun k => edgeError (a k) C) atTop (nhds 0) := by
  have hs : Tendsto (fun k => Real.sqrt (arcUpper (a k))) atTop (nhds 0) := by
    simpa [Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp
      (arcUpper_tendsto_zero a hN hNtop hE)
  simpa [edgeError] using (circleEdgeError_tendsto_zero a hN hE).add
    (hs.const_mul (Real.sqrt C / 2))

theorem eventually_small_edges {N : ℕ → ℕ} (a : ∀ k, Angles (N k))
    (hN : ∀ k, 3 ≤ N k) (hNtop : Tendsto N atTop atTop)
    (hE : Tendsto (fun k => energy (a k)) atTop (nhds 0)) (C : ℝ) :
    ∀ᶠ k in atTop, edgeError (a k) C ≤ 1 / 4000 := by
  exact (edgeError_tendsto_zero a hN hNtop hE C).eventually_le_const (by norm_num)

theorem eventually_regular (HI : LocalDFT.ClassicalDFTInversion)
    (HS : LocalPhase.ClassicalGeometricSine) (HT : LocalNonlinear.ScalarLogTaylor)
    {N : ℕ → ℕ} (a : ∀ k, Angles (N k)) (hN : ∀ k, 4 ≤ N k)
    (hNtop : Tendsto N atTop atTop)
    (HF : ∀ k, LocalFourier.ClassicalOrthogonality (N k) (LocalPhase.regularRoot (N k)))
    (hEnergy : Tendsto (fun k => energy (a k)) atTop (nhds 0))
    (f : ℕ → ℕ → ℂ) (hf : ∀ k, Function.Periodic (f k) (N k))
    (b : ℕ → ℂ) (hb : ∀ k, 1 / 2 ≤ ‖b k‖) (E : ℕ → ℝ) (hE : ∀ k, 0 ≤ E k)
    (C : ℝ) (hbound : ∀ k, (N k : ℝ) ^ 2 * E k ^ 2 ≤ C)
    (hSobolev : ∀ k j, ‖f k (j + 1) - f k j‖ ≤ E k * Real.sqrt (window (a k) 1 j))
    (hmax : ∀ k, Configuration.objective (Configuration.regular (N k)) ≤
      Configuration.objective (fun j : Fin (N k) =>
        LocalObjective.perturbedVertices (N k) (perturbation (a k) (f k) (b k)) j)) :
    ∀ᶠ k in atTop, Configuration.IsRegular (fun j : Fin (N k) =>
      LocalObjective.perturbedVertices (N k) (perturbation (a k) (f k) (b k)) j) := by
  filter_upwards [eventually_small_edges a (fun k => by have := hN k; omega)
    hNtop hEnergy C] with k hk
  by_contra hnonreg
  have hstrict := LocalConfiguration.strict_local_rigidity HI HS HT (hN k) (HF k)
    (perturbation (a k) (f k) (b k))
    (perturbation_periodic (a k) (by have := hN k; omega) (f k) (hf k) (b k))
    (edgeError_nonneg (a k) C) hk
    (total_edge_bound (a k) (by have := hN k; omega) (f k) (b k) (hb k)
      (hE k) (hbound k) (hSobolev k)) hnonreg
  exact (not_lt_of_ge (hmax k)) hstrict

/-- Finite endpoint for the original, unscaled exterior-map values. -/
theorem original_regular_of_small_error (HI : LocalDFT.ClassicalDFTInversion)
    (HS : LocalPhase.ClassicalGeometricSine) (HT : LocalNonlinear.ScalarLogTaylor)
    {n : ℕ} (a : Angles n) (hn : 4 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (f : ℕ → ℂ) (hf : Function.Periodic f n) (offset b : ℂ) (hb : 1 / 2 ≤ ‖b‖)
    {E C : ℝ} (hE : 0 ≤ E) (hbound : (n : ℝ) ^ 2 * E ^ 2 ≤ C)
    (hSobolev : ∀ j, ‖f (j + 1) - f j‖ ≤ E * Real.sqrt (window a 1 j))
    (hsmall : edgeError a C ≤ 1 / 4000)
    (hmax : Configuration.objective (Configuration.regular n) ≤
      Configuration.objective (originalPoints a f offset b)) :
    Configuration.IsRegular (originalPoints a f offset b) := by
  let u := perturbation a f b
  let y : Configuration.Points n := fun j => LocalObjective.perturbedVertices n u j
  have hu : Function.Periodic u n := perturbation_periodic a (by omega) f hf b
  have hstep := total_edge_bound a (by omega : 2 ≤ n) f b hb hE hbound hSobolev
  have hη := edgeError_nonneg a C
  have hinj : Function.Injective y := LocalConfiguration.small_perturbation_injective
    HS hn u hu hη (by linarith) hstep
  have hL : 0 < Configuration.boundaryLength y := by
    rw [← LocalConfiguration.perimeter_eq_boundaryLength (by omega)
      (LocalObjective.perturbedVertices n u) (LocalConfiguration.periodic_of_perturbed (by omega) u hu)]
    exact LocalRigidity.small_perturbation_perimeter_pos hn u (by linarith) hstep
  have hb0 : b ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖b‖)
  have he := originalPoints_affine a f offset b hb0
  have hobj : Configuration.objective (originalPoints a f offset b) = Configuration.objective y := by
    rw [he]
    exact Configuration.objective_affine y offset b hb0 (Configuration.discriminant_pos y hinj) hL
  have hyreg : Configuration.IsRegular y := by
    by_contra hnonreg
    have hstrict := LocalConfiguration.strict_local_rigidity HI HS HT hn HF u hu hη hsmall hstep hnonreg
    rw [hobj] at hmax
    exact (not_lt_of_ge hmax) hstrict
  rw [he]
  exact Configuration.isRegular_affine hyreg offset b hb0

theorem eventually_original_regular (HI : LocalDFT.ClassicalDFTInversion)
    (HS : LocalPhase.ClassicalGeometricSine) (HT : LocalNonlinear.ScalarLogTaylor)
    {N : ℕ → ℕ} (a : ∀ k, Angles (N k)) (hN : ∀ k, 4 ≤ N k)
    (hNtop : Tendsto N atTop atTop)
    (HF : ∀ k, LocalFourier.ClassicalOrthogonality (N k) (LocalPhase.regularRoot (N k)))
    (hEnergy : Tendsto (fun k => energy (a k)) atTop (nhds 0))
    (f : ℕ → ℕ → ℂ) (hf : ∀ k, Function.Periodic (f k) (N k))
    (offset b : ℕ → ℂ) (hb : ∀ k, 1 / 2 ≤ ‖b k‖) (E : ℕ → ℝ) (hE : ∀ k, 0 ≤ E k)
    (C : ℝ) (hbound : ∀ k, (N k : ℝ) ^ 2 * E k ^ 2 ≤ C)
    (hSobolev : ∀ k j, ‖f k (j + 1) - f k j‖ ≤ E k * Real.sqrt (window (a k) 1 j))
    (hmax : ∀ k, Configuration.objective (Configuration.regular (N k)) ≤
      Configuration.objective (originalPoints (a k) (f k) (offset k) (b k))) :
    ∀ᶠ k in atTop, Configuration.IsRegular (originalPoints (a k) (f k) (offset k) (b k)) := by
  filter_upwards [eventually_small_edges a (fun k => by have := hN k; omega)
    hNtop hEnergy C] with k hk
  exact original_regular_of_small_error HI HS HT (a k) (hN k) (HF k) (f k) (hf k)
    (offset k) (b k) (hb k) (hE k) (hbound k) (hSobolev k) hk (hmax k)

end
end Erdos1045.GapExterior

import FinitePerimeterAngles
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Baire.Lemmas

/-! Generic directions have a strict support maximizer. Density of those
directions is proved from proper linear kernels, including configurations
with repeated points and collinear triples. -/

namespace ExteriorReduction.Reinhardt

open Complex Set Metric
open Erdos1045.Configuration Erdos1045.HullGeometry
open scoped ComplexConjugate

noncomputable section

def realProjection (v : ℂ) : ℂ →L[ℝ] ℝ := v.re • Complex.reCLM + v.im • Complex.imCLM

theorem realProjection_apply (v u : ℂ) :
    realProjection v u = (v * conj u).re := by
  simp [realProjection, Complex.mul_re]

theorem realProjection_self (v : ℂ) : realProjection v v = ‖v‖ ^ 2 := by
  change v.re * v.re + v.im * v.im = ‖v‖ ^ 2
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]

theorem projection_nonzero_dense {v : ℂ} (hv : v ≠ 0) :
    Dense {u : ℂ | (v * conj u).re ≠ 0} := by
  let L := realProjection v
  have hker : L.ker ≠ ⊤ := by
    intro he
    have hvker : v ∈ L.ker := by rw [he]; trivial
    have hh : realProjection v v = 0 := hvker
    rw [realProjection_self] at hh
    exact (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)) hh
  have hint : interior (L.ker : Set ℂ) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hn
    exact hker (L.ker.eq_top_of_nonempty_interior' hn)
  have hd := interior_eq_empty_iff_dense_compl.mp hint
  convert hd using 1
  ext u
  change (v * conj u).re ≠ 0 ↔ realProjection v u ≠ 0
  rw [realProjection_apply]

theorem separating_directions_dense {n : ℕ} (z : Points n) :
    Dense {u : ℂ | ∀ i j, z i ≠ z j → ((z i - z j) * conj u).re ≠ 0} := by
  let S (i j : Fin n) : Set ℂ := {u | z i ≠ z j → ((z i - z j) * conj u).re ≠ 0}
  have hSopen (i j : Fin n) : IsOpen (S i j) := by
    by_cases hij : z i = z j
    · simp [S, hij]
    · have he : S i j = {u | ((z i - z j) * conj u).re ≠ 0} := by
        ext u
        exact ⟨fun h => h hij, fun h _ => h⟩
      rw [he]
      exact isOpen_ne_fun (by fun_prop) continuous_const
  have hSdense (i j : Fin n) : Dense (S i j) := by
    by_cases hij : z i = z j
    · simp [S, hij]
    · have he : S i j = {u | ((z i - z j) * conj u).re ≠ 0} := by
        ext u
        exact ⟨fun h => h hij, fun h _ => h⟩
      rw [he]
      exact projection_nonzero_dense (sub_ne_zero.mpr hij)
  have hd : Dense (⋂ i, ⋂ j, S i j) :=
    dense_iInter_of_isOpen (fun i => isOpen_iInter_of_finite (hSopen i))
      (fun i => dense_iInter_of_isOpen (hSopen i) (hSdense i))
  convert hd using 1
  ext u
  simp [S]

theorem strictNormalCones_dense {n : ℕ} (hn : 0 < n) (z : Points n) :
    Dense (⋃ i, strictNormalCone z i) := by
  apply (separating_directions_dense z).mono
  intro u hu
  let f : Fin n → ℝ := fun i => (z i * conj u).re
  have hnonempty : (Set.range f).Nonempty := ⟨f ⟨0, hn⟩, Set.mem_range_self _⟩
  obtain ⟨i, hi⟩ := hnonempty.csSup_mem (Set.finite_range f)
  apply mem_iUnion.mpr
  refine ⟨i, ?_⟩
  intro j hji
  have hle : f j ≤ f i := by
    rw [hi]
    exact le_csSup (Set.finite_range f).bddAbove (Set.mem_range_self j)
  have hdiff := hu i j hji.symm
  simp only [sub_mul, Complex.sub_re] at hdiff ⊢
  exact lt_of_le_of_ne (sub_nonneg.mpr hle) hdiff.symm

/-- The closures of the finitely many strict angular cells cover the full
closed angular interval. No general-position hypothesis is used. -/
theorem strictNormalAngles_closure_cover {n : ℕ} (hn : 0 < n) (z : Points n) :
    Icc (-Real.pi) Real.pi ⊆ closure (⋃ i, strictNormalAngles z i) := by
  have hs : Ioo (-Real.pi) Real.pi ⊆ closure (⋃ i, strictNormalAngles z i) := by
    intro t ht
    have harg := arg_circleDirection ht
    have hslit : circleDirection t ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff_arg.mpr ⟨by rw [harg]; exact ht.2.ne,
        Complex.exp_ne_zero _⟩
    have hh := mem_closure_image (Complex.continuousAt_arg hslit)
      (strictNormalCones_dense hn z (circleDirection t))
    rw [harg, Set.image_iUnion] at hh
    exact hh
  have hh := closure_mono hs
  rw [closure_Ioo (by linarith [Real.pi_pos]), closure_closure] at hh
  exact hh

#print axioms strictNormalCones_dense
#print axioms strictNormalAngles_closure_cover

end
end ExteriorReduction.Reinhardt

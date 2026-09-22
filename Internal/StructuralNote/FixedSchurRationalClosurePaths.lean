import StructuralNote.FixedSchurRationalWindowClosureDerivative
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! Smooth paths in the actual rational closure manifold. -/

namespace StructuralNote.FixedSchurRationalClosurePaths

open Complex Filter
open RationalChart RationalConfiguration
open FixedSchurRationalWindowClosureDerivative
open scoped BigOperators Topology ContDiff

noncomputable section

theorem rotation_contDiff : ContDiff ℝ ∞ RationalChart.rotation := by
  change ContDiff ℝ ∞ (fun t : ℝ => Complex.equivRealProdCLM.symm
    ((1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2)))
  apply Complex.equivRealProdCLM.symm.contDiff.comp
  apply ContDiff.prodMk
  · exact (contDiff_const.sub (contDiff_id.pow 2)).div
      (contDiff_const.add (contDiff_id.pow 2))
      (fun t => ne_of_gt (RationalChart.denominator_pos t))
  · exact ((contDiff_const.mul contDiff_id).div
      (contDiff_const.add (contDiff_id.pow 2))
      (fun t => ne_of_gt (RationalChart.denominator_pos t)))

private theorem angleParameter_contDiff {m : ℕ} (j : Fin m) :
    ContDiff ℝ ∞ (fun Z : RationalConfiguration.Variables m → ℝ =>
      RationalConfiguration.angleParameter Z j) := by
  unfold RationalConfiguration.angleParameter
  split <;> fun_prop

private theorem crossingParameter_contDiff {m : ℕ} (j : Fin m) :
    ContDiff ℝ ∞ (fun Z : RationalConfiguration.Variables m → ℝ =>
      RationalConfiguration.crossingParameter Z j) := by
  unfold RationalConfiguration.crossingParameter
  fun_prop

/-- The literal rational closure is smooth to every finite order. -/
theorem rational_closure_contDiff {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) :
    ContDiff ℝ ∞ (RationalConfiguration.closure hm σ) := by
  unfold RationalConfiguration.closure
  have hinc (j : Fin m) : ContDiff ℝ ∞
      (fun Z : RationalConfiguration.Variables m → ℝ =>
        RationalConfiguration.increment hm σ Z j) := by
    unfold RationalConfiguration.increment RationalChart.crossingIncrement
    have hd₀ : ContDiff ℝ ∞ (fun Z : RationalConfiguration.Variables m → ℝ =>
        RationalConfiguration.diameter hm Z j) := by
      unfold RationalConfiguration.diameter
      exact contDiff_const.mul
        (rotation_contDiff.comp (angleParameter_contDiff _))
    have hd₁ : ContDiff ℝ ∞ (fun Z : RationalConfiguration.Variables m → ℝ =>
        RationalConfiguration.diameter hm Z (j.val + 1)) := by
      unfold RationalConfiguration.diameter
      exact contDiff_const.mul
        (rotation_contDiff.comp (angleParameter_contDiff _))
    have hU : ContDiff ℝ ∞ (fun Z : RationalConfiguration.Variables m → ℝ =>
        RationalConfiguration.crossingUnit Z j) := by
      unfold RationalConfiguration.crossingUnit
      exact contDiff_const.mul
        (rotation_contDiff.comp (crossingParameter_contDiff _))
    exact contDiff_const.mul (((contDiff_const.mul hU).sub hd₀).sub hd₁)
  have hsum (S : Finset (Fin m)) : ContDiff ℝ ∞
      (fun Z : RationalConfiguration.Variables m → ℝ =>
        ∑ j ∈ S, RationalConfiguration.increment hm σ Z j) := by
    induction S using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; fun_prop
    | @insert a S ha ih =>
        simp only [Finset.sum_insert ha]
        exact (hinc a).add ih
  simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
    hsum (Finset.univ : Finset (Fin m))

/-- Every vector in the kernel of the actual closure derivative is the
velocity of an exactly closed smooth path through the rational point. -/
theorem exists_smooth_closed_path {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X u : RationalConfiguration.Variables m → ℝ)
    (hclosure : RationalConfiguration.closure hm σ X = 0)
    (hfull : Function.Surjective (closureFDeriv hm σ X))
    (hu : closureFDeriv hm σ X u = 0) :
    ∃ Z : ℝ → (RationalConfiguration.Variables m → ℝ),
      Z 0 = X ∧ ContDiffAt ℝ ∞ Z 0 ∧
        (∀ᶠ t in nhds (0 : ℝ), RationalConfiguration.closure hm σ (Z t) = 0) ∧
        deriv Z 0 = u := by
  let f := RationalConfiguration.closure hm σ
  let f' := closureFDeriv hm σ X
  have hcf : ContDiffAt ℝ ∞ f X := (rational_closure_contDiff hm σ).contDiffAt
  have hf : HasStrictFDerivAt f f' X := by
    exact hcf.hasStrictFDerivAt (by simp)
  have htop : f'.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact hfull
  let hker : f'.ker.ClosedComplemented :=
    f'.ker_closedComplemented_of_finiteDimensional_range
  let φ := hf.implicitFunctionDataOfComplemented f f' htop hker
  let g := hf.implicitFunctionOfComplemented f f' htop hker
  let uk : f'.ker := ⟨u, hu⟩
  let Z : ℝ → (RationalConfiguration.Variables m → ℝ) :=
    fun t => g (f X) (t • uk)
  have hright : ContDiffAt ℝ ∞ φ.rightFun φ.pt := by
    dsimp [φ, HasStrictFDerivAt.implicitFunctionDataOfComplemented]
    fun_prop
  have hphi : ContDiffAt ℝ ∞ φ.implicitFunction.uncurry (φ.prodFun φ.pt) :=
    φ.contDiffAt_implicitFunction (by simpa [φ] using hcf) hright (by simp)
  have hbase : φ.prodFun φ.pt = (f X, (0 : f'.ker)) := by
    simp [φ]
  have hline : ContDiffAt ℝ ∞ (fun t : ℝ => (f X, t • uk)) 0 := by
    fun_prop
  have hg : ContDiffAt ℝ ∞ g.uncurry (f X, (0 : f'.ker)) := by
    rw [hbase] at hphi
    simpa only [g, φ, HasStrictFDerivAt.implicitFunctionOfComplemented] using hphi
  have hgpartial : ContDiffAt ℝ ∞ (g (f X)) (0 : f'.ker) := by
    have hp : ContDiffAt ℝ ∞ (fun z : f'.ker => (f X, z)) 0 := by
      fun_prop
    have hc : ContDiffAt ℝ ∞
        (g.uncurry ∘ fun z : f'.ker => (f X, z)) 0 := hg.comp 0 hp
    convert hc using 1
    funext z
    rfl
  have hZsmooth : ContDiffAt ℝ ∞ Z 0 := by
    have hs : ContDiffAt ℝ ∞ (fun t : ℝ => t • uk) 0 := by
      fun_prop
    have hgpartial' : ContDiffAt ℝ ∞ (g (f X)) ((0 : ℝ) • uk) := by
      simpa only [zero_smul] using hgpartial
    have hc : ContDiffAt ℝ ∞
        (g (f X) ∘ fun t : ℝ => t • uk) 0 := hgpartial'.comp 0 hs
    convert hc using 1
    funext t
    rfl
  have hZX : Z 0 = X := by
    change g (f X) (0 • uk) = X
    simp only [zero_smul]
    exact hf.implicitFunctionOfComplemented_apply_image htop hker
  have hmap : ∀ᶠ p : ℂ × f'.ker in nhds (f X, 0),
      f (g p.1 p.2) = p.1 := by
    simpa only [g] using hf.map_implicitFunctionOfComplemented_eq htop hker
  have hclosed : ∀ᶠ t in nhds (0 : ℝ),
      RationalConfiguration.closure hm σ (Z t) = 0 := by
    have ht : Tendsto (fun t : ℝ => (f X, t • uk)) (nhds 0) (nhds (f X, 0)) := by
      have ht' := hline.continuousAt
      change Tendsto (fun t : ℝ => (f X, t • uk)) (nhds 0)
        (nhds ((fun t : ℝ => (f X, t • uk)) 0)) at ht'
      simpa only [zero_smul] using ht'
    filter_upwards [ht.eventually hmap] with t ht'
    simpa only [Z, f, hclosure] using ht'
  have himp := hf.to_implicitFunctionOfComplemented htop hker
  have hlineDeriv : HasDerivAt (fun t : ℝ => t • uk) uk 0 := by
    simpa only [one_smul] using (hasDerivAt_id' (0 : ℝ)).smul_const uk
  have hZderiv : deriv Z 0 = u := by
    have hout : HasFDerivAt
        (hf.implicitFunctionOfComplemented f f' htop hker (f X)) f'.ker.subtypeL
        ((0 : ℝ) • uk) := by
      simpa only [zero_smul] using himp.hasFDerivAt
    have hc := hout.comp_hasDerivAt 0 hlineDeriv
    change deriv (fun t : ℝ => g (f X) (t • uk)) 0 = u
    have he : (fun t : ℝ => g (f X) (t • uk)) =
        (hf.implicitFunctionOfComplemented f f' htop hker (f X) ∘
          fun t : ℝ => t • uk) := by
      funext t
      rfl
    calc
      deriv (fun t : ℝ => g (f X) (t • uk)) 0 =
          deriv (hf.implicitFunctionOfComplemented f f' htop hker (f X) ∘
            fun t : ℝ => t • uk) 0 := congrArg (fun h => deriv h 0) he
      _ = f'.ker.subtypeL uk := hc.deriv
      _ = u := rfl
  exact ⟨Z, hZX, hZsmooth, hclosed, hZderiv⟩

end
end StructuralNote.FixedSchurRationalClosurePaths



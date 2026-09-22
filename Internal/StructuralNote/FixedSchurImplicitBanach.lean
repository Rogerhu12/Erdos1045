import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed

/-! A smooth local fixed point from a contraction on a neighborhood. -/

namespace StructuralNote.FixedSchurImplicitBanach

open Filter Metric
open scoped Topology ContDiff

noncomputable section

variable {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

theorem residual_partial (F : P × Q → Q) (p : P) (q : Q)
    (hF : DifferentiableAt ℝ F (p, q)) :
    (fderiv ℝ (fun u : P × Q => u.2 - F u) (p, q)).comp
      (ContinuousLinearMap.inr ℝ P Q) = 1 - fderiv ℝ (fun z => F (p, z)) q := by
  have hi : HasFDerivAt (fun z : Q => (p, z))
      (ContinuousLinearMap.inr ℝ P Q) q := by
    convert (hasFDerivAt_const p q).prodMk (hasFDerivAt_id q) using 1 <;> rfl
  have hslice := hF.hasFDerivAt.comp q hi
  have hres := (differentiableAt_snd.sub hF).hasFDerivAt.comp q hi
  have hd := (hasFDerivAt_id q).sub hslice.differentiableAt.hasFDerivAt
  exact hres.unique hd

variable [CompleteSpace Q]

theorem residual_partial_invertible (F : P × Q → Q) (p : P) (q f : Q) {R : ℝ}
    (hF : DifferentiableAt ℝ F (p, q)) (hq : ‖q - f‖ < R)
    (hLip : LipschitzOnWith (1 / 2) (fun z => F (p, z)) (closedBall f R)) :
    ((fderiv ℝ (fun u : P × Q => u.2 - F u) (p, q)).comp
      (ContinuousLinearMap.inr ℝ P Q)).IsInvertible := by
  rw [residual_partial F p q hF]
  have hmem : closedBall f R ∈ 𝓝 q :=
    closedBall_mem_nhds_of_mem (by simpa only [mem_ball, dist_eq_norm] using hq)
  have hn := norm_fderiv_le_of_lipschitzOn ℝ hmem hLip
  have hu := isUnit_one_sub_of_norm_lt_one (by norm_num at hn; linarith :
    ‖fderiv ℝ (fun z => F (p, z)) q‖ < 1)
  obtain ⟨u, hu⟩ := hu
  exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩

theorem exists_smooth_fixedPoint [CompleteSpace P]
    (F : P × Q → Q) (p : P) (q f : Q) {R : ℝ}
    (hF : ContDiffAt ℝ ∞ F (p, q)) (hq : ‖q - f‖ < R)
    (hLip : LipschitzOnWith (1 / 2) (fun z => F (p, z)) (closedBall f R))
    (hfix : F (p, q) = q) :
    ∃ g : P → Q, g p = q ∧ ContDiffAt ℝ ∞ g p ∧
      (∀ᶠ p' in 𝓝 p, F (p', g p') = g p' ∧ ‖g p' - f‖ < R) := by
  have hG : ContDiffAt ℝ ∞ (fun u : P × Q => u.2 - F u) (p, q) :=
    contDiffAt_snd.sub hF
  have hInv := residual_partial_invertible F p q f (hF.differentiableAt (by simp)) hq hLip
  let g := hG.implicitFunction (by simp) hInv
  have hgp : g p = q := hG.implicitFunction_apply_self (by simp) hInv
  have hg : ContDiffAt ℝ ∞ g p := hG.contDiffAt_implicitFunction (by simp) hInv
  have hz : ∀ᶠ p' in 𝓝 p, g p' - F (p', g p') = 0 := by
    simpa only [hfix, sub_self] using hG.eventually_apply_implicitFunction (by simp) hInv
  have hb : ∀ᶠ p' in 𝓝 p, ‖g p' - f‖ < R :=
    (hg.continuousAt.sub continuousAt_const).norm.eventually
      (gt_mem_nhds (by simpa only [Pi.sub_apply, hgp] using hq))
  refine ⟨g, hgp, hg, ?_⟩
  filter_upwards [hz, hb] with p' hp' hb'
  exact ⟨(sub_eq_zero.mp hp').symm, hb'⟩

end
end StructuralNote.FixedSchurImplicitBanach

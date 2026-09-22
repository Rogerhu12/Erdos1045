import EventualExact.LensClosureNonlinear
import EventualExact.BoxLensLift
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! Smooth local solution of the actual finite square-root closure equation. -/

namespace Erdos1045.EventualExact.LensClosure

open Complex Filter
open scoped BigOperators Topology ContDiff
noncomputable section

abbrev Parameters (m : ℕ) :=
  (Fin m → ℝ) × (Fin m → ℝ) × (Fin m → ℝ) × (Fin m → ℝ)

def closureFamily {m : ℕ} (p : Parameters m) (ξ : ℂ) : ℂ :=
  closure p.1 p.2.1 p.2.2.1 p.2.2.2 ξ

theorem heightParameter_contDiff {m : ℕ} (j : Fin m) :
    ContDiff ℝ ∞ (fun u : Parameters m × ℂ => heightParameter u.1.2.2.2 u.2 j) := by
  unfold heightParameter
  have hH := (harmonicFunctional (midpoint m j)).contDiff (n := ∞)
  fun_prop

/-- Joint smoothness holds on the genuine positive square-root domain. -/
theorem closureFamily_contDiffAt {m : ℕ} (p : Parameters m) (ξ : ℂ)
    (ht : ∀ j, |heightParameter p.2.2.2 ξ j| < 2) :
    ContDiffAt ℝ ∞ (Function.uncurry closureFamily) (p, ξ) := by
  have hh (j : Fin m) : ContDiffAt ℝ ∞
      (fun u : Parameters m × ℂ => Lens.height (heightParameter u.1.2.2.2 u.2 j)) (p, ξ) := by
    unfold Lens.height
    apply (contDiffAt_const.sub ((heightParameter_contDiff j).contDiffAt.pow 2)).sqrt
    have h := ht j
    have hsq : heightParameter p.2.2.2 ξ j ^ 2 < 4 := by
      nlinarith [(abs_lt.mp h).1, (abs_lt.mp h).2]
    dsimp
    linarith
  change ContDiffAt ℝ ∞ (fun u : Parameters m × ℂ =>
    ∑ j, increment (u.1.1 j) (u.1.2.1 j) (u.1.2.2.1 j)
      (heightParameter u.1.2.2.2 u.2 j)) (p, ξ)
  apply ContDiffAt.sum
  intro j _
  unfold increment unit Lens.width
  have ht' := (heightParameter_contDiff j).contDiffAt (x := (p, ξ))
  have hcast : ContDiff ℝ ∞ (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  fun_prop

theorem closureFamily_partial {m : ℕ} (p : Parameters m) (ξ : ℂ)
    (ht : ∀ j, |heightParameter p.2.2.2 ξ j| < 2) :
    (fderiv ℝ (Function.uncurry closureFamily) (p, ξ)).comp
      (ContinuousLinearMap.inr ℝ (Parameters m) ℂ) =
      closureDerivative p.1 p.2.2.1 p.2.2.2 ξ := by
  have hf := (closureFamily_contDiffAt p ξ ht).differentiableAt (by simp)
  have hi : HasFDerivAt (fun η : ℂ => (p, η))
      (ContinuousLinearMap.inr ℝ (Parameters m) ℂ) ξ := by
    convert (hasFDerivAt_const p ξ).prodMk (hasFDerivAt_id ξ) using 1 <;> rfl
  have hc := hf.hasFDerivAt.comp ξ hi
  have hd := closure_hasFDerivAt p.1 p.2.1 p.2.2.1 p.2.2.2 ξ (fun j => by
    have h := ht j
    nlinarith [(abs_lt.mp h).1, (abs_lt.mp h).2])
  exact hc.unique hd

theorem closureFamily_partial_invertible {m : ℕ} (hm : 2 ≤ m)
    (p : Parameters m) (ξ : ℂ) (hs : ∀ j, |p.2.2.1 j| ≤ 1)
    (hsmall : ∀ j, |p.1 j - midpoint m j| + |heightParameter p.2.2.2 ξ j| ≤ 1 / 4) :
    ((fderiv ℝ (Function.uncurry closureFamily) (p, ξ)).comp
      (ContinuousLinearMap.inr ℝ (Parameters m) ℂ)).IsInvertible := by
  have ht (j : Fin m) : |heightParameter p.2.2.2 ξ j| < 2 := by
    have h := hsmall j
    linarith [abs_nonneg (p.1 j - midpoint m j)]
  rw [closureFamily_partial p ξ ht]
  have hb := (closure_regular hm p.1 p.2.1 p.2.2.1 p.2.2.2 ξ hs hsmall).2
  exact ⟨(LinearEquiv.ofBijective
    (closureDerivative p.1 p.2.2.1 p.2.2.2 ξ).toLinearMap hb).toContinuousLinearEquiv, rfl⟩

/-- Exact local root, smooth in all four arrays, and locally unique in the root variable. -/
theorem exists_smooth_closure_root {m : ℕ} (hm : 2 ≤ m)
    (p : Parameters m) (ξ : ℂ) (hs : ∀ j, |p.2.2.1 j| ≤ 1)
    (hsmall : ∀ j, |p.1 j - midpoint m j| + |heightParameter p.2.2.2 ξ j| ≤ 1 / 4)
    (hzero : closureFamily p ξ = 0) :
    ∃ g : Parameters m → ℂ, g p = ξ ∧ ContDiffAt ℝ ∞ g p ∧
      (∀ᶠ p' in 𝓝 p, closureFamily p' (g p') = 0) ∧
      (∀ᶠ u in 𝓝 (p, ξ), closureFamily u.1 u.2 = 0 ↔ g u.1 = u.2) := by
  have ht (j : Fin m) : |heightParameter p.2.2.2 ξ j| < 2 := by
    have h := hsmall j
    linarith [abs_nonneg (p.1 j - midpoint m j)]
  let hf := closureFamily_contDiffAt p ξ ht
  let hi := closureFamily_partial_invertible hm p ξ hs hsmall
  refine ⟨hf.implicitFunction (by simp) hi,
    hf.implicitFunction_apply_self (by simp) hi,
    hf.contDiffAt_implicitFunction (by simp) hi, ?_, ?_⟩
  · simpa only [Function.uncurry, hzero] using
      hf.eventually_apply_implicitFunction (by simp) hi
  · simpa only [Function.uncurry, hzero] using
      hf.eventually_apply_eq_iff_implicitFunction (by simp) hi

theorem closure_roots_eq_on_ball {m : ℕ} (hm : 2 ≤ m)
    (p : Parameters m) {R : ℝ} (hs : ∀ j, |p.2.2.1 j| ≤ 1)
    (hsmall : ∀ j, |p.1 j - midpoint m j| + |p.2.2.2 j| + R ≤ 1 / 4)
    {ξ η : ℂ} (hξ : ‖ξ‖ ≤ R) (hη : ‖η‖ ≤ R)
    (hξzero : closureFamily p ξ = 0) (hηzero : closureFamily p η = 0) : ξ = η := by
  have hLip := correction_lipschitz_on_ball hm p.1 p.2.1 p.2.2.1 p.2.2.2 hs hsmall
  have hfξ := (correction_fixed_iff (by omega) p.1 p.2.1 p.2.2.1 p.2.2.2 ξ).2 hξzero
  have hfη := (correction_fixed_iff (by omega) p.1 p.2.1 p.2.2.1 p.2.2.2 η).2 hηzero
  have h := (lipschitzOnWith_iff_norm_sub_le.mp hLip)
    (mem_closedBall_zero_iff.mpr hξ) (mem_closedBall_zero_iff.mpr hη)
  rw [hfξ, hfη] at h
  norm_num at h
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (ξ - η)]

/-- Ball uniqueness identifies the local smooth branch with every quantitative small root. -/
theorem exists_smooth_closure_root_agree_ball {m : ℕ} (hm : 2 ≤ m)
    (p : Parameters m) (ξ : ℂ) {R : ℝ} (hR : 0 < R)
    (hs : ∀ j, |p.2.2.1 j| ≤ 1)
    (hsmall : ∀ j, |p.1 j - midpoint m j| + |p.2.2.2 j| + 2 * R ≤ 1 / 4)
    (hξ : ‖ξ‖ ≤ R) (hzero : closureFamily p ξ = 0) :
    ∃ g : Parameters m → ℂ, g p = ξ ∧ ContDiffAt ℝ ∞ g p ∧
      (∀ᶠ p' in 𝓝 p, closureFamily p' (g p') = 0 ∧
        ((∀ j, |p'.2.2.1 j| ≤ 1) →
          (∀ j, |p'.1 j - midpoint m j| + |p'.2.2.2 j| + 2 * R ≤ 1 / 4) →
          ∀ η : ℂ, ‖η‖ ≤ R → closureFamily p' η = 0 → g p' = η)) := by
  have hp := ball_height_small p.1 p.2.2.2 hsmall
    (mem_closedBall_zero_iff.mpr (hξ.trans (by linarith : R ≤ 2 * R)))
  obtain ⟨g, hgp, hg, hgz, _⟩ := exists_smooth_closure_root hm p ξ hs hp hzero
  have hgsmall : ∀ᶠ p' in 𝓝 p, ‖g p'‖ < 2 * R := by
    have he : ∀ᶠ y : ℝ in 𝓝 ‖g p‖, y < 2 * R := gt_mem_nhds (by
      rw [hgp]
      linarith)
    exact hg.continuousAt.norm.eventually he
  refine ⟨g, hgp, hg, ?_⟩
  filter_upwards [hgz, hgsmall] with p' hz hn
  refine ⟨hz, ?_⟩
  intro hs' hsmall' η hη hηzero
  exact closure_roots_eq_on_ball hm p' hs' hsmall' hn.le
    (hη.trans (by linarith : R ≤ 2 * R)) hz hηzero

def boxParameters {m : ℕ} (q : Fin (2 * m) → ℝ) : Parameters m :=
  (midpoint m, fun _ => BoxLensLift.baseWidth (2 * m),
    fun j => BoxLensLift.coordinate q (BoxLensLift.halfIndex j),
    fun j => BoxLensLift.tangential q (BoxLensLift.halfIndex j))

@[simp] theorem closureFamily_boxParameters {m : ℕ} (q : Fin (2 * m) → ℝ) (ξ : ℂ) :
    closureFamily (boxParameters q) ξ = BoxLensLift.boxClosure q ξ := rfl

theorem boxParameters_double_radius_small {m : ℕ} (hm : 16 ≤ m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ FiniteBox.Q (by omega)) (j : Fin m) :
    |(boxParameters q).1 j - midpoint m j| + |(boxParameters q).2.2.2 j| +
      2 * BoxLensLift.rootRadius (2 * m) ≤ 1 / 4 := by
  have ht := BoxLensLift.tangential_small (by omega) q hq.2 (BoxLensLift.halfIndex j)
  have hR := BoxLensLift.rootRadius_le (by omega : 32 ≤ 2 * m)
  simp only [boxParameters, sub_self, abs_zero, zero_add]
  linarith

/-- The previously chosen `boxRoot` is the restriction of this genuine smooth local branch. -/
theorem exists_smooth_boxRoot {m : ℕ} (hm : 16 ≤ m)
    (q : Fin (2 * m) → ℝ) (hq : q ∈ FiniteBox.Q (by omega)) :
    ∃ g : Parameters m → ℂ,
      g (boxParameters q) = BoxLensLift.boxRoot hm q hq ∧
      ContDiffAt ℝ ∞ g (boxParameters q) ∧
      (∀ᶠ p in 𝓝 (boxParameters q), closureFamily p (g p) = 0 ∧
        ∀ (q' : Fin (2 * m) → ℝ) (hq' : q' ∈ FiniteBox.Q (by omega)),
          p = boxParameters q' → g p = BoxLensLift.boxRoot hm q' hq') := by
  have hR : 0 < BoxLensLift.rootRadius (2 * m) := by
    have hn : (0 : ℝ) < (2 * m : ℕ) := by exact_mod_cast (show 0 < 2 * m by omega)
    unfold BoxLensLift.rootRadius
    positivity
  have hs (q' : Fin (2 * m) → ℝ) (hq' : q' ∈ FiniteBox.Q (by omega)) (j : Fin m) :
      |(boxParameters q').2.2.1 j| ≤ 1 :=
    BoxLensLift.coordinate_bound (by omega) q' hq'.2 (BoxLensLift.halfIndex j)
  obtain ⟨g, hgp, hg, he⟩ := exists_smooth_closure_root_agree_ball (by omega)
    (boxParameters q) (BoxLensLift.boxRoot hm q hq) hR (hs q hq)
    (boxParameters_double_radius_small hm q hq)
    (BoxLensLift.boxRoot_spec hm q hq).1 (BoxLensLift.boxRoot_spec hm q hq).2
  refine ⟨g, hgp, hg, ?_⟩
  filter_upwards [he] with p hp
  refine ⟨hp.1, ?_⟩
  intro q' hq' hparam
  subst p
  exact hp.2 (hs q' hq') (boxParameters_double_radius_small hm q' hq')
    (BoxLensLift.boxRoot hm q' hq') (BoxLensLift.boxRoot_spec hm q' hq').1
    (BoxLensLift.boxRoot_spec hm q' hq').2

end
end Erdos1045.EventualExact.LensClosure

import InteriorConvexCriterionComplete
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Connected.Clopen

/-!
Local maximum principles needed by a direct proof of the exterior convexity
criterion.  These lemmas permit a continuous scalar envelope whose holomorphic
representatives exist only above a threshold.  Consequently a rotated average
need not stay in the exterior of the omitted convex set everywhere.

The geometric construction and continuity of that envelope are not asserted
here: those remain separate obligations.
-/

namespace ExteriorReduction.ExteriorConvexCriterion

open Complex Metric Set Filter
open scoped Topology
open scoped ComplexConjugate

noncomputable section

/-- A continuous scalar function locally equal to a holomorphic norm wherever
it exceeds `C` satisfies the maximum principle, provided its upper limit at
infinity is at most `C`.  No global holomorphic representative is required. -/
theorem scalar_envelope_maximum {u : ℂ → ℝ} {C : ℝ}
    (hu : Continuous u)
    (hlocal : ∀ z, C < u z → ∃ F : ℂ → ℂ, AnalyticAt ℂ F z ∧
      ∀ᶠ w in 𝓝 z, u w = ‖F w‖)
    (hinfty : ∀ R : ℝ, C < R → ∀ᶠ w in cocompact ℂ, u w < R) :
    ∀ z, u z ≤ C := by
  intro z
  by_contra hbad
  have hbad' : C < u z := lt_of_not_ge hbad
  obtain ⟨a, hmax⟩ := hu.exists_forall_ge' z ((hinfty (u z) hbad').mono fun _ h => h.le)
  have hCa : C < u a := hbad'.trans_le (hmax z)
  have hopen : IsOpen {w : ℂ | u w = u a} := by
    refine isOpen_iff_mem_nhds.mpr ?_
    intro w hw
    obtain ⟨F, hF, heq⟩ := hlocal w (by simpa only [mem_ofPred_eq] using hw ▸ hCa)
    have hFw : u w = ‖F w‖ := heq.self_of_nhds
    have hFm : IsLocalMax (norm ∘ F) w := by
      filter_upwards [heq] with v hv
      change ‖F v‖ ≤ ‖F w‖
      rw [← hv, ← hFw, hw]
      exact hmax v
    have hconst := Complex.norm_eventually_eq_of_isLocalMax
      (hF.eventually_analyticAt.mono fun _ h => h.differentiableAt) hFm
    filter_upwards [heq, hconst] with v hv hc
    rw [hv, hc, ← hFw, hw]
  have hclosed : IsClosed {w : ℂ | u w = u a} := isClosed_eq hu continuous_const
  have hall : {w : ℂ | u w = u a} = univ :=
    (show IsClopen {w : ℂ | u w = u a} from ⟨hclosed, hopen⟩).eq_univ ⟨a, rfl⟩
  have hevent := hinfty (u a) hCa
  obtain ⟨w, hw⟩ := hevent.exists
  have hwa : u w = u a := by
    have : w ∈ ({v : ℂ | u v = u a} : Set ℂ) := by rw [hall]; trivial
    exact this
  exact (ne_of_lt hw) hwa

/-- The second-order real maximum test only needs smoothness near the point. -/
theorem second_deriv_nonpos_of_local_max_at {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 2 f 0) (hmax : IsLocalMax f 0) :
    deriv (deriv f) 0 ≤ 0 := by
  have hfirst : deriv f 0 = 0 := hmax.deriv_eq_zero
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
  have hzero : (0 : ℝ) ∈ ball 0 r := mem_ball_self hr
  have hiter (n : ℕ) : iteratedDerivWithin n f (ball 0 r) 0 =
      iteratedDeriv n f 0 := iteratedDerivWithin_of_isOpen isOpen_ball hzero
  have htaylor (t : ℝ) : taylorWithinEval f 2 (ball 0 r) 0 t =
      f 0 + (deriv (deriv f) 0 / 2) * t ^ 2 := by
    simp [show 2 = 1 + 1 from rfl, taylorWithinEval_succ,
      hiter, iteratedDeriv_succ, hfirst]
    ring
  have hlim : Tendsto (fun t : ℝ =>
      (f t - (f 0 + (deriv (deriv f) 0 / 2) * t ^ 2)) / t ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
    have h := Real.taylor_tendsto (f := f) (n := 2)
      (convex_ball 0 r) hzero (hfs.mono hrs)
    rw [nhdsWithin_eq_nhds.mpr (isOpen_ball.mem_nhds hzero)] at h
    simp only [htaylor, sub_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hevent : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      (f t - (f 0 + (deriv (deriv f) 0 / 2) * t ^ 2)) / t ^ 2 ≤
        -(deriv (deriv f) 0 / 2) := by
    filter_upwards [hmax.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht htne
    have htpos : 0 < t ^ 2 := sq_pos_of_ne_zero (by simpa using htne)
    rw [div_le_iff₀ htpos]
    linarith
  have h := le_of_tendsto hlim hevent
  linarith

/-- A local version of the complex-path maximum test: the inverse of a
rotated average need only be defined holomorphically close to parameter zero. -/
theorem analytic_local_real_max_second_deriv {A : ℂ → ℂ}
    (hA : AnalyticAt ℂ A 0) (hfirst : deriv A 0 = 0)
    (hbound : ∀ᶠ t : ℝ in 𝓝 0, ‖A (t : ℂ)‖ ≤ ‖A 0‖) :
    (deriv (deriv A) 0 * conj (A 0)).re ≤ 0 := by
  let H : ℝ → ℂ := fun t => A (t : ℂ)
  have hof : ContDiffAt ℝ 2 (fun t : ℝ => (t : ℂ)) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have hH : ContDiffAt ℝ 2 H 0 :=
    ContDiffAt.comp (f := fun t : ℝ => (t : ℂ)) (g := A) (n := 2) 0
      (hA.contDiffAt.restrict_scalars ℝ) hof
  have hAn : ∀ᶠ t : ℝ in 𝓝 0, AnalyticAt ℂ A (t : ℂ) := by
    exact (Complex.continuous_ofReal.continuousAt.tendsto).eventually hA.eventually_analyticAt
  have hHd : deriv H =ᶠ[𝓝 0] fun t : ℝ => deriv A (t : ℂ) := by
    filter_upwards [hAn] with t ht
    exact ht.differentiableAt.hasDerivAt.comp_ofReal.deriv
  have hHd0 : deriv H 0 = 0 := by simpa using hHd.self_of_nhds.trans hfirst
  have hHdd : HasDerivAt (deriv H) (deriv (deriv A) 0) 0 := by
    exact hA.deriv.differentiableAt.hasDerivAt.comp_ofReal.congr_of_eventuallyEq hHd
  have hmax : IsLocalMax (fun t => ‖H t‖ ^ 2) 0 := by
    filter_upwards [hbound] with t ht
    change ‖A (t : ℂ)‖ ^ 2 ≤ ‖A (0 : ℂ)‖ ^ 2
    nlinarith [norm_nonneg (A (t : ℂ)), norm_nonneg (A 0)]
  have hF := second_deriv_nonpos_of_local_max_at (hH.norm_sq ℝ) hmax
  have hderiv : deriv (fun t => ‖H t‖ ^ 2) =ᶠ[𝓝 0]
      fun t => 2 * inner ℝ (H t) (deriv H t) := by
    filter_upwards [hH.eventually (by norm_num)] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasDerivAt.norm_sq).deriv
  rw [hderiv.deriv_eq] at hF
  have hsecond := (((hH.differentiableAt (by norm_num)).hasDerivAt).inner ℝ hHdd).const_mul 2
  rw [hsecond.deriv] at hF
  have hi : inner ℝ (H 0) (deriv (deriv A) 0) ≤ 0 := by
    simp only [hHd0, inner_zero_right] at hF
    linarith
  simpa [Complex.inner, mul_comm, H] using hi

#print axioms scalar_envelope_maximum
#print axioms analytic_local_real_max_second_deriv

/-- The local differential consequence of the rotated-average norm estimate.
This applies on an exterior domain as soon as its scalar envelope estimate
has been proved; the average only needs to admit the inverse near zero. -/
theorem logDeriv_nonneg_of_local_rotation_bound {g G : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 0) (hg : AnalyticAt ℂ g z) (hG : AnalyticAt ℂ G (g z))
    (hleft : G ∘ g =ᶠ[𝓝 z] id)
    (hbound : ∀ᶠ t : ℝ in 𝓝 0,
      ‖G (InteriorConvexCriterion.rotationMean g z (t : ℂ))‖ ≤ ‖z‖) :
    0 ≤ (1 + z * deriv (deriv g) z / deriv g z).re := by
  let V : ℂ → ℂ := InteriorConvexCriterion.rotationMean g z
  let A : ℂ → ℂ := G ∘ V
  have hV0 : V 0 = g z := InteriorConvexCriterion.rotationMean_zero g z
  have hA0 : A 0 = z := by simpa [A, hV0] using hleft.self_of_nhds
  have hV : AnalyticAt ℂ V 0 := InteriorConvexCriterion.rotationMean_analyticAt_zero hg
  have hG' : AnalyticAt ℂ G (V 0) := by simpa [hV0] using hG
  have hA : AnalyticAt ℂ A 0 := hG'.comp hV
  have hVfirst : deriv V 0 = 0 := InteriorConvexCriterion.rotationMean_deriv_zero hg
  have hAfirst : deriv A 0 = 0 := by
    have hd := hG'.differentiableAt.hasDerivAt.comp 0 hV.differentiableAt.hasDerivAt
    simpa [A, hVfirst] using hd.deriv
  have hAbound : ∀ᶠ t : ℝ in 𝓝 0, ‖A (t : ℂ)‖ ≤ ‖A 0‖ := by
    simpa only [hA0, A, Function.comp_apply, V] using hbound
  have hsecond := analytic_local_real_max_second_deriv hA hAfirst hAbound
  have hAdd : deriv (deriv A) 0 = deriv G (g z) *
      -(deriv (deriv g) z * z ^ 2 + deriv g z * z) := by
    have hd := iteratedDeriv_comp_two hG'.contDiffAt hV.contDiffAt
    simpa [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, A, hVfirst, hV0,
      V, InteriorConvexCriterion.rotationMean_second_deriv_zero hg] using hd
  have hinv : deriv G (g z) * deriv g z = 1 := by
    have hd := hG.differentiableAt.hasDerivAt.comp z hg.differentiableAt.hasDerivAt
    rw [← hd.deriv, hleft.deriv_eq]
    exact deriv_id z
  have hdne : deriv g z ≠ 0 := by
    intro h
    simp [h] at hinv
  have hinv' : deriv G (g z) = (deriv g z)⁻¹ := by
    apply (mul_right_cancel₀ hdne)
    simpa [hdne] using hinv
  have halgebra : (deriv G (g z) *
      -(deriv (deriv g) z * z ^ 2 + deriv g z * z) * conj z).re =
      -(‖z‖ ^ 2) * (1 + z * deriv (deriv g) z / deriv g z).re := by
    rw [hinv']
    have heq : (deriv g z)⁻¹ *
        -(deriv (deriv g) z * z ^ 2 + deriv g z * z) * conj z =
        -((‖z‖ ^ 2 : ℝ) : ℂ) *
          (1 + z * deriv (deriv g) z / deriv g z) := by
      push_cast
      rw [← Complex.mul_conj']
      field_simp
      ring
    rw [heq, Complex.mul_re]
    simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  rw [hAdd, hA0, halgebra] at hsecond
  have hpos : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  nlinarith

#print axioms logDeriv_nonneg_of_local_rotation_bound

end
end ExteriorReduction.ExteriorConvexCriterion

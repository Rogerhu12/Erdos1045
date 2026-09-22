import EventualExact.LocalGradientLimit
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Actual radial integration. This reproduces the earlier RadialPrice proof with
its redundant simplifier arguments removed, preserving the immutable old source. -/

namespace StructuralNote.RadialObjectivePrice

open Erdos1045 Erdos1045.EventualExact
open Complex Configuration LocalGradient Filter Set
open scoped BigOperators ComplexConjugate Topology
noncomputable section

theorem eventually_injective_of_hasDerivAt {n : ℕ} {p : ℝ → Points n}
    {t : ℝ} {v : Points n} (hp : ∀ i, HasDerivAt (fun s => p s i) (v i) t)
    (hz : Function.Injective (p t)) : ∀ᶠ s in 𝓝 t, Function.Injective (p s) := by
  have hne (i j : Fin n) : ∀ᶠ s in 𝓝 t, i ≠ j → p s i ≠ p s j := by
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    · have h := ((hp i).continuousAt.sub (hp j).continuousAt).eventually_ne
        (sub_ne_zero.mpr (hz.ne hij))
      filter_upwards [h] with s hs
      exact fun _ => sub_ne_zero.mp hs
  have h := eventually_all.2 (fun i => eventually_all.2 (hne i))
  filter_upwards [h] with s hs
  intro i j hij
  by_contra hne
  exact hs i j hne hij

theorem hasDerivAt_log_pair {n : ℕ} {p : ℝ → Points n}
    {t : ℝ} {v : Points n} (hp : ∀ i, HasDerivAt (fun s => p s i) (v i) t)
    (hz : Function.Injective (p t)) (i j : Fin n) :
    HasDerivAt (fun s => Real.log ‖p s i - p s j‖)
      (((v i - v j) / (p t i - p t j)).re) t := by
  by_cases hij : i = j
  · subst j
    simpa only [sub_self, norm_zero, Real.log_zero, zero_div, zero_re] using
      (hasDerivAt_const t (0 : ℝ))
  · have hn : ‖p t i - p t j‖ ^ 2 ≠ 0 :=
      pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hz.ne hij)))
    have hd := ((((hp i).sub (hp j)).norm_sq).log hn).div_const 2
    convert hd using 1 <;> try rfl
    · funext s
      simp only [Pi.sub_apply, Real.log_pow, Nat.cast_ofNat]
      ring
    · rw [Complex.inner, Complex.div_re, Complex.normSq_eq_norm_sq]
      simp only [mul_re, conj_re, conj_im, Pi.sub_apply]
      ring

theorem pair_derivative_sum {n : ℕ} (z v : Points n) :
    (∑ i, ∑ j, ((v i - v j) / (z i - z j)).re) =
      ∑ i, inner ℝ (realGradient z i) (v i) := by
  have hp (i j : Fin n) : ((v i - v j) / (z i - z j)).re =
      (v i / (z i - z j)).re + (v j / (z j - z i)).re := by
    rw [show z j - z i = -(z i - z j) by ring, div_neg, sub_div]
    simp only [sub_re, neg_re]
    ring
  simp_rw [hp, Finset.sum_add_distrib]
  have hs : (∑ i, ∑ j, (v j / (z j - z i)).re) =
      ∑ i, ∑ j, (v i / (z i - z j)).re := Finset.sum_comm
  rw [hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [realGradient_inner, FeketeStationarity.nodeGradient_eq_univ, conj_conj]
  simp only [Finset.sum_mul, Complex.re_sum, div_eq_mul_inv, mul_comm (v i)]
  ring

/-- Every coordinate may move simultaneously; the function is the original `log discriminant`. -/
theorem hasDerivAt_log_discriminant_path {n : ℕ} {p : ℝ → Points n}
    {t : ℝ} {v : Points n} (hp : ∀ i, HasDerivAt (fun s => p s i) (v i) t)
    (hz : Function.Injective (p t)) :
    HasDerivAt (fun s => Real.log (discriminant (p s)))
      (∑ i, inner ℝ (realGradient (p t) i) (v i)) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hasDerivAt_log_pair hp hz i j))
  rw [pair_derivative_sum] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_injective_of_hasDerivAt hp hz] with s hs
  exact LocalConfiguration.logDiscriminant_eq_sum (p s) hs

def path {n : ℕ} (θ b : Fin n → ℝ) (c : Points n) (t : ℝ) : Points n :=
  fun i => ExteriorBoundary.unit (θ i) *
    (((1 - t * b i : ℝ) : ℂ) * LocalPhase.regularRoot n ^ (i : ℕ) + c i)

def velocity {n : ℕ} (θ b : Fin n → ℝ) : Points n :=
  fun i => -(b i : ℂ) * (ExteriorBoundary.unit (θ i) * LocalPhase.regularRoot n ^ (i : ℕ))

def mass {n : ℕ} (b : Fin n → ℝ) : ℝ := (n : ℝ) * ∑ i, b i

def gradientDeviation {n : ℕ} (z : Points n) : ℝ :=
  ‖fun i : Fin n => realGradient z i -
    ((n : ℂ) - 1) * LocalPhase.regularRoot n ^ (i : ℕ)‖ / (n : ℝ)

theorem path_hasDerivAt {n : ℕ} (θ b : Fin n → ℝ) (c : Points n)
    (t : ℝ) (i : Fin n) : HasDerivAt (fun s => path θ b c s i) (velocity θ b i) t := by
  have hr := ((hasDerivAt_id t).mul_const (b i)).const_sub 1
  have hd := (hr.ofReal_comp.mul_const (LocalPhase.regularRoot n ^ (i : ℕ))).add_const (c i)
  convert hd.const_mul (ExteriorBoundary.unit (θ i)) using 1 <;> try rfl
  simp only [velocity, ofReal_neg, one_mul]
  ring

theorem gradientDeviation_eq_gradientError (n : ℕ) (u : ℕ → ℂ) :
    gradientDeviation (fun j : Fin n => LocalPhase.regularRoot n ^ (j : ℕ) + u j) =
      gradientError n u := rfl

theorem norm_velocity {n : ℕ} (θ b : Fin n → ℝ) (i : Fin n) (hb : 0 ≤ b i) :
    ‖velocity θ b i‖ = b i := by
  simp [velocity, norm_pow, LocalChord.root_norm, abs_of_nonneg hb]

theorem reference_inner_velocity {n : ℕ} (θ b : Fin n → ℝ) (i : Fin n) :
    inner ℝ (((n : ℂ) - 1) * LocalPhase.regularRoot n ^ (i : ℕ)) (velocity θ b i) =
      -((n : ℝ) - 1) * b i * Real.cos (θ i) := by
  let w := LocalPhase.regularRoot n ^ (i : ℕ)
  have hnw : ‖w‖ = 1 := by simp [w, norm_pow, LocalChord.root_norm]
  have hw : w * conj w = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnw]; norm_num
  have hi : inner ℝ w (ExteriorBoundary.unit (θ i) * w) = Real.cos (θ i) := by
    rw [Complex.inner]
    calc
      _ = (ExteriorBoundary.unit (θ i) * (w * conj w)).re := by congr 1; ring
      _ = (ExteriorBoundary.unit (θ i)).re := by rw [hw, mul_one]
      _ = _ := by simp [ExteriorBoundary.unit, Complex.exp_re]
  have he : ((n : ℂ) - 1) * w = ((n : ℝ) - 1) • w := by
    simp [Complex.real_smul]
  have hv : velocity θ b i = (-b i) • (ExteriorBoundary.unit (θ i) * w) := by
    simp [velocity, Complex.real_smul, w]
  change inner ℝ (((n : ℂ) - 1) * w) (velocity θ b i) = _
  rw [he, hv, real_inner_smul_left, real_inner_smul_right, hi]
  ring

theorem vertex_derivative_bound {n : ℕ} (hn : 0 < n) (θ b : Fin n → ℝ) (z : Points n)
    {ε δ : ℝ} (hε : gradientDeviation z ≤ ε) (hδ : 0 ≤ δ)
    (i : Fin n) (hb : 0 ≤ b i) (hθ : |θ i| ≤ δ) :
    inner ℝ (realGradient z i) (velocity θ b i) ≤
      -(1 - 1 / (n : ℝ) - ε - δ) * ((n : ℝ) * b i) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hg : ‖realGradient z i - ((n : ℂ) - 1) * LocalPhase.regularRoot n ^ (i : ℕ)‖ ≤ ε * n := by
    have hpi := norm_le_pi_norm (fun j : Fin n => realGradient z j -
      ((n : ℂ) - 1) * LocalPhase.regularRoot n ^ (j : ℕ)) i
    exact hpi.trans ((div_le_iff₀ hnR).1 hε)
  have hc : 1 - δ ≤ Real.cos (θ i) := by
    have hh := Real.abs_cos_sub_cos_le (θ i) 0
    simp only [Real.cos_zero, sub_zero] at hh
    have := (abs_le.mp (hh.trans hθ)).1
    linarith
  have herr := real_inner_le_norm
    (realGradient z i - ((n : ℂ) - 1) * LocalPhase.regularRoot n ^ (i : ℕ)) (velocity θ b i)
  rw [norm_velocity θ b i hb, inner_sub_left, reference_inner_velocity] at herr
  have he := mul_le_mul_of_nonneg_right hg hb
  have hh := mul_le_mul_of_nonneg_left hc (mul_nonneg (by linarith : 0 ≤ (n : ℝ) - 1) hb)
  have hnb := mul_nonneg hb hδ
  have hninv : (n : ℝ) * (1 / (n : ℝ)) = 1 := by field_simp
  nlinarith

theorem radial_derivative_bound {n : ℕ} (hn : 0 < n) (θ b : Fin n → ℝ) (c : Points n)
    {ε δ t : ℝ} (hb : ∀ i, 0 ≤ b i) (hδ : 0 ≤ δ) (hθ : ∀ i, |θ i| ≤ δ)
    (hgrad : gradientDeviation (path θ b c t) ≤ ε) :
    (∑ i, inner ℝ (realGradient (path θ b c t) i) (velocity θ b i)) ≤
      -(1 - 1 / (n : ℝ) - ε - δ) * mass b := by
  calc
    _ ≤ ∑ i, -(1 - 1 / (n : ℝ) - ε - δ) * ((n : ℝ) * b i) :=
      Finset.sum_le_sum (fun i _ => vertex_derivative_bound hn θ b _ hgrad hδ i (hb i) (hθ i))
    _ = _ := by simp only [mass, ← Finset.mul_sum]

/-- Integration of the actual derivative; the angle-loss constant is exactly one. -/
theorem finite_price {n : ℕ} (hn : 0 < n) (θ b : Fin n → ℝ) (c : Points n)
    {ε δ : ℝ} (hb : ∀ i, 0 ≤ b i) (hδ : 0 ≤ δ) (hθ : ∀ i, |θ i| ≤ δ)
    (hinj : ∀ t ∈ Icc (0 : ℝ) 1, Function.Injective (path θ b c t))
    (hgrad : ∀ t ∈ Icc (0 : ℝ) 1, gradientDeviation (path θ b c t) ≤ ε) :
    Real.log (discriminant (path θ b c 1)) ≤ Real.log (discriminant (path θ b c 0)) -
      (1 - 1 / (n : ℝ) - ε - δ) * mass b := by
  let F (t : ℝ) := Real.log (discriminant (path θ b c t))
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt F
      (∑ i, inner ℝ (realGradient (path θ b c t) i) (velocity θ b i)) t :=
    hasDerivAt_log_discriminant_path (path_hasDerivAt θ b c t) (hinj t ht)
  have hcont : ContinuousOn F (Icc (0 : ℝ) 1) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Icc (0 : ℝ) 1)) :=
    fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hbound : ∀ t ∈ interior (Icc (0 : ℝ) 1), deriv F t ≤
      -(1 - 1 / (n : ℝ) - ε - δ) * mass b := by
    intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    exact radial_derivative_bound hn θ b c hb hδ hθ (hgrad t (interior_subset ht))
  have h := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le hcont hdiff hbound
    0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [sub_zero, mul_one] at h
  change F 1 ≤ F 0 - _
  linarith

end
end StructuralNote.RadialObjectivePrice

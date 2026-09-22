import Erdos1045.ClosedInterpolation
import EventualExact.ExteriorSupportBounds
import EventualExact.PolarLogPotential
import EventualExact.AngularHarmonicBound
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! The actual Fekete gradient is a supporting normal, including polygon vertices. -/

namespace Erdos1045.EventualExact.FeketeStationarity

open Complex Set ExteriorClassical Configuration CircleMatrix MatrixDefect
open scoped BigOperators ComplexConjugate
noncomputable section

def nodeGradient {n : ℕ} (z : Points n) (i : Fin n) : ℂ :=
  conj (∑ j ∈ Finset.univ.erase i, (z i - z j)⁻¹)

theorem basis_eval_product {n : ℕ} (z : Points n) (i : Fin n) (w : ℂ) :
    (Lagrange.basis Finset.univ z i).eval w =
      ∏ j ∈ Finset.univ.erase i, (w - z j) / (z i - z j) := by
  simp [Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod, div_eq_mul_inv,
    mul_comm]

theorem basis_hasDerivAt {n : ℕ} {z : Points n} (hz : Function.Injective z)
    (i : Fin n) : HasDerivAt (fun w => (Lagrange.basis Finset.univ z i).eval w)
      (conj (nodeGradient z i)) (z i) := by
  have hd := HasDerivAt.fun_finsetProd (u := Finset.univ.erase i)
    (fun j _ => ((hasDerivAt_id (z i)).sub_const (z j)).div_const (z i - z j))
  have hone : ∀ j ∈ Finset.univ.erase i, (z i - z j) / (z i - z j) = 1 := by
    intro j hj
    exact div_self (sub_ne_zero.mpr (hz.ne (Finset.mem_erase.mp hj).1.symm))
  have hp : ∀ j ∈ Finset.univ.erase i,
      (∏ k ∈ (Finset.univ.erase i).erase j, (z i - z k) / (z i - z k)) = 1 := by
    intro j _
    exact Finset.prod_eq_one fun k hk => hone k (Finset.mem_erase.mp hk).2
  have he : (∑ j ∈ Finset.univ.erase i,
      (∏ k ∈ (Finset.univ.erase i).erase j, (z i - z k) / (z i - z k)) •
        (1 / (z i - z j))) = ∑ j ∈ Finset.univ.erase i, (z i - z j)⁻¹ := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hp j hj, one_smul, one_div]
  simpa only [id_eq, ← basis_eval_product, nodeGradient, conj_conj, he] using hd

theorem fekete_basis_norm_le {n : ℕ} {z : Points n} (hz : Function.Injective z)
    (hf : Fekete z) (i : Fin n) {w : ℂ} (hw : w ∈ hull z) :
    ‖(Lagrange.basis Finset.univ z i).eval w‖ ≤ 1 := by
  have hsub : Set.range (Function.update z i w) ⊆ hull z := by
    rintro _ ⟨j, rfl⟩
    by_cases h : j = i
    · subst j
      simpa using hw
    · simpa [Function.update_of_ne h, hull] using
        (subset_convexHull ℝ (Set.range z) (Set.mem_range_self j))
  have hbound := hf (Function.update z i w) hsub
  rw [← vandermonde_detSq, ← vandermonde_detSq, detSq,
    vandermonde_replace_det z hz i w, map_mul] at hbound
  simp only [detSq] at hbound
  have hpositive : 0 < Complex.normSq (vandermonde z).det := by
    change 0 < detSq (vandermonde z)
    rw [vandermonde_detSq]
    exact discriminant_pos z hz
  have hsq : Complex.normSq ((Lagrange.basis Finset.univ z i).eval w) ≤ 1 := by
    nlinarith
  rw [Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg ((Lagrange.basis Finset.univ z i).eval w)]

theorem fekete_gradient_support {n : ℕ} {z : Points n} (hz : Function.Injective z)
    (hf : Fekete z) (i : Fin n) {w : ℂ} (hw : w ∈ hull z) :
    (conj (nodeGradient z i) * (w - z i)).re ≤ 0 := by
  have hmax : IsMaxOn (fun w => ‖(Lagrange.basis Finset.univ z i).eval w‖ ^ 2)
      (hull z) (z i) := by
    intro v hv
    change ‖(Lagrange.basis Finset.univ z i).eval v‖ ^ 2 ≤
      ‖(Lagrange.basis Finset.univ z i).eval (z i)‖ ^ 2
    rw [Lagrange.eval_basis_self hz.injOn (Finset.mem_univ i)]
    have h := fekete_basis_norm_le hz hf i hv
    simp only [norm_one, one_pow]
    nlinarith [norm_nonneg ((Lagrange.basis Finset.univ z i).eval v)]
  have hd := ((basis_hasDerivAt hz i).hasFDerivAt.restrictScalars ℝ).norm_sq
  have htan : w - z i ∈ posTangentConeAt (hull z) (z i) :=
    sub_mem_posTangentConeAt_of_segment_subset ((convex_convexHull ℝ (Set.range z)).segment_subset
      (subset_convexHull ℝ (Set.range z) (Set.mem_range_self i)) hw)
  have h := hmax.localize.hasFDerivWithinAt_nonpos hd.hasFDerivWithinAt htan
  have h' : 2 * (conj (nodeGradient z i) * (w - z i)).re ≤ 0 := by
    simpa [Lagrange.eval_basis_self hz.injOn (Finset.mem_univ i), Complex.inner,
      mul_comm, mul_add] using h
  linarith

theorem normalized_gradient_support {n : ℕ} {z : Points n} (hz : Function.Injective z)
    (hf : Fekete z) (i : Fin n) (c : ℂ) (hg : nodeGradient z i ≠ 0) :
    let ν := nodeGradient z i / (‖nodeGradient z i‖ : ℂ)
    ‖ν‖ = 1 ∧ ∀ w ∈ hull z, (conj ν * (w - c)).re ≤ (conj ν * (z i - c)).re := by
  dsimp only
  have hn : 0 < ‖nodeGradient z i‖ := norm_pos_iff.mpr hg
  constructor
  · simp [hn.ne']
  · intro w hw
    have h := fekete_gradient_support hz hf i hw
    have he : (conj (nodeGradient z i / (‖nodeGradient z i‖ : ℂ)) * (w - c)).re -
        (conj (nodeGradient z i / (‖nodeGradient z i‖ : ℂ)) * (z i - c)).re =
        (conj (nodeGradient z i) * (w - z i)).re / ‖nodeGradient z i‖ := by
      rw [← sub_re, ← mul_sub]
      simp only [sub_sub_sub_cancel_right, map_div₀, conj_ofReal]
      rw [div_mul_eq_mul_div, div_ofReal_re]
    have := div_nonpos_of_nonpos_of_nonneg h hn.le
    linarith

theorem hasDerivAt_log_distance_sum {n : ℕ} {z : Points n}
    (hz : Function.Injective z) (i : Fin n) {p : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (hp : HasDerivAt p v t) (hpt : p t = z i) :
    HasDerivAt (fun u => ∑ j ∈ Finset.univ.erase i, Real.log (‖p u - z j‖ ^ 2))
      (2 * (conj (nodeGradient z i) * v).re) t := by
  have hdj (j : Fin n) (hj : j ∈ Finset.univ.erase i) :
      HasDerivAt (fun u => Real.log (‖p u - z j‖ ^ 2))
        (2 * (v / (z i - z j)).re) t := by
    have hn : ‖p t - z j‖ ^ 2 ≠ 0 := by
      rw [hpt]
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr
        (sub_ne_zero.mpr (hz.ne (Finset.mem_erase.mp hj).1.symm)))
    have hd := ((hp.sub_const (z j)).norm_sq).log hn
    convert hd using 1
    rw [hpt, Complex.inner, Complex.div_re, Complex.normSq_eq_norm_sq]
    simp only [mul_re, conj_re, conj_im]
    ring
  have hd := HasDerivAt.fun_sum hdj
  have he : (∑ j ∈ Finset.univ.erase i, 2 * (v / (z i - z j)).re) =
      2 * (conj (nodeGradient z i) * v).re := by
    simp only [nodeGradient, conj_conj, Finset.sum_mul, Complex.re_sum, div_eq_mul_inv,
      mul_comm v, Finset.mul_sum]
  exact he ▸ hd

theorem hasDerivAt_polar_curve {h : ℝ → ℝ} {t s : ℝ} (hh : HasDerivAt h s t) :
    HasDerivAt (fun u => polarPoint (h u) u)
      (((s : ℂ) + I) * polarPoint (h t) t) t := by
  have hr := hh.exp.ofReal_comp
  have ha := ((hasDerivAt_id t).ofReal_comp.mul_const I).cexp
  convert hr.fun_mul ha using 1
  · rfl
  · rfl
  · simp only [polarPoint, ofReal_mul, ofReal_one, one_mul, id_eq]
    ring

theorem polarForceExpression_eq_gradient {n : ℕ} {z : Points n}
    (hz : Function.Injective z) (height θ : Fin n → ℝ) (c : ℂ)
    (hpolar : ∀ j, z j = c + polarPoint (height j) (θ j)) (i : Fin n) (s : ℝ)
    (hx : ∀ j, j ≠ i → 1 - Real.cos (θ i - θ j) ≠ 0)
    (hD : ∀ j, j ≠ i → polarDenominator (height i - height j) (θ i - θ j) ≠ 0) :
    polarForceExpression height θ i s =
      2 * (conj (nodeGradient z i) * (((s : ℂ) + I) * (z i - c))).re := by
  let h : ℝ → ℝ := fun u => height i + s * (u - θ i)
  have hh : HasDerivAt h s (θ i) := by
    simpa [h] using (((hasDerivAt_id (θ i)).sub_const (θ i)).const_mul s).const_add (height i)
  have hi : h (θ i) = height i := by simp [h]
  have hp := (hasDerivAt_polar_curve hh).const_add c
  have hpt : c + polarPoint (h (θ i)) (θ i) = z i := by rw [hi, hpolar i]
  have hd := hasDerivAt_log_distance_sum hz i hp hpt
  have he := hasDerivAt_polar_log_sum i hh hi hx hD
  have hf : (fun u => ∑ j ∈ Finset.univ.erase i,
      Real.log (‖c + polarPoint (h u) u - z j‖ ^ 2)) =
      (fun u => ∑ j ∈ Finset.univ.erase i,
      Real.log (‖polarPoint (h u) u - polarPoint (height j) (θ j)‖ ^ 2)) := by
    funext u
    apply Finset.sum_congr rfl
    intro j _
    rw [hpolar j, add_sub_add_left_eq_sub]
  rw [hf] at hd
  have heq := he.unique hd
  simpa only [hi, hpolar i, add_sub_cancel_left] using heq

theorem normal_polar_tangent_zero {ν r : ℂ} (hr : (conj ν * r).re ≠ 0) :
    (conj ν * (((PolarSlopeEnergy.polarSlope r (I * ν) : ℝ) : ℂ) + I) * r).re = 0 := by
  have hs : PolarSlopeEnergy.polarSlope r (I * ν) =
      (conj ν * r).im / (conj ν * r).re := by
    unfold PolarSlopeEnergy.polarSlope
    have h := PolarSlopeEnergy.radialPairing_tangent r ν 1
    simpa using congrArg (fun q : ℂ => q.re / q.im) h
  rw [hs, show conj ν * (((((conj ν * r).im / (conj ν * r).re) : ℝ) : ℂ) + I) * r =
    (((((conj ν * r).im / (conj ν * r).re) : ℝ) : ℂ) + I) * (conj ν * r) by ring]
  rw [mul_re]
  simp only [add_re, add_im, ofReal_re, ofReal_im, I_re, I_im, add_zero,
    zero_add, one_mul]
  rw [div_mul_cancel₀ _ hr, sub_self]

theorem gradient_polar_tangent_zero {g r : ℂ} (hg : g ≠ 0)
    (hr : (conj (g / (‖g‖ : ℂ)) * r).re ≠ 0) :
    (conj g * ((((PolarSlopeEnergy.polarSlope r (I * (g / (‖g‖ : ℂ))) : ℝ) : ℂ) + I) * r)).re = 0 := by
  let ν := g / (‖g‖ : ℂ)
  have hn : (‖g‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg)
  have he : g = (‖g‖ : ℂ) * ν := by dsimp [ν]; field_simp
  have ht := normal_polar_tangent_zero hr
  change (conj ν * (((PolarSlopeEnergy.polarSlope r (I * ν) : ℝ) : ℂ) + I) * r).re = 0 at ht
  change (conj g * ((((PolarSlopeEnergy.polarSlope r (I * ν) : ℝ) : ℂ) + I) * r)).re = 0
  rw [he, map_mul, conj_ofReal]
  rw [show (‖g‖ : ℂ) * conj ν *
      ((((PolarSlopeEnergy.polarSlope r (I * ν) : ℝ) : ℂ) + I) * r) =
      (‖g‖ : ℂ) * (conj ν * (((PolarSlopeEnergy.polarSlope r (I * ν) : ℝ) : ℂ) + I) * r) by ring]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, ht, mul_zero]

theorem exists_stationary_small_slope {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hc : 1 / 2 ≤ d.capacity)
    (he : ExteriorSupport.errorRadius d ≤ 1 / 4)
    (hz : Function.Injective z) (hf : Fekete z) (height θ : Fin n → ℝ)
    (hpolar : ∀ j, z j = ExteriorSupport.center d + polarPoint (height j) (θ j))
    (i : Fin n)
    (hx : ∀ j, j ≠ i → 1 - Real.cos (θ i - θ j) ≠ 0)
    (hD : ∀ j, j ≠ i → polarDenominator (height i - height j) (θ i - θ j) ≠ 0) :
    ∃ s : ℝ, |s| ≤ 8 * Real.sqrt (ExteriorSupport.errorRadius d) ∧
      polarForceExpression height θ i s = 0 := by
  by_cases hg : nodeGradient z i = 0
  · refine ⟨0, by simp, ?_⟩
    rw [polarForceExpression_eq_gradient hz height θ _ hpolar i 0 hx hD, hg]
    simp
  let ν := nodeGradient z i / (‖nodeGradient z i‖ : ℂ)
  obtain ⟨hν, hs⟩ := normalized_gradient_support hz hf i (ExteriorSupport.center d) hg
  have hmem : z i ∈ hull z := subset_convexHull ℝ (Set.range z) (Set.mem_range_self i)
  have hr : 0 < (conj ν * (z i - ExteriorSupport.center d)).re := by
    have h := ExteriorSupport.support_lower d HF hν hs
    dsimp only [ν]
    linarith
  refine ⟨PolarSlopeEnergy.polarSlope (z i - ExteriorSupport.center d) (I * ν), ?_, ?_⟩
  · simpa only [ofReal_one, mul_one] using
      ExteriorSupport.tangent_slope_le_error d HF hc he hν hmem hs 1
  · rw [polarForceExpression_eq_gradient hz height θ _ hpolar i _ hx hD,
      gradient_polar_tangent_zero hg hr.ne', mul_zero]

/-- Actual increasing cyclic angles discharge all pairwise denominator conditions. -/
theorem exists_stationary_slopes {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hc : 1 / 2 ≤ d.capacity)
    (he : ExteriorSupport.errorRadius d ≤ 1 / 4)
    (hz : Function.Injective z) (hf : Fekete z) (height : Fin n → ℝ)
    (a : CyclicAngles.Angles n)
    (hpolar : ∀ j, z j = ExteriorSupport.center d + polarPoint (height j) (a.angle j)) :
    ∃ s : Fin n → ℝ,
      (∀ i, |s i| ≤ 8 * Real.sqrt (ExteriorSupport.errorRadius d)) ∧
      ∀ i, polarForceExpression height (fun j => a.angle j) i (s i) = 0 := by
  have hex (i : Fin n) : ∃ s : ℝ,
      |s| ≤ 8 * Real.sqrt (ExteriorSupport.errorRadius d) ∧
      polarForceExpression height (fun j => a.angle j) i s = 0 := by
    have hp (j : Fin n) (hj : j ≠ i) : 0 < 1 - Real.cos (a.angle i - a.angle j) := by
      have h := one_sub_cos_lower_quadratic (AngularHarmonicBound.shortAngle_abs_le_pi a i j)
      rw [AngularHarmonicBound.shortAngle_cos] at h
      have hsq := sq_pos_of_ne_zero (AngularHarmonicBound.shortAngle_ne_zero a hj.symm)
      have hpos : 0 < 2 * AngularHarmonicBound.shortAngle a i j ^ 2 / Real.pi ^ 2 :=
        div_pos (mul_pos (by norm_num) hsq) (sq_pos_of_pos Real.pi_pos)
      exact hpos.trans_le h
    exact exists_stationary_small_slope d HF hc he hz hf height (fun j => a.angle j)
      hpolar i (fun j hj => (hp j hj).ne')
      (fun j hj => ((hp j hj).trans_le (polarDenominator_ge _ _)).ne')
  choose s hs hz using hex
  exact ⟨s, hs, hz⟩

theorem nodeGradient_eq_univ {n : ℕ} (z : Points n) (i : Fin n) :
    nodeGradient z i = conj (∑ j, (z i - z j)⁻¹) := by
  unfold nodeGradient
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp

theorem nodeGradient_permutation {n : ℕ} (z : Points n) (σ : Equiv.Perm (Fin n))
    (i : Fin n) : nodeGradient (fun j => z (σ j)) i = nodeGradient z (σ i) := by
  rw [nodeGradient_eq_univ, nodeGradient_eq_univ]
  congr 1
  exact Equiv.sum_comp σ (fun j => (z (σ i) - z j)⁻¹)

/-- The exterior map keeps its original ordering while physical angles may reorder the nodes. -/
theorem exists_stationary_slopes_permuted {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hc : 1 / 2 ≤ d.capacity)
    (he : ExteriorSupport.errorRadius d ≤ 1 / 4)
    (hz : Function.Injective z) (hf : Fekete z) (height : Fin n → ℝ)
    (a : CyclicAngles.Angles n) (σ : Equiv.Perm (Fin n))
    (hpolar : ∀ j, z (σ j) = ExteriorSupport.center d + polarPoint (height j) (a.angle j)) :
    ∃ s : Fin n → ℝ,
      (∀ i, |s i| ≤ 8 * Real.sqrt (ExteriorSupport.errorRadius d)) ∧
      ∀ i, polarForceExpression height (fun j => a.angle j) i (s i) = 0 := by
  have hz' : Function.Injective (fun j => z (σ j)) := hz.comp σ.injective
  have hex (i : Fin n) : ∃ s : ℝ,
      |s| ≤ 8 * Real.sqrt (ExteriorSupport.errorRadius d) ∧
      polarForceExpression height (fun j => a.angle j) i s = 0 := by
    have hp (j : Fin n) (hj : j ≠ i) : 0 < 1 - Real.cos (a.angle i - a.angle j) := by
      have h := one_sub_cos_lower_quadratic (AngularHarmonicBound.shortAngle_abs_le_pi a i j)
      rw [AngularHarmonicBound.shortAngle_cos] at h
      have hsq := sq_pos_of_ne_zero (AngularHarmonicBound.shortAngle_ne_zero a hj.symm)
      exact (div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hsq)
        (sq_pos_of_pos Real.pi_pos)).trans_le h
    have hforce (s : ℝ) := polarForceExpression_eq_gradient hz' height
      (fun j => a.angle j) (ExteriorSupport.center d) hpolar i s
      (fun j hj => (hp j hj).ne')
      (fun j hj => ((hp j hj).trans_le (polarDenominator_ge _ _)).ne')
    by_cases hg : nodeGradient (fun j => z (σ j)) i = 0
    · refine ⟨0, by simp, ?_⟩
      rw [hforce, hg]
      simp
    let ν := nodeGradient (fun j => z (σ j)) i /
      (‖nodeGradient (fun j => z (σ j)) i‖ : ℂ)
    have hg' : nodeGradient z (σ i) ≠ 0 := by
      rwa [← nodeGradient_permutation z σ i]
    obtain ⟨hν, hs⟩ := normalized_gradient_support hz hf (σ i) (ExteriorSupport.center d) hg'
    rw [← nodeGradient_permutation z σ i] at hν hs
    have hmem : z (σ i) ∈ hull z :=
      subset_convexHull ℝ (Set.range z) (Set.mem_range_self (σ i))
    have hr : 0 < (conj ν * (z (σ i) - ExteriorSupport.center d)).re := by
      have h := ExteriorSupport.support_lower d HF hν hs
      dsimp only [ν]
      linarith
    refine ⟨PolarSlopeEnergy.polarSlope (z (σ i) - ExteriorSupport.center d) (I * ν), ?_, ?_⟩
    · simpa only [ofReal_one, mul_one] using
        ExteriorSupport.tangent_slope_le_error d HF hc he hν hmem hs 1
    · rw [hforce, gradient_polar_tangent_zero hg hr.ne', mul_zero]
  choose s hs hzero using hex
  exact ⟨s, hs, hzero⟩

end
end Erdos1045.EventualExact.FeketeStationarity

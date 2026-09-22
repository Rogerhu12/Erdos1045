import EventualExact.FeketeStationarity
import EventualExact.SchurEnergyBounds
import Erdos1045.LocalConfiguration

/-! Actual second derivatives and negative kernels along angular rotation paths. -/

namespace Erdos1045.EventualExact.AngularObjectiveCurvature

open Complex Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

def angularOrbit (θ : ℝ) (Y : ℂ) (s : ℝ) : ℂ :=
  Complex.exp (((s * θ : ℝ) : ℂ) * I) * Y

theorem angularOrbit_hasDerivAt (θ : ℝ) (Y : ℂ) (s : ℝ) :
    HasDerivAt (angularOrbit θ Y) (I * (θ : ℂ) * angularOrbit θ Y s) s := by
  have h := ((((hasDerivAt_id s).mul_const θ).ofReal_comp.mul_const I).cexp).mul_const Y
  convert h using 1
  · rfl
  · rfl
  · unfold angularOrbit
    simp only [id_eq, one_mul]
    ring

theorem log_norm_sq_hasDerivAt {f : ℝ → ℂ} {v : ℂ} {s : ℝ}
    (hf : HasDerivAt f v s) (hne : f s ≠ 0) :
    HasDerivAt (fun t => Real.log (‖f t‖ ^ 2)) (2 * (v / f s).re) s := by
  have h := hf.norm_sq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
  convert h using 1
  rw [Complex.inner, Complex.div_re, normSq_eq_norm_sq]
  simp only [mul_re, conj_re, conj_im]
  ring

def pairLog (θ φ : ℝ) (X Y : ℂ) (s : ℝ) : ℝ :=
  Real.log (‖angularOrbit θ X s - angularOrbit φ Y s‖ ^ 2)

def pairLogFirst (θ φ : ℝ) (X Y : ℂ) (s : ℝ) : ℝ :=
  2 * (I * ((θ : ℂ) * angularOrbit θ X s - (φ : ℂ) * angularOrbit φ Y s) /
    (angularOrbit θ X s - angularOrbit φ Y s)).re

theorem pairLog_hasDerivAt (θ φ : ℝ) (X Y : ℂ) (s : ℝ)
    (hne : angularOrbit θ X s ≠ angularOrbit φ Y s) :
    HasDerivAt (pairLog θ φ X Y) (pairLogFirst θ φ X Y s) s := by
  have h := log_norm_sq_hasDerivAt
    ((angularOrbit_hasDerivAt θ X s).sub (angularOrbit_hasDerivAt φ Y s)) (sub_ne_zero.mpr hne)
  convert h using 1
  · rfl
  · unfold pairLogFirst
    simp only [Pi.sub_apply]
    congr 2
    ring

theorem pair_quotient_derivative_algebra (x y : ℂ) (θ φ : ℝ) :
    ((I * ((θ : ℂ) * (I * θ * x) - (φ : ℂ) * (I * φ * y))) * (x - y) -
      (I * ((θ : ℂ) * x - (φ : ℂ) * y)) * (I * θ * x - I * φ * y)) / (x - y) ^ 2 =
      x * y / (x - y) ^ 2 * (((θ - φ) ^ 2 : ℝ) : ℂ) := by
  push_cast
  have he : ((I * ((θ : ℂ) * (I * θ * x) - (φ : ℂ) * (I * φ * y))) * (x - y) -
      (I * ((θ : ℂ) * x - (φ : ℂ) * y)) * (I * θ * x - I * φ * y)) =
      x * y * ((θ : ℂ) - φ) ^ 2 := by
    ring_nf
    simp only [I_sq]
    ring
  rw [he]
  ring

/-- This is the second derivative of one squared-distance logarithm; its coefficient is two. -/
theorem pairLogFirst_hasDerivAt (θ φ : ℝ) (X Y : ℂ) (s : ℝ)
    (hne : angularOrbit θ X s ≠ angularOrbit φ Y s) :
    HasDerivAt (pairLogFirst θ φ X Y)
      (2 * (angularOrbit θ X s * angularOrbit φ Y s /
        (angularOrbit θ X s - angularOrbit φ Y s) ^ 2).re * (θ - φ) ^ 2) s := by
  have hx := angularOrbit_hasDerivAt θ X s
  have hy := angularOrbit_hasDerivAt φ Y s
  have hc := (((hx.const_mul (θ : ℂ)).sub (hy.const_mul (φ : ℂ))).const_mul I).div
    (hx.sub hy) (sub_ne_zero.mpr hne)
  have hd := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hc).const_mul 2
  convert hd using 1 <;> try rfl
  change 2 * Complex.re (_ / _) * (θ - φ) ^ 2 = 2 * Complex.re ((_ - _) / _)
  simp only [Pi.sub_apply]
  rw [pair_quotient_derivative_algebra]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  ring

theorem pairLog_second_deriv (θ φ : ℝ) (X Y : ℂ) (s : ℝ)
    (hne : angularOrbit θ X s ≠ angularOrbit φ Y s) :
    HasDerivAt (deriv (pairLog θ φ X Y))
      (2 * (angularOrbit θ X s * angularOrbit φ Y s /
        (angularOrbit θ X s - angularOrbit φ Y s) ^ 2).re * (θ - φ) ^ 2) s := by
  have hn := ((angularOrbit_hasDerivAt θ X s).continuousAt.sub
    (angularOrbit_hasDerivAt φ Y s).continuousAt).eventually_ne (sub_ne_zero.mpr hne)
  apply (pairLogFirst_hasDerivAt θ φ X Y s hne).congr_of_eventuallyEq
  filter_upwards [hn] with t ht
  exact (pairLog_hasDerivAt θ φ X Y t (sub_ne_zero.mp ht)).deriv

theorem unit_pair_kernel {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) :
    a * b / (a - b) ^ 2 = ((-1 / ‖a - b‖ ^ 2 : ℝ) : ℂ) := by
  have ha' : a * conj a = 1 := by rw [mul_conj, normSq_eq_norm_sq, ha]; norm_num
  have hb' : b * conj b = 1 := by rw [mul_conj, normSq_eq_norm_sq, hb]; norm_num
  have h : a * b * conj (a - b) = -(a - b) := by
    rw [map_sub]
    calc
      a * b * (conj a - conj b) = b * (a * conj a) - a * (b * conj b) := by ring
      _ = -(a - b) := by rw [ha', hb']; ring
  have he : a * b * (‖a - b‖ ^ 2 : ℝ) = -(a - b) ^ 2 := by
    rw [← normSq_eq_norm_sq, ← mul_conj]
    calc
      a * b * ((a - b) * conj (a - b)) = (a - b) * (a * b * conj (a - b)) := by ring
      _ = -(a - b) ^ 2 := by rw [h]; ring
  have hn : (‖a - b‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hab))
  push_cast
  field_simp [sub_ne_zero.mpr hab, hn]
  simpa only [ofReal_pow] using he

private theorem stable_ratio_re {B D : ℂ} (hB : ‖B - 1‖ ≤ 1 / 16)
    (hD : ‖D - 1‖ ≤ 1 / 64) : 1 / 2 ≤ (B / D ^ 2).re := by
  have hDu : ‖D‖ ≤ 2 := by
    have h := norm_add_le (D - 1) (1 : ℂ)
    simp only [sub_add_cancel, norm_one] at h
    linarith
  have hDl : 1 / 2 ≤ ‖D‖ := by
    have h := norm_sub_le D (D - 1)
    have he : D - (D - 1) = 1 := by ring
    rw [he, norm_one] at h
    linarith
  have hD0 : D ≠ 0 := norm_pos_iff.mp (by linarith)
  have hD2 : ‖D ^ 2 - 1‖ ≤ 1 / 16 := by
    have hplus : ‖D + 1‖ ≤ 3 := (norm_add_le D 1).trans (by rw [norm_one]; linarith)
    calc
      ‖D ^ 2 - 1‖ = ‖(D - 1) * (D + 1)‖ := by congr 1; ring
      _ = ‖D - 1‖ * ‖D + 1‖ := norm_mul _ _
      _ ≤ (1 / 64) * 3 := mul_le_mul hD hplus (norm_nonneg _) (by norm_num)
      _ ≤ 1 / 16 := by norm_num
  have hnum : ‖B - D ^ 2‖ ≤ 1 / 8 := by
    have h := norm_sub_le (B - 1) (D ^ 2 - 1)
    rw [sub_sub_sub_cancel_right] at h
    linarith
  have herr : ‖B / D ^ 2 - 1‖ ≤ 1 / 2 := by
    rw [div_sub_one (pow_ne_zero 2 hD0), norm_div, norm_pow]
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith : 0 < ‖D‖))).2
    nlinarith
  have hr := (abs_re_le_norm (B / D ^ 2 - 1)).trans herr
  simp only [sub_re, one_re] at hr
  linarith [(abs_le.mp hr).1]

/-- Uniform negativity under absolute vertex and relative chord perturbations. -/
theorem pair_kernel_negative {a b x y : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : a ≠ b) (hx : ‖x - a‖ ≤ 1 / 64) (hy : ‖y - b‖ ≤ 1 / 64)
    (hchord : ‖(x - y) / (a - b) - 1‖ ≤ 1 / 64) :
    x ≠ y ∧ (x * y / (x - y) ^ 2).re ≤ -1 / (2 * ‖a - b‖ ^ 2) := by
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have hb0 : b ≠ 0 := norm_ne_zero_iff.mp (by rw [hb]; norm_num)
  have hyu : ‖y‖ ≤ 65 / 64 := by
    have h := norm_add_le (y - b) b
    rw [sub_add_cancel, hb] at h
    linarith
  have hproduct : ‖x * y - a * b‖ ≤ 1 / 16 := by
    calc
      ‖x * y - a * b‖ = ‖(x - a) * y + a * (y - b)‖ := by congr 1; ring
      _ ≤ ‖(x - a) * y‖ + ‖a * (y - b)‖ := norm_add_le _ _
      _ = ‖x - a‖ * ‖y‖ + ‖y - b‖ := by rw [norm_mul, norm_mul, ha, one_mul]
      _ ≤ (1 / 64) * (65 / 64) + 1 / 64 := by gcongr
      _ ≤ 1 / 16 := by norm_num
  have hB : ‖x * y / (a * b) - 1‖ ≤ 1 / 16 := by
    rwa [div_sub_one (mul_ne_zero ha0 hb0), norm_div, norm_mul, ha, hb, one_mul,
      div_one]
  have hxy : x ≠ y := by
    intro h
    rw [h, sub_self, zero_div, zero_sub, norm_neg, norm_one] at hchord
    norm_num at hchord
  have hr := stable_ratio_re hB hchord
  have he : x * y / (x - y) ^ 2 = a * b / (a - b) ^ 2 *
      ((x * y / (a * b)) / ((x - y) / (a - b)) ^ 2) := by
    field_simp
  rw [unit_pair_kernel ha hb hab] at he
  have her := congrArg Complex.re he
  rw [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at her
  refine ⟨hxy, ?_⟩
  have hn : 0 < ‖a - b‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hab))
  have hh := mul_le_mul_of_nonpos_left hr
    (div_nonpos_of_nonpos_of_nonneg (by norm_num : (-1 : ℝ) ≤ 0) hn.le)
  rw [← her] at hh
  convert hh using 1 <;> try rfl
  field_simp

def angularLogDiscriminant {n : ℕ} (θ : Fin n → ℝ) (Y : Fin n → ℂ) (s : ℝ) : ℝ :=
  Real.log (Configuration.discriminant (fun i => angularOrbit (θ i) (Y i) s))

def angularFirst {n : ℕ} (θ : Fin n → ℝ) (Y : Fin n → ℂ) (s : ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, pairLogFirst (θ i) (θ j) (Y i) (Y j) s / 2

def angularCurvature {n : ℕ} (θ : Fin n → ℝ) (Y : Fin n → ℂ) (s : ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i,
    (angularOrbit (θ i) (Y i) s * angularOrbit (θ j) (Y j) s /
      (angularOrbit (θ i) (Y i) s - angularOrbit (θ j) (Y j) s) ^ 2).re * (θ i - θ j) ^ 2

theorem angularOrbit_eventually_injective {n : ℕ} (θ : Fin n → ℝ) (Y : Fin n → ℂ) (s : ℝ)
    (hinj : Function.Injective (fun i => angularOrbit (θ i) (Y i) s)) :
    ∀ᶠ t in 𝓝 s, Function.Injective (fun i => angularOrbit (θ i) (Y i) t) := by
  have h (i j : Fin n) : ∀ᶠ t in 𝓝 s,
      i ≠ j → angularOrbit (θ i) (Y i) t ≠ angularOrbit (θ j) (Y j) t := by
    by_cases hij : i = j
    · exact Eventually.of_forall (by simp [hij])
    · have he := ((angularOrbit_hasDerivAt (θ i) (Y i) s).continuousAt.sub
        (angularOrbit_hasDerivAt (θ j) (Y j) s).continuousAt).eventually_ne
        (sub_ne_zero.mpr (hinj.ne hij))
      filter_upwards [he] with t ht
      exact fun _ => sub_ne_zero.mp ht
  have he := (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => h i j)
  filter_upwards [he] with t ht
  intro i j hij
  by_contra hne
  exact ht i j hne hij

theorem angularLogDiscriminant_eq_pair_sum {n : ℕ} (θ : Fin n → ℝ) (Y : Fin n → ℂ) (s : ℝ)
    (hinj : Function.Injective (fun i => angularOrbit (θ i) (Y i) s)) :
    angularLogDiscriminant θ Y s =
      ∑ i, ∑ j ∈ Finset.univ.erase i, pairLog (θ i) (θ j) (Y i) (Y j) s / 2 := by
  rw [angularLogDiscriminant, LocalConfiguration.logDiscriminant_eq_sum _ hinj]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_erase _ (by simp [pairLog])]
  apply Finset.sum_congr rfl
  intro j _
  simp only [pairLog, Real.log_pow]
  ring

theorem angularLogDiscriminant_hasDerivAt {n : ℕ} (θ : Fin n → ℝ) (Y : Fin n → ℂ) (s : ℝ)
    (hinj : Function.Injective (fun i => angularOrbit (θ i) (Y i) s)) :
    HasDerivAt (angularLogDiscriminant θ Y) (angularFirst θ Y s) s := by
  have hd := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n))) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ.erase i) fun j hj =>
      (pairLog_hasDerivAt (θ i) (θ j) (Y i) (Y j) s
        (hinj.ne (Finset.ne_of_mem_erase hj).symm)).div_const 2
  apply hd.congr_of_eventuallyEq
  filter_upwards [angularOrbit_eventually_injective θ Y s hinj] with t ht
  exact angularLogDiscriminant_eq_pair_sum θ Y t ht

theorem angularFirst_hasDerivAt {n : ℕ} (θ : Fin n → ℝ) (Y : Fin n → ℂ) (s : ℝ)
    (hinj : Function.Injective (fun i => angularOrbit (θ i) (Y i) s)) :
    HasDerivAt (angularFirst θ Y) (angularCurvature θ Y s) s := by
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j hj
  have hd := (pairLogFirst_hasDerivAt (θ i) (θ j) (Y i) (Y j) s
    (hinj.ne (Finset.ne_of_mem_erase hj).symm)).div_const 2
  convert hd using 1 <;> try rfl
  ring

/-- The actual logarithm of the discriminant has the stated finite angular Hessian. -/
theorem angularLogDiscriminant_second_deriv {n : ℕ} (θ : Fin n → ℝ) (Y : Fin n → ℂ) (s : ℝ)
    (hinj : Function.Injective (fun i => angularOrbit (θ i) (Y i) s)) :
    HasDerivAt (deriv (angularLogDiscriminant θ Y)) (angularCurvature θ Y s) s := by
  apply (angularFirst_hasDerivAt θ Y s hinj).congr_of_eventuallyEq
  filter_upwards [angularOrbit_eventually_injective θ Y s hinj] with t ht
  exact (angularLogDiscriminant_hasDerivAt θ Y t ht).deriv

/-- The ordinary chord-difference energy, with every unordered pair counted once. -/
def angularChordEnergy {n : ℕ} (a : Fin n → ℂ) (θ : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j ∈ Finset.univ.erase i, (θ i - θ j) ^ 2 / ‖a i - a j‖ ^ 2) / 2

theorem angularCurvature_negative {n : ℕ} (θ : Fin n → ℝ) (Y a : Fin n → ℂ) (s : ℝ)
    (ha : ∀ i, ‖a i‖ = 1) (hainj : Function.Injective a)
    (hvertex : ∀ i, ‖angularOrbit (θ i) (Y i) s - a i‖ ≤ 1 / 64)
    (hchord : ∀ i j, i ≠ j →
      ‖(angularOrbit (θ i) (Y i) s - angularOrbit (θ j) (Y j) s) / (a i - a j) - 1‖ ≤ 1 / 64) :
    angularCurvature θ Y s ≤ -angularChordEnergy a θ := by
  unfold angularCurvature angularChordEnergy
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have hij := (Finset.ne_of_mem_erase hj).symm
  have hk := (pair_kernel_negative (ha i) (ha j) (hainj.ne hij)
    (hvertex i) (hvertex j) (hchord i j hij)).2
  have he := mul_le_mul_of_nonneg_right hk (sq_nonneg (θ i - θ j))
  convert he using 1
  field_simp

theorem pairEnergy_eq_chord_sum {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    SchurSpectrum.pairEnergy hn c =
      (∑ i : Fin n, ∑ j : Fin n,
        normSq (c i - c j) / normSq (LocalPhase.regularRoot n ^ (i : ℕ) -
          LocalPhase.regularRoot n ^ (j : ℕ))) / 2 := by
  let f : ℕ → ℕ → ℝ := fun i j => normSq (SchurSpectrum.periodize hn c i -
    SchurSpectrum.periodize hn c j) / normSq (LocalPhase.regularRoot n ^ i -
      LocalPhase.regularRoot n ^ j)
  have hp (i j : ℕ) : f (i + n) j = f i j := by
    simp only [f, SchurSpectrum.periodize_periodic hn c i, pow_add,
      LocalDFT.regularRoot_pow hn, mul_one]
  have hshift (j : ℕ) : (∑ h ∈ Finset.range n, f (j + h) j) =
      ∑ i ∈ Finset.range n, f i j := by
    have h := CyclicAngles.sum_shift_of_drift (fun i => f i j) 0
      (fun i => by rw [hp]; ring) j
    simpa only [mul_zero, add_zero, Nat.add_comm] using h
  unfold SchurSpectrum.pairEnergy LocalDFT.energyA
  simp only [LocalDFT.pairRatio, normSq_div]
  change (∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n, f (j + h) j) / 2 = _
  rw [Finset.sum_erase _ (by simp [f]), Finset.sum_comm]
  simp_rw [hshift]
  rw [Finset.sum_comm]
  congr 1
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [f, SchurSpectrum.periodize, Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt j.isLt]

theorem angularChordEnergy_eq_pairEnergy {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) :
    angularChordEnergy (fun i => LocalPhase.regularRoot n ^ (i : ℕ)) θ =
      SchurSpectrum.pairEnergy hn (fun i => (θ i : ℂ)) := by
  rw [pairEnergy_eq_chord_sum]
  unfold angularChordEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_erase _ (by simp)]
  apply Finset.sum_congr rfl
  intro j _
  rw [← ofReal_sub, normSq_ofReal, normSq_eq_norm_sq]
  ring

/-- Concrete finite negative curvature with the project's existing `A` energy. -/
theorem angularLogDiscriminant_second_deriv_le {n : ℕ} (hn : 0 < n)
    (θ : Fin n → ℝ) (Y : Fin n → ℂ) (s : ℝ)
    (hvertex : ∀ i, ‖angularOrbit (θ i) (Y i) s - LocalPhase.regularRoot n ^ (i : ℕ)‖ ≤ 1 / 64)
    (hchord : ∀ i j, i ≠ j →
      ‖(angularOrbit (θ i) (Y i) s - angularOrbit (θ j) (Y j) s) /
        (LocalPhase.regularRoot n ^ (i : ℕ) - LocalPhase.regularRoot n ^ (j : ℕ)) - 1‖ ≤ 1 / 64) :
    deriv (deriv (angularLogDiscriminant θ Y)) s ≤
      -SchurSpectrum.pairEnergy hn (fun i => (θ i : ℂ)) := by
  have ha (i : Fin n) : ‖LocalPhase.regularRoot n ^ (i : ℕ)‖ = 1 := by
    rw [norm_pow, ClosedFourier.root_norm, one_pow]
  have hainj : Function.Injective (fun i : Fin n => LocalPhase.regularRoot n ^ (i : ℕ)) := by
    intro i j hij
    have h := ClosedFourier.regularRoot_primitive hn
    exact Fin.ext (h.pow_inj (by omega) (by omega) hij)
  have hi : Function.Injective (fun i => angularOrbit (θ i) (Y i) s) := by
    intro i j hij
    by_contra hne
    exact (pair_kernel_negative (ha i) (ha j) (hainj.ne hne)
      (hvertex i) (hvertex j) (hchord i j hne)).1 hij
  rw [(angularLogDiscriminant_second_deriv θ Y s hi).deriv]
  have h := angularCurvature_negative θ Y _ s ha hainj hvertex hchord
  rwa [angularChordEnergy_eq_pairEnergy hn] at h

private theorem symmetric_sum_eq_twice_upper {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hs : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) =
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), f i j := by
  have hp (i j : Fin n) : f i j =
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp [hdiag]
    · simp [h, not_lt_of_gt h]
  have he : (∑ i : Fin n, ∑ j : Fin n, if j < i then f i j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n, f i j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_erase _ (hdiag i)]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ((if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun j _ => hp i j)
    _ = (∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0) +
        (∑ i : Fin n, ∑ j : Fin n, if j < i then f i j else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = 2 * ∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0 := by rw [he]; ring
    _ = _ := by simp only [Finset.sum_filter]

/-- The manuscript's unordered-pair form, including its exact coefficient two. -/
theorem angularLogDiscriminant_second_deriv_unordered {n : ℕ}
    (θ : Fin n → ℝ) (Y : Fin n → ℂ) (s : ℝ)
    (hinj : Function.Injective (fun i => angularOrbit (θ i) (Y i) s)) :
    deriv (deriv (angularLogDiscriminant θ Y)) s =
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
        (angularOrbit (θ i) (Y i) s * angularOrbit (θ j) (Y j) s /
          (angularOrbit (θ i) (Y i) s - angularOrbit (θ j) (Y j) s) ^ 2).re * (θ i - θ j) ^ 2 := by
  rw [(angularLogDiscriminant_second_deriv θ Y s hinj).deriv]
  apply symmetric_sum_eq_twice_upper
  · intro i j
    have hc : (angularOrbit (θ i) (Y i) s - angularOrbit (θ j) (Y j) s) ^ 2 =
        (angularOrbit (θ j) (Y j) s - angularOrbit (θ i) (Y i) s) ^ 2 := by ring
    have hr : (θ i - θ j) ^ 2 = (θ j - θ i) ^ 2 := by ring
    rw [hc, hr, mul_comm (angularOrbit (θ i) (Y i) s)]
  · intro i
    simp

end
end Erdos1045.EventualExact.AngularObjectiveCurvature

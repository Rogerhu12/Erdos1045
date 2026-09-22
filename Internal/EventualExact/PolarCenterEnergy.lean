import EventualExact.DiscreteEnergyBounds
import EventualExact.DiscreteSobolev

/-! Energy and actual Schur-coordinate bounds for removing the polar angle. -/

noncomputable section
open scoped BigOperators

namespace Erdos1045.EventualExact.PolarCenterEnergy

open Complex FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum SchurLiftBounds

def phase (t : ℝ) : ℂ := GapRigidity.circle (-t)

def center {ι : Type*} (β : ℂ) (θ : ι → ℝ) (e : ι → ℂ) (j : ι) : ℂ :=
  β * phase (θ j) * e j

theorem center_eq_exp {ι : Type*} (β : ℂ) (θ : ι → ℝ) (e : ι → ℂ) (j : ι) :
    center β θ e j = β * Complex.exp (-(θ j : ℂ) * Complex.I) * e j := by
  simp only [center, phase, GapRigidity.circle, Complex.ofReal_neg]

theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 := GapRigidity.circle_norm _

theorem phase_lipschitz (s t : ℝ) : ‖phase s - phase t‖ ≤ |s - t| := by
  have h := GapRigidity.circle_lipschitz (-s) (-t)
  simpa only [phase, neg_sub_neg, abs_sub_comm] using h

theorem phase_sub_one (t : ℝ) : ‖phase t - 1‖ ≤ |t| := by
  simpa [phase, GapRigidity.circle] using phase_lipschitz t 0

theorem center_norm {ι : Type*} (β : ℂ) (θ : ι → ℝ) (e : ι → ℂ) (j : ι) :
    ‖center β θ e j‖ = ‖β‖ * ‖e j‖ := by
  simp only [center, norm_mul, phase_norm, mul_one]

theorem center_difference_bound {ι : Type*} (β : ℂ) (θ : ι → ℝ) (e : ι → ℂ)
    (i j : ι) : ‖center β θ e j - center β θ e i‖ ≤
      ‖β‖ * (‖e j - e i‖ + ‖e i‖ * |θ j - θ i|) := by
  have he : center β θ e j - center β θ e i =
      β * (phase (θ j) * (e j - e i) + (phase (θ j) - phase (θ i)) * e i) := by
    unfold center
    ring
  rw [he, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg β)
  calc
    _ ≤ ‖phase (θ j) * (e j - e i)‖ + ‖(phase (θ j) - phase (θ i)) * e i‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul, norm_mul, phase_norm, one_mul]
      nlinarith [mul_le_mul_of_nonneg_right (phase_lipschitz (θ j) (θ i)) (norm_nonneg (e i))]

theorem center_pairRatio_bound (β : ℂ) (θ : ℕ → ℝ) (e : ℕ → ℂ) {H : ℝ}
    (_hH : 0 ≤ H) (he : ∀ j, ‖e j‖ ≤ H) (n j h : ℕ) :
    ‖LocalDFT.pairRatio n (center β θ e) j h‖ ≤
      ‖β‖ * (‖LocalDFT.pairRatio n e j h‖ + H *
        ‖LocalDFT.pairRatio n (fun k => (θ k : ℂ)) j h‖) := by
  have hb := center_difference_bound β θ e j (j + h)
  have hh := mul_le_mul_of_nonneg_right (he j) (abs_nonneg (θ (j + h) - θ j))
  have hb' : ‖center β θ e (j + h) - center β θ e j‖ ≤
      ‖β‖ * (‖e (j + h) - e j‖ + H * |θ (j + h) - θ j|) := by
    exact hb.trans (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg β))
  have hd := div_le_div_of_nonneg_right hb'
    (norm_nonneg (LocalPhase.regularRoot n ^ (j + h) - LocalPhase.regularRoot n ^ j))
  simp only [LocalDFT.pairRatio, norm_div, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ _ := hd
    _ = _ := by ring

theorem center_pairRatio_square (β : ℂ) (θ : ℕ → ℝ) (e : ℕ → ℂ) {H : ℝ}
    (hH : 0 ≤ H) (he : ∀ j, ‖e j‖ ≤ H) (n j h : ℕ) :
    normSq (LocalDFT.pairRatio n (center β θ e) j h) ≤
      2 * ‖β‖ ^ 2 * (normSq (LocalDFT.pairRatio n e j h) + H ^ 2 *
        normSq (LocalDFT.pairRatio n (fun k => (θ k : ℂ)) j h)) := by
  have hb := center_pairRatio_bound β θ e hH he n j h
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simp only [normSq_eq_norm_sq]
  have hv := mul_nonneg (sq_nonneg ‖β‖)
    (sq_nonneg (‖LocalDFT.pairRatio n e j h‖ - H *
      ‖LocalDFT.pairRatio n (fun k => (θ k : ℂ)) j h‖))
  nlinarith

theorem sequence_energy_bound (β : ℂ) (θ : ℕ → ℝ) (e : ℕ → ℂ) {H : ℝ}
    (hH : 0 ≤ H) (he : ∀ j, ‖e j‖ ≤ H) (n : ℕ) :
    LocalDFT.energyA n (center β θ e) ≤ 2 * ‖β‖ ^ 2 *
      (LocalDFT.energyA n e + H ^ 2 * LocalDFT.energyA n (fun j => (θ j : ℂ))) := by
  have hs := Finset.sum_le_sum (s := (Finset.range n).erase 0) (fun h _ =>
    Finset.sum_le_sum (s := Finset.range n) (fun j _ => center_pairRatio_square β θ e hH he n j h))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  unfold LocalDFT.energyA
  nlinarith

theorem energy_bound {n : ℕ} (hn : 0 < n) (β : ℂ) (θ : Fin n → ℝ) (e : Fin n → ℂ) :
    pairEnergy hn (center β θ e) ≤ 2 * ‖β‖ ^ 2 *
      (pairEnergy hn e + ‖e‖ ^ 2 * DiscreteEnergy.realEnergy hn θ) := by
  let θ' (j : ℕ) := θ ⟨j % n, Nat.mod_lt _ hn⟩
  have hh (j : ℕ) : ‖periodize hn e j‖ ≤ ‖e‖ := norm_le_pi_norm e _
  exact sequence_energy_bound β θ' (periodize hn e) (norm_nonneg e) hh n

theorem scale_phase_error (β : ℂ) (t : ℝ) :
    ‖β * phase t - 1‖ ≤ ‖β - 1‖ + ‖β‖ * |t| := by
  rw [show β * phase t - 1 = (β - 1) + β * (phase t - 1) by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (phase_sub_one t) (norm_nonneg β))

theorem error_difference_bound {ι : Type*} (β : ℂ) (θ : ι → ℝ) (e : ι → ℂ)
    {T H : ℝ} (_hT : 0 ≤ T) (_hH : 0 ≤ H) (ht : ∀ j, |θ j| ≤ T) (he : ∀ j, ‖e j‖ ≤ H)
    (i j : ι) :
    ‖(center β θ e j - e j) - (center β θ e i - e i)‖ ≤
      (‖β - 1‖ + ‖β‖ * T) * ‖e j - e i‖ + ‖β‖ * H * |θ j - θ i| := by
  have hid : (center β θ e j - e j) - (center β θ e i - e i) =
      (β * phase (θ j) - 1) * (e j - e i) + β * (phase (θ j) - phase (θ i)) * e i := by
    unfold center
    ring
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul]
  have hphase : ‖β * phase (θ j) - 1‖ ≤ ‖β - 1‖ + ‖β‖ * T :=
    (scale_phase_error β (θ j)).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (ht j) (norm_nonneg β)))
  have h₁ := mul_le_mul_of_nonneg_right hphase (norm_nonneg (e j - e i))
  have h₂ := mul_le_mul (phase_lipschitz (θ j) (θ i)) (he i) (norm_nonneg (e i)) (abs_nonneg _)
  have h₃ := mul_le_mul_of_nonneg_left h₂ (norm_nonneg β)
  nlinarith

theorem error_difference_square {n : ℕ} (hn : 0 < n) (β : ℂ) (θ : Fin n → ℝ) (e : Fin n → ℂ)
    (j : Fin n) :
    normSq (difference hn (center β θ e - e) j) ≤
      2 * (‖β - 1‖ + ‖β‖ * ‖θ‖) ^ 2 * normSq (difference hn e j) +
      2 * ‖β‖ ^ 2 * ‖e‖ ^ 2 * normSq (difference hn (fun k => (θ k : ℂ)) j) := by
  have ht (j : Fin n) : |θ j| ≤ ‖θ‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm θ j
  have he (j : Fin n) : ‖e j‖ ≤ ‖e‖ := norm_le_pi_norm e j
  have h := error_difference_bound β θ e (norm_nonneg θ) (norm_nonneg e) ht he j (successor hn j)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simp only [normSq_eq_norm_sq, difference, Pi.sub_apply, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  nlinarith [sq_nonneg ((‖β - 1‖ + ‖β‖ * ‖θ‖) * ‖e (successor hn j) - e j‖ -
    ‖β‖ * ‖e‖ * |θ (successor hn j) - θ j|)]

theorem constraint_abs_le_difference {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ) (j : Fin n) :
    |constraint (by omega) c j| ≤ (n : ℝ) ^ 2 / 4 * ‖difference (by omega) c j‖ := by
  have hratio := QuarticWindowBound.short_pairRatio_bound (show 0 < n by omega)
    (by omega : 0 < 1) (by omega : 2 * 1 ≤ n) (periodize (by omega) c) j.val
  rw [QuarticWindowBound.average_eq] at hratio
  simp only [Finset.sum_range_one, Nat.add_zero, Nat.cast_one, div_one,
    QuarticWindowBound.incrementNorm] at hratio
  have hd : periodize (by omega) c (j.val + 1) - periodize (by omega) c j =
      difference (by omega) c j := by
    simp only [periodize, difference, successor, Nat.mod_eq_of_lt j.isLt]
  rw [hd] at hratio
  have him := (Complex.abs_im_le_norm (edgeRatio (by omega) c j)).trans hratio
  rw [constraint_eq_edgeImaginary hn, abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left him (Nat.cast_nonneg n)
    _ = _ := by ring

theorem constraint_meanSquare_le_difference {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ) :
    meanSquare (constraint (by omega) c) ≤
      (n : ℝ) ^ 3 / 16 * ∑ j, normSq (difference (by omega) c j) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    pow_le_pow_left₀ (abs_nonneg _) (constraint_abs_le_difference hn c j) 2)
  simp only [sq_abs, mul_pow, ← normSq_eq_norm_sq, ← Finset.mul_sum] at hs
  have hh := div_le_div_of_nonneg_right hs (Nat.cast_nonneg n)
  unfold meanSquare
  calc
    _ ≤ _ := hh
    _ = _ := by field_simp; ring

/-- A direct mean-square bound for the actual q(c)-q(e), before energy comparison. -/
theorem constraint_difference_le_steps {n : ℕ} (hn : 2 ≤ n)
    (β : ℂ) (θ : Fin n → ℝ) (e : Fin n → ℂ) :
    meanSquare (constraint (by omega) (center β θ e) - constraint (by omega) e) ≤
      (n : ℝ) ^ 3 / 8 *
        ((‖β - 1‖ + ‖β‖ * ‖θ‖) ^ 2 * ∑ j, normSq (difference (by omega) e j) +
          ‖β‖ ^ 2 * ‖e‖ ^ 2 * ∑ j, normSq (difference (by omega) (fun k => (θ k : ℂ)) j)) := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    error_difference_square (show 0 < n by omega) β θ e j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (n : ℝ) ^ 3 / 16)
  rw [← constraint_sub hn]
  calc
    _ ≤ _ := (constraint_meanSquare_le_difference hn (center β θ e - e)).trans hh
    _ = _ := by ring

/-- Substitution of the proved discrete energy bounds gives the scale needed in (5.5). -/
theorem constraint_difference_le_energy {n : ℕ} (hn : 2 ≤ n)
    (β : ℂ) (θ : Fin n → ℝ) (e : Fin n → ℂ) :
    meanSquare (constraint (by omega) (center β θ e) - constraint (by omega) e) ≤
      Real.pi ^ 2 * n *
        ((‖β - 1‖ + ‖β‖ * ‖θ‖) ^ 2 * pairEnergy (by omega) e +
          ‖β‖ ^ 2 * ‖e‖ ^ 2 * DiscreteEnergy.realEnergy (by omega) θ) := by
  have he := mul_le_mul_of_nonneg_left (DiscreteEnergy.difference_energy_le (show 0 < n by omega) e)
    (by positivity : 0 ≤ (n : ℝ) / 8 * (‖β - 1‖ + ‖β‖ * ‖θ‖) ^ 2)
  have ht := mul_le_mul_of_nonneg_left
    (DiscreteEnergy.difference_energy_le (show 0 < n by omega) (fun k => (θ k : ℂ)))
    (by positivity : 0 ≤ (n : ℝ) / 8 * ‖β‖ ^ 2 * ‖e‖ ^ 2)
  refine (constraint_difference_le_steps hn β θ e).trans ?_
  dsimp [DiscreteEnergy.realEnergy]
  nlinarith

theorem realColumn_norm {n : ℕ} (θ : Fin n → ℝ) : ‖(fun j => (θ j : ℂ))‖ = ‖θ‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg θ)).mpr
    intro j
    simpa only [Complex.norm_real] using norm_le_pi_norm θ j
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun j => (θ j : ℂ)))).mpr
    intro j
    simpa only [Complex.norm_real] using norm_le_pi_norm (fun j => (θ j : ℂ)) j

theorem realColumn_sobolev {n : ℕ} (hn : 2 ≤ n) (θ : Fin n → ℝ) (hθ : ∑ j, θ j = 0) :
    ‖θ‖ ^ 2 ≤ 12 * Real.log n / (n : ℝ) ^ 2 * DiscreteEnergy.realEnergy (by omega) θ := by
  have hmean : (∑ j, (θ j : ℂ)) = 0 := by rw [← Complex.ofReal_sum, hθ, Complex.ofReal_zero]
  have h := DiscreteSobolev.sup_sq_le hn (fun j => (θ j : ℂ)) hmean
  simpa only [realColumn_norm, DiscreteEnergy.realEnergy] using h

/-- The q discrepancy is O(log(n)/n) in mean square under the actual bounded-energy
normalization and a scale error O(n⁻²); no bound on q itself is needed. -/
theorem constraint_difference_le_logarithmic {n : ℕ} (hn : 2 ≤ n)
    (β : ℂ) (θ : Fin n → ℝ) (e : Fin n → ℂ)
    (hθ : ∑ j, θ j = 0) (he : ∑ j, e j = 0) :
    meanSquare (constraint (by omega) (center β θ e) - constraint (by omega) e) ≤
      2 * Real.pi ^ 2 * n * ‖β - 1‖ ^ 2 * pairEnergy (by omega) e +
        36 * Real.pi ^ 2 * ‖β‖ ^ 2 * Real.log n / n * pairEnergy (by omega) e *
          DiscreteEnergy.realEnergy (by omega) θ := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he0 := pairEnergy_nonneg (show 0 < n by omega) e
  have ht0 := pairEnergy_nonneg (show 0 < n by omega) (fun j => (θ j : ℂ))
  have hθs := realColumn_sobolev hn θ hθ
  have hes := DiscreteSobolev.sup_sq_le hn e he
  have hab : (‖β - 1‖ + ‖β‖ * ‖θ‖) ^ 2 ≤ 2 * ‖β - 1‖ ^ 2 + 2 * ‖β‖ ^ 2 * ‖θ‖ ^ 2 := by
    nlinarith [sq_nonneg (‖β - 1‖ - ‖β‖ * ‖θ‖)]
  have hab' := mul_le_mul_of_nonneg_right hab he0
  have hθm := mul_le_mul_of_nonneg_left hθs
    (mul_nonneg (by positivity : 0 ≤ 2 * ‖β‖ ^ 2) he0)
  have hem := mul_le_mul_of_nonneg_left hes
    (mul_nonneg (sq_nonneg ‖β‖) ht0)
  have hbracket : (‖β - 1‖ + ‖β‖ * ‖θ‖) ^ 2 * pairEnergy (by omega) e +
        ‖β‖ ^ 2 * ‖e‖ ^ 2 * DiscreteEnergy.realEnergy (by omega) θ ≤
      2 * ‖β - 1‖ ^ 2 * pairEnergy (by omega) e +
        36 * ‖β‖ ^ 2 * Real.log n / (n : ℝ) ^ 2 * pairEnergy (by omega) e *
          DiscreteEnergy.realEnergy (by omega) θ := by
    dsimp [DiscreteEnergy.realEnergy] at *
    ring_nf at hab' hθm hem ⊢
    linarith
  calc
    _ ≤ _ := (constraint_difference_le_energy hn β θ e).trans
      (mul_le_mul_of_nonneg_left hbracket (by positivity))
    _ = _ := by field_simp

end Erdos1045.EventualExact.PolarCenterEnergy

import StructuralNote.GeometricRelativeRemainder
import StructuralNote.SignedPressureAngular
import EventualExact.LogDiscriminantGradient

/-! Exact antipodal cancellation in the genuine initial angular derivative. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.AngularAntipodalFirst

open Erdos1045 Erdos1045.EventualExact Complex
open Configuration AngularObjectiveCurvature GeometricRelativeRemainder

def vertexTerm {n : ℕ} (Y : Points n) (θ : Fin n → ℝ) (p : Fin n × Fin n) : ℝ :=
  -(Y p.1 / (Y p.1 - Y p.2)).im * (θ p.1 - θ p.2)

theorem pair_first_eq_vertex {X Y : ℂ} (θ φ : ℝ) :
    (I * ((θ : ℂ) * X - (φ : ℂ) * Y) / (X - Y)).re =
      -(X / (X - Y)).im * (θ - φ) := by
  by_cases hd : X - Y = 0
  · simp [hd]
  have he : ((θ : ℂ) * X - (φ : ℂ) * Y) / (X - Y) =
      ((θ - φ : ℝ) : ℂ) * (X / (X - Y)) + (φ : ℂ) := by
    push_cast
    field_simp
    ring
  rw [mul_div_assoc, he]
  simp only [mul_add, add_re, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
    zero_mul, one_mul, mul_zero, sub_zero, add_zero]
  ring

theorem angularFirst_eq_vertex_sum {n : ℕ} (Y : Points n) (θ : Fin n → ℝ) :
    angularFirst θ Y 0 = ∑ p : Fin n × Fin n, vertexTerm Y θ p := by
  rw [Fintype.sum_prod_type]
  unfold angularFirst
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_erase _ (by simp [pairLogFirst])]
  apply Finset.sum_congr rfl
  intro j _
  simp only [pairLogFirst, angularOrbit, zero_mul, ofReal_zero, exp_zero, one_mul]
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  exact pair_first_eq_vertex (θ i) (θ j)

theorem regular_vertex_sum_zero {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) :
    (∑ p : Fin n × Fin n, vertexTerm (SignedPressureAngular.root n) θ p) = 0 := by
  let w := SignedPressureAngular.root n
  have hp : (∑ i, ∑ j, ((I * (θ i : ℂ) * w i - I * (θ j : ℂ) * w j) / (w i - w j)).re) =
      ∑ i, inner ℝ (LocalGradient.realGradient w i) (I * (θ i : ℂ) * w i) := by
    let v (i : Fin n) := I * (θ i : ℂ) * w i
    have hpair (i j : Fin n) : ((v i - v j) / (w i - w j)).re =
        (v i / (w i - w j)).re + (v j / (w j - w i)).re := by
      rw [show w j - w i = -(w i - w j) by ring, div_neg, sub_div]
      simp only [sub_re, neg_re]
      ring
    change (∑ i, ∑ j, ((v i - v j) / (w i - w j)).re) =
      ∑ i, inner ℝ (LocalGradient.realGradient w i) (v i)
    simp_rw [hpair, Finset.sum_add_distrib]
    have hswap : (∑ i, ∑ j, (v j / (w j - w i)).re) =
        ∑ i, ∑ j, (v i / (w i - w j)).re := Finset.sum_comm
    rw [hswap, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [LocalGradient.realGradient_inner, FeketeStationarity.nodeGradient_eq_univ, conj_conj]
    simp only [Finset.sum_mul, Complex.re_sum, div_eq_mul_inv, mul_comm (v i)]
    ring
  have hr : (∑ i, inner ℝ (LocalGradient.realGradient w i) (I * (θ i : ℂ) * w i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hg := LocalGradient.realGradient_regular hn i
    change LocalGradient.realGradient w i = ((n : ℂ) - 1) * w i at hg
    rw [hg, Complex.inner]
    have hw : w i * (starRingEnd ℂ) (w i) = 1 := by
      rw [mul_conj, normSq_eq_norm_sq, SignedPressureAngular.root_norm, one_pow]
      rfl
    have he : I * (θ i : ℂ) * w i * (starRingEnd ℂ) (((n : ℂ) - 1) * w i) =
        I * (θ i : ℂ) * ((n : ℂ) - 1) := by
      simp only [map_mul, map_sub, map_natCast, map_one]
      calc
        _ = I * (θ i : ℂ) * ((n : ℂ) - 1) * (w i * (starRingEnd ℂ) (w i)) := by ring
        _ = _ := by rw [hw, mul_one]
    rw [he]
    simp
  rw [hr] at hp
  rw [Fintype.sum_prod_type]
  convert hp using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show I * (θ i : ℂ) * w i - I * (θ j : ℂ) * w j =
    I * ((θ i : ℂ) * w i - (θ j : ℂ) * w j) by ring, pair_first_eq_vertex]
  rfl

theorem paired_vertex_ratio {w c d ρ : ℂ} (hd : d ≠ 0)
    (hp : 1 + ρ ≠ 0) (hm : 1 - ρ ≠ 0) :
    ((w + c) / (d * (1 + ρ)) + (w - c) / (d * (1 - ρ))) / 2 - w / d =
      (w * ρ ^ 2 - c * ρ) / (d * (1 - ρ ^ 2)) := by
  have hs : 1 - ρ ^ 2 ≠ 0 := by
    rw [show 1 - ρ ^ 2 = (1 + ρ) * (1 - ρ) by ring]
    exact mul_ne_zero hp hm
  field_simp
  ring

def firstError {n : ℕ} (D C : Points n) (p : Fin n × Fin n) : ℂ :=
  (D p.1 * quotient C D p ^ 2 - C p.1 * quotient C D p) /
    ((D p.1 - D p.2) * (1 - quotient C D p ^ 2))

theorem antipodal_vertex_identity {n : ℕ} (e : Equiv.Perm (Fin n))
    (D C : Points n) (θ : Fin n → ℝ) (hD : Function.Injective D)
    (hDanti : ∀ i, D (e i) = -D i) (hC : ∀ i, C (e i) = C i)
    (hθ : ∀ i, θ (e i) = θ i) (hsmall : ∀ p, ‖quotient C D p‖ < 1)
    (p : Fin n × Fin n) :
    (vertexTerm (configuration D C) θ p +
      vertexTerm (configuration D C) θ ((Equiv.prodCongr e e) p)) / 2 - vertexTerm D θ p =
      -(firstError D C p).im * (θ p.1 - θ p.2) := by
  rcases p with ⟨i,j⟩
  by_cases hij : i = j
  · subst j
    simp [vertexTerm]
  have hd := sub_ne_zero.mpr (hD.ne hij)
  have hp := AntipodalLog.one_add_ne_zero (hsmall (i,j))
  have hm : 1 - quotient C D (i,j) ≠ 0 := by
    simpa only [sub_eq_add_neg] using AntipodalLog.one_add_ne_zero
      (show ‖-quotient C D (i,j)‖ < 1 by simpa only [norm_neg] using hsmall (i,j))
  have ha := paired_vertex_ratio (w := D i) (c := C i) hd hp hm
  have he : configuration D C (e i) / (configuration D C (e i) - configuration D C (e j)) =
      (D i - C i) / ((D i - D j) * (1 - quotient C D (i,j))) := by
    have hden : (D i - D j) * (1 - quotient C D (i,j)) =
        (D i - C i) - (D j - C j) := by
      unfold quotient
      field_simp
      ring
    rw [hden]
    simp only [configuration, hDanti, hC]
    calc
      _ = -(D i - C i) / -((D i - C i) - (D j - C j)) := by congr 1 <;> ring
      _ = _ := neg_div_neg_eq _ _
  have hf : configuration D C i / (configuration D C i - configuration D C j) =
      (D i + C i) / ((D i - D j) * (1 + quotient C D (i,j))) := by
    rw [chord_factorization D C i j (hD.ne hij)]
    rfl
  have hai := congrArg Complex.im ha
  change _ = (firstError D C (i,j)).im at hai
  simp only [sub_im, div_ofNat_im, add_im] at hai
  rw [show (Equiv.prodCongr e e) (i,j) = (e i, e j) from rfl]
  dsimp only [vertexTerm]
  rw [hf, he, hθ, hθ]
  linear_combination -(θ i - θ j) * hai

/-- The linear center error cancels in the actual first angular derivative. -/
theorem angularFirst_antipodal {n : ℕ} (e : Equiv.Perm (Fin n))
    (D C : Points n) (θ : Fin n → ℝ) (hD : Function.Injective D)
    (hDanti : ∀ i, D (e i) = -D i) (hC : ∀ i, C (e i) = C i)
    (hθ : ∀ i, θ (e i) = θ i) (hsmall : ∀ p, ‖quotient C D p‖ < 1) :
    angularFirst θ (configuration D C) 0 - angularFirst θ D 0 =
      ∑ p : Fin n × Fin n, -(firstError D C p).im * (θ p.1 - θ p.2) := by
  simp only [angularFirst_eq_vertex_sum]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun p _ =>
    antipodal_vertex_identity e D C θ hD hDanti hC hθ hsmall p)
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib,
    Equiv.sum_comp (Equiv.prodCongr e e)] at hs
  linarith only [hs]

end StructuralNote.AngularAntipodalFirst

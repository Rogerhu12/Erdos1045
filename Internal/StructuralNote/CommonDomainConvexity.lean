import StructuralNote.CommonFiberCanonical
import EventualExact.AngularObjectiveCurvature

/-! Convexity of the literal common parameter domain, including the linear
closure constraint. -/

namespace StructuralNote.CommonDomainConvexity

open Erdos1045 Erdos1045.EventualExact Complex SchurSpectrum SchurLift FiniteFourierLift
open CommonDomainClosure CommonTangentialParameters CommonDomainRadius CommonFiberCanonical
open AngularObjectiveCurvature
open scoped BigOperators
noncomputable section

theorem normSq_convex (x y : ℂ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    normSq ((a : ℂ) * x + (b : ℂ) * y) ≤ a * normSq x + b * normSq y := by
  have he : normSq ((a : ℂ) * x + (b : ℂ) * y) =
      a * normSq x + b * normSq y - a * b * normSq (x - y) := by
    rw [show b = 1 - a by linarith]
    simp only [normSq_apply, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im,
      sub_re, sub_im]
    ring
  rw [he]
  exact sub_le_self _ (mul_nonneg (mul_nonneg ha hb) (normSq_nonneg _))

theorem energy_convex {n : ℕ} (hn : 0 < n) (c d : Fin n → ℂ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    pairEnergy hn (fun j => (a : ℂ) * c j + (b : ℂ) * d j) ≤
      a * pairEnergy hn c + b * pairEnergy hn d := by
  have hp (i j : Fin n) :
      normSq ((a : ℂ) * c i + (b : ℂ) * d i - ((a : ℂ) * c j + (b : ℂ) * d j)) ≤
        a * normSq (c i - c j) + b * normSq (d i - d j) := by
    convert normSq_convex (c i - c j) (d i - d j) ha hb hab using 1
    congr 1
    ring
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      div_le_div_of_nonneg_right (hp i j)
        (normSq_nonneg (LocalPhase.regularRoot n ^ (i : ℕ) - LocalPhase.regularRoot n ^ (j : ℕ)))))
  simp only [add_div, mul_div_assoc, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  simp only [pairEnergy_eq_chord_sum]
  linarith only [hs]

theorem constraint_linear {n : ℕ} (hn : 0 < n) (c d : Fin n → ℂ) (a b : ℝ) :
    constraint hn (fun j => (a : ℂ) * c j + (b : ℂ) * d j) =
      fun j => a * constraint hn c j + b * constraint hn d j := by
  funext j
  simp only [constraint, difference, mul_re, mul_im, add_re, add_im, sub_re, sub_im,
    ofReal_re, ofReal_im]
  ring

theorem parameterSpace_linear {m : ℕ} (hm : 0 < m) (c d : Fin (2 * m) → ℂ)
    (hc : ParameterSpace hm c) (hd : ParameterSpace hm d) (a b : ℝ) :
    ParameterSpace hm (fun j => (a : ℂ) * c j + (b : ℂ) * d j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    dsimp only
    rw [hc.1 j, hd.1 j]
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hc.2.1, hd.2.1,
      mul_zero, mul_zero, add_zero]
  · rw [constraint_linear, hc.2.2, hd.2.2]
    simp only [Pi.zero_apply, mul_zero, add_zero]
    rfl

theorem weighted_lt {X Y R a b : ℝ} (hX : X < R) (hY : Y < R)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : a * X + b * Y < R := by
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have ha' : a = 0 := ha0.symm
    have hb' : b = 1 := by linarith
    simpa only [ha', hb', zero_mul, one_mul, zero_add] using hY
  · have h1 := mul_lt_mul_of_pos_left hX ha0
    have h2 := mul_le_mul_of_nonneg_left hY.le hb
    calc
      _ < a * R + b * R := add_lt_add_of_lt_of_le h1 h2
      _ = R := by rw [← add_mul, hab, one_mul]

theorem domain_convex {m : ℕ} (hm : 0 < m) : Convex ℝ (domain hm) := by
  intro x hx y hy a b ha hb hab
  change InDomain hm (a • x.1 + b • y.1) (a • x.2 + b • y.2)
  have hθeq : (fun j => ((a • x.1 + b • y.1) j : ℂ)) =
      (fun j => (a : ℂ) * (x.1 j : ℂ) + (b : ℂ) * (y.1 j : ℂ)) := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofReal_add, ofReal_mul]
  have hveq : a • x.2 + b • y.2 = (fun j => (a : ℂ) * x.2 j + (b : ℂ) * y.2 j) := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, real_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hθeq]
    intro j
    dsimp only
    have hxj : (x.1 (FourierMultiplier.halfTurn hm j) : ℂ) = x.1 j := hx.1 j
    have hyj : (y.1 (FourierMultiplier.halfTurn hm j) : ℂ) = y.1 j := hy.1 j
    rw [hxj, hyj]
  · rw [hθeq, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hx.2.1, hy.2.1, mul_zero, mul_zero, add_zero]
  · rw [hveq]
    exact parameterSpace_linear hm x.2 y.2 hx.2.2.1 hy.2.2.1 a b
  · rw [hθeq, hveq]
    have hθ := energy_convex (by omega : 0 < 2 * m)
      (fun j => (x.1 j : ℂ)) (fun j => (y.1 j : ℂ)) ha hb hab
    have hv := energy_convex (by omega : 0 < 2 * m) x.2 y.2 ha hb hab
    have hlt := weighted_lt hx.2.2.2 hy.2.2.2 ha hb hab
    linarith only [hθ, hv, hlt]

end
end StructuralNote.CommonDomainConvexity

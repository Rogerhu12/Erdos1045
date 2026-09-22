import StructuralNote.CommonFiberHessianGeometryChord
import StructuralNote.RadialInterpolationEnergy

/-! Energy of the angular velocity error on the actual common domain. -/

namespace StructuralNote.CommonFiberHessianGeometryEnergy

open Erdos1045 Erdos1045.EventualExact Complex
open FiniteFourierLift SchurSpectrum DiscreteEnergy AngularObjectiveCurvature
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure CommonDomainRadius
open CommonFiberGeometry CommonFiberHessianGeometryChord SignedPressureAngular
open GeometricRelativeRemainder AngularFirstEnergy
open scoped BigOperators
noncomputable section

theorem mean_zero_square_sum {n : ℕ} (hn : 2 ≤ n) (η : Fin n → ℝ)
    (hmean : ∑ j, (η j : ℂ) = 0) :
    (n : ℝ) * ∑ j, η j ^ 2 ≤ 4 * realEnergy (by omega) η := by
  have hp := mean_zero_poincare hn (fun j => (η j : ℂ)) hmean
  simp only [normSq_ofReal, ← pow_two] at hp
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsum : 0 ≤ ∑ j, η j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  change _ ≤ pairEnergy (by omega) (fun j => (η j : ℂ)) at hp
  dsimp only [realEnergy]
  nlinarith

theorem product_quotient_square {n : ℕ} (f : Fin n → ℂ) (η : Fin n → ℝ)
    {P R : ℝ}
    (hf : ∀ j, ‖f j‖ ≤ P) (hq : ∀ i j, ‖quotient f (root n) (i, j)‖ ≤ R)
    (i j : Fin n) :
    ‖quotient (fun k => f k * (η k : ℂ)) (root n) (i, j)‖ ^ 2 ≤
      2 * P ^ 2 * ‖quotient (fun k => (η k : ℂ)) (root n) (i, j)‖ ^ 2 + 2 * R ^ 2 * η j ^ 2 := by
  have he : quotient (fun k => f k * (η k : ℂ)) (root n) (i, j) =
      f i * quotient (fun k => (η k : ℂ)) (root n) (i, j) +
        quotient f (root n) (i, j) * (η j : ℂ) := by
    simp only [quotient, div_eq_mul_inv]
    ring
  rw [he, ← normSq_eq_norm_sq]
  simp only [normSq_eq_norm_sq]
  have hs := normSq_add_le
    (f i * quotient (fun k => (η k : ℂ)) (root n) (i, j))
    (quotient f (root n) (i, j) * (η j : ℂ))
  rw [normSq_mul, normSq_mul, normSq_ofReal] at hs
  simp only [normSq_eq_norm_sq, ← pow_two] at hs
  have hp := pow_le_pow_left₀ (norm_nonneg _) (hf i) 2
  have hr := pow_le_pow_left₀ (norm_nonneg _) (hq i j) 2
  nlinarith only [hs, mul_le_mul_of_nonneg_right hp
    (sq_nonneg ‖quotient (fun k => (η k : ℂ)) (root n) (i, j)‖),
    mul_le_mul_of_nonneg_right hr (sq_nonneg (η j))]

theorem product_energy {n : ℕ} (hn : 2 ≤ n) (f : Fin n → ℂ) (η : Fin n → ℝ)
    (hmean : ∑ j, (η j : ℂ) = 0) {P R : ℝ}
    (hf : ∀ j, ‖f j‖ ≤ P) (hq : ∀ i j, ‖quotient f (root n) (i, j)‖ ≤ R) :
    pairEnergy (by omega) (fun j => f j * (η j : ℂ)) ≤
      (2 * P ^ 2 + 4 * R ^ 2) * realEnergy (by omega) η := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun p (_ : p ∈ (Finset.univ : Finset (Fin n × Fin n))) =>
    product_quotient_square f η hf hq p.1 p.2)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hη : (∑ p : Fin n × Fin n, η p.2 ^ 2) = (n : ℝ) * ∑ j, η j ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hη] at hs
  have hp := mul_le_mul_of_nonneg_left (mean_zero_square_sum hn η hmean) (sq_nonneg R)
  rw [pairEnergy_eq_quotient_sum]
  have he := pairEnergy_eq_quotient_sum (by omega : 0 < n) (fun j => (η j : ℂ))
  change realEnergy (by omega) η = _ at he
  nlinarith only [hs, hp, he]

theorem domain_angularError_ratio {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v) (i j : Fin (2 * m)) :
    ‖quotient (angularError θ) (root (2 * m)) (i, j)‖ ≤
      11 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hb := quotient_of_step (by omega) (angularError θ) (by positivity)
    (domain_angularError_step hm θ v hdom) i j
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hb
  have he : (2 * m : ℝ) / 4 * (42 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2) =
      (21 / 2 : ℝ) * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by field_simp; ring
  rw [he] at hb
  apply hb.trans
  apply div_le_div_of_nonneg_right _ hn.le
  nlinarith [show (0 : ℝ) ≤ logOrder (2 * m) by positivity]

theorem domain_angularError_energy {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (hdom : InDomain hm θ v)
    (η : Fin (2 * m) → ℝ) (hmean : ∑ j, (η j : ℂ) = 0) :
    pairEnergy (by omega) (fun j => I * angularError θ j * (η j : ℂ)) ≤
      600 * (logOrder (2 * m) : ℝ) ^ 2 / (2 * m : ℝ) ^ 2 * realEnergy (by omega) η := by
  have hpoint (j : Fin (2 * m)) := (angularError_point θ j).trans (domain_theta_coarse hm θ v hdom j)
  have h := product_energy (by omega : 2 ≤ 2 * m) (angularError θ) η hmean
    hpoint (domain_angularError_ratio hm θ v hdom)
  have he : (fun j => I * angularError θ j * (η j : ℂ)) =
      (fun j => I * (angularError θ j * (η j : ℂ))) := by funext j; ring
  rw [he, RadialInterpolationEnergy.pairEnergy_scale, norm_I, one_pow, one_mul]
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (pairEnergy_nonneg _ _)
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  field_simp
  nlinarith [sq_nonneg (logOrder (2 * m) : ℝ)]

end
end StructuralNote.CommonFiberHessianGeometryEnergy

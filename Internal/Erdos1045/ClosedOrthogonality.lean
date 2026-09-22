import Erdos1045.LocalDFT
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! The previously parameterized finite character orthogonality is constructed
from mathlib's primitive-root theorem and the finite geometric-sum identity. -/

namespace Erdos1045.ClosedFourier

open Complex LocalPhase
open scoped BigOperators
noncomputable section

theorem regularRoot_primitive {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (regularRoot n) n := by
  have he : regularRoot n = Complex.exp (2 * Real.pi * I / (n : ℂ)) := by
    unfold regularRoot
    congr 1
    push_cast
    ring
  rw [he]
  exact Complex.isPrimitiveRoot_exp n hn.ne'

theorem root_norm (n : ℕ) : ‖regularRoot n‖ = 1 := by
  simp [regularRoot, Complex.norm_exp]

theorem root_pow_mod {n : ℕ} (hn : 0 < n) (r : ℕ) :
    regularRoot n ^ r = regularRoot n ^ (r % n) := by
  calc
    _ = regularRoot n ^ (r % n + n * (r / n)) := by rw [Nat.mod_add_div]
    _ = _ := by rw [pow_add, pow_mul, LocalDFT.regularRoot_pow hn, one_pow, mul_one]

theorem root_pow_eq_iff {n : ℕ} (hn : 0 < n) (r s : ℕ) :
    regularRoot n ^ r = regularRoot n ^ s ↔ r % n = s % n := by
  rw [root_pow_mod hn r, root_pow_mod hn s]
  constructor
  · exact (regularRoot_primitive hn).pow_inj (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)
  · exact congrArg (fun k => regularRoot n ^ k)

theorem geometric_sum_of_pow_one (q : ℂ) (n : ℕ) (hq : q ^ n = 1) :
    (∑ h ∈ Finset.range n, q ^ h) = if q = 1 then (n : ℂ) else 0 := by
  by_cases hq1 : q = 1
  · simp [hq1]
  · rw [if_neg hq1]
    have h := geom_sum_mul q n
    rw [hq, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hq1)

theorem sum_pow {n : ℕ} (hn : 0 < n) (m : ℕ) :
    (∑ h ∈ Finset.range n, regularRoot n ^ (h * m)) =
      if n ∣ m then (n : ℂ) else 0 := by
  have hp : (regularRoot n ^ m) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm m n, pow_mul, LocalDFT.regularRoot_pow hn, one_pow]
  have hs := geometric_sum_of_pow_one (regularRoot n ^ m) n hp
  simpa only [← pow_mul, Nat.mul_comm m, (regularRoot_primitive hn).pow_eq_one_iff_dvd] using hs

theorem sum_mul_conj {n : ℕ} (hn : 0 < n) (r s : ℕ) :
    (∑ h ∈ Finset.range n, regularRoot n ^ (h * r) *
      (starRingEnd ℂ) (regularRoot n ^ (h * s))) =
      if r % n = s % n then (n : ℂ) else 0 := by
  have hnorm (k : ℕ) : ‖regularRoot n ^ k‖ = 1 := by rw [norm_pow, root_norm, one_pow]
  have hp : (regularRoot n ^ r / regularRoot n ^ s) ^ n = 1 := by
    rw [div_pow, ← pow_mul, ← pow_mul, Nat.mul_comm r n, Nat.mul_comm s n,
      pow_mul, pow_mul, LocalDFT.regularRoot_pow hn, one_pow, one_pow, div_self one_ne_zero]
  have he (h : ℕ) : regularRoot n ^ (h * r) *
      (starRingEnd ℂ) (regularRoot n ^ (h * s)) =
        (regularRoot n ^ r / regularRoot n ^ s) ^ h := by
    rw [← Complex.inv_eq_conj (hnorm (h * s)), div_pow]
    simp only [← pow_mul, Nat.mul_comm r h, Nat.mul_comm s h, div_eq_mul_inv]
  have hiff : regularRoot n ^ r / regularRoot n ^ s = 1 ↔ r % n = s % n := by
    have hw : regularRoot n ≠ 0 := Complex.exp_ne_zero _
    rw [div_eq_one_iff_eq (pow_ne_zero _ hw), root_pow_eq_iff hn]
  simp_rw [he]
  simpa only [hiff] using geometric_sum_of_pow_one _ n hp

theorem orthogonality (n : ℕ) (hn : 0 < n) :
    LocalFourier.ClassicalOrthogonality n (regularRoot n) :=
  ⟨sum_pow hn, sum_mul_conj hn⟩

end
end Erdos1045.ClosedFourier

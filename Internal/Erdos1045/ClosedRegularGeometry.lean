import Erdos1045.ClosedOrthogonality
import Erdos1045.ClosedCircle

/-! Exact discriminant and odd-cardinality diameter of the regular polygon.
These proofs use concrete coordinates, finite Fourier orthogonality, and
elementary sine monotonicity; no convex-geometry interface is assumed. -/

namespace Erdos1045.ClosedRegularGeometry

open Complex Configuration CircleMatrix
open scoped BigOperators
noncomputable section

theorem regular_eq_root_power (n : ℕ) (j : Fin n) :
    regular n j = LocalPhase.regularRoot n ^ (j : ℕ) := by
  unfold regular LocalPhase.regularRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem regular_vandermonde_gram {n : ℕ} (hn : 0 < n) :
    (vandermonde (regular n)).conjTranspose * vandermonde (regular n) = (n : ℂ) • 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, vandermonde,
    regular_eq_root_power, ← pow_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have he : (∑ l : Fin n, star (LocalPhase.regularRoot n ^ ((l : ℕ) * (i : ℕ))) *
      LocalPhase.regularRoot n ^ ((l : ℕ) * (j : ℕ))) =
      ∑ l ∈ Finset.range n, LocalPhase.regularRoot n ^ (l * (j : ℕ)) *
        (starRingEnd ℂ) (LocalPhase.regularRoot n ^ (l * (i : ℕ))) := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [starRingEnd_apply]
    ring
  rw [he, ClosedFourier.sum_mul_conj hn,
    Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt i.isLt]
  by_cases hij : i = j
  · simp [hij]
  · have hji : j.val ≠ i.val := by intro h; exact hij (Fin.ext h.symm)
    simp [hij, hji]

theorem regular_discriminant (n : ℕ) (hn : 3 ≤ n) :
    discriminant (regular n) = (n : ℝ) ^ n := by
  have h := congrArg Matrix.det (regular_vandermonde_gram (by omega : 0 < n))
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_smul,
    Fintype.card_fin, Matrix.det_one, mul_one] at h
  have hnorm : (Complex.normSq (vandermonde (regular n)).det : ℂ) = (n : ℂ) ^ n := by
    rw [← Complex.mul_conj]
    simpa only [Complex.star_def, mul_comm] using h
  rw [← vandermonde_detSq]
  exact_mod_cast hnorm

theorem sine_half_bound {n k : ℕ} (hn : 0 < n) (hk : 2 * k + 1 ≤ n) :
    Real.sin ((k : ℝ) * Real.pi / n) ≤ Real.cos (Real.pi / (2 * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : 2 * (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  have harg : (k : ℝ) * Real.pi / n ≤ Real.pi / 2 - Real.pi / (2 * n) := by
    apply (div_le_iff₀ hnR).mpr
    have he : (Real.pi / 2 - Real.pi / (2 * (n : ℝ))) * n =
        ((n : ℝ) - 1) * Real.pi / 2 := by field_simp
    rw [he]
    nlinarith [Real.pi_pos]
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ (k : ℝ) * Real.pi / n by
      have hp : 0 ≤ (k : ℝ) * Real.pi / n := by positivity
      linarith [Real.pi_pos])
    (sub_le_self _ (by positivity : 0 ≤ Real.pi / (2 * (n : ℝ))))
    harg
  simpa only [Real.sin_pi_div_two_sub] using hs

theorem sine_integer_bound {n k : ℕ} (hn : 0 < n) (hodd : Odd n) (hk : k ≤ n) :
    |Real.sin ((k : ℝ) * Real.pi / n)| ≤ Real.cos (Real.pi / (2 * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hnonneg : 0 ≤ Real.sin ((k : ℝ) * Real.pi / n) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    apply (div_le_iff₀ hnR).mpr
    nlinarith [Real.pi_pos]
  rw [abs_of_nonneg hnonneg]
  by_cases hhalf : 2 * k + 1 ≤ n
  · exact sine_half_bound hn hhalf
  · have href : 2 * (n - k) + 1 ≤ n := by obtain ⟨q, hq⟩ := hodd; omega
    have hs := sine_half_bound hn href
    have he : ((n - k : ℕ) : ℝ) * Real.pi / n = Real.pi - (k : ℝ) * Real.pi / n := by
      rw [Nat.cast_sub hk]
      field_simp
    rwa [he, Real.sin_pi_sub] at hs

theorem regular_diameter (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    DiameterAtMost (2 * Real.cos (Real.pi / (2 * n))) (regular n) := by
  have hord (i j : Fin n) (hij : i.val ≤ j.val) :
      ‖regular n i - regular n j‖ ≤ 2 * Real.cos (Real.pi / (2 * n)) := by
    have h := circlePoint_chord (2 * Real.pi * (i : ℝ) / n) (2 * Real.pi * (j : ℝ) / n)
    change ‖regular n j - regular n i‖ = _ at h
    rw [norm_sub_rev] at h
    have he : (2 * Real.pi * (j : ℝ) / n - 2 * Real.pi * (i : ℝ) / n) / 2 =
        ((j.val - i.val : ℕ) : ℝ) * Real.pi / n := by
      rw [Nat.cast_sub hij]
      ring
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    rw [h]
    exact mul_le_mul_of_nonneg_left (sine_integer_bound (by omega) hodd
      (show j.val - i.val ≤ n by omega)) (by norm_num)
  intro i j
  by_cases hij : i.val ≤ j.val
  · exact hord i j hij
  · rw [norm_sub_rev]
    exact hord j i (by omega)

end
end Erdos1045.ClosedRegularGeometry

import Erdos1045.LocalFourier
import Erdos1045.LocalTrigonometry
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Converting the finite Fourier calculation to the sine coefficients

The explicit classical input is the universal trigonometric closed form of a
finite geometric sum. All phase signs in the Hessian calculation are proved.
-/

namespace Erdos1045.LocalPhase

open Complex
open scoped BigOperators
noncomputable section

def regularRoot (n : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I)

def phase (n r : ℕ) : ℂ :=
  Complex.exp ((((r : ℝ) * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I)

/-- The usual finite geometric-sum sine formula, for every polygon order and
every positive integer degree. It contains no perturbation or energy estimate. -/
def ClassicalGeometricSine : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k →
    LocalFourier.geom k (regularRoot n) =
      (LocalTrigonometry.mode (n : ℝ) (k : ℝ) : ℂ) * phase n (k - 1)

theorem phase_normSq (n r : ℕ) : normSq (phase n r) = 1 := by
  rw [normSq_eq_norm_sq]
  simp [phase, Complex.norm_exp]

theorem phase_product {n r s : ℕ} (hn : 0 < n) (hrs : r + s = n) :
    phase n r * phase n s = -1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum : (r : ℝ) + s = n := by exact_mod_cast hrs
  have hangle : (r : ℝ) * Real.pi / n + (s : ℝ) * Real.pi / n = Real.pi := by
    rw [← add_div, ← add_mul, hsum]
    field_simp
  unfold phase
  rw [← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, hangle]
  exact Complex.exp_pi_mul_I

theorem geom_shifted (H : ClassicalGeometricSine) {n : ℕ} (hn : 2 ≤ n) (r : ℕ) :
    LocalFourier.geom (r + 1) (regularRoot n) =
      (LocalTrigonometry.mode (n : ℝ) (r + 1 : ℝ) : ℂ) * phase n r := by
  simpa using H n hn (r + 1) (by omega)

theorem geom_shifted_normSq (H : ClassicalGeometricSine) {n : ℕ}
    (hn : 2 ≤ n) (r : ℕ) :
    normSq (LocalFourier.geom (r + 1) (regularRoot n)) =
      LocalTrigonometry.mode (n : ℝ) (r + 1 : ℝ) ^ 2 := by
  rw [geom_shifted H hn, normSq_mul, phase_normSq, normSq_ofReal]
  ring

/-- Exact formula (6.8), with shifted indices and the phase product `-1`
proved explicitly. The first shifted coefficient is zero by normalization. -/
theorem edge_imaginary_energy (HS : ClassicalGeometricSine) {n : ℕ}
    (hn : 2 ≤ n) (HF : LocalFourier.ClassicalOrthogonality n (regularRoot n))
    (b : ℕ → ℂ) (hb : b 0 = 0) :
    (∑ j ∈ Finset.range n,
      (LocalFourier.ratioFourier n (regularRoot n) b j 1).im ^ 2) =
      (n : ℝ) / 2 *
        ((∑ r ∈ Finset.range n,
            LocalTrigonometry.mode (n : ℝ) (r + 1 : ℝ) ^ 2 * normSq (b r)) +
          (∑ r ∈ Finset.range n,
            ((LocalTrigonometry.mode (n : ℝ) (r + 1 : ℝ) *
              LocalTrigonometry.mode (n : ℝ) (LocalFourier.partner n r + 1 : ℝ) : ℝ) : ℂ) *
              b r * b (LocalFourier.partner n r)).re) := by
  have hn0 : 0 < n := by omega
  have hnrm (r : ℕ) :
      normSq (b r * LocalFourier.geom (r + 1) (regularRoot n)) =
        LocalTrigonometry.mode (n : ℝ) (r + 1 : ℝ) ^ 2 * normSq (b r) := by
    rw [normSq_mul, geom_shifted_normSq HS hn]
    ring
  have hprod (r : ℕ) (hr : r ∈ Finset.range n) :
      (b r * LocalFourier.geom (r + 1) (regularRoot n)) *
        (b (LocalFourier.partner n r) *
          LocalFourier.geom (LocalFourier.partner n r + 1) (regularRoot n)) =
      -(((LocalTrigonometry.mode (n : ℝ) (r + 1 : ℝ) *
          LocalTrigonometry.mode (n : ℝ) (LocalFourier.partner n r + 1 : ℝ) : ℝ) : ℂ) *
          b r * b (LocalFourier.partner n r)) := by
    by_cases hr0 : r = 0
    · simp [hr0, hb]
    · have hpair : r + LocalFourier.partner n r = n := by
        simp only [LocalFourier.partner, if_neg hr0]
        have := Finset.mem_range.mp hr
        omega
      rw [geom_shifted HS hn, geom_shifted HS hn, Complex.ofReal_mul]
      calc
        _ = (LocalTrigonometry.mode (n : ℝ) (r + 1 : ℝ) : ℂ) *
            (LocalTrigonometry.mode (n : ℝ) (LocalFourier.partner n r + 1 : ℝ) : ℂ) *
            b r * b (LocalFourier.partner n r) *
              (phase n r * phase n (LocalFourier.partner n r)) := by ring
        _ = _ := by rw [phase_product hn0 hpair]; ring
  have he := LocalFourier.imaginary_synthesis_energy HF hn0
    (fun r => b r * LocalFourier.geom (r + 1) (regularRoot n))
  simp_rw [hnrm] at he
  have hp := Finset.sum_congr (s₁ := Finset.range n) rfl hprod
  rw [hp, Finset.sum_neg_distrib, Complex.neg_re, sub_neg_eq_add] at he
  simpa only [LocalFourier.ratioFourier, pow_one] using he

end

end Erdos1045.LocalPhase

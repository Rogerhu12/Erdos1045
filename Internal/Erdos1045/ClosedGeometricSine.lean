import Erdos1045.ClosedOrthogonality

/-! The finite geometric-sine formula is proved from the defining complex
exponential identity for sine, with the natural-index phase shift explicit. -/

namespace Erdos1045.ClosedFourier

open Complex LocalPhase
noncomputable section

theorem exp_double_sub_one (z : ℂ) :
    Complex.exp (2 * z * I) - 1 = 2 * I * Complex.sin z * Complex.exp (z * I) := by
  symm
  rw [Complex.sin]
  calc
    _ = Complex.exp (z * I) * Complex.exp (z * I) -
        Complex.exp (-z * I) * Complex.exp (z * I) := by
      ring_nf
      simp [Complex.I_sq]
    _ = _ := by
      rw [← Complex.exp_add, ← Complex.exp_add,
        show z * I + z * I = 2 * z * I by ring,
        show -z * I + z * I = 0 by ring, Complex.exp_zero]

theorem geometricSine : LocalPhase.ClassicalGeometricSine := by
  intro n hn k hk
  let x : ℂ := ((Real.pi / (n : ℝ) : ℝ) : ℂ)
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hx : Complex.sin x ≠ 0 := by
    simpa only [x, Complex.ofReal_sin] using
      Complex.ofReal_ne_zero.mpr (LocalTrigonometry.base_sine_pos hnR).ne'
  have hw : regularRoot n ≠ 1 := (regularRoot_primitive (by omega)).ne_one (by omega)
  have hew : regularRoot n = Complex.exp (2 * x * I) := by
    unfold regularRoot x
    congr 1
    push_cast
    ring
  have hewk : regularRoot n ^ k = Complex.exp (2 * ((k : ℂ) * x) * I) := by
    rw [hew, ← Complex.exp_nat_mul]
    congr 1
    ring
  have hephase : phase n (k - 1) = Complex.exp (((k : ℂ) - 1) * x * I) := by
    unfold phase x
    rw [Nat.cast_sub hk, Nat.cast_one]
    congr 1
    push_cast
    ring
  have hemode : (LocalTrigonometry.mode (n : ℝ) (k : ℝ) : ℂ) =
      Complex.sin ((k : ℂ) * x) / Complex.sin x := by
    unfold LocalTrigonometry.mode x
    push_cast
    congr 2
    ring
  have heproduct : Complex.exp (((k : ℂ) - 1) * x * I) * Complex.exp (x * I) =
      Complex.exp ((k : ℂ) * x * I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  apply mul_right_cancel₀ (sub_ne_zero.mpr hw)
  rw [LocalFourier.geom_mul_sub_one, hewk, exp_double_sub_one, hemode, hephase,
    hew, exp_double_sub_one]
  have halg : (Complex.sin ((k : ℂ) * x) / Complex.sin x) *
      Complex.exp (((k : ℂ) - 1) * x * I) * (2 * I * Complex.sin x * Complex.exp (x * I)) =
      2 * I * Complex.sin ((k : ℂ) * x) *
        (Complex.exp (((k : ℂ) - 1) * x * I) * Complex.exp (x * I)) := by
    field_simp
  rw [halg, heproduct]

end
end Erdos1045.ClosedFourier

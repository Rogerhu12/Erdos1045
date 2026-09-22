import StructuralNote.CommonTangentialReconstruction
import EventualExact.QuadraticStability

/-! Exact polarization of the actual Schur lift. The linear term uses all n
sites, hence has coefficient 1/n with the established energy normalization. -/

namespace StructuralNote.CommonFiberSchurExpansion

open Erdos1045.EventualExact Complex FourierMultiplier FiniteFourierLift
open SchurLift SchurSpectrum QuadraticStability CommonTangentialParameters
open scoped BigOperators
noncomputable section

theorem integral_add {n : ℕ} (d e : Fin n → ℂ) : integral (d + e) = integral d + integral e := by
  funext j
  simp only [integral, synthesis, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.val = 0
  · simp [integralCoefficients, hp]
  · simp [integralCoefficients, hp, coefficient, Pi.add_apply, add_mul,
      Finset.sum_add_distrib, add_div]

theorem firstCoefficient_add {n : ℕ} (f g : Fin n → ℝ) :
    firstCoefficient (f + g) = firstCoefficient f + firstCoefficient g := by
  simp [firstCoefficient, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem canonicalLift_add {n : ℕ} (f g : Fin n → ℝ) :
    canonicalLift (f + g) = canonicalLift f + canonicalLift g := by
  have he : SchurLift.increment (f + g) = SchurLift.increment f + SchurLift.increment g := by
    funext j
    simp only [SchurLift.increment, firstCoefficient_add, Pi.add_apply,
      ofReal_add, add_mul, Complex.add_im]
    push_cast
    ring
  rw [canonicalLift, he, integral_add]
  rfl

theorem bilinear_add_left {n : ℕ} (hn : 0 < n) (c d e : Fin n → ℂ) :
    bilinear hn (c + d) e = bilinear hn c e + bilinear hn d e := by
  simp only [bilinear, ratio_add, add_mul, Complex.add_re, Finset.sum_add_distrib, add_div]

theorem bilinear_add_right {n : ℕ} (hn : 0 < n) (c d e : Fin n → ℂ) :
    bilinear hn c (d + e) = bilinear hn c d + bilinear hn c e := by
  simp only [bilinear, ratio_add, mul_add, Complex.add_re, Finset.sum_add_distrib, add_div]

theorem normalized_energy_add {n : ℕ} (f g : Fin n → ℝ) :
    normalizedBoxEnergy (operator n) (f + g) = normalizedBoxEnergy (operator n) f +
      normalizedBoxEnergy (operator n) g + finitePairing (operator n f) g / n := by
  simp only [normalizedBoxEnergy, boxEnergy_add (selfAdjoint n), Fintype.card_fin,
    add_div, finitePairing_comm g]
  ring

theorem canonical_kernel_bilinear {m : ℕ} (hm : 2 ≤ m) (f : Fin (2 * m) → ℝ)
    (hf : FiniteBox.Antiperiodic (by omega) f) (v : Fin (2 * m) → ℂ)
    (hv : HalfPeriodic (by omega) v) (hq : constraint (by omega) v = 0) :
    bilinear (by omega) (canonicalLift f) v = 0 := by
  have ho := geometric_orthogonal_decomposition hm f hf v hv hq
  rw [potential_add, pairPotential_canonicalLift hm f hf] at ho
  linarith

theorem canonical_bilinear {m : ℕ} (hm : 2 ≤ m) (f g : Fin (2 * m) → ℝ)
    (hf : FiniteBox.Antiperiodic (by omega) f)
    (hg : FiniteBox.Antiperiodic (by omega) g) :
    -2 * bilinear (by omega) (canonicalLift f) (canonicalLift g) =
      finitePairing (operator (2 * m) f) g / (2 * m : ℝ) := by
  have hfg : FiniteBox.Antiperiodic (by omega) (f + g) := by
    intro j
    simp only [Pi.add_apply, hf j, hg j]
    ring
  have h := pairPotential_canonicalLift hm (f + g) hfg
  rw [canonicalLift_add, potential_add, pairPotential_canonicalLift hm f hf,
    pairPotential_canonicalLift hm g hg, normalized_energy_add] at h
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  linarith

theorem canonical_remainder_bilinear {m : ℕ} (hm : 2 ≤ m) (f : Fin (2 * m) → ℝ)
    (hf : FiniteBox.Antiperiodic (by omega) f) (R : Fin (2 * m) → ℂ)
    (hR : HalfPeriodic (by omega) R) :
    -2 * bilinear (by omega) (canonicalLift f) R =
      finitePairing (operator (2 * m) f) (constraint (by omega) R) / (2 * m : ℝ) := by
  let g := constraint (by omega) R
  have hg : FiniteBox.Antiperiodic (by omega) g := constraint_halfTurn (by omega) R hR
  let w := R - canonicalLift g
  have hw : HalfPeriodic (by omega) w := by
    intro j
    simp only [w, Pi.sub_apply, hR j, canonicalLift_halfTurn hm g hg]
  have hwq : constraint (by omega) w = 0 := by
    rw [show w = R - canonicalLift g from rfl, constraint_sub (by omega),
      constraint_canonicalLift (by omega)]
    exact sub_self g
  have hwz := canonical_kernel_bilinear hm f hf w hw hwq
  have hb := canonical_bilinear hm f g hf hg
  have he : R = canonicalLift g + w := by
    dsimp [w]
    abel
  conv_lhs => rw [he, bilinear_add_right, hwz, add_zero]
  exact hb

/-- The full three-term expansion with the actual geometric bilinear remainder. -/
theorem exact_expansion {m : ℕ} (hm : 2 ≤ m) (f : Fin (2 * m) → ℝ)
    (hf : FiniteBox.Antiperiodic (by omega) f) (v R : Fin (2 * m) → ℂ)
    (hv : HalfPeriodic (by omega) v) (hvq : constraint (by omega) v = 0)
    (hR : HalfPeriodic (by omega) R) :
    pairPotential (by omega) (canonicalLift f + v + R) =
      normalizedBoxEnergy (operator (2 * m)) f + pairPotential (by omega) v +
        finitePairing (operator (2 * m) f) (constraint (by omega) R) / (2 * m : ℝ) +
        pairPotential (by omega) R - 2 * bilinear (by omega) v R := by
  rw [potential_add, geometric_orthogonal_decomposition hm f hf v hv hvq, bilinear_add_left]
  have hb := canonical_remainder_bilinear hm f hf R hR
  linarith

theorem quadratic_remainder_bound {n : ℕ} (hn : 0 < n) (v R : Fin n → ℂ) :
    |pairPotential hn R - 2 * bilinear hn v R| ≤
      pairEnergy hn R + 2 * Real.sqrt (pairEnergy hn v) * Real.sqrt (pairEnergy hn R) := by
  have hb := bilinear_abs_le hn v R
  have hP := potential_abs_le_energy hn R
  have ht := abs_sub (pairPotential hn R) (2 * bilinear hn v R)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
  nlinarith

/-- Only actual energy bounds are required to control the quadratic remainder. -/
theorem expansion_error_bound {m : ℕ} (hm : 2 ≤ m) (f : Fin (2 * m) → ℝ)
    (hf : FiniteBox.Antiperiodic (by omega) f) (v R : Fin (2 * m) → ℂ)
    (hv : HalfPeriodic (by omega) v) (hvq : constraint (by omega) v = 0)
    (hR : HalfPeriodic (by omega) R) :
    |pairPotential (by omega) (canonicalLift f + v + R) -
      (normalizedBoxEnergy (operator (2 * m)) f + pairPotential (by omega) v +
        finitePairing (operator (2 * m) f) (constraint (by omega) R) / (2 * m : ℝ))| ≤
      pairEnergy (by omega) R +
        2 * Real.sqrt (pairEnergy (by omega) v) * Real.sqrt (pairEnergy (by omega) R) := by
  rw [exact_expansion hm f hf v R hv hvq hR]
  convert quadratic_remainder_bound (by omega) v R using 1
  congr 1
  ring

theorem expansion_error_of_energy_bounds {m : ℕ} (hm : 2 ≤ m) (f : Fin (2 * m) → ℝ)
    (hf : FiniteBox.Antiperiodic (by omega) f) (v R : Fin (2 * m) → ℂ)
    (hv : HalfPeriodic (by omega) v) (hvq : constraint (by omega) v = 0)
    (hR : HalfPeriodic (by omega) R) {a r : ℝ}
    (ha : pairEnergy (by omega) v ≤ a) (hr : pairEnergy (by omega) R ≤ r) :
    |pairPotential (by omega) (canonicalLift f + v + R) -
      (normalizedBoxEnergy (operator (2 * m)) f + pairPotential (by omega) v +
        finitePairing (operator (2 * m) f) (constraint (by omega) R) / (2 * m : ℝ))| ≤
      r + 2 * Real.sqrt a * Real.sqrt r := by
  apply (expansion_error_bound hm f hf v R hv hvq hR).trans
  gcongr

end
end StructuralNote.CommonFiberSchurExpansion

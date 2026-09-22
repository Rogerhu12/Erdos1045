import StructuralNote.CommonFiberRefinedRoot
import StructuralNote.CommonFiberInnerReconstructionEnergy

/-! The zero-parameter canonical center is exactly the previously constructed
nonlinear box lift. The first harmonic is absorbed into the closure root. -/

namespace StructuralNote.CommonFiberInnerReconstruction

open Erdos1045 Erdos1045.EventualExact Complex LensClosure FiniteFourierLift
open SchurLift SchurLiftBounds SchurSpectrum BoxLensLift
open CommonTangentialParameters CommonFiberGeometry CommonFiberSmooth CommonFiberCanonical
open CommonFiberRefinedRoot
open scoped BigOperators
noncomputable section

def schurRoot {n : ℕ} (q : Fin n → ℝ) : ℂ :=
  ((4 * Real.sin (angle n) / n : ℝ) : ℂ) * I * (starRingEnd ℂ) (firstCoefficient q)

theorem schurRoot_height {m : ℕ} (q : Fin (2 * m) → ℝ) (j : Fin m) :
    harmonicFunctional (midpoint m j) (schurRoot q) = tangential q (BoxLensLift.halfIndex j) := by
  rw [tangential, frame_halfIndex]
  simp only [schurRoot, harmonicFunctional_apply, mul_re, mul_im, ofReal_re,
    ofReal_im, I_re, I_im, conj_re, conj_im, unit_re, unit_im]
  ring

theorem schurRoot_norm_le {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ)
    (hq : ∀ j, |q j| ≤ FiniteBox.amplitude n) : ‖schurRoot q‖ ≤ 2 * radius n := by
  have hA := FiniteBox.amplitude_pos (by omega : 2 ≤ n)
  have hf := firstCoefficient_bound hn q
  have hq2 := meanSquare_le_of_bound (by omega) q hA.le hq
  have hb : normSq (firstCoefficient q) ≤ FiniteBox.amplitude n ^ 2 := by
    nlinarith [normSq_nonneg (firstCoefficient q)]
  have hnrm : ‖schurRoot q‖ ^ 2 = (4 * Real.sin (angle n) / n) ^ 2 * normSq (firstCoefficient q) := by
    simp only [schurRoot, norm_mul, norm_real, Real.norm_eq_abs, norm_I, norm_conj,
      mul_one, mul_pow, sq_abs, ← normSq_eq_norm_sq]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (radius_nonneg n))).mp
  rw [hnrm, radius_identity (by omega)]
  have he := mul_le_mul_of_nonneg_left hb (sq_nonneg (4 * Real.sin (angle n) / n))
  convert he using 1
  ring

theorem schurRoot_numeric {n : ℕ} (hn : 3 ≤ n) (q : Fin n → ℝ)
    (hq : ∀ j, |q j| ≤ FiniteBox.amplitude n) : ‖schurRoot q‖ ≤ 32 / (n : ℝ) ^ 2 := by
  apply (schurRoot_norm_le hn q hq).trans
  have h := radius_le_numeric (show 0 < n by omega)
  calc
    _ ≤ 2 * (16 / (n : ℝ) ^ 2) := by gcongr
    _ = _ := by ring

def halfWord {m : ℕ} (q : Fin (2 * m) → ℝ) (j : Fin m) : ℝ :=
  coordinate q (BoxLensLift.halfIndex j)

theorem shifted_zero_height {m : ℕ} (q : Fin (2 * m) → ℝ) (η : ℂ) (j : Fin m) :
    heightParameter (0 : Fin m → ℝ) (schurRoot q + η) j =
      heightParameter (fun k => tangential q (BoxLensLift.halfIndex k)) η j := by
  simp only [heightParameter, Pi.zero_apply, zero_add, map_add, schurRoot_height]

theorem shifted_zero_closure {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ) (η : ℂ) :
    closureFamily (data hm (halfWord q) (0, 0)) (schurRoot q + η) = boxClosure q η := by
  simp only [closureFamily, data, zero_phase, zero_halfAngle, zero_coordinates,
    LensClosure.closure, shifted_zero_height]
  simp only [boxClosure, LensClosure.closure, baseWidth, angle, halfWord,
    Nat.cast_mul, Nat.cast_ofNat]

theorem shifted_boxRoot_bound {m : ℕ} (hm : 128 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    ‖schurRoot q + boxRoot (by omega) q hq‖ ≤ 1024 / (2 * m : ℝ) ^ 2 := by
  have hn : (256 : ℝ) ≤ 2 * m := by exact_mod_cast (show 256 ≤ 2 * m by omega)
  have hq1 := schurRoot_numeric (show 3 ≤ 2 * m by omega) q hq.2
  have hq2 := (boxRoot_spec (show 16 ≤ m by omega) q hq).1
  simp only [rootRadius, Nat.cast_mul, Nat.cast_ofNat] at hq1 hq2
  have hb : (1024 : ℝ) / (2 * m : ℝ) ^ 4 ≤ 1 / (2 * m : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (2 * m : ℝ) ^ 4)
      (by positivity : (0 : ℝ) < (2 * m : ℝ) ^ 2)).mpr
    nlinarith [mul_nonneg (sq_nonneg (2 * m : ℝ)) (show 0 ≤ (2 * m : ℝ) ^ 2 - 1024 by nlinarith)]
  have h := norm_add_le (schurRoot q) (boxRoot (by omega) q hq)
  have hi : (0 : ℝ) ≤ ((2 * m : ℝ) ^ 2)⁻¹ := by positivity
  simp only [div_eq_mul_inv] at hq1 hq2 hb ⊢
  linarith

theorem canonical_zero_root_eq_boxRoot {m : ℕ} (hm : 128 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    CommonFiberCanonical.root (by omega) (halfWord q) (0, 0) = schurRoot q + boxRoot (by omega) q hq := by
  have hσ : ∀ j, |halfWord q j| ≤ 1 := fun j => coordinate_bound (by omega) q hq.2 _
  have hnew : RootCondition (by omega) (halfWord q) (0, 0) (schurRoot q + boxRoot (by omega) q hq) := by
    refine ⟨shifted_boxRoot_bound hm q hq, ?_⟩
    rw [shifted_zero_closure]
    exact (boxRoot_spec (by omega) q hq).2
  have he := CommonDomainClosure.exists_unique_parameter_root hm 0 0 (halfWord q)
    (by simp) (zero_parameterSpace (by omega))
    (by simpa only [Pi.zero_apply, ofReal_zero, ← Pi.zero_def, zero_pairEnergy] using
      (show (0 : ℝ) ≤ 1 / (2 * m : ℝ) by positivity))
    (by rw [zero_pairEnergy]; positivity) hσ
  exact he.unique (canonical_zero_spec hm (halfWord q) hσ) hnew

theorem canonical_zero_center_eq_boxLift {m : ℕ} (hm : 128 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    center (by omega) 0 0 (halfWord q) (CommonFiberCanonical.root (by omega) (halfWord q) (0, 0)) =
      liftedCenter (by omega) q hq := by
  rw [canonical_zero_root_eq_boxRoot hm q hq]
  unfold center liftedCenter correctedCenter correctedIncrement
  congr 2
  funext j
  simp only [fiberIncrement, zero_phase, zero_halfAngle, zero_coordinates,
    shifted_zero_height, correctedHalfIncrement, halfWord]
  simp only [baseWidth, angle, Nat.cast_mul, Nat.cast_ofNat]

theorem canonical_zero_schur_energy {m : ℕ} (hm : 128 ≤ m) (q : Fin (2 * m) → ℝ)
    (hq : q ∈ FiniteBox.Q (by omega)) :
    pairEnergy (by omega)
      (center (by omega) 0 0 (halfWord q) (CommonFiberCanonical.root (by omega) (halfWord q) (0, 0)) -
        canonicalLift q) ≤ 131072 / (2 * m : ℝ) ^ 4 := by
  rw [canonical_zero_center_eq_boxLift hm q hq]
  have hd := DiscreteEnergy.pairEnergy_le_difference (show 0 < 2 * m by omega)
    (liftedCenter (by omega) q hq - canonicalLift q)
  have hs : (∑ j : Fin (2 * m), normSq (difference (by omega)
      (liftedCenter (by omega) q hq - canonicalLift q) j)) ≤
      (2 * m : ℝ) * (2048 / (2 * m : ℝ) ^ 4) ^ 2 := by
    have hp (j : Fin (2 * m)) := liftedCenter_difference_error (show 16 ≤ m by omega) q hq j
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hp
    calc
      _ ≤ ∑ _j : Fin (2 * m), (2048 / (2 * m : ℝ) ^ 4) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [normSq_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) (hp j) 2
      _ = _ := by simp
  apply hd.trans
  calc
    _ ≤ ((2 * m : ℕ) : ℝ) ^ 3 / 32 * ((2 * m : ℝ) * (2048 / (2 * m : ℝ) ^ 4) ^ 2) := by gcongr
    _ = _ := by
      have hn : (2 * m : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

end
end StructuralNote.CommonFiberInnerReconstruction

import StructuralNote.ExplicitThresholdFunctions
import StructuralNote.ExplicitGradientThreshold
import StructuralNote.SinglePressureEstimate

/-! Explicit smallness of the local analytic budgets used before the strong estimate. -/

namespace StructuralNote.ExplicitLocalBudgets

open Erdos1045 Erdos1045.EventualExact Erdos1045.ExplicitThreshold
open PolarAngleControl ExtremalPolarCenter ActualAngularLoss
open RadialInterpolationQuotients ExplicitGradientThreshold
open PressureAngularAbsorption SignedPressureRemainder
noncomputable section

theorem log_div_power_small {n k : ℕ} {A ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) (hk : 1 ≤ k)
    (hn : decayThreshold A ε ≤ n) : A * Real.log n / (n : ℝ) ^ k < ε := by
  have hkR : (1 / 4 : ℝ) ≤ k := by
    have hh : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith only [hh]
  have hh := monomial_small (n := n) (j := 1) hA hε (by norm_num) hkR hn
  rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast, pow_one] at hh
  have hlog : Real.log (n : ℝ) ≤ logBudget n := by unfold logBudget; linarith
  have hmul := mul_le_mul_of_nonneg_left hlog hA
  calc
    _ ≤ A * logBudget n / (n : ℝ) ^ k :=
      div_le_div_of_nonneg_right hmul (by positivity)
    _ < ε := by simpa only [div_eq_mul_inv] using hh

def sizeThreshold (ε : ℝ) : ℕ := decayThreshold (384 * Real.pi ^ 2) ε

theorem size_small {n : ℕ} {ε : ℝ} (hε : 0 < ε) (hn : sizeThreshold ε ≤ n) :
    sizeBudget n < ε := by
  exact log_div_power_small (by positivity) hε (by norm_num : 1 ≤ 2) hn

def coordinateThreshold (ε : ℝ) : ℕ := sizeThreshold ((min 1 ε / 100) ^ 2)

theorem coordinate_small {n : ℕ} {η ε : ℝ} (hε : 0 < ε) (hη : 0 ≤ η)
    (hηsmall : η ≤ min 1 ε / 100) (hn : coordinateThreshold ε ≤ n) :
    coordinateBudget n η ≤ ε := by
  let t : ℝ := min 1 ε / 100
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 / 100 := by dsimp [t]; linarith only [min_le_left (1 : ℝ) ε]
  have hte : 100 * t ≤ ε := by dsimp [t]; linarith only [min_le_right (1 : ℝ) ε]
  have hs : Real.sqrt (sizeBudget n) ≤ t := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨ht.le, (size_small (sq_pos_of_pos ht) hn).le⟩
  have hs0 := Real.sqrt_nonneg (sizeBudget n)
  have hprod : 2 * Real.sqrt (sizeBudget n) * (4 * η + 2 * Real.sqrt (sizeBudget n)) ≤
      2 * t * (4 * t + 2 * t) := by gcongr
  change η ≤ t at hηsmall
  unfold coordinateBudget
  nlinarith only [hprod, hs, hs0, hηsmall, ht, ht1, hte]

def pairThreshold (ε : ℝ) : ℕ :=
  max (sizeThreshold ((min 1 ε / 100) ^ 2))
    (inverseThreshold (512 * Real.pi ^ 2) (ε / 4))

theorem pair_small {n : ℕ} {η ε : ℝ} (hε : 0 < ε) (_hη : 0 ≤ η)
    (hηsmall : η ≤ min 1 ε / 100) (hn : pairThreshold ε ≤ n) : pairBudget n η < ε := by
  have hsize := (le_max_left _ _).trans hn
  have hinv := (le_max_right _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hinv
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith only [hnR]
  have ht : 0 < min 1 ε / 100 := by positivity
  have hs : Real.sqrt (sizeBudget n) ≤ min 1 ε / 100 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨ht.le, (size_small (sq_pos_of_pos ht) hsize).le⟩
  have hi := inverse_small (show 0 < ε / 4 by positivity) hinv
  have hi2 : 512 * Real.pi ^ 2 / (n : ℝ) ^ 2 ≤ 512 * Real.pi ^ 2 / n := by
    apply div_le_div_of_nonneg_left (by positivity) hn0
    nlinarith only [hnR]
  unfold pairBudget
  linarith only [hs, hi2, hi, hηsmall, min_le_right (1 : ℝ) ε, hε]

def pathEnergy : ℝ := 32768 * Real.pi ^ 4 + 2688 * Real.pi ^ 2

def pathTolerance (ε : ℝ) : ℝ := min 1 (pairTolerance pathEnergy ε) / 100

def pathThreshold (ε : ℝ) : ℕ := pairThreshold (pairTolerance pathEnergy ε)

theorem pathTolerance_pos {ε : ℝ} (hε : 0 < ε) : 0 < pathTolerance ε := by
  have hh := pairTolerance_pos (C := pathEnergy) hε
  unfold pathTolerance
  positivity

theorem model_path_gradient {m : ℕ} (hm : 2 ≤ m) {ε η : ℝ} (hε : 0 < ε)
    (hn : pathThreshold ε ≤ 2 * m) (hη : η ≤ pathTolerance ε)
    {z : Configuration.Points (2 * m)} {σ : Equiv.Perm (Fin (2 * m))}
    {α β : ℂ} {u : ℕ → ℂ}
    (hmodel : CommonLocalization.NormalizedRelativeEdgeModel z σ α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hE : ExtremalEnergyBound.totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2)
    (hp : PolarBounds m u η) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    RadialObjectivePrice.gradientDeviation (ActualRadialPrice.actualPath m ‖β‖ u t) < ε := by
  have htol := pairTolerance_pos (C := pathEnergy) hε
  have hpair := pair_small htol hmodel.error_nonneg hη hn
  have hηquarter : η ≤ 1 / 4 := by
    have hh : pathTolerance ε ≤ 1 / 100 := by
      unfold pathTolerance
      linarith only [min_le_left (1 : ℝ) (pairTolerance pathEnergy ε)]
    linarith only [hη, hh]
  rw [ActualRadialPrice.actualPath, ActualRadialGradient.radial_path_identity,
    RadialObjectivePrice.gradientDeviation_eq_gradientError]
  have hb0 : 0 ≤ pairBudget (2 * m) η := by
    unfold pairBudget
    have := hmodel.error_nonneg
    positivity
  apply gradient_small (by omega) (pathSequence m ‖β‖ u t)
    (pathSequence_periodic (by omega) ‖β‖ u hmodel.periodic t) hε hb0 hpair.le
  · intro i h hh
    exact model_path_pair_le hm hmodel hηquarter hz hE hp ht
      (by have := (Finset.mem_Ico.mp hh).1; omega) (Finset.mem_Ico.mp hh).2 i
  · exact model_path_sequence_energy hm hmodel hηquarter hz hE hp ht

def canonicalThreshold (B A : ℝ) : ℕ :=
  max (inverseThreshold (1040 * Real.sqrt (32 * Real.pi ^ 4 * B ^ 2)) (1 / 1024))
    (decayThreshold (1536 * A) (1 / 1024))

theorem canonical_small {n : ℕ} {δ B A : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ)
    (hδsmall : δ ≤ 1 / 1000) (hn : canonicalThreshold B A ≤ n) :
    CanonicalNonlinearError.coefficient n δ B A ≤ 1 / 128 := by
  have hi := (le_max_left _ _).trans hn
  have hd := (le_max_right _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hi
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : Real.sqrt (2 * CanonicalNonlinearError.canonicalBudget n B) =
      Real.sqrt (32 * Real.pi ^ 4 * B ^ 2) / (n : ℝ) := by
    have he : 2 * CanonicalNonlinearError.canonicalBudget n B =
        (32 * Real.pi ^ 4 * B ^ 2) / (n : ℝ) ^ 2 := by
      unfold CanonicalNonlinearError.canonicalBudget
      ring
    rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq hn0.le]
  have hcan := inverse_small (by norm_num : (0 : ℝ) < 1 / 1024) hi
  have hlog := log_div_power_small (mul_nonneg (by norm_num) hA)
    (by norm_num : (0 : ℝ) < 1 / 1024) (by norm_num : 1 ≤ 2) hd
  have hδsq := pow_le_pow_left₀ hδ hδsmall 2
  unfold CanonicalNonlinearError.coefficient
  rw [hs, ← mul_div_assoc]
  nlinarith only [hcan, hlog, hδsq]

def absorptionThreshold : ℕ :=
  max 16 (max (sizeThreshold (1 / 65536))
    (max (inverseThreshold (512 * Real.pi ^ 2) (1 / 32))
      (max (inverseThreshold (4 * (31 * Real.pi / 64) * Real.pi ^ 2) (1 / 16))
        (decayThreshold (192 * (33 * Real.pi ^ 2) ^ 2) (1 / 256)))))

theorem absorption_small {n : ℕ} (hn : absorptionThreshold ≤ n) :
    16 ≤ n ∧ sizeBudget n ≤ 1 / 256 ∧
    512 * Real.pi ^ 2 / (n : ℝ) ≤ 1 / 2 ∧
    4 * (31 * Real.pi / 64) * Real.pi ^ 2 / (n : ℝ) ≤ 1 / 16 ∧
    radialErrorCoefficient n (31 * Real.pi / 64) ≤ 1 / 8 ∧
    residualCoefficient n ≤ 1 / 256 := by
  simp only [absorptionThreshold, max_le_iff] at hn
  have hs := (size_small (by norm_num : (0 : ℝ) < 1 / 65536) hn.2.1).le
  have hi := (inverse_small (by norm_num : (0 : ℝ) < 1 / 32) hn.2.2.1).le
  have he := (inverse_small (by norm_num : (0 : ℝ) < 1 / 16) hn.2.2.2.1).le
  have hd := (log_div_power_small (by positivity : 0 ≤ 192 * (33 * Real.pi ^ 2) ^ 2)
    (by norm_num : (0 : ℝ) < 1 / 256) (by norm_num : 1 ≤ 2) hn.2.2.2.2).le
  have hroot : Real.sqrt (sizeBudget n) ≤ 1 / 256 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · norm_num
      exact hs
  refine ⟨hn.1, hs.trans (by norm_num), hi.trans (by norm_num), he, ?_, hd⟩
  have hG : 0 ≤ (31 * Real.pi / 64) / 2 := by positivity
  have hG1 : (31 * Real.pi / 64) / 2 ≤ 1 := by linarith only [Real.pi_lt_four]
  have hsum : 512 * Real.pi ^ 2 / (n : ℝ) + 4 * Real.sqrt (sizeBudget n) ≤ 1 / 16 := by
    linarith only [hi, hroot]
  have hmul := mul_le_mul_of_nonneg_left hsum hG
  unfold radialErrorCoefficient
  nlinarith only [hmul, hG1]

end
end StructuralNote.ExplicitLocalBudgets

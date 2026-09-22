import StructuralNote.FixedSchurWordPotential
import StructuralNote.FixedSchurPairingBounds
import StructuralNote.SolNearMaximumSigns

/-! The angular term in the common-parameter comparison for genuine
near-maximizing words. Sign alignment is derived from the finite deficit. -/

namespace StructuralNote.FixedSchurNearWordAngular

open Erdos1045.EventualExact FourierMultiplier SchurLiftBounds FiniteBox
open FixedSchurDomainSmallness FixedSchurWordPotential FixedSchurPairingBounds
open FixedDualClassificationFinite SolNearMaximumSigns SolWordHamming Filter
open scoped BigOperators Topology

noncomputable section

def signedPotential {m : ℕ} {hm : 0 < m} (s : SignPattern hm) : Fin (2 * m) → ℝ :=
  fun j => patternSign s j * operator (2 * m) (baseWord (patternSign s)) j

theorem meanSquare_abs_sub_le {n : ℕ} (f g : Fin n → ℝ) :
    meanSquare (fun j => |f j| - |g j|) ≤ meanSquare (f - g) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  apply Finset.sum_le_sum
  intro j _
  have h := pow_le_pow_left₀ (abs_nonneg _) (abs_abs_sub_abs_le_abs_sub (f j) (g j)) 2
  simpa only [sq_abs, Pi.sub_apply] using h

theorem aligned_angular_bound {m : ℕ} (hm : 2048 ≤ 2 * m)
    (s t : SignPattern (by omega)) (η : Fin (2 * m) → ℝ)
    (hs : ∀ j, signedPotential s j = |operator (2 * m) (baseWord (patternSign s)) j|)
    (ht : ∀ j, signedPotential t j = |operator (2 * m) (baseWord (patternSign t)) j|) :
    |(∑ j, (signedPotential s j - signedPotential t j) * η j) / 2| ≤
      6 * (hamming s t : ℝ) * Real.sqrt (meanSquare η) := by
  have hmean : meanSquare (signedPotential s - signedPotential t) ≤
      meanSquare (operator (2 * m) (baseWord (patternSign s)) -
        operator (2 * m) (baseWord (patternSign t))) := by
    simpa only [meanSquare, Pi.sub_apply, hs, ht] using
      meanSquare_abs_sub_le (operator (2 * m) (baseWord (patternSign s)))
        (operator (2 * m) (baseWord (patternSign t)))
  have hroot := (Real.sqrt_le_sqrt hmean).trans (potential_l2_difference hm s t)
  have hp := normalized_pairing_cauchy (show 0 < 2 * m by omega)
    (signedPotential s - signedPotential t) η
  simp only [finitePairing, Pi.sub_apply, Nat.cast_mul, Nat.cast_ofNat] at hp
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hnpos : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  calc
    _ = ((2 * m : ℝ) / 2) *
        |(∑ j, (signedPotential s j - signedPotential t j) * η j) / (2 * m : ℝ)| := by
      rw [abs_div, abs_div, abs_of_pos hnpos]
      norm_num
      field_simp
    _ ≤ ((2 * m : ℝ) / 2) *
        ((12 * (hamming s t : ℝ) / (2 * m : ℝ)) * Real.sqrt (meanSquare η)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hp.trans (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _))
    _ = _ := by field_simp; ring

theorem eventual_near_angular_bound (C₀ : ℝ) :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 0 < m) (s t : SignPattern hm)
      (η : Fin (2 * m) → ℝ),
      deficit hm s ≤ C₀ / (2 * m : ℝ) ^ 2 →
      deficit hm t ≤ C₀ / (2 * m : ℝ) ^ 2 →
      |(∑ j, (signedPotential s j - signedPotential t j) * η j) / 2| ≤
        6 * (hamming s t : ℝ) * Real.sqrt (meanSquare η) := by
  filter_upwards [near_maximum_signs_eventually C₀, eventually_ge_atTop 1024] with m hsign hmN
  intro hm s t η hs ht
  apply aligned_angular_bound (by omega) s t η
  · intro j
    exact (hsign hm s hs j).2
  · intro j
    exact (hsign hm t ht j).2

end
end StructuralNote.FixedSchurNearWordAngular

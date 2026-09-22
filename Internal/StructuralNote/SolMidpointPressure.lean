import StructuralNote.SolScalarGap
import StructuralNote.SolAntipodalMidpoint
import EventualExact.PressureSupport

namespace StructuralNote.SolMidpointPressure

open Erdos1045.EventualExact FourierMultiplier FiniteBox PressureSupport
open FixedDualClassificationKernel SolScalarGap SolAntipodalMidpoint
open FiniteCompressionEnergy
open scoped BigOperators
noncomputable section

theorem halfTurn_ne {m : ℕ} (hm : 0 < m) (i : Fin (2 * m)) : halfTurn hm i ≠ i := by
  intro h
  have hh := halfTurn_lt_iff hm i
  rw [h] at hh
  tauto

/-- Flip the antipodal coordinate pair through its midpoint. -/
def flipPair {m : ℕ} (hm : 0 < m) (f : Fin (2 * m) → ℝ) (i : Fin (2 * m)) :
    Fin (2 * m) → ℝ := f - (2 * f i) • spike hm i

theorem flipPair_bounded {m : ℕ} (hm : 0 < m) {A : ℝ}
    (f : Fin (2 * m) → ℝ) (hfabs : ∀ j, |f j| = A)
    (hfanti : FiniteBox.Antiperiodic hm f) (i j : Fin (2 * m)) :
    |flipPair hm f i j| ≤ A := by
  by_cases hji : j = i
  · subst j
    have hih : i ≠ halfTurn hm i := (halfTurn_ne hm i).symm
    simp only [flipPair, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, spike, point,
      if_neg hih]
    simp only [if_true]
    rw [show f i - 2 * f i * (1 - 0) = -f i by ring, abs_neg, hfabs]
  · by_cases hjh : j = halfTurn hm i
    · subst j
      have hfi := hfanti i
      have hne := halfTurn_ne hm i
      simp only [flipPair, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, spike, point,
        if_neg hne, hfi]
      simp only [if_true]
      rw [show -f i - 2 * f i * (0 - 1) = f i by ring, hfabs]
    · have hih : i ≠ halfTurn hm j := by
        intro h
        have this := congrArg (halfTurn hm) h
        rw [SchurLift.halfTurn_involutive hm] at this
        exact hjh this.symm
      simpa [flipPair, spike, point, hji, hjh] using (hfabs j).le

theorem pairing_spike {m : ℕ} (hm : 0 < m) (g : Fin (2 * m) → ℝ)
    (hg : ∀ j, g (halfTurn hm j) = -g j) (i : Fin (2 * m)) :
    finitePairing (spike hm i) g = 2 * g i := by
  change finitePairing (point i - point (halfTurn hm i)) g = _
  have hsub : finitePairing (point i - point (halfTurn hm i)) g =
      finitePairing (point i) g - finitePairing (point (halfTurn hm i)) g := by
    simp [finitePairing, sub_mul, Finset.sum_sub_distrib]
  rw [hsub, pairing_point, pairing_point, hg i]
  ring

theorem normalized_parallelogram_lower {n : ℕ} (hn : 0 < n)
    (x y : Fin n → ℝ) :
    normalizedBoxEnergy (operator n) (x - y) / 2 ≤
      normalizedBoxEnergy (operator n) x + normalizedBoxEnergy (operator n) y := by
  have hp := boxEnergy_nonneg (positiveSemidefinite n) (x + y)
  have hs := selfAdjoint n
  have hxy := hs x y
  unfold finitePairing at hxy
  unfold normalizedBoxEnergy
  simp only [Fintype.card_fin]
  have hnR : (0 : ℝ) < n := by positivity
  field_simp
  unfold boxEnergy at hp ⊢
  simp only [map_sub, map_add, finitePairing, Pi.sub_apply, Pi.add_apply,
    sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hp ⊢
  simp_rw [mul_add] at hp
  simp only [Finset.sum_add_distrib] at hp
  simp_rw [mul_sub] at ⊢
  simp only [Finset.sum_sub_distrib] at ⊢
  nlinarith [hp, hxy]

theorem competitor_gap {m : ℕ} (hm : 0 < m) (q x : Fin (2 * m) → ℝ)
    (hx : ∀ j, |x j| ≤ amplitude (2 * m)) :
    normalizedBoxEnergy (operator (2 * m)) (x - q) +
        (finitePairing x (operator (2 * m) q) -
          amplitude (2 * m) * ∑ j, |operator (2 * m) q j|) / (2 * m : ℕ) ≤
      G hm q := by
  have hB := energy_le_maximum hm x hx
  change normalizedBoxEnergy (operator (2 * m)) x ≤ B hm at hB
  have he := boxEnergy_sub (selfAdjoint (2 * m)) q x
  have hn : (0 : ℝ) < (2 * m : ℕ) := by positivity
  simp only [G, V, potentialAverage, normalizedBoxEnergy, Fintype.card_fin]
  simp only [normalizedBoxEnergy, Fintype.card_fin] at hB
  have hp : finitePairing q (operator (2 * m) q) =
      2 * boxEnergy (operator (2 * m)) q := by unfold boxEnergy; ring
  have hpair : finitePairing (x - q) (operator (2 * m) q) =
      finitePairing x (operator (2 * m) q) - finitePairing q (operator (2 * m) q) := by
    simp [finitePairing, Finset.sum_sub_distrib, sub_mul]
  rw [hpair, hp] at he
  field_simp at hB ⊢
  nlinarith

/-- Manuscript Lemma 7.1, for the actual multiplier and every real input.
Antiperiodicity is not needed for the inequality, so the statement is stronger. -/
theorem midpoint_pressure {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (i : Fin (2 * m)) :
    2 * amplitude (2 * m) * finiteKernel (2 * m) 0 / (2 * m : ℝ) -
        (2 * m : ℝ) * G hm q / (2 * amplitude (2 * m)) ≤
      |operator (2 * m) q i| := by
  let A := amplitude (2 * m)
  let g := operator (2 * m) q
  let s := patternSign (seedPattern hm)
  let f := roundedBoxVertex A s g
  let f' := flipPair hm f i
  have hA : 0 < A := amplitude_pos (by omega)
  have hs : IsSignVector s := patternSign_is_sign _
  have hfabs : ∀ j, |f j| = A := by
    intro j
    rcases roundedSign_is_sign (x := g j) (hs j) with h | h <;>
      simp [f, roundedBoxVertex, h, abs_of_pos hA]
  have hfanti : FiniteBox.Antiperiodic hm f := by
    exact roundedBoxVertex_antiperiodic (halfTurn hm)
      (patternSign_antiperiodic _) (operator_antiperiodic hm q)
  have hf : ∀ j, |f j| ≤ A := fun j => (hfabs j).le
  have hf' : ∀ j, |f' j| ≤ A := flipPair_bounded hm f hfabs hfanti i
  have hfg : finitePairing f g = A * ∑ j, |g j| := by
    unfold finitePairing
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change A * roundedSign (s j) (g j) * g j = A * |g j|
    rw [mul_assoc, roundedSign_mul (hs j)]
  have hfig : f i * g i = A * |g i| := by
    change A * roundedSign (s i) (g i) * g i = A * |g i|
    rw [mul_assoc, roundedSign_mul (hs i)]
  have hsp := pairing_spike hm g (operator_antiperiodic hm q) i
  have hscalar : finitePairing ((2 * f i) • spike hm i) g = 4 * f i * g i := by
    change (∑ j, (2 * f i * spike hm i j) * g j) = _
    rw [show (∑ j, (2 * f i * spike hm i j) * g j) =
      (2 * f i) * finitePairing (spike hm i) g by
        unfold finitePairing
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring, hsp]
    ring
  have hf'g : finitePairing f' g = A * ∑ j, |g j| - 4 * A * |g i| := by
    have hsub : finitePairing f' g = finitePairing f g -
        finitePairing ((2 * f i) • spike hm i) g := by
      simp [f', flipPair, finitePairing, sub_mul, Finset.sum_sub_distrib]
    rw [hsub, hscalar, hfg]
    nlinarith [hfig]
  have h1 := competitor_gap hm q f hf
  have h2 := competitor_gap hm q f' hf'
  rw [hfg, sub_self, zero_div, add_zero] at h1
  rw [hf'g] at h2
  have hd : (f - q) - (f' - q) = (2 * f i) • spike hm i := by
    funext j
    simp [f', flipPair]
  have hpar := normalized_parallelogram_lower (by omega : 0 < 2 * m) (f - q) (f' - q)
  rw [hd] at hpar
  have hscale : normalizedBoxEnergy (operator (2 * m)) ((2 * f i) • spike hm i) =
      (2 * f i) ^ 2 * normalizedBoxEnergy (operator (2 * m)) (spike hm i) := by
    unfold normalizedBoxEnergy boxEnergy finitePairing
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Fintype.card_fin]
    have hsum : (∑ x, (2 * f i * spike hm i x) *
        (2 * f i * operator (2 * m) (spike hm i) x)) =
        (2 * f i) ^ 2 * ∑ x, spike hm i x * operator (2 * m) (spike hm i) x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hsum]
    ring
  rw [hscale, spike_energy hm i] at hpar
  have hfi2 : (2 * f i) ^ 2 = (2 * A) ^ 2 := by
    nlinarith [sq_abs (f i), hfabs i]
  rw [hfi2] at hpar
  have hn : (0 : ℝ) < (2 * m : ℕ) := by positivity
  have hmR : (0 : ℝ) < m := by positivity
  have hlower : 2 * A ^ 2 * finiteKernel (2 * m) 0 / (m : ℝ) ^ 2 ≤
      normalizedBoxEnergy (operator (2 * m)) (f - q) +
        normalizedBoxEnergy (operator (2 * m)) (f' - q) := by
    field_simp at hpar ⊢
    nlinarith
  dsimp only [A, g] at h1 h2 hlower ⊢
  field_simp at h2 hlower
  ring_nf at h2
  have h2clean : normalizedBoxEnergy (operator (2 * m)) (f' - q) * (2 * (m : ℝ)) -
      4 * amplitude (2 * m) * |operator (2 * m) q i| ≤
      (2 * (m : ℝ)) * G hm q := by
    convert h2 using 1 <;> simp only [Nat.mul_comm, Nat.cast_mul, Nat.cast_ofNat] <;> ring
  have h2' : (m : ℝ) * normalizedBoxEnergy (operator (2 * m)) (f' - q) -
      2 * amplitude (2 * m) * |operator (2 * m) q i| ≤ (m : ℝ) * G hm q := by
    nlinarith [h2clean]
  have h2m := mul_le_mul_of_nonneg_left h2' hmR.le
  have h1m := mul_le_mul_of_nonneg_left h1 (sq_nonneg (m : ℝ))
  have hcore : amplitude (2 * m) ^ 2 * finiteKernel (2 * m) 0 ≤
      (m : ℝ) ^ 2 * G hm q + amplitude (2 * m) * m *
        |operator (2 * m) q i| := by
    nlinarith
  rw [show 2 * amplitude (2 * m) * finiteKernel (2 * m) 0 / (2 * m : ℝ) -
      (2 * m : ℝ) * G hm q / (2 * amplitude (2 * m)) =
      (amplitude (2 * m) ^ 2 * finiteKernel (2 * m) 0 -
        (m : ℝ) ^ 2 * G hm q) / (amplitude (2 * m) * m) by field_simp]
  apply (div_le_iff₀ (mul_pos hA hmR)).2
  nlinarith

end
end StructuralNote.SolMidpointPressure

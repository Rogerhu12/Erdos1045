import EventualExact.AntipodalLogRemainder

/-! The antipodal quartic estimate for the geometric objective, with its actual Schur quadratic. -/

noncomputable section
open scoped BigOperators

namespace Erdos1045.EventualExact.AntipodalLog

open Complex FourierMultiplier SchurSpectrum LocalObjective

theorem periodize_half_periodic {m : ℕ} (hm : 0 < m) (c : Fin (2 * m) → ℂ)
    (hc : HalfPeriodic hm c) : Function.Periodic (periodize (by omega) c) m := by
  intro j
  let i : Fin (2 * m) := ⟨j % (2 * m), Nat.mod_lt _ (by omega)⟩
  have he : (⟨(j + m) % (2 * m), Nat.mod_lt _ (by omega)⟩ : Fin (2 * m)) =
      halfTurn hm i := by
    apply Fin.ext
    simp only [halfTurn, i, Nat.add_mod, Nat.mod_mod]
  change c ⟨(j + m) % (2 * m), Nat.mod_lt _ (by omega)⟩ = c i
  rw [he, hc]

theorem pairPotential_eq_real_sum {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    pairPotential hn c = -(∑ h ∈ (Finset.range n).erase 0,
      ∑ j ∈ Finset.range n, (LocalDFT.pairRatio n (periodize hn c) j h ^ 2).re) / 2 := by
  simp [pairPotential, Complex.div_ofNat_re, ← pow_two, neg_div]

def fourthEnergy (n : ℕ) (u : ℕ → ℂ) : ℝ :=
  (∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n,
    ‖LocalDFT.pairRatio n u j h‖ ^ 4) / 2

theorem geometric_quartic_remainder {m : ℕ} (hm : 2 ≤ m) (c : Fin (2 * m) → ℂ)
    (hc : HalfPeriodic (by omega) c) {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hstep : ∀ j, ‖periodize (by omega) c (j + 1) - periodize (by omega) c j‖ ≤
      η * ‖LocalPhase.regularRoot (2 * m) - 1‖) :
    |logDistanceProduct (2 * m) (perturbedVertices (2 * m) (periodize (by omega) c)) -
      logDistanceProduct (2 * m) (regularVertices (2 * m)) - pairPotential (by omega) c| ≤
      fourthEnergy (2 * m) (periodize (by omega) c) := by
  let u := periodize (by omega : 0 < 2 * m) c
  have hup := periodize_periodic (by omega) c
  have hhalf := periodize_half_periodic (by omega) c hc
  have hlog := pair_log_difference ClosedFourier.geometricSine (by omega) u hup hη hsmall hstep
  have hsum : logDistanceProduct (2 * m) (perturbedVertices (2 * m) u) -
      logDistanceProduct (2 * m) (regularVertices (2 * m)) - pairPotential (by omega) c =
      ∑ h ∈ (Finset.range (2 * m)).erase 0,
        ((∑ j ∈ Finset.range (2 * m), Real.log ‖1 + LocalDFT.pairRatio (2 * m) u j h‖) +
        (∑ j ∈ Finset.range (2 * m), (LocalDFT.pairRatio (2 * m) u j h ^ 2).re) / 2) := by
    rw [hlog, pairPotential_eq_real_sum]
    simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
    dsimp only [u]
    ring
  change |logDistanceProduct (2 * m) (perturbedVertices (2 * m) u) -
    logDistanceProduct (2 * m) (regularVertices (2 * m)) - pairPotential (by omega) c| ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ h ∈ (Finset.range (2 * m)).erase 0,
        |(∑ j ∈ Finset.range (2 * m), Real.log ‖1 + LocalDFT.pairRatio (2 * m) u j h‖) +
        (∑ j ∈ Finset.range (2 * m), (LocalDFT.pairRatio (2 * m) u j h ^ 2).re) / 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h ∈ (Finset.range (2 * m)).erase 0,
        (∑ j ∈ Finset.range (2 * m), ‖LocalDFT.pairRatio (2 * m) u j h‖ ^ 4) / 2 := by
      apply Finset.sum_le_sum
      intro h hh
      apply pair_sum_quartic (by omega) u hhalf h
      intro j
      have hb := LocalMaximum.pair_ratio_bound ClosedFourier.geometricSine
        (by omega) u hup hη hstep hh j
      linarith
    _ = fourthEnergy (2 * m) u := by rw [fourthEnergy, Finset.sum_div]

theorem fourthEnergy_le {n : ℕ} (u : ℕ → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ h ∈ (Finset.range n).erase 0, ∀ j, ‖LocalDFT.pairRatio n u j h‖ ≤ δ) :
    fourthEnergy n u ≤ δ ^ 2 * LocalDFT.energyA n u := by
  unfold fourthEnergy LocalDFT.energyA
  rw [← mul_div_assoc, Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum
  intro h hh
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [Complex.normSq_eq_norm_sq]
  have hs := (sq_le_sq₀ (norm_nonneg _) hδ).2 (hbound h hh j)
  nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg ‖LocalDFT.pairRatio n u j h‖)]

/-- An explicit form of manuscript (4.13): the error is at most 4 eta^2 A(c).
For eta=O(1/n) and bounded A(c), this is uniformly O(1/n^2). -/
theorem geometric_log_error_le {m : ℕ} (hm : 2 ≤ m) (c : Fin (2 * m) → ℂ)
    (hc : HalfPeriodic (by omega) c) {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hstep : ∀ j, ‖periodize (by omega) c (j + 1) - periodize (by omega) c j‖ ≤
      η * ‖LocalPhase.regularRoot (2 * m) - 1‖) :
    |logDistanceProduct (2 * m) (perturbedVertices (2 * m) (periodize (by omega) c)) -
      logDistanceProduct (2 * m) (regularVertices (2 * m)) - pairPotential (by omega) c| ≤
      4 * η ^ 2 * pairEnergy (by omega) c := by
  apply (geometric_quartic_remainder hm c hc hη hsmall hstep).trans
  have hb := fourthEnergy_le (periodize (by omega) c) (by positivity : 0 ≤ 2 * η)
    (fun h hh j => LocalMaximum.pair_ratio_bound ClosedFourier.geometricSine (by omega)
      _ (periodize_periodic _ _) hη hstep hh j)
  simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, pairEnergy] using hb

end Erdos1045.EventualExact.AntipodalLog

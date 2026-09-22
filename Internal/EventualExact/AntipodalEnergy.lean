import EventualExact.AntipodalDecomposition
import EventualExact.AntipodalLogRemainder

/-! Orthogonality of the actual antipodal splitting for both geometric energies. -/

namespace Erdos1045.EventualExact.AntipodalDecomposition

open Complex FourierMultiplier SchurLift SchurSpectrum
open scoped BigOperators
noncomputable section

def evenSequence (m : ℕ) (u : ℕ → ℂ) (j : ℕ) : ℂ := (u j + u (j + m)) / 2

def oddSequence (m : ℕ) (u : ℕ → ℂ) (j : ℕ) : ℂ := (u j - u (j + m)) / 2

theorem evenSequence_periodic (m : ℕ) (u : ℕ → ℂ) (hu : Function.Periodic u (2 * m)) :
    Function.Periodic (evenSequence m u) m := by
  intro j
  unfold evenSequence
  rw [show j + m + m = j + 2 * m by omega, hu]
  ring

theorem oddSequence_antiperiodic (m : ℕ) (u : ℕ → ℂ) (hu : Function.Periodic u (2 * m)) (j : ℕ) :
    oddSequence m u (j + m) = -oddSequence m u j := by
  unfold oddSequence
  rw [show j + m + m = j + 2 * m by omega, hu]
  ring

theorem oddSequence_periodic (m : ℕ) (u : ℕ → ℂ) (hu : Function.Periodic u (2 * m)) :
    Function.Periodic (oddSequence m u) (2 * m) := by
  intro j
  rw [show j + 2 * m = (j + m) + m by omega, oddSequence_antiperiodic m u hu,
    oddSequence_antiperiodic m u hu, neg_neg]

theorem sum_half_shift {α : Type*} [AddCommMonoid α] {m : ℕ} (hm : 0 < m)
    (f : ℕ → α) (hf : Function.Periodic f (2 * m)) :
    (∑ j ∈ Finset.range (2 * m), f (j + m)) = ∑ j ∈ Finset.range (2 * m), f j := by
  have hmod (j : Fin (2 * m)) : f (halfTurn hm j) = f (j.val + m) :=
    (CyclicAngles.periodic_mod f hf (j.val + m)).symm
  have he := Equiv.sum_comp (Equiv.ofBijective (halfTurn hm) (halfTurn_involutive hm).bijective)
    (fun j : Fin (2 * m) => f j)
  change (∑ j : Fin (2 * m), f (halfTurn hm j)) = ∑ j : Fin (2 * m), f j at he
  simp_rw [hmod] at he
  rwa [Fin.sum_univ_eq_sum_range (fun j => f (j + m)), Fin.sum_univ_eq_sum_range f] at he

theorem pairRatio_shift {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) (j h : ℕ) :
    LocalDFT.pairRatio (2 * m) (fun k => u (k + m)) j h =
      -LocalDFT.pairRatio (2 * m) u (j + m) h := by
  unfold LocalDFT.pairRatio
  rw [show j + m + h = (j + h) + m by omega,
    pow_add _ (j + h) m, pow_add _ j m, root_halfTurn hm]
  simp only [mul_neg_one]
  rw [show -LocalPhase.regularRoot (2 * m) ^ (j + h) - -LocalPhase.regularRoot (2 * m) ^ j =
    -(LocalPhase.regularRoot (2 * m) ^ (j + h) - LocalPhase.regularRoot (2 * m) ^ j) by ring,
    div_neg, neg_neg]

theorem pairRatio_evenSequence {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) (j h : ℕ) :
    LocalDFT.pairRatio (2 * m) (evenSequence m u) j h =
      (LocalDFT.pairRatio (2 * m) u j h - LocalDFT.pairRatio (2 * m) u (j + m) h) / 2 := by
  rw [show LocalDFT.pairRatio (2 * m) u (j + m) h =
      -LocalDFT.pairRatio (2 * m) (fun k => u (k + m)) j h by rw [pairRatio_shift hm, neg_neg]]
  simp only [LocalDFT.pairRatio, evenSequence]
  ring

theorem pairRatio_oddSequence {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) (j h : ℕ) :
    LocalDFT.pairRatio (2 * m) (oddSequence m u) j h =
      (LocalDFT.pairRatio (2 * m) u j h + LocalDFT.pairRatio (2 * m) u (j + m) h) / 2 := by
  rw [show LocalDFT.pairRatio (2 * m) u (j + m) h =
      -LocalDFT.pairRatio (2 * m) (fun k => u (k + m)) j h by rw [pairRatio_shift hm, neg_neg]]
  simp only [LocalDFT.pairRatio, oddSequence]
  ring

theorem normSq_halves (x y : ℂ) :
    normSq ((x - y) / 2) + normSq ((x + y) / 2) = (normSq x + normSq y) / 2 := by
  simp only [normSq_div, normSq_add, normSq_sub]
  norm_num
  ring

theorem imSq_halves (x y : ℂ) :
    (((x - y) / 2).im) ^ 2 + (((x + y) / 2).im) ^ 2 = (x.im ^ 2 + y.im ^ 2) / 2 := by
  simp only [Complex.div_ofNat_im, sub_im, add_im]
  ring

theorem ratio_square_split {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (h : ℕ) :
    (∑ j ∈ Finset.range (2 * m), normSq (LocalDFT.pairRatio (2 * m) (evenSequence m u) j h)) +
      (∑ j ∈ Finset.range (2 * m), normSq (LocalDFT.pairRatio (2 * m) (oddSequence m u) j h)) =
        ∑ j ∈ Finset.range (2 * m), normSq (LocalDFT.pairRatio (2 * m) u j h) := by
  have hp := AntipodalLog.pairRatio_periodic (by omega) u hu h
  have hs := sum_half_shift hm (fun j => normSq (LocalDFT.pairRatio (2 * m) u j h))
    (fun j => congrArg normSq (hp j))
  rw [← Finset.sum_add_distrib]
  simp_rw [pairRatio_evenSequence hm, pairRatio_oddSequence hm, normSq_halves]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hs]
  ring

theorem energyA_split {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) (hu : Function.Periodic u (2 * m)) :
    LocalDFT.energyA (2 * m) (evenSequence m u) + LocalDFT.energyA (2 * m) (oddSequence m u) =
      LocalDFT.energyA (2 * m) u := by
  unfold LocalDFT.energyA
  rw [← add_div, ← Finset.sum_add_distrib]
  simp_rw [ratio_square_split hm u hu]

theorem energyB_split {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) (hu : Function.Periodic u (2 * m)) :
    LocalDFT.energyB (2 * m) (evenSequence m u) + LocalDFT.energyB (2 * m) (oddSequence m u) =
      LocalDFT.energyB (2 * m) u := by
  have hp := AntipodalLog.pairRatio_periodic (by omega) u hu 1
  have hs := sum_half_shift hm (fun j => (LocalDFT.pairRatio (2 * m) u j 1).im ^ 2)
    (fun j => congrArg (fun z : ℂ => z.im ^ 2) (hp j))
  unfold LocalDFT.energyB
  rw [← Finset.sum_add_distrib]
  simp_rw [pairRatio_evenSequence hm, pairRatio_oddSequence hm, imSq_halves]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hs]
  ring

theorem even_energyA_le {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) (hu : Function.Periodic u (2 * m)) :
    LocalDFT.energyA (2 * m) (evenSequence m u) ≤ LocalDFT.energyA (2 * m) u := by
  have hs := energyA_split hm u hu
  linarith [LocalMaximum.energyA_nonneg (2 * m) (oddSequence m u)]

theorem odd_energyA_le {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) (hu : Function.Periodic u (2 * m)) :
    LocalDFT.energyA (2 * m) (oddSequence m u) ≤ LocalDFT.energyA (2 * m) u := by
  have hs := energyA_split hm u hu
  linarith [LocalMaximum.energyA_nonneg (2 * m) (evenSequence m u)]

theorem even_energyB_le {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) (hu : Function.Periodic u (2 * m)) :
    LocalDFT.energyB (2 * m) (evenSequence m u) ≤ LocalDFT.energyB (2 * m) u := by
  have hs := energyB_split hm u hu
  linarith [LocalMaximum.energyB_nonneg (2 * m) (oddSequence m u)]

theorem evenSequence_mean_zero {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) (hmean : (∑ j ∈ Finset.range (2 * m), u j) = 0) :
    (∑ j ∈ Finset.range (2 * m), evenSequence m u j) = 0 := by
  simp only [evenSequence, ← Finset.sum_div, Finset.sum_add_distrib, sum_half_shift hm u hu,
    hmean, add_zero, zero_div]

theorem evenSequence_constraint_energy {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) :
    SchurLiftBounds.meanSquare (fun j : Fin (2 * m) =>
      -(2 * m : ℝ) * (LocalDFT.pairRatio (2 * m) (evenSequence m u) j 1).im) =
      (2 * m : ℝ) * LocalDFT.energyB (2 * m) (evenSequence m u) := by
  unfold SchurLiftBounds.meanSquare LocalDFT.energyB
  simp_rw [mul_pow, neg_sq]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range
    (fun j => (LocalDFT.pairRatio (2 * m) (evenSequence m u) j 1).im ^ 2)]
  push_cast
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

end
end Erdos1045.EventualExact.AntipodalDecomposition

import StructuralNote.MatchingActivityActualChartEntry
import StructuralNote.SolMidpointPressure
import StructuralNote.FiniteBoxEnergySymmetry

/-! The exact algebraic bridge from pressure-sign alignment to finite-box
word deficit. -/

namespace StructuralNote.MatchingActivityActualWordDeficit

open Erdos1045.EventualExact FourierMultiplier FiniteBox
open FixedDualClassificationFinite SolScalarGap
open scoped BigOperators
noncomputable section

def PressureAligned {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (s : SignPattern hm) : Prop :=
  ∀ j, patternSign s j * operator (2 * m) q j =
    |operator (2 * m) q j|

theorem pairing_vertex_eq_abs_sum {m : ℕ} (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) (s : SignPattern hm)
    (halign : PressureAligned hm q s) :
    finitePairing (vertex (amplitude (2 * m)) s) (operator (2 * m) q) =
      amplitude (2 * m) * ∑ j, |operator (2 * m) q j| := by
  unfold finitePairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [FiniteBox.vertex, boxVertex]
  rw [mul_assoc, halign j]

/-- For a word aligned with the pressure of `q`, the scalar gap is exactly its
finite-box deficit plus the nonnegative Schur energy of the discrepancy. -/
theorem gap_eq_deficit_add_energy {m : ℕ} (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) (s : SignPattern hm)
    (halign : PressureAligned hm q s) :
    G hm q = deficit hm s +
      normalizedBoxEnergy (operator (2 * m))
        (vertex (amplitude (2 * m)) s - q) := by
  have hpair := pairing_vertex_eq_abs_sum hm q s halign
  have hsub := boxEnergy_sub (selfAdjoint (2 * m)) q
    (vertex (amplitude (2 * m)) s)
  have hn : (0 : ℝ) < (2 * m : ℕ) := by positivity
  have hqq : finitePairing q (operator (2 * m) q) =
      2 * boxEnergy (operator (2 * m)) q := by
    unfold boxEnergy
    ring
  have hcross : finitePairing (vertex (amplitude (2 * m)) s - q)
      (operator (2 * m) q) =
      amplitude (2 * m) * ∑ j, |operator (2 * m) q j| -
        2 * boxEnergy (operator (2 * m)) q := by
    calc
      _ = finitePairing (vertex (amplitude (2 * m)) s)
          (operator (2 * m) q) - finitePairing q (operator (2 * m) q) := by
        simp only [finitePairing, Pi.sub_apply, sub_mul,
          Finset.sum_sub_distrib]
      _ = _ := by rw [hpair, hqq]
  have hvertex : vertex (amplitude (2 * m)) s - q =
      -(q - vertex (amplitude (2 * m)) s) := by
    funext j
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  have henergy_sym :
      boxEnergy (operator (2 * m))
          (vertex (amplitude (2 * m)) s - q) =
        boxEnergy (operator (2 * m))
          (q - vertex (amplitude (2 * m)) s) := by
    rw [hvertex]
    unfold boxEnergy finitePairing
    simp only [map_neg, Pi.neg_apply]
    ring
  rw [hvertex]
  change G hm q = deficit hm s +
    normalizedBoxEnergy (operator (2 * m))
      (fun j => -(q - vertex (amplitude (2 * m)) s) j)
  rw [FiniteBoxEnergySymmetry.normalizedBoxEnergy_neg (by omega)]
  unfold G V potentialAverage deficit normalizedBoxEnergy
  simp only [Fintype.card_fin]
  rw [hcross] at hsub
  rw [henergy_sym] at hsub
  field_simp
  field_simp at hsub
  nlinarith

theorem deficit_le_gap_of_aligned {m : ℕ} (hm : 0 < m)
    (q : Fin (2 * m) → ℝ) (s : SignPattern hm)
    (halign : PressureAligned hm q s) :
    deficit hm s ≤ G hm q := by
  rw [gap_eq_deficit_add_energy hm q s halign]
  exact le_add_of_nonneg_right
    (div_nonneg (boxEnergy_nonneg (positiveSemidefinite (2 * m)) _)
      (by positivity))

end
end StructuralNote.MatchingActivityActualWordDeficit

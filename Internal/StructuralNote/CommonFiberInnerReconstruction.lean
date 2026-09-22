import StructuralNote.CommonFiberInnerReconstructionBase
import StructuralNote.CommonFiberInnerReconstructionPath

/-! Actual inner-ball reconstruction around the canonical Schur lift. The
energy remainder is uniform over all box words, without a first-moment premise. -/

namespace StructuralNote.CommonFiberInnerReconstruction

open Erdos1045 Erdos1045.EventualExact Complex Filter FourierMultiplier
open SchurLift SchurSpectrum BoxLensLift QuadraticStability
open CommonTangentialParameters CommonFiberGeometry CommonFiberSmooth CommonFiberCanonical
open CommonFiberDifferentialEstimate
open scoped BigOperators Topology
noncomputable section

def antiWord {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (j : Fin (2 * m)) : ℝ :=
  (if j.val < m then 1 else -1) * σ ⟨j.val % m, Nat.mod_lt _ hm⟩

theorem antiWord_halfTurn {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) :
    FiniteBox.Antiperiodic hm (antiWord hm σ) := by
  intro j
  have he : (halfTurn hm j).val % m = j.val % m := by
    simp only [halfTurn]
    rw [Nat.mod_mod_of_dvd _ (show m ∣ 2 * m from ⟨2, by omega⟩), Nat.add_mod_right]
  simp only [antiWord, he, FiniteBox.halfTurn_lt_iff]
  by_cases hj : j.val < m <;> simp [hj]

theorem antiWord_halfIndex {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (j : Fin m) :
    antiWord hm σ (BoxLensLift.halfIndex j) = σ j := by
  simp [antiWord, BoxLensLift.halfIndex, j.isLt, Nat.mod_eq_of_lt j.isLt]

def boxInput {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) : Fin (2 * m) → ℝ :=
  fun j => FiniteBox.amplitude (2 * m) * antiWord hm σ j

theorem boxInput_antiperiodic {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) :
    FiniteBox.Antiperiodic hm (boxInput hm σ) := by
  intro j
  simp only [boxInput, antiWord_halfTurn hm σ j, mul_neg]

theorem boxInput_mem_Q {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (hσ : ∀ j, |σ j| ≤ 1) :
    boxInput hm σ ∈ FiniteBox.Q hm := by
  refine ⟨boxInput_antiperiodic hm σ, ?_⟩
  intro j
  have hA := (FiniteBox.amplitude_pos (show 2 ≤ 2 * m by omega)).le
  have hs : |antiWord hm σ j| ≤ 1 := by
    unfold antiWord
    split <;> simpa using hσ ⟨j.val % m, Nat.mod_lt _ hm⟩
  simpa only [boxInput, abs_mul, abs_of_nonneg hA, mul_one] using
    mul_le_mul_of_nonneg_left hs hA

theorem halfWord_boxInput {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) :
    halfWord (boxInput hm σ) = σ := by
  funext j
  simp only [halfWord, coordinate, boxInput, antiWord_halfIndex]
  exact mul_div_cancel_left₀ (σ j) (FiniteBox.amplitude_pos (show 2 ≤ 2 * m by omega)).ne'

def reconstructionR {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (x : FreeParameters m) : Fin (2 * m) → ℂ :=
  centerAt hm σ x - canonicalLift (boxInput hm σ) - x.2

theorem reconstruction_identity {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (x : FreeParameters m) :
    centerAt hm σ x = canonicalLift (boxInput hm σ) + x.2 + reconstructionR hm σ x := by
  unfold reconstructionR
  abel

theorem eventual_inner_reconstruction_energy : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (σ : Fin m → ℝ) (x : FreeParameters m) (K : ℝ),
    (∀ j, |σ j| ≤ 1) → x ∈ domain hm →
    pairEnergy (by omega) (fun j => (x.1 j : ℂ)) + pairEnergy (by omega) x.2 ≤ K / (2 * m : ℝ) ^ 2 →
    pairEnergy (by omega) (reconstructionR hm σ x) ≤
      (8000000000 * K + 262144) / (2 * m : ℝ) ^ 3 := by
  filter_upwards [eventual_inner_path_remainder, eventually_ge_atTop 128] with m hpath hm128
  intro hm σ x K hσ hx hK
  have hp := hpath hm σ x K hσ hx hK
  have hb := canonical_zero_schur_energy hm128 (boxInput hm σ) (boxInput_mem_Q hm σ hσ)
  rw [halfWord_boxInput] at hb
  change pairEnergy (by omega) (centerAt hm σ 0 - canonicalLift (boxInput hm σ)) ≤ _ at hb
  have he : reconstructionR hm σ x = (centerAt hm σ x - centerAt hm σ 0 - x.2) +
      (centerAt hm σ 0 - canonicalLift (boxInput hm σ)) := by
    unfold reconstructionR
    abel
  rw [he]
  have ha := pairEnergy_add_le (by omega : 0 < 2 * m)
    (centerAt hm σ x - centerAt hm σ 0 - x.2)
    (centerAt hm σ 0 - canonicalLift (boxInput hm σ))
  have hn : (2 : ℝ) ≤ 2 * m := by exact_mod_cast (show 2 ≤ 2 * m by omega)
  have hpow : (2 * m : ℝ) ^ 3 ≤ (2 * m : ℝ) ^ 4 := by
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 * m by positivity) 3]
  have hb' := hb.trans (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 131072)
    (by positivity : (0 : ℝ) < (2 * m : ℝ) ^ 3) hpow)
  calc
    _ ≤ 2 * (4000000000 * K / (2 * m : ℝ) ^ 3) + 2 * (131072 / (2 * m : ℝ) ^ 3) := by linarith
    _ = _ := by ring

theorem eventual_reconstruction_halfPeriodic : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (σ : Fin m → ℝ) (x : FreeParameters m),
    (∀ j, |σ j| ≤ 1) → x ∈ domain hm → HalfPeriodic hm (reconstructionR hm σ x) := by
  filter_upwards [eventual_size_conditions] with m hs
  intro hm σ x hσ hx j
  have hc := center_halfPeriodic hm x.1 x.2 σ (CommonFiberCanonical.root hm σ x)
    (root_spec hs.1 σ x hs.2.1 hσ hx).2 j
  have hf := canonicalLift_halfTurn (show 2 ≤ m by omega) (boxInput hm σ) (boxInput_antiperiodic hm σ) j
  simp only [reconstructionR, centerAt, Pi.sub_apply, hc, hf, hx.2.2.1.1 j]

theorem reconstruction_mean_zero {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (x : FreeParameters m)
    (hx : x ∈ domain hm) : (∑ j, reconstructionR hm σ x j) = 0 := by
  simp only [reconstructionR, centerAt, Pi.sub_apply, Finset.sum_sub_distrib,
    center_mean_zero, canonicalLift_mean_zero (n := 2 * m) (by omega), hx.2.2.1.2.1, sub_self]

end
end StructuralNote.CommonFiberInnerReconstruction

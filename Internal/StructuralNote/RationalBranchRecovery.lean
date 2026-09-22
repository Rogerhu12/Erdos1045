import StructuralNote.RationalAngleBranch

/-! The two explicit harmonic coordinates (10.8) and the actual reconstruction
of the free tangential vector. The two closure identities are proved from the
midpoint Gram matrix, rather than imposed as branch-selection assumptions. -/

namespace StructuralNote.RationalBranchRecovery

open Erdos1045.EventualExact LensClosure CommonTangentialParameters
open scoped BigOperators
noncomputable section

def correction {m : ℕ} (t : Fin m → ℝ) : ℂ :=
  ⟨2 / m * ∑ j, t j * Real.cos (midpoint m j),
   2 / m * ∑ j, t j * Real.sin (midpoint m j)⟩

def freeCoordinates {m : ℕ} (t : Fin m → ℝ) (j : Fin m) : ℝ :=
  t j - harmonicFunctional (midpoint m j) (correction t)

def freeVector {m : ℕ} (hm : 0 < m) (t : Fin m → ℝ) : Fin (2 * m) → ℂ :=
  reconstruct hm (freeCoordinates t)

theorem freeCoordinates_closed {m : ℕ} (hm : 2 ≤ m) (t : Fin m → ℝ) : Closed (freeCoordinates t) := by
  have hmc : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  obtain ⟨hc, hs, hcs⟩ := midpoint_gram hm
  constructor
  · calc
      (∑ j, freeCoordinates t j * Real.cos (midpoint m j)) =
          (∑ j, t j * Real.cos (midpoint m j)) -
          (correction t).re * (∑ j, Real.cos (midpoint m j) ^ 2) -
          (correction t).im * (∑ j, Real.cos (midpoint m j) * Real.sin (midpoint m j)) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp only [freeCoordinates, harmonicFunctional_apply]
        ring
      _ = 0 := by rw [hc, hcs]; dsimp [correction]; field_simp; ring
  · calc
      (∑ j, freeCoordinates t j * Real.sin (midpoint m j)) =
          (∑ j, t j * Real.sin (midpoint m j)) -
          (correction t).re * (∑ j, Real.cos (midpoint m j) * Real.sin (midpoint m j)) -
          (correction t).im * (∑ j, Real.sin (midpoint m j) ^ 2) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp only [freeCoordinates, harmonicFunctional_apply]
        ring
      _ = 0 := by rw [hs, hcs]; dsimp [correction]; field_simp; ring

theorem heightParameter_freeCoordinates {m : ℕ} (t : Fin m → ℝ) :
    heightParameter (freeCoordinates t) (correction t) = t := by
  funext j
  simp [heightParameter, freeCoordinates]

theorem freeVector_mem {m : ℕ} (hm : 2 ≤ m) (t : Fin m → ℝ) :
    ParameterSpace (by omega) (freeVector (by omega) t) :=
  reconstruct_mem (by omega) _ (freeCoordinates_closed hm t)

theorem coordinates_freeVector {m : ℕ} (hm : 2 ≤ m) (t : Fin m → ℝ) :
    coordinates (by omega) (freeVector (by omega) t) = freeCoordinates t :=
  coordinates_reconstruct (by omega) _ (freeCoordinates_closed hm t)

theorem heightParameter_freeVector {m : ℕ} (hm : 2 ≤ m) (t : Fin m → ℝ) :
    heightParameter (coordinates (by omega) (freeVector (by omega) t)) (correction t) = t := by
  rw [coordinates_freeVector hm t, heightParameter_freeCoordinates]

theorem correction_heightParameter {m : ℕ} (hm : 2 ≤ m) (ν : Fin m → ℝ)
    (hν : Closed ν) (ξ : ℂ) : correction (heightParameter ν ξ) = ξ := by
  have hmc : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  obtain ⟨hc, hs, hcs⟩ := midpoint_gram hm
  have hreal : (∑ j, heightParameter ν ξ j * Real.cos (midpoint m j)) =
      (∑ j, ν j * Real.cos (midpoint m j)) + ξ.re * (∑ j, Real.cos (midpoint m j) ^ 2) +
        ξ.im * (∑ j, Real.cos (midpoint m j) * Real.sin (midpoint m j)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [heightParameter, harmonicFunctional_apply]
    ring
  have himag : (∑ j, heightParameter ν ξ j * Real.sin (midpoint m j)) =
      (∑ j, ν j * Real.sin (midpoint m j)) + ξ.re * (∑ j, Real.cos (midpoint m j) * Real.sin (midpoint m j)) +
        ξ.im * (∑ j, Real.sin (midpoint m j) ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [heightParameter, harmonicFunctional_apply]
    ring
  apply Complex.ext
  · change 2 / m * (∑ j, heightParameter ν ξ j * Real.cos (midpoint m j)) = ξ.re
    rw [hreal, hν.1, hc, hcs]
    field_simp
    ring
  · change 2 / m * (∑ j, heightParameter ν ξ j * Real.sin (midpoint m j)) = ξ.im
    rw [himag, hν.2, hs, hcs]
    field_simp
    ring

theorem decomposition_unique {m : ℕ} (hm : 2 ≤ m) (t ν : Fin m → ℝ) (ξ : ℂ)
    (hν : Closed ν) (he : heightParameter ν ξ = t) :
    ξ = correction t ∧ ν = freeCoordinates t := by
  have hξ : correction t = ξ := he ▸ correction_heightParameter hm ν hν ξ
  refine ⟨hξ.symm, ?_⟩
  funext j
  have hj := congrFun he j
  rw [← hξ, heightParameter] at hj
  unfold freeCoordinates
  linarith

open RationalAngleBranch

theorem rational_closure_eq_recovered_closure {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (hX : SmallWindow X) (hσ : ∀ j, σ j ^ 2 = 1) :
    RationalConfiguration.closure (by omega) σ X =
      LensClosure.closure (phase (by omega) X) (fun j => 2 * Real.cos (halfAngle (by omega) X j))
        σ (coordinates (by omega) (freeVector (by omega) (tangential (by omega) σ X)))
        (correction (tangential (by omega) σ X)) := by
  unfold LensClosure.closure RationalConfiguration.closure
  rw [heightParameter_freeVector hm]
  apply Finset.sum_congr rfl
  intro j _
  exact smallWindow_increment_eq_lens hm σ X hX j (hσ j)

end
end StructuralNote.RationalBranchRecovery

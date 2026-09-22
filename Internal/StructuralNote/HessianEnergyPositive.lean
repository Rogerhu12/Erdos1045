import StructuralNote.HessianVelocityEnergy

/-! The fixed-mean gauge removes all zero directions of the chord energy. -/

namespace StructuralNote.HessianEnergyPositive

open Erdos1045 Erdos1045.EventualExact Complex SchurSpectrum HessianVelocityEnergy
open scoped BigOperators
noncomputable section

theorem energy_zero_iff {n : ℕ} (hn : 2 ≤ n) (g : Fin n → ℂ) (hg : ∑ j, g j = 0) :
    pairEnergy (by omega) g = 0 ↔ g = 0 := by
  constructor
  · intro hz
    have hp := mean_zero_mass hn g hg
    rw [hz, mul_zero] at hp
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hs : (∑ j, normSq (g j)) = 0 := by
      have hh : (∑ j, normSq (g j)) ≤ 0 := by
        nlinarith only [hp, hnR]
      exact le_antisymm hh (Finset.sum_nonneg (fun j _ => normSq_nonneg _))
    funext j
    have hj : normSq (g j) ≤ ∑ i, normSq (g i) :=
      Finset.single_le_sum (fun i _ => normSq_nonneg (g i)) (Finset.mem_univ j)
    rw [hs] at hj
    exact normSq_eq_zero.mp (le_antisymm hj (normSq_nonneg _))
  · intro hz
    subst g
    simp only [pairEnergy, LocalDFT.energyA, LocalDFT.pairRatio, periodize, Pi.zero_apply,
      sub_self, zero_div, normSq_zero, Finset.sum_const_zero]

theorem total_energy_pos {n : ℕ} (hn : 2 ≤ n) (η : Fin n → ℝ) (h : Fin n → ℂ)
    (hη : ∑ j, (η j : ℂ) = 0) (hh : ∑ j, h j = 0) (hne : η ≠ 0 ∨ h ≠ 0) :
    0 < pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h := by
  have he := pairEnergy_nonneg (by omega : 0 < n) (fun j => (η j : ℂ))
  have ha := pairEnergy_nonneg (by omega : 0 < n) h
  by_contra hnpos
  have hzero : pairEnergy (by omega) (fun j => (η j : ℂ)) = 0 ∧ pairEnergy (by omega) h = 0 := by
    constructor <;> linarith
  have hηzero := (energy_zero_iff hn (fun j => (η j : ℂ)) hη).mp hzero.1
  have hη' : η = 0 := by
    funext j
    have hj := congrFun hηzero j
    change (η j : ℂ) = 0 at hj
    change η j = 0
    exact_mod_cast hj
  exact hne.elim (fun hh => hh hη') (fun hh' => hh' ((energy_zero_iff hn h hh).mp hzero.2))

end
end StructuralNote.HessianEnergyPositive

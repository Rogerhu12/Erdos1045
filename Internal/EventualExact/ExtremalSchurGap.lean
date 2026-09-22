import EventualExact.AntipodalEnergy
import EventualExact.ExtremalEdgeBudget
import EventualExact.SchurPressureGap
import EventualExact.SchurEnergyBounds

/-! A strict Schur-potential gap for the genuine antipodal center constraint of extremizers. -/

namespace Erdos1045.EventualExact.ExtremalSchurGap

open Filter Configuration HullGeometry CommonLocalization
open AntipodalDecomposition FourierMultiplier SchurLiftBounds SchurSpectrum
open ExtremalEnergyBound SchurOperatorBounds
open scoped Topology
noncomputable section

/-- The actual constraint of the even center column, in the retained normalized coordinates. -/
def evenConstraint (m : ℕ) (u : ℕ → ℂ) : Fin (2 * m) → ℝ := fun j =>
  -(2 * m : ℝ) * (LocalDFT.pairRatio (2 * m) (evenSequence m u) j 1).im

theorem evenConstraint_meanSquare {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ) :
    meanSquare (evenConstraint m u) =
      (2 * m : ℝ) * LocalDFT.energyB (2 * m) (evenSequence m u) :=
  evenSequence_constraint_energy hm u

theorem evenConstraint_budget {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m)) :
    meanSquare (evenConstraint m u) ≤ (2 * m : ℝ) * LocalDFT.energyB (2 * m) u := by
  rw [evenConstraint_meanSquare hm u]
  exact mul_le_mul_of_nonneg_left (even_energyB_le hm u hu) (by positivity)

theorem evenConstraint_schur_bounds {m : ℕ} (hm : 2048 ≤ 2 * m) (u : ℕ → ℂ)
    (hu : Function.Periodic u (2 * m))
    (hB : (2 * m : ℝ) * LocalDFT.energyB (2 * m) u ≤
      3 * Real.pi ^ 2 / 2 + Real.pi ^ 2 / 16) :
    ‖operator (2 * m) (evenConstraint m u)‖ ≤ 7 * Real.pi / 8 ∧
      pairEnergy (by omega) (fun j => (operator (2 * m) (evenConstraint m u) j : ℂ)) +
        pairEnergy (by omega) (fun j => ((|operator (2 * m) (evenConstraint m u) j| : ℝ) : ℂ)) ≤
          8 * Real.pi ^ 2 * ((2 * m : ℕ) : ℝ) ^ 2 := by
  have hmass := (evenConstraint_budget (by omega) u hu).trans hB
  constructor
  · exact operator_sup_le_seven_eighths_pi hm _ le_rfl hmass
  · have hmass' : meanSquare (evenConstraint m u) ≤ 2 * Real.pi ^ 2 := by
      nlinarith [sq_nonneg Real.pi]
    calc
      _ ≤ 4 * ((2 * m : ℕ) : ℝ) ^ 2 * meanSquare (evenConstraint m u) :=
        operator_energy_smoothing (by omega) (even_two_mul m) _
      _ ≤ 4 * ((2 * m : ℕ) : ℝ) ^ 2 * (2 * Real.pi ^ 2) :=
        mul_le_mul_of_nonneg_left hmass' (by positivity)
      _ = _ := by ring

/-- Every actual even-order diameter-extremal sequence has these same coordinates,
the sharp asymptotic center-constraint budget, and a fixed strict Schur gap. -/
theorem diameter_sequence_schur_gap {M : ℕ → ℕ} (hM2 : ∀ k, 2 ≤ M k)
    (hM : Tendsto M atTop atTop) (z : ∀ k, Points (2 * M k))
    (hz : ∀ k, ExtremalNormalization.DiameterExtremal (z k)) :
    ∃ (σ : ∀ k, Equiv.Perm (Fin (2 * M k))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ),
      Tendsto η atTop (𝓝 0) ∧
      (∀ᶠ k in atTop,
        NormalizedRelativeEdgeModel (z k) (σ k) (α k) (β k) (u k) (η k) ∧
        boundaryLength (z k ∘ σ k) ≤ hullPerimeter (z k) ∧
        totalEnergy (2 * M k) (u k) ≤ 32 * Real.pi ^ 2 ∧
        LocalDFT.positiveQuadratic (2 * M k) (u k) ≤
          diameterBudget (2 * M k) + 128 * Real.pi ^ 2 * η k ∧
        (2 * M k : ℝ) * LocalDFT.energyB (2 * M k) (u k) ≤ edgeBudget (2 * M k) (η k) ∧
        meanSquare (evenConstraint (M k) (u k)) ≤ edgeBudget (2 * M k) (η k) ∧
        ‖operator (2 * M k) (evenConstraint (M k) (u k))‖ ≤ 7 * Real.pi / 8 ∧
        pairEnergy (by have := hM2 k; omega)
            (fun j => (operator (2 * M k) (evenConstraint (M k) (u k)) j : ℂ)) +
          pairEnergy (by have := hM2 k; omega)
            (fun j => ((|operator (2 * M k) (evenConstraint (M k) (u k)) j| : ℝ) : ℂ)) ≤
              8 * Real.pi ^ 2 * ((2 * M k : ℕ) : ℝ) ^ 2) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        meanSquare (evenConstraint (M k) (u k)) ≤ 3 * Real.pi ^ 2 / 2 + ε) := by
  have hN4 (k : ℕ) : 4 ≤ 2 * M k := by have := hM2 k; omega
  have hN : Tendsto (fun k => 2 * M k) atTop atTop :=
    tendsto_atTop_mono (fun k => by omega : ∀ k, M k ≤ 2 * M k) hM
  obtain ⟨σ, α, β, u, η, hη, hmodel, hedge⟩ :=
    diameter_sequence_edge_energy hN4 hN z hz
  have hlarge : ∀ᶠ k in atTop, 2048 ≤ 2 * M k := hN.eventually (eventually_ge_atTop 2048)
  have hε : 0 < Real.pi ^ 2 / 16 := by positivity
  refine ⟨σ, α, β, u, η, hη, ?_, ?_⟩
  · filter_upwards [hmodel, hedge _ hε, hlarge] with k hk hB hn
    have hm : 0 < M k := by have := hM2 k; omega
    have hqe := evenConstraint_budget hm (u k) hk.1.periodic
    have hB' : (2 * M k : ℝ) * LocalDFT.energyB (2 * M k) (u k) ≤
        3 * Real.pi ^ 2 / 2 + Real.pi ^ 2 / 16 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hB
    have hgap := evenConstraint_schur_bounds hn (u k) hk.1.periodic hB'
    refine ⟨hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, ?_, ?_, hgap.1, hgap.2⟩
    · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hk.2.2.2.2
    · have hb : (2 * M k : ℝ) * LocalDFT.energyB (2 * M k) (u k) ≤
          edgeBudget (2 * M k) (η k) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hk.2.2.2.2
      exact hqe.trans hb
  · intro ε hε
    filter_upwards [hmodel, hedge ε hε] with k hk hB
    have hm : 0 < M k := by have := hM2 k; omega
    refine (evenConstraint_budget hm (u k) hk.1.periodic).trans ?_
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hB

end
end Erdos1045.EventualExact.ExtremalSchurGap

import StructuralNote.FixedSchurChosenLinearization
import StructuralNote.FixedSchurQuadraticExpansion
import StructuralNote.FixedSchurPairingBounds
import StructuralNote.FixedSchurChartCenterBounds
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Exact second derivative and mixed L2/L1 control of the scalar quadratic
term on a chosen fixed-Schur path. -/

namespace StructuralNote.FixedSchurQuadraticDerivatives

open Filter Erdos1045.EventualExact FourierMultiplier SchurLiftBounds SchurOperatorBounds
open CommonDomainClosure CommonFiberCanonicalDirections FixedSchurChosenPath
open FixedSchurChosenLinearization FixedSchurQuadraticExpansion FixedSchurPairingBounds
open FixedSchurChartCenterBounds
open scoped BigOperators Topology

noncomputable section

theorem linear_hasDerivAt {n : ℕ} (T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    {q : ℝ → Fin n → ℝ} {q' : Fin n → ℝ} {t : ℝ}
    (hq : ∀ j, HasDerivAt (fun r => q r j) (q' j) t) (j : Fin n) :
    HasDerivAt (fun r => T (q r) j) (T q' j) t := by
  exact hasDerivAt_pi.mp ((LinearMap.toContinuousLinearMap T).hasFDerivAt.comp_hasDerivAt
    t (hasDerivAt_pi.mpr hq)) j

theorem pairing_hasDerivAt {n : ℕ} {f g : ℝ → Fin n → ℝ}
    {f' g' : Fin n → ℝ} {t : ℝ}
    (hf : ∀ j, HasDerivAt (fun r => f r j) (f' j) t)
    (hg : ∀ j, HasDerivAt (fun r => g r j) (g' j) t) :
    HasDerivAt (fun r => finitePairing (f r) (g r))
      (finitePairing f' (g t) + finitePairing (f t) g') t := by
  simpa only [finitePairing, Pi.mul_apply, Finset.sum_add_distrib] using
    HasDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => (hf j).mul (hg j))

theorem energy_hasDerivAt {n : ℕ} {q : ℝ → Fin n → ℝ}
    {q' : Fin n → ℝ} {t : ℝ}
    (hq : ∀ j, HasDerivAt (fun r => q r j) (q' j) t) :
    HasDerivAt (fun r => normalizedBoxEnergy (operator n) (q r))
      (finitePairing (operator n (q t)) q' / n) t := by
  have hd₀ := (pairing_hasDerivAt hq (linear_hasDerivAt (operator n) hq)).div_const 2
  have hd := hd₀.div_const (n : ℝ)
  simp only [normalizedBoxEnergy, boxEnergy, Fintype.card_fin]
  apply hd.congr_deriv
  rw [selfAdjoint n (q t) q', finitePairing_comm q']
  ring

def quadraticSecond {n : ℕ} (q q' q'' : Fin n → ℝ) : ℝ :=
  finitePairing (operator n q') q' / n + finitePairing (operator n q) q'' / n

theorem energy_second_derivative {n : ℕ} {q q' : ℝ → Fin n → ℝ}
    {q'' : Fin n → ℝ} {t : ℝ}
    (hq : ∀ᶠ z in 𝓝 t, ∀ j, HasDerivAt (fun r => q r j) (q' z j) z)
    (hq' : ∀ j, HasDerivAt (fun r => q' r j) (q'' j) t) :
    HasDerivAt (deriv (fun r => normalizedBoxEnergy (operator n) (q r)))
      (quadraticSecond (q t) (q' t) q'') t := by
  have hd := (pairing_hasDerivAt
    (linear_hasDerivAt (operator n) hq.self_of_nhds) hq').div_const (n : ℝ)
  have hd' : HasDerivAt (fun r => finitePairing (operator n (q r)) (q' r) / n)
      (quadraticSecond (q t) (q' t) q'') t := by
    simpa only [quadraticSecond, add_div] using hd
  apply hd'.congr_of_eventuallyEq
  filter_upwards [hq] with r hr
  exact (energy_hasDerivAt hr).deriv

theorem quadraticSecond_abs_le {m : ℕ} (hm : 2048 ≤ 2 * m)
    (q q' q'' : Fin (2 * m) → ℝ) (hq : ‖q‖ ≤ 5) :
    |quadraticSecond q q' q''| ≤ meanSquare q' / 2 +
      5 * (∑ j, |q'' j|) / (2 * m : ℝ) := by
  have hn : 0 < 2 * m := by omega
  have hop (j : Fin (2 * m)) : |operator (2 * m) q j| ≤ 5 := by
    have hp := operator_pointwise_sq_le hn q j
    have hw := SchurWeights.weight_square_sum_lt_half hm
    have hms := meanSquare_le_twentyFive hn q hq
    have hc := mul_le_mul_of_nonneg_right hw.le (meanSquare_nonneg q)
    have habs := abs_nonneg (operator (2 * m) q j)
    nlinarith [sq_abs (operator (2 * m) q j)]
  have hpair := normalized_pairing_sup hn (operator (2 * m) q) q'' hop
  have henergy := energy_le_meanSquare hn (⟨m, by omega⟩ : Even (2 * m)) q'
  have hfirst : |finitePairing (operator (2 * m) q') q' / (2 * m : ℕ)| ≤ meanSquare q' / 2 := by
    have he : finitePairing (operator (2 * m) q') q' / (2 * m : ℕ) =
        2 * normalizedBoxEnergy (operator (2 * m)) q' := by
      rw [finitePairing_comm]
      unfold normalizedBoxEnergy boxEnergy
      simp only [Fintype.card_fin]
      ring
    rw [he, abs_of_nonneg (mul_nonneg (by norm_num) henergy.1)]
    linarith only [henergy.2]
  exact (abs_add_le _ _).trans ((add_le_add hfirst hpair).trans_eq (by
    simp only [Nat.cast_mul, Nat.cast_ofNat]))

theorem eventual_chosen_quadratic_second : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      HasDerivAt (deriv (fun t => normalizedBoxEnergy (operator (2 * m))
        (chosenQPath (by omega) s θ η v h t)))
        (quadraticSecond (FixedSchurChart.coordinate (by omega) s θ v)
          (chosenFirstDerivative (by omega) s θ η v h)
          (chosenSecondDerivative (by omega) s θ η v h)) 0 := by
  filter_upwards [eventual_chosen_path_jets] with m hjets
  intro hm s θ η v h hdom hdir
  have hj := hjets hm s θ η v h hdom hdir
  have hq := Filter.eventually_all.mpr (fun j => (hj j).1)
  have hd := energy_second_derivative hq (fun j => (hj j).2.2.1)
  have hz : chosenQPath (by omega) s θ η v h 0 =
      FixedSchurChart.coordinate (by omega) s θ v := by
    simp [chosenQPath, chosenParameterPath, CommonFiberCanonicalPaths.affinePath]
  rw [hz] at hd
  exact hd

end
end StructuralNote.FixedSchurQuadraticDerivatives

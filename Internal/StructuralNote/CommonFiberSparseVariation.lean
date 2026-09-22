import StructuralNote.CommonFiberSparseDifference
import StructuralNote.ClosedSourceIntegration
import StructuralNote.TotalVariation
import StructuralNote.CommonFiberNonlocalChain

/-! Both estimates in (9.20) for actual common-parameter configurations whose
words differ at finitely many sites. -/

namespace StructuralNote.CommonFiberSparseVariation

open Erdos1045 Erdos1045.EventualExact Complex Filter LensClosure
open FiniteFourierLift SchurSpectrum CommonClosureEnergy CommonTangentialParameters
open CommonDomainClosure CommonDomainRadius CommonFiberGeometry CommonFiberCanonical
open CommonFiberDifferentialEstimate CommonFiberSparseDifference CommonFiberNonlocalChain TotalVariation
open scoped BigOperators Topology
noncomputable section

theorem variation_periodize {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    variation n (periodize hn c) = ∑ j, ‖difference hn c j‖ := by
  rw [variation, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [QuarticWindowBound.incrementNorm, periodize_difference, Nat.mod_eq_of_lt j.isLt]

theorem center_difference_variation {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (σ τ : Fin m → ℝ) (ξ η : ℂ)
    (hξz : closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) σ (coordinates hm v) ξ = 0)
    (hηz : closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) τ (coordinates hm v) η = 0) :
    variation (2 * m) (periodize (by omega) (center hm θ v σ ξ - center hm θ v τ η)) =
      2 * ∑ j, ‖fiberIncrement hm θ v σ ξ j - fiberIncrement hm θ v τ η j‖ := by
  have hd : difference (by omega) (center hm θ v σ ξ - center hm θ v τ η) =
      BoxLensLift.repeatHalf hm (fiberIncrement hm θ v σ ξ - fiberIncrement hm θ v τ η) := by
    funext j
    have he : difference (by omega) (center hm θ v σ ξ - center hm θ v τ η) j =
        difference (by omega) (center hm θ v σ ξ) j - difference (by omega) (center hm θ v τ η) j := by
      simp only [difference, Pi.sub_apply]
      ring
    rw [he, center_difference hm θ v σ ξ hξz, center_difference hm θ v τ η hηz]
    rfl
  rw [variation_periodize, hd, ClosedSourceIntegration.repeatHalf_map_sum]
  rfl

theorem variation_consequences {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) {J : ℝ}
    (hvar : variation n (periodize hn c) ≤ 360 * J / (n : ℝ) ^ 2) :
    pairEnergy hn c ≤ 8100 * J ^ 2 * (1 + Real.log n) / (n : ℝ) ^ 2 ∧
      pairNormSum n (periodize hn c) ≤ 45 * J := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ 1 + Real.log n := by
    have hl := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    linarith
  have hu := periodize_periodic hn c
  constructor
  · have hs := pow_le_pow_left₀ (variation_nonneg _ _) hvar 2
    have hb := energyA_le_log hn (periodize hn c) hu
    apply hb.trans
    calc
      _ ≤ (n : ℝ) ^ 2 / 16 * (360 * J / (n : ℝ) ^ 2) ^ 2 * (1 + Real.log n) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs (by positivity)) hlog
      _ = _ := by field_simp; ring
  · apply (pairNormSum_le hn (periodize hn c) hu).trans
    calc
      _ ≤ (n : ℝ) ^ 2 / 8 * (360 * J / (n : ℝ) ^ 2) := by gcongr
      _ = _ := by field_simp; ring

theorem eventual_canonical_sparse_variation : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
      (σ τ : Fin m → ℝ), InDomain hm θ v → (∀ j, |σ j| ≤ 1) → (∀ j, |τ j| ≤ 1) →
    ∀ (J : Finset (Fin m)), (∀ j, j ∉ J → σ j = τ j) →
    let H := center hm θ v σ (root hm σ (θ, v)) - center hm θ v τ (root hm τ (θ, v))
    variation (2 * m) (periodize (by omega) H) ≤ 360 * J.card / (2 * m : ℝ) ^ 2 ∧
      pairEnergy (by omega) H ≤ 8100 * (J.card : ℝ) ^ 2 * (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 ∧
      pairNormSum (2 * m) (periodize (by omega) H) ≤ 45 * J.card := by
  filter_upwards [eventual_canonical_sparse_difference, eventual_size_conditions] with m hs hsize
  intro hm θ v σ τ hdom hσ hτ J hagree
  have hrootσ := root_spec hsize.1 σ (θ, v) hsize.2.1 hσ hdom
  have hrootτ := root_spec hsize.1 τ (θ, v) hsize.2.1 hτ hdom
  have hb := (hs hm θ v σ τ hdom hσ hτ J hagree).2
  dsimp only
  have hvar := center_difference_variation hm θ v σ τ _ _ hrootσ.2 hrootτ.2
  have hv : variation (2 * m) (periodize (by omega)
      (center hm θ v σ (root hm σ (θ, v)) - center hm θ v τ (root hm τ (θ, v)))) ≤
        360 * J.card / (2 * m : ℝ) ^ 2 := by
    rw [hvar]
    simp only [div_eq_mul_inv] at hb ⊢
    nlinarith only [hb]
  refine ⟨hv, ?_⟩
  have hh := variation_consequences (by omega : 0 < 2 * m) _
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hv)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh

end
end StructuralNote.CommonFiberSparseVariation

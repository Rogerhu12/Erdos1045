import StructuralNote.CommonFiberHessianGeometryChord
import StructuralNote.TotalVariation

/-! Uniform gradient control derived from the actual common-domain chord estimates. -/

namespace StructuralNote.CommonFiberHessianGeometryGradient

open Erdos1045 Erdos1045.EventualExact Complex
open LensClosure FiniteFourierLift SchurSpectrum LocalGradient
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure CommonDomainRadius
open CommonFiberGeometry CommonFiberHessianGeometryChord SignedPressureAngular
open scoped BigOperators ComplexConjugate
noncomputable section

theorem reciprocal_sum_le (n : ℕ) :
    (∑ h ∈ Finset.Ico 1 n, (1 / (h : ℝ) + 1 / ((n - h : ℕ) : ℝ))) ≤
      2 * (1 + Real.log n) := by
  rw [Finset.sum_add_distrib, sum_Ico_reflect n (fun h => 1 / (h : ℝ))]
  have hH : (∑ h ∈ Finset.Ico 1 n, (1 / (h : ℝ))) ≤ (harmonic n : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      have h := Finset.mem_Ico.mp hk
      exact Finset.mem_Icc.mpr ⟨h.1, h.2.le⟩
    · intro k _ _
      positivity
  linarith [harmonic_le_one_add_log n]

theorem nodeGradient_uniform_lags {n : ℕ} (hn : 0 < n)
    (u : ℕ → ℂ) (hu : Function.Periodic u n) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / 2)
    (hpair : ∀ i : Fin n, ∀ h ∈ Finset.Ico 1 n, ‖LocalDFT.pairRatio n u i h‖ ≤ δ)
    (i : Fin n) :
    ‖FeketeStationarity.nodeGradient (fun j : Fin n => LocalPhase.regularRoot n ^ (j : ℕ) + u j) i -
      FeketeStationarity.nodeGradient (fun j : Fin n => LocalPhase.regularRoot n ^ (j : ℕ)) i‖ ≤
      (n : ℝ) * δ * (1 + Real.log n) := by
  let w (j : ℕ) := LocalPhase.regularRoot n ^ j
  let p (j : ℕ) := w j + u j
  have hw : Function.Periodic w n := by
    intro j
    dsimp [w]
    rw [pow_add, LocalDFT.regularRoot_pow hn, mul_one]
  have hp : Function.Periodic p n := by intro j; dsimp [p]; rw [hw j, hu j]
  let g (h : ℕ) := (p i - p (i + h))⁻¹ - (w i - w (i + h))⁻¹
  have hlocal (h : ℕ) (hh : h ∈ Finset.Ico 1 n) :
      ‖g h‖ ≤ (n : ℝ) / 2 * δ * (1 / (h : ℝ) + 1 / ((n - h : ℕ) : ℝ)) := by
    have ht := Finset.mem_Ico.mp hh
    have ha : w i - w (i + h) ≠ 0 := by
      exact sub_ne_zero.mpr (sub_ne_zero.mp
        (LocalDFT.vertex_difference_ne_zero hn (by omega) ht.2 i)).symm
    have hqeq : (u i - u (i + h)) / (w i - w (i + h)) = LocalDFT.pairRatio n u i h := by
      dsimp [LocalDFT.pairRatio, w]
      rw [← neg_div_neg_eq]
      congr 1 <;> ring
    have hb := inverse_perturbation_bound ha (by rw [hqeq]; exact (hpair i h hh).trans hsmall)
    have hg : ‖g h‖ ≤ 2 * ‖LocalDFT.pairRatio n u i h‖ / ‖w (i + h) - w i‖ := by
      convert hb using 1
      · congr 2
        dsimp [g, p]
        congr 1
        ring
      · rw [hqeq, norm_sub_rev]
    calc
      _ ≤ 2 * δ / ‖w (i + h) - w i‖ := hg.trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hpair i h hh) (by norm_num)) (norm_nonneg _))
      _ = (2 * δ) * (1 / ‖w (i + h) - w i‖) := by ring
      _ ≤ (2 * δ) * ((n : ℝ) / 4 * (1 / (h : ℝ) + 1 / ((n - h : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (reciprocal_chord_bound hn (by omega) ht.2 i) (by positivity)
      _ = _ := by ring
  change ‖FeketeStationarity.nodeGradient (fun j : Fin n => p j) i -
    FeketeStationarity.nodeGradient (fun j : Fin n => w j) i‖ ≤ _
  rw [nodeGradient_eq_lags hn p hp, nodeGradient_eq_lags hn w hw, ← map_sub,
    Complex.norm_conj, ← Finset.sum_sub_distrib]
  calc
    ‖∑ h ∈ Finset.Ico 1 n, g h‖ ≤ ∑ h ∈ Finset.Ico 1 n, ‖g h‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Ico 1 n,
        (n : ℝ) / 2 * δ * (1 / (h : ℝ) + 1 / ((n - h : ℕ) : ℝ)) := Finset.sum_le_sum hlocal
    _ = (n : ℝ) / 2 * δ * ∑ h ∈ Finset.Ico 1 n,
        (1 / (h : ℝ) + 1 / ((n - h : ℕ) : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (n : ℝ) / 2 * δ * (2 * (1 + Real.log n)) :=
      mul_le_mul_of_nonneg_left (reciprocal_sum_le n) (by positivity)
    _ = _ := by ring

theorem realGradient_uniform_lags {n : ℕ} (hn : 0 < n)
    (u : ℕ → ℂ) (hu : Function.Periodic u n) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / 2)
    (hpair : ∀ i : Fin n, ∀ h ∈ Finset.Ico 1 n, ‖LocalDFT.pairRatio n u i h‖ ≤ δ)
    (i : Fin n) :
    ‖realGradient (fun j : Fin n => LocalPhase.regularRoot n ^ (j : ℕ) + u j) i -
      realGradient (fun j : Fin n => LocalPhase.regularRoot n ^ (j : ℕ)) i‖ ≤
      2 * (n : ℝ) * δ * (1 + Real.log n) := by
  rw [realGradient, realGradient, ← mul_sub, norm_mul]
  norm_num only [Complex.norm_ofNat]
  have h := nodeGradient_uniform_lags hn u hu hδ hsmall hpair i
  nlinarith

theorem domain_gradient_bound {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hdom : InDomain (by omega) θ v) (hσ : ∀ j, |σ j| ≤ 1)
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hz : closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j)) σ (coordinates (by omega) v) ξ = 0)
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m)
    (hsmall : 300 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ≤ 1 / 2)
    (i : Fin (2 * m)) :
    ‖realGradient (configuration (by omega) θ v σ ξ) i - realGradient (root (2 * m)) i‖ ≤
      600 * (logOrder (2 * m) : ℝ) * (1 + Real.log (2 * m : ℝ)) := by
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  let u := periodize (by omega : 0 < 2 * m) (perturbation (by omega) θ v σ ξ)
  have hu := periodize_periodic (by omega : 0 < 2 * m) (perturbation (by omega) θ v σ ξ)
  have hpair (j : Fin (2 * m)) (h : ℕ) (hh : h ∈ Finset.Ico 1 (2 * m)) :
      ‖LocalDFT.pairRatio (2 * m) u j h‖ ≤ 300 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) := by
    have ht := Finset.mem_Ico.mp hh
    have hb := pairRatio_of_step (by omega : 0 < 2 * m) u hu
      (NonlocalFeasibility.periodize_step_bound (by omega) _
        (domain_perturbation_step hm θ v σ ξ hdom hσ hξ hz horder)) (by omega : 0 < h) ht.2 j
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hb
    exact hb.trans_eq (by field_simp; ring)
  have hb := realGradient_uniform_lags (by omega : 0 < 2 * m) u hu
    (by positivity) hsmall hpair i
  have he : (fun j : Fin (2 * m) => LocalPhase.regularRoot (2 * m) ^ (j : ℕ) + u j) =
      configuration (by omega) θ v σ ξ := by
    funext j
    simp only [u, periodize_fin, perturbation, root, add_sub_cancel]
  rw [he] at hb
  change ‖realGradient (configuration (by omega) θ v σ ξ) i - realGradient (root (2 * m)) i‖ ≤ _ at hb
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hb
  exact hb.trans_eq (by field_simp; ring)

end
end StructuralNote.CommonFiberHessianGeometryGradient

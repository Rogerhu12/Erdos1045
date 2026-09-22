import EventualExact.RadialDeficitControl
import EventualExact.QuadraticStability

/-! Uniform actual pair energy along the radial interpolation, derived from maximality. -/

namespace StructuralNote.RadialInterpolationEnergy

open Erdos1045 Erdos1045.EventualExact
open Complex Configuration CommonLocalization AntipodalDecomposition
open PolarAngleControl PolarRepresentation PolarCenterEnergy NormalizedPolarRepresentation
open RadialDeficitControl SchurSpectrum DiscreteEnergy
open scoped BigOperators
noncomputable section

theorem pairEnergy_scale {n : ℕ} (hn : 0 < n) (a : ℂ) (c : Fin n → ℂ) :
    pairEnergy hn (fun j => a * c j) = ‖a‖ ^ 2 * pairEnergy hn c := by
  have hr (j h : ℕ) : LocalDFT.pairRatio n (periodize hn (fun k => a * c k)) j h =
      a * LocalDFT.pairRatio n (periodize hn c) j h := by
    unfold LocalDFT.pairRatio periodize
    ring
  simp only [pairEnergy, LocalDFT.energyA, hr, normSq_eq_norm_sq, norm_mul, mul_pow, ← Finset.mul_sum]
  ring

theorem pairEnergy_root {n : ℕ} (hn : 0 < n) :
    pairEnergy hn (fun j : Fin n => LocalPhase.regularRoot n ^ (j : ℕ)) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  have hp : Function.Periodic (fun j => LocalPhase.regularRoot n ^ j) n := by
    intro j
    dsimp only
    rw [pow_add, LocalDFT.regularRoot_pow hn, mul_one]
  rw [pairEnergy_restrict hn _ hp]
  have hr (h : ℕ) (hh : h ∈ (Finset.range n).erase 0) (j : ℕ) :
      LocalDFT.pairRatio n (fun k => LocalPhase.regularRoot n ^ k) j h = 1 := by
    unfold LocalDFT.pairRatio
    exact div_self (LocalDFT.vertex_difference_ne_zero hn (Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hh))
      (Finset.mem_range.mp (Finset.mem_of_mem_erase hh)) j)
  unfold LocalDFT.energyA
  simp_rw [Finset.sum_congr rfl (fun h hh => Finset.sum_congr rfl (fun j _ => congrArg normSq (hr h hh j)))]
  simp only [normSq_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hn), Finset.card_range, Nat.cast_sub hn, Nat.cast_one]
  ring

def baseDeviation (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (j : Fin (2 * m)) : ℂ :=
  ((r - 1 : ℝ) : ℂ) * reference m j + (r : ℂ) * u j

def radialColumn (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (j : Fin (2 * m)) : ℂ :=
  (deficit m r u j : ℂ) * reference m j

def correction (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (j : Fin (2 * m)) : ℂ :=
  phase (-angle m u j) * radialColumn m r u j

def pathDeviation (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (t : ℝ) (j : Fin (2 * m)) : ℂ :=
  baseDeviation m r u j + ((1 - t : ℝ) : ℂ) * correction m r u j

theorem path_identity (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (t : ℝ) (j : Fin (2 * m)) :
    reference m j + pathDeviation m r u t j =
      phase (-angle m u j) * ((((1 - t * deficit m r u j : ℝ) : ℂ)) * reference m j +
        deangledCenter m r u j) := by
  have hp := polar_identity m r u j
  unfold pathDeviation baseDeviation correction radialColumn
  push_cast
  have hb : (radius m r u j : ℂ) = 1 - (deficit m r u j : ℂ) := by
    simp only [deficit, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [hb] at hp
  linear_combination hp

theorem base_energy_bound {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hη : η ≤ 1 / 4)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hE : ExtremalEnergyBound.totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2) :
    pairEnergy (by omega) (baseDeviation m ‖β‖ u) ≤ 320 * Real.pi ^ 2 := by
  have hs := ExtremalScaleBound.model_matching_deficit_bound hm h hη hz hE
  have hb0 := norm_nonneg β
  have hb := hs.1
  have hroot := pairEnergy_root (show 0 < 2 * m by omega)
  have hroot' : pairEnergy (by omega) (fun j : Fin (2 * m) => reference m j) ≤ (2 * m : ℝ) ^ 2 / 2 := by
    change pairEnergy (by omega) (fun j : Fin (2 * m) => LocalPhase.regularRoot (2 * m) ^ (j : ℕ)) ≤ _
    rw [hroot]
    push_cast
    nlinarith [show (0 : ℝ) ≤ 2 * m by positivity]
  have hsmall : (‖β‖ - 1) ^ 2 ≤ 1 - ‖β‖ ^ 2 := by nlinarith
  have hm1 := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ (2 * m : ℝ) ^ 2 / 2 by positivity)
  have hm2 := mul_le_mul_of_nonneg_left hroot' (sq_nonneg (‖β‖ - 1))
  have hfirst : pairEnergy (by omega) (fun j : Fin (2 * m) =>
      (((‖β‖ - 1 : ℝ) : ℂ)) * reference m j) ≤ 128 * Real.pi ^ 2 := by
    rw [pairEnergy_scale, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    nlinarith [hs.2.1]
  have hsecond : pairEnergy (by omega) (fun j : Fin (2 * m) => (‖β‖ : ℂ) * u j) ≤ 32 * Real.pi ^ 2 := by
    rw [pairEnergy_scale, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      pairEnergy_restrict (by omega) u h.periodic]
    have hA := model_pair_energy_le u hE
    have hsq : ‖β‖ ^ 2 ≤ 1 := by nlinarith
    exact (mul_le_of_le_one_left (LocalMaximum.energyA_nonneg _ _) hsq).trans hA
  have hadd := QuadraticStability.pairEnergy_add_le (show 0 < 2 * m by omega)
    (fun j : Fin (2 * m) => (((‖β‖ - 1 : ℝ) : ℂ)) * reference m j)
    (fun j : Fin (2 * m) => (‖β‖ : ℂ) * u j)
  change pairEnergy (by omega) (baseDeviation m ‖β‖ u) ≤ _ at hadd
  linarith

theorem correction_energy_bound {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hη : η ≤ 1 / 4)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hE : ExtremalEnergyBound.totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2)
    (hp : PolarBounds m u η) :
    pairEnergy (by omega) (correction m ‖β‖ u) ≤ 16384 * Real.pi ^ 4 + 1024 * Real.pi ^ 2 := by
  have hcol := model_deficit_energy hm h hη hz hE
  have hnorm : ‖radialColumn m ‖β‖ u‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).2
    intro j
    have hlo : 0 ≤ deficit m ‖β‖ u j := sub_nonneg.mpr (model_radius_le_one (by omega) h hz.1 j)
    have hhi : deficit m ‖β‖ u j ≤ 1 := by
      have hr := radius_nonneg m (norm_nonneg β) u j
      unfold deficit
      linarith
    simpa only [radialColumn, norm_mul, reference_norm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlo] using hhi
  have hang : pairEnergy (by omega) (fun j : Fin (2 * m) => (-angle m u j : ℂ)) ≤ 512 * Real.pi ^ 2 := by
    have hperiod : Function.Periodic (fun j => (angle m u j : ℂ)) (2 * m) := by
      intro j
      dsimp only
      have ha := angle_periodic (by omega) u h.periodic
      rw [show j + 2 * m = j + m + m by omega, ha (j + m), ha j]
    have he : (fun j : Fin (2 * m) => (-angle m u j : ℂ)) =
        fun j : Fin (2 * m) => (-1 : ℂ) * (angle m u j : ℂ) := by funext j; simp
    rw [he, pairEnergy_scale, norm_neg, norm_one, one_pow, one_mul,
      pairEnergy_restrict (by omega) _ hperiod]
    exact hp.angle_energy
  have he := energy_bound (show 0 < 2 * m by omega) 1 (fun j : Fin (2 * m) => -angle m u j)
    (radialColumn m ‖β‖ u)
  have hfun : center 1 (fun j : Fin (2 * m) => -angle m u j) (radialColumn m ‖β‖ u) =
      correction m ‖β‖ u := by
    funext j
    simp only [center, one_mul, correction]
  rw [hfun] at he
  simp only [norm_one, one_pow, mul_one, realEnergy, Complex.ofReal_neg] at he
  have hsq : ‖radialColumn m ‖β‖ u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (radialColumn m ‖β‖ u)]
  have hprod := mul_le_of_le_one_left (pairEnergy_nonneg (show 0 < 2 * m by omega)
    (fun j : Fin (2 * m) => (-angle m u j : ℂ))) hsq
  change pairEnergy (by omega) (radialColumn m ‖β‖ u) ≤ _ at hcol
  nlinarith only [he, hprod, hang, hcol]

theorem model_path_energy {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hη : η ≤ 1 / 4)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hE : ExtremalEnergyBound.totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2)
    (hp : PolarBounds m u η) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    pairEnergy (by omega) (pathDeviation m ‖β‖ u t) ≤ 32768 * Real.pi ^ 4 + 2688 * Real.pi ^ 2 := by
  have hA := base_energy_bound hm h hη hz hE
  have hB := correction_energy_bound hm h hη hz hE hp
  have hs : (1 - t) ^ 2 ≤ 1 := by rcases ht with ⟨h0, h1⟩; nlinarith
  have hscale : pairEnergy (by omega) (fun j => ((1 - t : ℝ) : ℂ) * correction m ‖β‖ u j) ≤
      pairEnergy (by omega) (correction m ‖β‖ u) := by
    rw [pairEnergy_scale, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact mul_le_of_le_one_left (pairEnergy_nonneg _ _) hs
  have hadd := QuadraticStability.pairEnergy_add_le (show 0 < 2 * m by omega)
    (baseDeviation m ‖β‖ u) (fun j => ((1 - t : ℝ) : ℂ) * correction m ‖β‖ u j)
  change pairEnergy (by omega) (pathDeviation m ‖β‖ u t) ≤ _ at hadd
  linarith

end
end StructuralNote.RadialInterpolationEnergy

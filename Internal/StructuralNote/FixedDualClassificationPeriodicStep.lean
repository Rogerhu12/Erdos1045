import StructuralNote.FixedDualClassificationParseval
import EventualExact.FiniteBoxMaximum

/-! The actual grid step function as a measurable function on the circle,
with its half-turn relation and its exact signed Fourier coefficients. -/

namespace StructuralNote.FixedDualClassificationPeriodicStep

open Real Set MeasureTheory AddCircle FixedDualClassificationStep
open FixedDualClassificationParseval
open Erdos1045.EventualExact Erdos1045.EventualExact.FourierMultiplier
open Erdos1045.EventualExact.FiniteBox
open scoped BigOperators
noncomputable section

local instance period_pos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev Circle := AddCircle (2 * Real.pi)

def circleProfile {n : ℕ} (q : Fin n → ℝ) (scale : ℝ) : Circle → ℝ :=
  liftIco (2 * Real.pi) 0 (stepProfile q scale)

theorem circleProfile_measurable {n : ℕ} (q : Fin n → ℝ) (scale : ℝ) :
    Measurable (circleProfile q scale) := by
  exact (stepProfile_measurable q scale).comp
    (measurable_subtype_coe.comp (measurableEquivIco (2 * Real.pi) 0).measurable)

theorem circleProfile_bound {n : ℕ} (q : Fin n → ℝ) (scale A : ℝ)
    (hA : 0 ≤ A) (hq : ∀ j, |q j| ≤ A) (x : Circle) :
    |circleProfile q scale x| ≤ |scale| * A :=
  stepProfile_bound q scale A hA hq _

theorem circleProfile_coe {n : ℕ} (q : Fin n → ℝ) (scale : ℝ)
    {t : ℝ} (ht : t ∈ Ico 0 (2 * Real.pi)) :
    circleProfile q scale (t : Circle) = stepProfile q scale t := by
  exact liftIco_coe_apply (by simpa only [zero_add] using ht)

theorem circleProfile_fourierCoeff {n : ℕ} (hn : 0 < n)
    (q : Fin n → ℝ) (scale : ℝ) (p : ℤ) :
    fourierCoeff (fun x => (circleProfile q scale x : ℂ)) p =
      (scale * sinc (p * Real.pi / n) : ℝ) * signedMidpointCoefficient q p := by
  change fourierCoeff (liftIco (2 * Real.pi) 0
    (fun t => (stepProfile q scale t : ℂ))) p = _
  rw [fourierCoeff_liftIco_eq]
  simpa only [zero_add] using
    (profileCoefficient_eq_fourierCoeffOn hn q scale p).symm.trans (profileCoefficient_eq hn q scale p)

theorem exists_cell {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : t ∈ Ico 0 (2 * Real.pi)) :
    ∃ j : Fin n, t ∈ cell n j := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let y : ℝ := (n : ℝ) * t / (2 * Real.pi)
  have hy : 0 ≤ y := div_nonneg (mul_nonneg hnR.le ht.1) (by positivity)
  have hyn : y < n := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
    nlinarith [ht.2]
  have hj : ⌊y⌋₊ < n := (Nat.floor_lt hy).mpr hyn
  refine ⟨⟨⌊y⌋₊, hj⟩, ?_⟩
  have hlo := Nat.floor_le hy
  have hhi := Nat.lt_floor_add_one y
  change 2 * Real.pi * (⌊y⌋₊ : ℝ) / n ≤ t ∧
    t < 2 * Real.pi * ((⌊y⌋₊ + 1 : ℕ) : ℝ) / n
  constructor
  · apply (div_le_iff₀ hnR).mpr
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp hlo
    nlinarith
  · apply (lt_div_iff₀ hnR).mpr
    have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mp hhi
    push_cast
    nlinarith

theorem cellLeft_half_shift {m : ℕ} (hm : 0 < m) (j : ℕ) :
    cellLeft (2 * m) (j + m) = cellLeft (2 * m) j + Real.pi := by
  unfold cellLeft
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

theorem cell_half_index {m : ℕ} (hm : 0 < m) {j : Fin (2 * m)} {t : ℝ}
    (ht : t ∈ cell (2 * m) j) (htpi : t < Real.pi) : j.val < m := by
  by_contra! h
  have hl := (cellLeft_mono (2 * m) h).trans ht.1
  have he : cellLeft (2 * m) m = Real.pi := by
    have h := cellLeft_half_shift hm 0
    simpa only [zero_add, cellLeft, Nat.cast_zero, mul_zero, zero_div] using h
  rw [he] at hl
  linarith

theorem stepProfile_half_shift {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (hq : Antiperiodic hm q) (scale : ℝ) {t : ℝ} (ht : t ∈ Ico 0 Real.pi) :
    stepProfile q scale (t + Real.pi) = -stepProfile q scale t := by
  obtain ⟨j, hj⟩ := exists_cell (by omega : 0 < 2 * m) ⟨ht.1, by linarith [ht.2, pi_pos]⟩
  have hjm := cell_half_index hm hj ht.2
  let j' : Fin (2 * m) := ⟨j.val + m, by omega⟩
  have he : halfTurn hm j = j' := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (by omega)
  have hj' : t + Real.pi ∈ cell (2 * m) j' := by
    change cellLeft (2 * m) (j.val + m) ≤ t + Real.pi ∧
      t + Real.pi < cellLeft (2 * m) (j.val + m + 1)
    rw [cellLeft_half_shift hm, show j.val + m + 1 = (j.val + 1) + m by omega,
      cellLeft_half_shift hm]
    exact ⟨by linarith [hj.1], by linarith [hj.2]⟩
  rw [stepProfile_at_cell q scale j' hj', stepProfile_at_cell q scale j hj, ← he, hq]
  ring

theorem circleProfile_antiperiodic {m : ℕ} (hm : 0 < m) (q : Fin (2 * m) → ℝ)
    (hq : Antiperiodic hm q) (scale : ℝ) (x : Circle) :
    circleProfile q scale (x + (Real.pi : ℝ)) = -circleProfile q scale x := by
  have hh {t : ℝ} (ht : t ∈ Ico 0 Real.pi) :
      circleProfile q scale ((t + Real.pi : ℝ) : Circle) =
        -circleProfile q scale (t : Circle) := by
    rw [circleProfile_coe q scale ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩,
      circleProfile_coe q scale ⟨ht.1, by linarith [ht.2, pi_pos]⟩]
    exact stepProfile_half_shift hm q hq scale ht
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico x
  rw [← AddCircle.coe_add]
  by_cases htpi : t < Real.pi
  · exact hh ⟨ht.1, htpi⟩
  · have htp : t - Real.pi ∈ Ico 0 Real.pi := ⟨by linarith, by linarith [ht.2]⟩
    have h := hh htp
    rw [sub_add_cancel] at h
    rw [show t + Real.pi = (t - Real.pi) + 2 * Real.pi by ring, AddCircle.coe_add_period]
    linarith

end
end StructuralNote.FixedDualClassificationPeriodicStep

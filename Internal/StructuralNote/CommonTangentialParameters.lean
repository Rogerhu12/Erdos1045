import EventualExact.BoxLensLift

/-! The actual half-periodic kernel of the radial constraint has real tangential
coordinates, and its two closure equations follow from telescoping differences. -/

namespace StructuralNote.CommonTangentialParameters

open Erdos1045.EventualExact
open Complex FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum BoxLensLift
open scoped BigOperators
noncomputable section

local notation "conj" => (starRingEnd ℂ)

def ParameterSpace {m : ℕ} (hm : 0 < m) (v : Fin (2 * m) → ℂ) : Prop :=
  HalfPeriodic hm v ∧ (∑ j, v j) = 0 ∧ constraint (by omega) v = 0

def coordinates {m : ℕ} (hm : 0 < m) (v : Fin (2 * m) → ℂ) (j : Fin m) : ℝ :=
  (conj (LensClosure.unit (LensClosure.midpoint m j)) *
    difference (by omega) v (halfIndex j)).im

def halfIncrement {m : ℕ} (ν : Fin m → ℝ) (j : Fin m) : ℂ :=
  LensClosure.unit (LensClosure.midpoint m j) * I * (ν j : ℂ)

def Closed {m : ℕ} (ν : Fin m → ℝ) : Prop :=
  (∑ j, ν j * Real.cos (LensClosure.midpoint m j)) = 0 ∧
  (∑ j, ν j * Real.sin (LensClosure.midpoint m j)) = 0

theorem frame_tangential {n : ℕ} (hn : 2 ≤ n) (v : Fin n → ℂ)
    (hq : constraint (by omega) v = 0) (j : Fin n) :
    difference (by omega) v j = frame n j * I *
      ((conj (frame n j) * difference (by omega) v j).im : ℂ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsin : 0 < Real.sin (Real.pi / n) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    apply (div_lt_iff₀ hnR).2
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  have hz := congrFun hq j
  change (n : ℝ) / (2 * Real.sin (Real.pi / n)) *
    (conj (frame n j) * difference (by omega) v j).re = 0 at hz
  have hr : (conj (frame n j) * difference (by omega) v j).re = 0 :=
    (mul_eq_zero.mp hz).resolve_left (ne_of_gt (by positivity))
  have he : conj (frame n j) * difference (by omega) v j =
      I * ((conj (frame n j) * difference (by omega) v j).im : ℂ) := by
    apply Complex.ext <;> simp [hr]
  have hf : frame n j * conj (frame n j) = 1 := by
    rw [Complex.mul_conj, frame_normSq]
    rfl
  calc
    _ = frame n j * (conj (frame n j) * difference (by omega) v j) := by
      rw [← mul_assoc, hf, one_mul]
    _ = _ := by simpa only [mul_assoc] using congrArg (fun z => frame n j * z) he

theorem difference_coordinates {m : ℕ} (hm : 0 < m) (v : Fin (2 * m) → ℂ)
    (hq : constraint (by omega) v = 0) (j : Fin m) :
    difference (by omega) v (halfIndex j) = halfIncrement (coordinates hm v) j := by
  simpa only [frame_halfIndex, halfIncrement, coordinates] using
    frame_tangential (by omega : 2 ≤ 2 * m) v hq (halfIndex j)

theorem half_difference_sum {m : ℕ} (hm : 0 < m) (v : Fin (2 * m) → ℂ)
    (hv : HalfPeriodic hm v) :
    (∑ j : Fin m, difference (by omega) v (halfIndex j)) = 0 := by
  let u := periodize (by omega : 0 < 2 * m) v
  have hd (j : Fin m) : difference (by omega) v (halfIndex j) = u (j.val + 1) - u j := by
    simp only [difference, successor, halfIndex, u, periodize,
      Nat.mod_eq_of_lt (show j.val < 2 * m by omega)]
  have hclose : u m = u 0 := by
    have he := hv ⟨0, by omega⟩
    simpa only [u, periodize, halfTurn, Nat.zero_add, Nat.zero_mod,
      Nat.mod_eq_of_lt (show m < 2 * m by omega)] using he
  simp_rw [hd]
  rw [Fin.sum_univ_eq_sum_range (fun j => u (j + 1) - u j) m,
    Finset.sum_range_sub, hclose, sub_self]

theorem closed_iff_increment_sum {m : ℕ} (ν : Fin m → ℝ) :
    Closed ν ↔ (∑ j, halfIncrement ν j) = 0 := by
  have hr : (∑ j, halfIncrement ν j).re =
      -(∑ j, ν j * Real.sin (LensClosure.midpoint m j)) := by
    simp only [Complex.re_sum, halfIncrement, Complex.mul_re, Complex.mul_im,
      I_re, I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      mul_one, sub_zero, zero_sub, neg_mul, LensClosure.unit_im,
      Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi : (∑ j, halfIncrement ν j).im =
      ∑ j, ν j * Real.cos (LensClosure.midpoint m j) := by
    simp only [Complex.im_sum, halfIncrement, Complex.mul_re, Complex.mul_im,
      I_re, I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      mul_one, add_zero, zero_add, LensClosure.unit_re]
    apply Finset.sum_congr rfl
    intro j _
    ring
  constructor
  · rintro ⟨hc, hs⟩
    apply Complex.ext <;> simp [hr, hi, hc, hs]
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    rw [hr] at hre
    rw [hi] at him
    exact ⟨him, by simpa using hre⟩

theorem coordinates_closed {m : ℕ} (hm : 0 < m) (v : Fin (2 * m) → ℂ)
    (hv : HalfPeriodic hm v) (hq : constraint (by omega) v = 0) :
    Closed (coordinates hm v) := by
  apply (closed_iff_increment_sum _).2
  simp_rw [← difference_coordinates hm v hq]
  exact half_difference_sum hm v hv

theorem coordinates_unique {m : ℕ} (hm : 0 < m) (v : Fin (2 * m) → ℂ)
    (ν : Fin m → ℝ)
    (hν : ∀ j, difference (by omega) v (halfIndex j) = halfIncrement ν j) :
    ν = coordinates hm v := by
  funext j
  have hf : conj (LensClosure.unit (LensClosure.midpoint m j)) *
      LensClosure.unit (LensClosure.midpoint m j) = 1 := by
    rw [← frame_halfIndex, mul_comm, Complex.mul_conj, frame_normSq]
    rfl
  unfold coordinates
  rw [hν j]
  simp only [halfIncrement, ← mul_assoc, hf, one_mul, Complex.mul_im,
    I_re, I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, one_mul, zero_add]

theorem exists_unique_coordinates {m : ℕ} (hm : 0 < m) (v : Fin (2 * m) → ℂ)
    (hv : ParameterSpace hm v) :
    ∃! ν : Fin m → ℝ, Closed ν ∧
      ∀ j, difference (by omega) v (halfIndex j) = halfIncrement ν j := by
  refine ⟨coordinates hm v, ⟨coordinates_closed hm v hv.1 hv.2.2,
    difference_coordinates hm v hv.2.2⟩, ?_⟩
  intro ν hν
  exact coordinates_unique hm v ν hν.2

theorem coordinates_abs_le {m : ℕ} (hm : 0 < m) (v : Fin (2 * m) → ℂ) (j : Fin m) :
    |coordinates hm v j| ≤ ‖difference (by omega) v (halfIndex j)‖ := by
  have h := Complex.abs_im_le_norm (conj (LensClosure.unit (LensClosure.midpoint m j)) *
    difference (by omega) v (halfIndex j))
  simpa only [coordinates, norm_mul, Complex.norm_conj, LensClosure.norm_unit, one_mul] using h

end
end StructuralNote.CommonTangentialParameters

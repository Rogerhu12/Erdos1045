import StructuralNote.RationalConfiguration
import StructuralNote.CommonFiberGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds

/-! The arctangent coordinates in the branch selector and recovery of the
positive square root in the common lens parametrization. -/

namespace StructuralNote.RationalAngleBranch

open Erdos1045.EventualExact LensClosure RationalChart
open CommonFiberGeometry
open scoped BigOperators
noncomputable section

theorem rotation_eq_unit_arctan (t : ℝ) : rotation t = unit (2 * Real.arctan t) := by
  apply Complex.ext
  · rw [unit_re, Real.cos_two_mul, Real.cos_sq_arctan]
    dsimp [rotation]
    field_simp
    ring
  · rw [unit_im, Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    dsimp [rotation]
    have hs : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
    have hn : Real.sqrt (1 + t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (denominator_pos t)).ne'
    field_simp
    rw [hs]

theorem abs_arctan_le (t : ℝ) : |Real.arctan t| ≤ |t| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Real.arctan) (s := Set.univ) (C := 1)
    (fun x _ => Real.differentiableAt_arctan x)
    (fun x _ => show ‖deriv Real.arctan x‖ ≤ (1 : ℝ) by
      rw [(Real.hasDerivAt_arctan x).deriv, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < 1 / (1 + x ^ 2))]
      exact (div_le_one (denominator_pos x)).2 (by nlinarith [sq_nonneg x]))
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (x := 0) (y := t) (by trivial) (by trivial)
  simpa using h

theorem angle_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x => 2 * Real.arctan x) (2 / (1 + t ^ 2)) t := by
  simpa only [mul_one_div] using (Real.hasDerivAt_arctan t).const_mul 2

theorem angle_derivative_pos (t : ℝ) : 0 < 2 / (1 + t ^ 2) := by positivity

theorem angle_inverse {θ : ℝ} (hθ : |θ| < Real.pi) :
    2 * Real.arctan (Real.tan (θ / 2)) = θ := by
  rw [Real.arctan_tan (by linarith [(abs_lt.mp hθ).1]) (by linarith [(abs_lt.mp hθ).2])]
  ring

theorem positive_height {δ σ : ℝ} (hσ : σ ^ 2 = 1) (hδ : 0 ≤ Real.cos δ) :
    Lens.height (σ * (2 * Real.sin δ)) = 2 * Real.cos δ := by
  have he : 4 - (σ * (2 * Real.sin δ)) ^ 2 = (2 * Real.cos δ) ^ 2 := by
    rw [mul_pow, hσ, one_mul]
    nlinarith [Real.sin_sq_add_cos_sq δ]
  rw [Lens.height, he, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

theorem crossing_eq_lens_increment (β a δ σ : ℝ) (hσ : σ ^ 2 = 1)
    (hδ : 0 ≤ Real.cos δ) :
    RationalChart.crossingIncrement σ (unit (β - a)) (unit (β + a)) (unit (β + δ)) =
      LensClosure.increment β (2 * Real.cos a) σ (σ * (2 * Real.sin δ)) := by
  have he : unit (β - a) + unit (β + a) = unit β * ((2 * Real.cos a : ℝ) : ℂ) := unit_pair β a
  unfold RationalChart.crossingIncrement
  rw [show 2 * unit (β + δ) - unit (β - a) - unit (β + a) =
    2 * unit (β + δ) - (unit (β - a) + unit (β + a)) by ring, he, unit_add]
  rw [LensClosure.increment, Lens.width, positive_height hσ hδ]
  have hu : unit δ = ((Real.cos δ : ℝ) : ℂ) + (Real.sin δ : ℂ) * Complex.I := by
    simpa only [unit_re, unit_im] using (Complex.re_add_im (unit δ)).symm
  rw [hu]
  push_cast
  ring

def angle {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) (j : ℕ) : ℝ :=
  2 * Real.arctan (RationalConfiguration.angleParameter X ⟨j % m, Nat.mod_lt _ hm⟩)

def phase {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) (j : Fin m) : ℝ :=
  midpoint m j + (angle hm X j + angle hm X (j.val + 1)) / 2

def halfAngle {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) (j : Fin m) : ℝ :=
  Real.pi / (2 * m) + (angle hm X (j.val + 1) - angle hm X j) / 2

def crossingOffset {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) (j : Fin m) : ℝ :=
  2 * Real.arctan (RationalConfiguration.crossingParameter X j) -
    (angle hm X j + angle hm X (j.val + 1)) / 2

def tangential {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (j : Fin m) : ℝ :=
  σ j * (2 * Real.sin (crossingOffset hm X j))

theorem diameter_eq_unit {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ) (j : ℕ) :
    RationalConfiguration.diameter hm X j = unit (Real.pi / m * j + angle hm X j) := by
  rw [RationalConfiguration.diameter, rotation_eq_unit_arctan, unit_add]
  rfl

theorem increment_eq_lens {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (j : Fin m) (hσ : σ j ^ 2 = 1)
    (hδ : 0 ≤ Real.cos (crossingOffset hm X j)) :
    RationalConfiguration.increment hm σ X j = LensClosure.increment (phase hm X j)
      (2 * Real.cos (halfAngle hm X j)) (σ j) (tangential hm σ X j) := by
  have h₁ : Real.pi / m * j + angle hm X j = phase hm X j - halfAngle hm X j := by
    unfold phase halfAngle LensClosure.midpoint
    ring
  have h₂ : Real.pi / m * (j.val + 1 : ℕ) + angle hm X (j.val + 1) =
      phase hm X j + halfAngle hm X j := by
    unfold phase halfAngle LensClosure.midpoint
    push_cast
    ring
  have hu : RationalConfiguration.crossingUnit X j = unit (phase hm X j + crossingOffset hm X j) := by
    rw [RationalConfiguration.crossingUnit, rotation_eq_unit_arctan, ← unit_add]
    congr 1
    unfold phase crossingOffset
    ring
  rw [RationalConfiguration.increment, diameter_eq_unit, diameter_eq_unit, h₁, h₂, hu]
  exact crossing_eq_lens_increment _ _ _ _ hσ hδ

def SmallWindow {m : ℕ} (X : RationalConfiguration.Variables m → ℝ) : Prop :=
  ∀ i, |X i| < 1 / (2 * (m : ℝ))

theorem angleParameter_bound {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ)
    (hX : SmallWindow X) (j : Fin m) :
    |RationalConfiguration.angleParameter X j| < 1 / (2 * (m : ℝ)) := by
  unfold RationalConfiguration.angleParameter
  split
  · simp only [abs_zero]
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  · exact hX _

theorem angle_bound {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ)
    (hX : SmallWindow X) (j : ℕ) : |angle hm X j| < 2 / (2 * (m : ℝ)) := by
  unfold angle
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := angleParameter_bound hm X hX ⟨j % m, Nat.mod_lt _ hm⟩
  have he := abs_arctan_le (RationalConfiguration.angleParameter X ⟨j % m, Nat.mod_lt _ hm⟩)
  calc
    _ < 2 * (1 / (2 * (m : ℝ))) := mul_lt_mul_of_pos_left (he.trans_lt h) (by norm_num)
    _ = _ := by ring

theorem crossingOffset_bound {m : ℕ} (hm : 0 < m) (X : RationalConfiguration.Variables m → ℝ)
    (hX : SmallWindow X) (j : Fin m) : |crossingOffset hm X j| < 4 / (2 * (m : ℝ)) := by
  have h₁ := angle_bound hm X hX j
  have h₂ := angle_bound hm X hX (j.val + 1)
  have hy : |RationalConfiguration.crossingParameter X j| < 1 / (2 * (m : ℝ)) := hX (.inr j)
  have hat := abs_arctan_le (RationalConfiguration.crossingParameter X j)
  have ha : |(angle hm X j + angle hm X (j.val + 1)) / 2| ≤
      (|angle hm X j| + |angle hm X (j.val + 1)|) / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  have hs := abs_sub_le (2 * Real.arctan (RationalConfiguration.crossingParameter X j)) 0
    ((angle hm X j + angle hm X (j.val + 1)) / 2)
  simp only [sub_zero, zero_sub, abs_neg] at hs
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hs
  unfold crossingOffset
  calc
    _ ≤ 2 * |RationalConfiguration.crossingParameter X j| +
        (|angle hm X j| + |angle hm X (j.val + 1)|) / 2 := by linarith
    _ < 2 * (1 / (2 * (m : ℝ))) + (2 / (2 * (m : ℝ)) + 2 / (2 * (m : ℝ))) / 2 := by
      gcongr
    _ = _ := by ring

theorem crossingOffset_cos_pos {m : ℕ} (hm : 2 ≤ m) (X : RationalConfiguration.Variables m → ℝ)
    (hX : SmallWindow X) (j : Fin m) : 0 < Real.cos (crossingOffset (by omega) X j) := by
  have hb := crossingOffset_bound (by omega : 0 < m) X hX j
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : 4 / (2 * (m : ℝ)) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have ha : |crossingOffset (by omega : 0 < m) X j| < 1 := hb.trans_le hd
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [(abs_lt.mp ha).1, (abs_lt.mp ha).2, Real.pi_gt_three]

theorem smallWindow_increment_eq_lens {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (hX : SmallWindow X) (j : Fin m)
    (hσ : σ j ^ 2 = 1) : RationalConfiguration.increment (by omega) σ X j =
      LensClosure.increment (phase (by omega) X j) (2 * Real.cos (halfAngle (by omega) X j))
        (σ j) (tangential (by omega) σ X j) :=
  increment_eq_lens (by omega) σ X j hσ (crossingOffset_cos_pos hm X hX j).le

theorem tangential_recovery {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ) (hX : SmallWindow X) (j : Fin m)
    (hσ : σ j ^ 2 = 1) :
    (unit (-phase (by omega) X j) * RationalConfiguration.increment (by omega) σ X j).im =
      tangential (by omega) σ X j := by
  rw [smallWindow_increment_eq_lens hm σ X hX j hσ, LensClosure.increment,
    ← mul_assoc, ← unit_add]
  simp only [neg_add_cancel, unit, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_mul, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]

end
end StructuralNote.RationalAngleBranch

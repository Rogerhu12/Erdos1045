import StructuralNote.AngularPathGeometry
import StructuralNote.NormalizedRadialPrice

/-! Actual normalized polar chord bounds, prior to any strong pressure estimate. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.PolarChordControl

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization
open PolarAngleControl PolarRepresentation PolarCenterEnergy PolarCenterNormalization
open NormalizedPolarRepresentation ExtremalPolarCenter AntipodalDecomposition
open GeometricRelativeRemainder SignedPressureAngular

theorem quotient_swap {n : ℕ} (f w : Points n) (i j : Fin n) :
    quotient f w (i, j) = quotient f w (j, i) := by
  unfold quotient
  rw [show f i - f j = -(f j - f i) by ring,
    show w i - w j = -(w j - w i) by ring, div_neg, neg_div, neg_neg]

theorem quotient_of_pair_bound {n : ℕ} (f : ℕ → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hpair : ∀ j h : ℕ, 0 < h → h < n → ‖LocalDFT.pairRatio n f j h‖ ≤ δ)
    (p : Fin n × Fin n) : ‖quotient (fun j => f j) (root n) p‖ ≤ δ := by
  have hlt (i j : Fin n) (hij : i.val < j.val) :
      ‖quotient (fun k => f k) (root n) (j, i)‖ ≤ δ := by
    have hb := hpair i.val (j.val - i.val) (by omega) (by omega)
    simpa only [LocalDFT.pairRatio, Nat.add_sub_of_le (Nat.le_of_lt hij), quotient, root] using hb
  rcases p with ⟨i, j⟩
  rcases lt_trichotomy i.val j.val with h | h | h
  · rw [quotient_swap]
    exact hlt i j h
  · have he := Fin.ext h
    subst j
    simpa only [quotient, sub_self, zero_div, norm_zero] using hδ
  · exact hlt j i h

theorem center_quotient_bound {n : ℕ} (θ : Fin n → ℝ) (C w : Points n) (p : Fin n × Fin n) :
    ‖quotient (fun j => phase (θ j) * C j) w p‖ ≤ ‖quotient C w p‖ +
      ‖C p.2‖ * ‖quotient (fun j => (θ j : ℂ)) w p‖ := by
  have hd := center_difference_bound (1 : ℂ) θ C p.2 p.1
  simp only [center, one_mul, norm_one] at hd
  have hdiv := div_le_div_of_nonneg_right hd (norm_nonneg (w p.1 - w p.2))
  simp only [quotient, norm_div, ← ofReal_sub, norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (‖C p.1 - C p.2‖ + ‖C p.2‖ * |θ p.1 - θ p.2|) / ‖w p.1 - w p.2‖ := hdiv
    _ = _ := by ring

theorem model_even_pair_le {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η)
    {h : ℕ} (hh : 0 < h) (hhn : h < 2 * m) (j : ℕ) :
    ‖LocalDFT.pairRatio (2 * m) (evenSequence m u) j h‖ ≤ 2 * η ∧
      ‖LocalDFT.pairRatio (2 * m) (oddSequence m u) j h‖ ≤ 2 * η := by
  have hp (k : ℕ) := LocalMaximum.pair_ratio_bound ClosedFourier.geometricSine (by omega) u
    hmodel.periodic hmodel.error_nonneg hmodel.relative_edges
    (Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr hhn⟩) k
  constructor
  · rw [pairRatio_evenSequence (by omega), norm_div]
    norm_num only [norm_ofNat]
    have hb := norm_sub_le (LocalDFT.pairRatio (2 * m) u j h) (LocalDFT.pairRatio (2 * m) u (j + m) h)
    linarith only [hb, hp j, hp (j + m)]
  · rw [pairRatio_oddSequence (by omega), norm_div]
    norm_num only [norm_ofNat]
    have hb := norm_add_le (LocalDFT.pairRatio (2 * m) u j h) (LocalDFT.pairRatio (2 * m) u (j + m) h)
    linarith only [hb, hp j, hp (j + m)]

theorem model_angle_quotient {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η) (hp : PolarBounds m u η)
    (p : Fin (2 * m) × Fin (2 * m)) :
    ‖quotient (fun j => (rawAngle m u j : ℂ)) (root (2 * m)) p‖ ≤
      4 * η + 2 * Real.sqrt (sizeBudget (2 * m)) := by
  apply quotient_of_pair_bound (fun j => (angle m u j : ℂ))
    (by have := hmodel.error_nonneg; positivity) _ p
  intro j h hh hhn
  have hb := angle_pairRatio_bound (by omega) u hp.odd_small hh hhn j
  have ho := (model_even_pair_le hm hmodel hh hhn j).2
  have hs := Real.le_sqrt_of_sq_le (hp.odd_size j)
  linarith only [hb, ho, hs]

theorem model_physical_quotient {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η) (hβ : ‖β‖ ≤ 1)
    (p : Fin (2 * m) × Fin (2 * m)) :
    ‖quotient (ExtremalPolarCenter.physicalCenter m β u) (root (2 * m)) p‖ ≤ 2 * η := by
  have he : quotient (ExtremalPolarCenter.physicalCenter m β u) (root (2 * m)) p =
      (‖β‖ : ℂ) * quotient (fun j => evenSequence m u j) (root (2 * m)) p := by
    simp only [quotient, ExtremalPolarCenter.physicalCenter]
    ring
  rw [he, norm_mul, norm_real, Real.norm_eq_abs, abs_norm]
  apply (mul_le_of_le_one_left (norm_nonneg _) hβ).trans
  exact quotient_of_pair_bound (evenSequence m u)
    (mul_nonneg (by norm_num) hmodel.error_nonneg)
    (fun j h hh hhn => (model_even_pair_le hm hmodel hh hhn j).1) p

theorem model_center_quotient {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η) (hp : PolarBounds m u η)
    (hβ : ‖β‖ ≤ 1) (hs : sizeBudget (2 * m) ≤ 1 / 16)
    (p : Fin (2 * m) × Fin (2 * m)) :
    ‖quotient (polarCenter m β u) (root (2 * m)) p‖ ≤
      2 * η + 2 * Real.sqrt (sizeBudget (2 * m)) * (4 * η + 2 * Real.sqrt (sizeBudget (2 * m))) := by
  have hθsize : ‖angles m u‖ ≤ 1 / 2 := by
    have ha := angles_size (by omega) u hp
    nlinarith [norm_nonneg (angles m u)]
  have hCsize : ‖ExtremalPolarCenter.physicalCenter m β u‖ ≤ Real.sqrt (sizeBudget (2 * m)) :=
    Real.le_sqrt_of_sq_le (physicalCenter_size (by omega) hβ u hp)
  have hshift := shifted_norm_le (show 0 < 2 * m by omega) (angles m u)
    (ExtremalPolarCenter.physicalCenter m β u) hθsize (physicalCenter_mean_zero (by omega) β u hmodel.periodic hmodel.mean_zero)
  have hpoint := (norm_le_pi_norm (fun j => ExtremalPolarCenter.physicalCenter m β u j -
    translation (angles m u) (ExtremalPolarCenter.physicalCenter m β u)) p.2).trans hshift
  have hb := center_quotient_bound (angles m u)
    (fun j => ExtremalPolarCenter.physicalCenter m β u j -
      translation (angles m u) (ExtremalPolarCenter.physicalCenter m β u)) (root (2 * m)) p
  have hq : quotient (fun j => ExtremalPolarCenter.physicalCenter m β u j -
      translation (angles m u) (ExtremalPolarCenter.physicalCenter m β u)) (root (2 * m)) p =
      quotient (ExtremalPolarCenter.physicalCenter m β u) (root (2 * m)) p := by
    unfold quotient
    congr 1
    ring
  rw [hq] at hb
  change ‖quotient (polarCenter m β u) (root (2 * m)) p‖ ≤ _ at hb
  have hmul := mul_le_mul (show ‖ExtremalPolarCenter.physicalCenter m β u p.2 -
      translation (angles m u) (ExtremalPolarCenter.physicalCenter m β u)‖ ≤
      2 * Real.sqrt (sizeBudget (2 * m)) by linarith only [hpoint, hCsize])
    (model_angle_quotient hm hmodel hp p) (norm_nonneg _) (by positivity : 0 ≤ 2 * Real.sqrt (sizeBudget (2 * m)))
  have hCq := model_physical_quotient hm hmodel hβ p
  exact hb.trans (add_le_add hCq hmul)

end StructuralNote.PolarChordControl

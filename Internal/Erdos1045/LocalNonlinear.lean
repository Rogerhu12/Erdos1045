import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# Nonlinear estimates for the local maximum argument

The only external analytic input in this file is a scalar Taylor bound for
the ordinary logarithm. It is uniform over all complex numbers in a fixed
disc, independent of polygons, Fourier coefficients, and the manuscript.
The finite-sum estimates (6.2)--(6.4) are proved below, not assumed.
-/

namespace Erdos1045.LocalNonlinear

open scoped BigOperators
noncomputable section

/-- A standard consequence of the power series of `log(1+z)`, through degree 2.
This is an explicit classical input, not a project axiom. -/
def ScalarLogTaylor : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ (1 / 2 : ℝ) →
    |2 * Real.log ‖1 + z‖ - 2 * z.re + (z ^ 2).re| ≤ 2 * ‖z‖ ^ 3

theorem pair_log_upper (hTaylor : ScalarLogTaylor) {η : ℝ}
    (_hη : 0 ≤ η) (hsmall : η ≤ 1 / 4) {z : ℂ} (hz : ‖z‖ ≤ 2 * η) :
    2 * Real.log ‖1 + z‖ ≤ 2 * z.re - (z ^ 2).re + 4 * η * ‖z‖ ^ 2 := by
  have ht := (abs_le.mp (hTaylor z (by linarith))).2
  have hm := mul_le_mul_of_nonneg_right hz (sq_nonneg ‖z‖)
  nlinarith

theorem norm_one_add_sq (z : ℂ) :
    ‖1 + z‖ ^ 2 = (1 + z.re) ^ 2 + z.im ^ 2 := by
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem norm_one_add_remainder (z : ℂ) :
    (‖1 + z‖ - (1 + z.re)) * (‖1 + z‖ + 1 + z.re) = z.im ^ 2 := by
  nlinarith [norm_one_add_sq z]

theorem norm_one_add_lower {η : ℝ} (hη : 0 ≤ η) (_hsmall : η ≤ 1 / 4)
    {z : ℂ} (hz : ‖z‖ ≤ η) :
    1 + z.re + z.im ^ 2 / (2 * (1 + η)) ≤ ‖1 + z‖ := by
  have hre := Complex.re_le_norm z
  have hrelo := (abs_le.mp (Complex.abs_re_le_norm z)).1
  have hnorm : ‖1 + z‖ ≤ 1 + η := by
    calc
      ‖1 + z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_add_le _ _
      _ ≤ 1 + η := by simpa using hz
  have hdiff : 0 ≤ ‖1 + z‖ - (1 + z.re) := by
    have h := Complex.re_le_norm (1 + z)
    simp only [Complex.add_re, Complex.one_re] at h
    linarith
  have hfactor : ‖1 + z‖ + 1 + z.re ≤ 2 * (1 + η) := by linarith
  have hprod := mul_le_mul_of_nonneg_left hfactor hdiff
  have hexact := norm_one_add_remainder z
  have hden : 0 < 2 * (1 + η) := by positivity
  have hquot : z.im ^ 2 / (2 * (1 + η)) ≤ ‖1 + z‖ - (1 + z.re) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  linarith

theorem norm_one_add_pos {η : ℝ} (hsmall : η ≤ 1 / 4)
    {z : ℂ} (hz : ‖z‖ ≤ η) : 0 < ‖1 + z‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (-z)
  simp only [norm_one, norm_neg, sub_neg_eq_add] at h
  linarith

section Finite

variable {ι : Type*} [Fintype ι]

def squareEnergy (ρ : ι → ℂ) : ℝ := ∑ i, ‖ρ i‖ ^ 2
def imaginaryEnergy (ρ : ι → ℂ) : ℝ := ∑ i, (ρ i).im ^ 2
def logarithmicGain (ρ : ι → ℂ) : ℝ := ∑ i, 2 * Real.log ‖1 + ρ i‖

theorem squareEnergy_nonneg (ρ : ι → ℂ) : 0 ≤ squareEnergy ρ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem imaginaryEnergy_nonneg (ρ : ι → ℂ) : 0 ≤ imaginaryEnergy ρ :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem imaginaryEnergy_le {η : ℝ} (ρ : ι → ℂ) (hρ : ∀ i, ‖ρ i‖ ≤ η) :
    imaginaryEnergy ρ ≤ Fintype.card ι * η ^ 2 := by
  calc
    imaginaryEnergy ρ ≤ ∑ _i : ι, η ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := (Complex.abs_im_le_norm (ρ i)).trans (hρ i)
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) ((norm_nonneg _).trans (hρ i))).mpr h
    _ = Fintype.card ι * η ^ 2 := by simp

theorem logarithmicGain_upper (hTaylor : ScalarLogTaylor) {η : ℝ}
    (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4) (ρ : ι → ℂ)
    (hρ : ∀ i, ‖ρ i‖ ≤ 2 * η) (hlinear : ∑ i, (ρ i).re = 0) :
    logarithmicGain ρ ≤ -(∑ i, ((ρ i) ^ 2).re) + 4 * η * squareEnergy ρ := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => pair_log_upper hTaylor hη hsmall (hρ i))
  simpa [logarithmicGain, squareEnergy, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hlinear] using hsum

theorem perimeter_sum_lower {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (ρ : ι → ℂ) (hρ : ∀ i, ‖ρ i‖ ≤ η) (hlinear : ∑ i, (ρ i).re = 0) :
    (Fintype.card ι : ℝ) + imaginaryEnergy ρ / (2 * (1 + η)) ≤
      ∑ i, ‖1 + ρ i‖ := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => norm_one_add_lower hη hsmall (hρ i))
  simpa [imaginaryEnergy, Finset.sum_add_distrib, Finset.sum_div, hlinear] using hsum

theorem perimeter_average_lower [Nonempty ι] {η : ℝ}
    (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (ρ : ι → ℂ) (hρ : ∀ i, ‖ρ i‖ ≤ η) (hlinear : ∑ i, (ρ i).re = 0) :
    1 + imaginaryEnergy ρ / (2 * Fintype.card ι * (1 + η)) ≤
      (∑ i, ‖1 + ρ i‖) / Fintype.card ι := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsum := perimeter_sum_lower hη hsmall ρ hρ hlinear
  apply (le_div_iff₀ hn).mpr
  have heq : (1 + imaginaryEnergy ρ / (2 * Fintype.card ι * (1 + η))) *
      Fintype.card ι = (Fintype.card ι : ℝ) + imaginaryEnergy ρ / (2 * (1 + η)) := by
    field_simp
  rw [heq]
  exact hsum

/-- The elementary logarithm estimate used after the exact norm identity. -/
theorem log_average_scalar {n B η : ℝ}
    (hn : 0 < n) (hB : 0 ≤ B) (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hBbound : B ≤ n * η ^ 2) :
    (1 - 2 * η) * B / (2 * n) ≤ Real.log (1 + B / (2 * n * (1 + η))) := by
  let x := B / (2 * n * (1 + η))
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hden : 0 < 2 * n * (1 + η) := by positivity
  have hxbound : x ≤ η ^ 2 / 2 := by
    dsimp [x]
    apply (div_le_iff₀ hden).mpr
    have hη3 : 0 ≤ n * η ^ 3 := by positivity
    nlinarith
  have hlog := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + x by positivity)
  have hratio : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
  rw [hratio] at hlog
  have hxden : 0 < 1 + x := by positivity
  have hcoeff : 0 ≤ (1 - 2 * η) * (1 + η) :=
    mul_nonneg (by linarith) (by linarith)
  have hscalar : (1 - 2 * η) * (1 + η) * (1 + x) ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hxbound hcoeff
    have hη2 : η ^ 2 ≤ η / 4 := by nlinarith
    nlinarith [sq_nonneg η, mul_nonneg hη hx]
  have hclaim : (1 - 2 * η) * B / (2 * n) ≤ x / (1 + x) := by
    apply (le_div_iff₀ hxden).mpr
    have heq : (1 - 2 * η) * B / (2 * n) = (1 - 2 * η) * (1 + η) * x := by
      dsimp [x]
      field_simp
    rw [heq]
    have hmul := mul_le_mul_of_nonneg_right hscalar hx
    nlinarith
  exact hclaim.trans hlog

theorem perimeter_log_lower [Nonempty ι] {η : ℝ}
    (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (ρ : ι → ℂ) (hρ : ∀ i, ‖ρ i‖ ≤ η) (hlinear : ∑ i, (ρ i).re = 0) :
    (1 - 2 * η) * imaginaryEnergy ρ / (2 * Fintype.card ι) ≤
      Real.log ((∑ i, ‖1 + ρ i‖) / Fintype.card ι) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hB := imaginaryEnergy_nonneg ρ
  have hfirst := log_average_scalar hn hB hη hsmall (imaginaryEnergy_le ρ hρ)
  apply hfirst.trans
  apply Real.log_le_log
  · positivity
  · exact perimeter_average_lower hη hsmall ρ hρ hlinear

end Finite

/-- The manuscript's nonlinear upper bound, before Fourier coercivity.
The two index types may have different sizes (pairs versus edges). -/
theorem objective_gain_upper {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (hTaylor : ScalarLogTaylor) {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (pairRatio : ι → ℂ) (edgeRatio : κ → ℂ)
    (hp : ∀ i, ‖pairRatio i‖ ≤ 2 * η) (he : ∀ i, ‖edgeRatio i‖ ≤ η)
    (hpl : ∑ i, (pairRatio i).re = 0) (hel : ∑ i, (edgeRatio i).re = 0) :
    logarithmicGain pairRatio -
        (Fintype.card κ : ℝ) * (Fintype.card κ - 1) *
          Real.log ((∑ i, ‖1 + edgeRatio i‖) / Fintype.card κ) ≤
      -(∑ i, ((pairRatio i) ^ 2).re) -
        (Fintype.card κ - 1) / 2 * imaginaryEnergy edgeRatio +
          4 * η * (squareEnergy pairRatio + Fintype.card κ * imaginaryEnergy edgeRatio) := by
  have hn : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hpair := logarithmicGain_upper hTaylor hη hsmall pairRatio hp hpl
  have hedge := perimeter_log_lower hη hsmall edgeRatio he hel
  have hprod := mul_le_mul_of_nonneg_left hedge
    (show 0 ≤ (Fintype.card κ : ℝ) * (Fintype.card κ - 1) by positivity)
  have hcancel : (Fintype.card κ : ℝ) * (Fintype.card κ - 1) *
      ((1 - 2 * η) * imaginaryEnergy edgeRatio / (2 * Fintype.card κ)) =
      (Fintype.card κ - 1) / 2 * (1 - 2 * η) * imaginaryEnergy edgeRatio := by
    field_simp
  rw [hcancel] at hprod
  have hB := imaginaryEnergy_nonneg edgeRatio
  have hηB := mul_nonneg hη hB
  have hnηB := mul_nonneg hn.le hηB
  nlinarith

end
end Erdos1045.LocalNonlinear

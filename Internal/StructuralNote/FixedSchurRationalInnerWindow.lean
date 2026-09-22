import StructuralNote.FixedSchurRationalReverseEnergy
import StructuralNote.FixedSchurReferenceDisplacement

/-! Recovery of an inner-scale fixed-Schur point satisfies the literal single
rational window. Coordinate recovery is explicit in the hypotheses; no old
tangential energy window is substituted for the selected reference energy. -/

namespace StructuralNote.FixedSchurRationalInnerWindow

open Filter Complex Erdos1045 Erdos1045.EventualExact LensClosure SchurSpectrum
open RationalCommonConfiguration FixedSchurRationalWindowEnergy
open FixedSchurRationalWindowDomain FixedSchurRationalReverseEnergy
open FixedSchurReferenceDisplacement CommonDomainClosure CommonDomainRadius
open FixedSchurChart FixedSchurLinear
open scoped BigOperators Topology
noncomputable section

def innerWindowConstant (B : ℝ) : ℝ :=
  4 * B ^ 2 + (5 / 4 : ℝ) * referenceConstant B + 96120 * B ^ 2

theorem angleMean_sq_le_theta_energy {m : ℕ} (hm : 0 < m)
    (X : RationalConfiguration.Variables m → ℝ) :
    angleMean hm X ^ 2 ≤
      12 * pairEnergy (by omega) (fun j => (theta hm X j : ℂ)) := by
  let j₀ : Fin (2 * m) := ⟨0, by omega⟩
  have hp := DiscreteSobolev.pointwise_sq_le (show 2 ≤ 2 * m by omega)
    (fun j => (theta hm X j : ℂ)) (theta_mean_zero hm X) j₀
  have he : theta hm X j₀ = -angleMean hm X := by
    simp [j₀, theta, RationalAngleBranch.angle, RationalConfiguration.angleParameter]
  simp only [he, norm_real, Real.norm_eq_abs, abs_neg, sq_abs,
    Nat.cast_mul, Nat.cast_ofNat] at hp
  have hn : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hn0 : (0 : ℝ) < 2 * m := by linarith
  have hlog : Real.log (2 * m : ℝ) ≤ (2 * m : ℝ) ^ 2 := by
    have hl := Real.log_le_sub_one_of_pos hn0
    nlinarith [sq_nonneg (2 * (m : ℝ) - 1)]
  have hcoef : 12 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 ≤ 12 := by
    apply (div_le_iff₀ (sq_pos_of_pos hn0)).2
    linarith
  exact hp.trans (mul_le_mul_of_nonneg_right hcoef (pairEnergy_nonneg _ _))

theorem eventual_selectedWindowEnergy_bound (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
      (X : RationalConfiguration.Variables m → ℝ),
      InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 →
      theta (by omega) X = θ →
      normalizedCenter (by omega) (rationalSign s) X =
        center (coordinate (by omega) s θ v) v →
      (∀ j, |extendedAngleParameter (by omega) X j| ≤ 1) →
      selectedWindowEnergy (by omega) s X ≤
        innerWindowConstant B / (2 * m : ℝ) ^ 2 := by
  filter_upwards [eventual_center_reference_energy B hB,
    eventual_fixedReferenceCenter_data] with m hcenter href
  intro hm s θ v X hdom henergy hθ hC hX
  have hangle : pairEnergy (by omega) (fun j => (θ j : ℂ)) ≤
      B ^ 2 / (2 * m : ℝ) ^ 2 := by
    linarith [pairEnergy_nonneg (by omega : 0 < 2 * m) v]
  have ha := parameter_energy_le_four (by omega : 0 < m) X hX
  have hmean := angleMean_sq_le_theta_energy (by omega : 0 < m) X
  rw [hθ] at ha hmean
  have hc := rawCenter_reference_energy_le (by omega : 0 < m) s X
  rw [hC] at hc
  have href := (href hm s).2.2
  have hd := hcenter hm s θ v hdom henergy
  have hmean' : angleMean (by omega) X ^ 2 ≤ 12 * (B ^ 2 / (2 * m : ℝ) ^ 2) := by
    linarith
  have hprod : 5 * angleMean (by omega) X ^ 2 *
      pairEnergy (by omega) (fixedReferenceCenter (by omega) s) ≤
      96120 * (B ^ 2 / (2 * m : ℝ) ^ 2) := by
    calc
      _ ≤ 5 * (12 * (B ^ 2 / (2 * m : ℝ) ^ 2)) * 1602 := by
        gcongr
        exact pairEnergy_nonneg _ _
      _ = _ := by ring
  unfold selectedWindowEnergy innerWindowConstant
  simp only [add_div, mul_div_assoc]
  linarith only [ha, hangle, hc, hd, hprod]

theorem eventual_selectedWindow_of_inner_recovery (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
      (X : RationalConfiguration.Variables m → ℝ),
      InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 →
      theta (by omega) X = θ →
      normalizedCenter (by omega) (rationalSign s) X =
        center (coordinate (by omega) s θ v) v →
      (∀ j, |extendedAngleParameter (by omega) X j| ≤ 1) →
      selectedWindowEnergy (by omega) s X <
        (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro n
    filter_upwards [eventually_ge_atTop n] with m hm
    omega
  have hr := hnat.eventually (fixed_inner_radius_eventually_lt (8 * innerWindowConstant B))
  filter_upwards [eventual_selectedWindowEnergy_bound B hB, hr] with m hbound hrad
  intro hm s θ v X hdom henergy hθ hC hX
  have hb := hbound hm s θ v X hdom henergy hθ hC hX
  unfold energyRadius at hrad
  have hrad' : innerWindowConstant B / (2 * m : ℝ) ^ 2 <
      (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc] at hrad
    rw [show (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) =
      ((logOrder (2 * m) : ℝ) ^ 2 / (2 * m : ℝ) ^ 2) / 8 by ring]
    linarith
  exact hb.trans_lt hrad'

end
end StructuralNote.FixedSchurRationalInnerWindow

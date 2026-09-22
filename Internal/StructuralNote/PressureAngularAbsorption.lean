import StructuralNote.StrongObjectiveEstimate

/-! Absorption of the actual signed angular pressure into the angular and canonical residual energies. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.PressureAngularAbsorption

open Erdos1045 Erdos1045.EventualExact Complex Configuration
open SchurSpectrum SchurLiftBounds DiscreteEnergy FourierMultiplier CanonicalNonlinearError

def angularConstant : ℝ :=
  8 * (24 * Real.pi ^ 3) ^ 2 + 8 * (33 * Real.pi ^ 2) ^ 2 *
    (320 * Real.pi ^ 2 + 64 * Real.pi ^ 2 * (65 * Real.pi ^ 2))

def residualCoefficient (n : ℕ) : ℝ := 192 * (33 * Real.pi ^ 2) ^ 2 * Real.log n / (n : ℝ) ^ 2

theorem angular_budget_absorption {n : ℕ} (hn : 3 ≤ n)
    (c : Points n) (q θ : Fin n → ℝ) (hmean : ∑ j, c j = 0)
    (hq : meanSquare q ≤ 65 * Real.pi ^ 2)
    (hA : pairEnergy (by omega) c ≤ 320 * Real.pi ^ 2) :
    (24 * Real.pi ^ 3 + 33 * Real.pi ^ 2 *
      Real.sqrt (pairEnergy (by omega) c + (n : ℝ) ^ 2 * ‖c‖ ^ 2)) / n *
      Real.sqrt (realEnergy (by omega) θ) ≤ realEnergy (by omega) θ / 16 +
      angularConstant / (n : ℝ) ^ 2 +
      residualCoefficient n * pairEnergy (by omega) (c - SchurLift.canonicalLift q) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hE : 0 ≤ realEnergy (by omega) θ := pairEnergy_nonneg (by omega) _
  have hH : 0 ≤ pairEnergy (by omega) c + (n : ℝ) ^ 2 * ‖c‖ ^ 2 := by
    exact add_nonneg (pairEnergy_nonneg (by omega) _) (by positivity)
  have hsup := center_sup_sq_le hn c q hmean hq
  have hsup' := mul_le_mul_of_nonneg_left hsup (sq_nonneg (n : ℝ))
  have hs : (n : ℝ) ^ 2 * ‖c‖ ^ 2 ≤ 64 * Real.pi ^ 2 * (65 * Real.pi ^ 2) +
      24 * Real.log n * pairEnergy (by omega) (c - SchurLift.canonicalLift q) := by
    convert hsup' using 1 <;> first | rfl | field_simp
  let K := (24 * Real.pi ^ 3 + 33 * Real.pi ^ 2 *
    Real.sqrt (pairEnergy (by omega) c + (n : ℝ) ^ 2 * ‖c‖ ^ 2)) / n
  have hk : K ^ 2 ≤
      (2 * (24 * Real.pi ^ 3) ^ 2 + 2 * (33 * Real.pi ^ 2) ^ 2 *
        (320 * Real.pi ^ 2 + 64 * Real.pi ^ 2 * (65 * Real.pi ^ 2) +
          24 * Real.log n * pairEnergy (by omega) (c - SchurLift.canonicalLift q))) / (n : ℝ) ^ 2 := by
    dsimp only [K]
    rw [div_pow]
    apply div_le_div_of_nonneg_right _ (sq_nonneg (n : ℝ))
    have hh := mul_le_mul_of_nonneg_left (add_le_add hA hs)
      (show 0 ≤ 2 * (33 * Real.pi ^ 2) ^ 2 by positivity)
    have hroot := Real.sq_sqrt hH
    nlinarith only [hh, hroot,
      sq_nonneg (24 * Real.pi ^ 3 - 33 * Real.pi ^ 2 *
        Real.sqrt (pairEnergy (by omega) c + (n : ℝ) ^ 2 * ‖c‖ ^ 2))]
  have hy : K * Real.sqrt (realEnergy (by omega) θ) ≤ realEnergy (by omega) θ / 16 + 4 * K ^ 2 := by
    nlinarith only [sq_nonneg (Real.sqrt (realEnergy (by omega) θ) / 4 - 2 * K), Real.sq_sqrt hE]
  change K * _ ≤ _
  have hbound : 4 * K ^ 2 ≤ angularConstant / (n : ℝ) ^ 2 +
      residualCoefficient n * pairEnergy (by omega) (c - SchurLift.canonicalLift q) := by
    calc
      _ ≤ 4 * ((2 * (24 * Real.pi ^ 3) ^ 2 + 2 * (33 * Real.pi ^ 2) ^ 2 *
          (320 * Real.pi ^ 2 + 64 * Real.pi ^ 2 * (65 * Real.pi ^ 2) +
            24 * Real.log n * pairEnergy (by omega) (c - SchurLift.canonicalLift q))) / (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hk (by norm_num)
      _ = _ := by unfold angularConstant residualCoefficient; ring
  linarith only [hy, hbound]

open Filter

theorem residualCoefficient_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto (fun k => residualCoefficient (N k)) atTop (𝓝 0) := by
  have hl : Tendsto (fun k => Real.log (N k) / (N k : ℝ) ^ 2) atTop (𝓝 0) := by
    have hh := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, Real.rpow_two] using hh.comp (tendsto_natCast_atTop_atTop.comp hN)
  simpa only [residualCoefficient, mul_div_assoc, mul_zero] using hl.const_mul (192 * (33 * Real.pi ^ 2) ^ 2)

end StructuralNote.PressureAngularAbsorption

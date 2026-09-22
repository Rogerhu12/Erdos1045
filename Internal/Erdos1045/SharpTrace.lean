import Erdos1045.Bootstrap
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# A sharp trace bound without asymptotic expansion of its coefficients

Complete the square at the actual finite-n coefficients. This produces an
explicit bound tending to π²/6 and avoids replacing every coefficient by its
limit in an expression containing nE.
-/

namespace Erdos1045.SharpTrace

open Filter
open scoped Topology
noncomputable section

theorem finite_trace_bound {n c δ E S ε T err : ℝ}
    (hn : 1 < n) (hc : 0 < c) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (henergy : E ^ 2 ≤ 8 * Real.pi * c * (1 + ε) * δ)
    (htrace : T ≤ -n * (n - 1) * δ + n * E * Real.sqrt S /
      (c * Real.sqrt (2 * Real.pi)) + err) :
    T ≤ n * (1 + ε) * S / (c * (n - 1)) + err := by
  let a := n * (n - 1) / (8 * Real.pi * c * (1 + ε))
  let b := n * Real.sqrt S / (c * Real.sqrt (2 * Real.pi))
  have hK : 0 < 8 * Real.pi * c * (1 + ε) := by positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hb2 : b ^ 2 = n ^ 2 * S / (c ^ 2 * (2 * Real.pi)) := by
    dsimp [b]
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hS,
      Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)]
  have hquot : b ^ 2 / (4 * a) = n * (1 + ε) * S / (c * (n - 1)) := by
    rw [hb2]
    dsimp [a]
    have hn0 : n ≠ 0 := by linarith
    have hn1 : n - 1 ≠ 0 := by linarith
    have hc0 := hc.ne'
    have he0 : 1 + ε ≠ 0 := by positivity
    have hp0 := Real.pi_ne_zero
    field_simp
    ring
  have hδ : E ^ 2 / (8 * Real.pi * c * (1 + ε)) ≤ δ :=
    (div_le_iff₀ hK).mpr (by simpa [mul_comm] using henergy)
  have hmul := mul_le_mul_of_nonneg_left hδ (show 0 ≤ n * (n - 1) by positivity)
  have hquad := Bootstrap.quadratic_upper_bound a b E ha
  rw [hquot] at hquad
  have haE : n * (n - 1) * (E ^ 2 / (8 * Real.pi * c * (1 + ε))) = a * E ^ 2 := by
    dsimp [a]
    ring
  rw [haE] at hmul
  have hbE : n * E * Real.sqrt S / (c * Real.sqrt (2 * Real.pi)) = b * E := by
    dsimp [b]
    ring
  rw [hbE] at htrace
  nlinarith

theorem finite_upper_eq {n c S ε : ℝ} (hn : n ≠ 0) :
    n * (1 + ε) * S / (c * (n - 1)) =
      (1 + ε) * S / (c * (1 - 1 / n)) := by
  field_simp

/-- Any dimension sequence tending to infinity can be used. -/
theorem upper_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {c S ε err : ℕ → ℝ} {L : ℝ}
    (hc : Tendsto c atTop (𝓝 1)) (hS : Tendsto S atTop (𝓝 L))
    (hε : Tendsto ε atTop (𝓝 0)) (herr : Tendsto err atTop (𝓝 0)) :
    Tendsto (fun j => (1 + ε j) * S j / (c j * (1 - 1 / (N j : ℝ))) + err j)
      atTop (𝓝 L) := by
  have hinv : Tendsto (fun j => (1 : ℝ) / N j) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp
        ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hN))
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hnum := (h1.add hε).mul hS
  have hden := hc.mul (h1.sub hinv)
  have h := (hnum.div hden (by norm_num : (1 : ℝ) * (1 - 0) ≠ 0)).add herr
  simpa using h

/-- A lower comparison at the same constant squeezes the trace and its deficit. -/
theorem squeeze_trace_and_defect {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {c S ε err lower value trace : ℕ → ℝ} {L : ℝ}
    (hc : Tendsto c atTop (𝓝 1)) (hS : Tendsto S atTop (𝓝 L))
    (hε : Tendsto ε atTop (𝓝 0)) (herr : Tendsto err atTop (𝓝 0))
    (hlower : Tendsto lower atTop (𝓝 L))
    (hlo : ∀ᶠ j in atTop, lower j ≤ value j)
    (hmid : ∀ᶠ j in atTop, value j ≤ trace j)
    (hhi : ∀ᶠ j in atTop, trace j ≤
      (1 + ε j) * S j / (c j * (1 - 1 / (N j : ℝ))) + err j) :
    Tendsto trace atTop (𝓝 L) ∧ Tendsto value atTop (𝓝 L) ∧
      Tendsto (fun j => trace j - value j) atTop (𝓝 0) := by
  have hupper := upper_tendsto hN hc hS hε herr
  have ht := tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    (hlo.and hmid |>.mono fun _ h => h.1.trans h.2) hhi
  have hv := tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower ht hlo hmid
  exact ⟨ht, hv, by simpa using ht.sub hv⟩

end
end Erdos1045.SharpTrace


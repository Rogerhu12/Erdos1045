import StructuralNote.CommonFiberGeometry

/-! Smooth local roots in the actual shared angle/tangential parameters, with
agreement on overlapping quantitative branches. -/

namespace StructuralNote.CommonFiberSmooth

open Erdos1045.EventualExact Complex Filter
open FiniteFourierLift SchurSpectrum LensClosure CommonClosureEnergy
open CommonTangentialParameters CommonFiberGeometry
open scoped BigOperators Topology ContDiff
noncomputable section

abbrev FreeParameters (m : ℕ) := (Fin (2 * m) → ℝ) × (Fin (2 * m) → ℂ)

def data {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (x : FreeParameters m) : Parameters m :=
  (phase hm x.1, fun j => 2 * Real.cos (halfAngle hm x.1 j), σ, coordinates hm x.2)

theorem data_contDiff {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) :
    ContDiff ℝ ∞ (data hm σ) := by
  have him : ContDiff ℝ ∞ (Complex.im : ℂ → ℝ) := Complex.imCLM.contDiff
  have hre : ContDiff ℝ ∞ (Complex.re : ℂ → ℝ) := Complex.reCLM.contDiff
  unfold data phase halfAngle angleAverage angleDifference coordinates difference
  fun_prop

theorem double_radius_small {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ) (x : FreeParameters m)
    (hmean : ∑ j, (x.1 j : ℂ) = 0)
    (hθ : pairEnergy (by omega) (fun j => (x.1 j : ℂ)) ≤ 1 / (2 * m))
    (hv : pairEnergy (by omega) x.2 ≤ 1 / (2 * m)) (j : Fin m) :
    |(data (by omega) σ x).1 j - LensClosure.midpoint m j| +
      |(data (by omega) σ x).2.2.2 j| + 2 * (1024 / (2 * m : ℝ) ^ 2) ≤ 1 / 4 := by
  have hmR : (128 : ℝ) ≤ m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have hθ' : pairEnergy (by omega) (fun j => (x.1 j : ℂ)) ≤ 1 / ((2 * m : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hθ
  have hv' : pairEnergy (by omega) x.2 ≤ 1 / ((2 * m : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hv
  have he := angleAverage_le (by omega) x.1 hmean hθ' (halfIndex j)
  have ht := (coordinates_abs_le (by omega) x.2 j).trans
    (difference_of_small_energy (by omega) x.2 hv' (halfIndex j))
  simp only [Nat.cast_mul, Nat.cast_ofNat] at he ht
  have h₁ : (4 : ℝ) / (2 * m) ≤ 1 / 64 := by apply (div_le_iff₀ hn0).mpr; linarith
  have h₂ : (10 : ℝ) / (2 * m) ≤ 5 / 128 := by apply (div_le_iff₀ hn0).mpr; linarith
  have h₃ : (1024 : ℝ) / (2 * m) ^ 2 ≤ 1 / 64 := by
    apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
    nlinarith
  simp only [data, phase, add_sub_cancel_left]
  linarith

theorem exists_smooth_root {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ) (x : FreeParameters m)
    (hσ : ∀ j, |σ j| ≤ 1) (hmean : ∑ j, (x.1 j : ℂ) = 0)
    (hθ : pairEnergy (by omega) (fun j => (x.1 j : ℂ)) ≤ 1 / (2 * m))
    (hv : pairEnergy (by omega) x.2 ≤ 1 / (2 * m)) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2) (hz : closureFamily (data (by omega) σ x) ξ = 0) :
    ∃ g : FreeParameters m → ℂ, g x = ξ ∧ ContDiffAt ℝ ∞ g x ∧
      (∀ᶠ y in 𝓝 x, closureFamily (data (by omega) σ y) (g y) = 0 ∧
        ∀ ζ : ℂ, ‖ζ‖ ≤ 1024 / (2 * m : ℝ) ^ 2 → closureFamily (data (by omega) σ y) ζ = 0 →
          (∑ j, (y.1 j : ℂ)) = 0 →
          pairEnergy (by omega) (fun j => (y.1 j : ℂ)) ≤ 1 / (2 * m) →
          pairEnergy (by omega) y.2 ≤ 1 / (2 * m) → g y = ζ) := by
  have hR : (0 : ℝ) < 1024 / (2 * m : ℝ) ^ 2 := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  obtain ⟨g, hgx, hg, he⟩ := exists_smooth_closure_root_agree_ball (by omega)
    (data (by omega) σ x) ξ hR hσ (double_radius_small hm σ x hmean hθ hv) hξ hz
  refine ⟨fun y => g (data (by omega) σ y), hgx,
    hg.comp x (data_contDiff (by omega) σ).contDiffAt, ?_⟩
  have hh := (data_contDiff (by omega) σ).continuous.continuousAt.eventually he
  filter_upwards [hh] with y hy
  refine ⟨hy.1, ?_⟩
  intro ζ hζ hzero hmean' hθ' hv'
  exact hy.2 hσ (double_radius_small hm σ y hmean' hθ' hv') ζ hζ hzero

theorem integral_contDiff (n : ℕ) : ContDiff ℝ ∞ (@FiniteFourierLift.integral n) := by
  unfold FiniteFourierLift.integral integralCoefficients FourierMultiplier.synthesis FourierMultiplier.coefficient
  apply contDiff_pi.mpr
  intro j
  apply ContDiff.sum
  intro p _
  by_cases hp : p.val = 0
  · simp only [if_pos hp, zero_mul]
    exact contDiff_const
  · simp only [if_neg hp]
    fun_prop

theorem fiberIncrement_contDiffAt {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (p : FreeParameters m × ℂ) (j : Fin m)
    (ht : |heightParameter (coordinates hm p.1.2) p.2 j| < 2) :
    ContDiffAt ℝ ∞ (fun u : FreeParameters m × ℂ => fiberIncrement hm u.1.1 u.1.2 σ u.2 j) p := by
  have hdata : ContDiff ℝ ∞ (fun u : FreeParameters m × ℂ => (data hm σ u.1, u.2)) := by
    have hd := data_contDiff hm σ
    fun_prop
  have hheight : ContDiffAt ℝ ∞ (fun u : FreeParameters m × ℂ =>
      heightParameter (coordinates hm u.1.2) u.2 j) p :=
    ((heightParameter_contDiff j).comp hdata).contDiffAt
  have hsqrt : ContDiffAt ℝ ∞ (fun u : FreeParameters m × ℂ =>
      Lens.height (heightParameter (coordinates hm u.1.2) u.2 j)) p := by
    unfold Lens.height
    apply (contDiffAt_const.sub (hheight.pow 2)).sqrt
    have hsq : heightParameter (coordinates hm p.1.2) p.2 j ^ 2 < 4 := by
      nlinarith [(abs_lt.mp ht).1, (abs_lt.mp ht).2]
    dsimp
    linarith
  have hcast : ContDiff ℝ ∞ (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  unfold fiberIncrement LensClosure.increment Lens.width unit phase halfAngle angleAverage angleDifference
  fun_prop

theorem center_contDiffAt {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (p : FreeParameters m × ℂ) (ht : ∀ j, |heightParameter (coordinates hm p.1.2) p.2 j| < 2) :
    ContDiffAt ℝ ∞ (fun u : FreeParameters m × ℂ => center hm u.1.1 u.1.2 σ u.2) p := by
  have hh : ContDiffAt ℝ ∞ (fun u : FreeParameters m × ℂ =>
      BoxLensLift.repeatHalf hm (fiberIncrement hm u.1.1 u.1.2 σ u.2)) p := by
    apply contDiffAt_pi.mpr
    intro j
    exact fiberIncrement_contDiffAt hm σ p ⟨j.val % m, Nat.mod_lt _ hm⟩ (ht _)
  exact (integral_contDiff (2 * m)).contDiffAt.comp p hh

theorem configuration_contDiffAt {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (p : FreeParameters m × ℂ) (ht : ∀ j, |heightParameter (coordinates hm p.1.2) p.2 j| < 2) :
    ContDiffAt ℝ ∞ (fun u : FreeParameters m × ℂ => configuration hm u.1.1 u.1.2 σ u.2) p := by
  have hc := center_contDiffAt hm σ p ht
  have hd : ContDiff ℝ ∞ (fun u : FreeParameters m × ℂ => diameterVector u.1.1) := by
    unfold diameterVector unit
    have hcast : ContDiff ℝ ∞ (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
    fun_prop
  exact hd.contDiffAt.add hc

/-- Smoothness includes the actual reconstructed configuration, rather than
only the implicit two-dimensional closure variable. -/
theorem exists_smooth_configuration {m : ℕ} (hm : 128 ≤ m) (σ : Fin m → ℝ) (x : FreeParameters m)
    (hσ : ∀ j, |σ j| ≤ 1) (hmean : ∑ j, (x.1 j : ℂ) = 0)
    (hθ : pairEnergy (by omega) (fun j => (x.1 j : ℂ)) ≤ 1 / (2 * m))
    (hv : pairEnergy (by omega) x.2 ≤ 1 / (2 * m)) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2) (hz : closureFamily (data (by omega) σ x) ξ = 0) :
    ∃ g : FreeParameters m → ℂ, g x = ξ ∧ ContDiffAt ℝ ∞ g x ∧
      ContDiffAt ℝ ∞ (fun y => configuration (by omega) y.1 y.2 σ (g y)) x ∧
      (∀ᶠ y in 𝓝 x, closureFamily (data (by omega) σ y) (g y) = 0) := by
  obtain ⟨g, hgx, hg, he⟩ := exists_smooth_root hm σ x hσ hmean hθ hv hξ hz
  have ht (j : Fin m) : |heightParameter (coordinates (by omega) x.2) ξ j| < 2 := by
    have hd := double_radius_small hm σ x hmean hθ hv j
    have hh : |heightParameter (coordinates (by omega) x.2) ξ j| ≤ |coordinates (by omega) x.2 j| + ‖ξ‖ :=
      (abs_add_le _ _).trans (add_le_add le_rfl (harmonicFunctional_le_norm _ ξ))
    have hR : (0 : ℝ) ≤ 1024 / (2 * m : ℝ) ^ 2 := by positivity
    dsimp [data] at hd
    linarith [abs_nonneg (phase (by omega) x.1 j - LensClosure.midpoint m j)]
  have hc : ContDiffAt ℝ ∞ (fun u : FreeParameters m × ℂ =>
      configuration (by omega) u.1.1 u.1.2 σ u.2) (x, g x) := by
    rw [hgx]
    exact configuration_contDiffAt (by omega) σ (x, ξ) ht
  have hp : ContDiffAt ℝ ∞ (fun y : FreeParameters m => (y, g y)) x := contDiffAt_id.prodMk hg
  refine ⟨g, hgx, hg, ?_, he.mono (fun _ h => h.1)⟩
  simpa only [Function.comp_def] using hc.comp x hp

end
end StructuralNote.CommonFiberSmooth

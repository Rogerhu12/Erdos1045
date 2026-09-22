import EventualExact.NormalizedPolarRepresentation

/-! The radial interpolation has bounded actual pair energy and small adjacent increments. -/

namespace Erdos1045.EventualExact.RadialDeficitControl

open Complex Configuration CommonLocalization AntipodalDecomposition
open PolarAngleControl PolarRepresentation SchurSpectrum DiscreteEnergy
open scoped BigOperators
noncomputable section

theorem pairEnergy_le_mass {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) :
    pairEnergy hn c ≤ (n : ℝ) ^ 2 / 8 * ∑ j, normSq (c j) := by
  have hw (p : Fin n) : weight n p ≤ (n : ℝ) ^ 2 / 4 := by
    unfold weight
    nlinarith [sq_nonneg ((p : ℝ) - n / 2)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
    mul_le_mul_of_nonneg_right (hw p) (normSq_nonneg (FourierMultiplier.coefficient c p)))
  rw [pairEnergy_spectrum hn, parseval hn]
  have h := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ n / 2 by positivity)
  rw [← Finset.mul_sum] at h
  nlinarith

theorem radialColumn_energy {n : ℕ} (hn : 0 < n) (b : Fin n → ℝ)
    (hb : ∀ j, 0 ≤ b j) :
    pairEnergy hn (fun j => (b j : ℂ) * LocalPhase.regularRoot n ^ (j : ℕ)) ≤
      ((n : ℝ) * ∑ j, b j) ^ 2 / 8 := by
  have he := pairEnergy_le_mass hn (fun j => (b j : ℂ) * LocalPhase.regularRoot n ^ (j : ℕ))
  have hnorm (j : Fin n) : normSq ((b j : ℂ) * LocalPhase.regularRoot n ^ (j : ℕ)) = b j ^ 2 := by
    rw [normSq_eq_norm_sq, norm_mul, norm_pow, LocalChord.root_norm, one_pow, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hnorm] at he
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun j _ => hb j)
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (n : ℝ) ^ 2 / 8 by positivity)
  calc
    _ ≤ _ := he.trans hm
    _ = _ := by ring

def deficit (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (j : ℕ) : ℝ := 1 - radius m r u j

theorem radius_difference_le (m : ℕ) {r : ℝ} (hr : 0 ≤ r) (u : ℕ → ℂ) (i j : ℕ) :
    |radius m r u j - radius m r u i| ≤ r *
      (‖oddSequence m u j - oddSequence m u i‖ + ‖oddSequence m u i‖ * ‖reference m j - reference m i‖) := by
  unfold radius
  rw [← mul_sub, abs_mul, abs_of_nonneg hr]
  apply mul_le_mul_of_nonneg_left _ hr
  have hl := abs_norm_sub_norm_le (1 + rotatedOdd m u j) (1 + rotatedOdd m u i)
  simp only [add_sub_add_left_eq_sub] at hl
  exact hl.trans (divided_difference_unit_bound (reference_norm m j) (reference_norm m i))

theorem deficit_step_bound {m : ℕ} (hm : 0 < m) {r η : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hη : 0 ≤ η) (u : ℕ → ℂ)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot (2 * m) - 1‖)
    (hsize : ∀ j, ‖oddSequence m u j‖ ^ 2 ≤ sizeBudget (2 * m)) (j : ℕ) :
    (2 * m : ℝ) * |deficit m r u (j + 1) - deficit m r u j| ≤ angleStepBudget (2 * m) η / 2 := by
  have hd := radius_difference_le m hr u j (j + 1)
  have he : ‖reference m (j + 1) - reference m j‖ = ‖LocalPhase.regularRoot (2 * m) - 1‖ := root_adjacent_norm _ _
  rw [he] at hd
  have hs := odd_step_le m u hstep j
  have ho := Real.le_sqrt_of_sq_le (hsize j)
  have hdrop : r * (‖oddSequence m u (j + 1) - oddSequence m u j‖ +
      ‖oddSequence m u j‖ * ‖LocalPhase.regularRoot (2 * m) - 1‖) ≤
      ‖oddSequence m u (j + 1) - oddSequence m u j‖ +
      ‖oddSequence m u j‖ * ‖LocalPhase.regularRoot (2 * m) - 1‖ :=
    mul_le_of_le_one_left (by positivity) hr1
  have hpoint : |radius m r u (j + 1) - radius m r u j| ≤
      (η + Real.sqrt (sizeBudget (2 * m))) * ‖LocalPhase.regularRoot (2 * m) - 1‖ := by
    have h0 := hd.trans hdrop
    have h1 := mul_le_mul_of_nonneg_right ho (norm_nonneg (LocalPhase.regularRoot (2 * m) - 1))
    nlinarith
  have hnR : (0 : ℝ) < 2 * m := by positivity
  have hedge := DiscreteEnergy.symbol_norm_upper (2 * m) 1
  simp only [FiniteFourierLift.differenceSymbol, pow_one, Nat.cast_one, mul_one,
    Nat.cast_mul, Nat.cast_ofNat] at hedge
  have hedge' := (le_div_iff₀ hnR).mp hedge
  have h2 := mul_le_mul_of_nonneg_left hpoint hnR.le
  have h3 := mul_le_mul_of_nonneg_left hedge' (show 0 ≤ η + Real.sqrt (sizeBudget (2 * m)) by positivity)
  have hb : deficit m r u (j + 1) - deficit m r u j =
      -(radius m r u (j + 1) - radius m r u j) := by unfold deficit; ring
  rw [hb, abs_neg]
  unfold angleStepBudget
  nlinarith

theorem model_deficit_energy {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hη : η ≤ 1 / 4)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hE : ExtremalEnergyBound.totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2) :
    pairEnergy (by omega) (fun j : Fin (2 * m) =>
      (deficit m ‖β‖ u j : ℂ) * reference m j) ≤ 8192 * Real.pi ^ 4 := by
  have hb (j : Fin (2 * m)) : 0 ≤ deficit m ‖β‖ u j :=
    sub_nonneg.mpr (model_radius_le_one (by omega) h hz.1 j)
  have ht := (ExtremalScaleBound.model_matching_deficit_bound hm h hη hz hE).2.2
  simp_rw [model_matching_norm (by omega) h] at ht
  have hn := radialColumn_energy (show 0 < 2 * m by omega) (fun j : Fin (2 * m) => deficit m ‖β‖ u j) hb
  have hτ0 : 0 ≤ (2 * m : ℝ) * ∑ j : Fin (2 * m), deficit m ‖β‖ u j :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => hb j)
  have hτ : (2 * m : ℝ) * ∑ j : Fin (2 * m), deficit m ‖β‖ u j ≤ 256 * Real.pi ^ 2 := ht
  have hs := pow_le_pow_left₀ hτ0 hτ 2
  change pairEnergy (by omega) (fun j : Fin (2 * m) => (deficit m ‖β‖ u j : ℂ) * reference m j) ≤ _ at hn
  push_cast at hn
  nlinarith

end
end Erdos1045.EventualExact.RadialDeficitControl

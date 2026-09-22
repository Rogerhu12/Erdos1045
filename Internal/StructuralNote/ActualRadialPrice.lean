import StructuralNote.ActualRadialGradient

/-! The radial loss for genuine diameter maximizers, with its gradient hypothesis discharged. -/

noncomputable section
open scoped BigOperators Topology

namespace StructuralNote.ActualRadialPrice

open Erdos1045 Erdos1045.EventualExact Complex Filter Configuration CommonLocalization
open PolarAngleControl PolarRepresentation RadialDeficitControl RadialInterpolationQuotients
open ActualRadialGradient RadialObjectivePrice

def actualPath (m : ℕ) (r : ℝ) (u : ℕ → ℂ) (t : ℝ) : Points (2 * m) :=
  path (fun j => angle m u j) (fun j => deficit m r u j) (fun j => deangledCenter m r u j) t

def actualMass (m : ℕ) (r : ℝ) (u : ℕ → ℂ) : ℝ :=
  mass (fun j : Fin (2 * m) => deficit m r u j)

theorem quotient_small_injective {n : ℕ} (hn : 0 < n) (u : ℕ → ℂ)
    (hpair : ∀ i h : ℕ, 0 < h → h < n → ‖LocalDFT.pairRatio n u i h‖ ≤ 1 / 2) :
    Function.Injective (fun j : Fin n => LocalPhase.regularRoot n ^ (j : ℕ) + u j) := by
  have hne (i j : Fin n) (hij : i.val < j.val) :
      LocalPhase.regularRoot n ^ (i : ℕ) + u i ≠ LocalPhase.regularRoot n ^ (j : ℕ) + u j := by
    intro he
    have hh : 0 < j.val - i.val := by omega
    have hhn : j.val - i.val < n := by omega
    have hd := LocalDFT.vertex_difference_ne_zero hn hh hhn i.val
    have hb := hpair i.val (j.val - i.val) hh hhn
    have he' : u j - u i = -(LocalPhase.regularRoot n ^ (j : ℕ) - LocalPhase.regularRoot n ^ (i : ℕ)) := by
      linear_combination -he
    unfold LocalDFT.pairRatio at hb
    rw [Nat.add_sub_of_le (Nat.le_of_lt hij)] at hb hd
    rw [he', neg_div, div_self hd, norm_neg, norm_one] at hb
    norm_num at hb
  intro i j hij
  rcases lt_trichotomy i.val j.val with h | h | h
  · exact (hne i j h hij).elim
  · exact Fin.ext h
  · exact (hne j i h hij.symm).elim

theorem model_path_injective {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η) (hη : η ≤ 1 / 4)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hE : ExtremalEnergyBound.totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2)
    (hp : PolarBounds m u η) (hsmall : pairBudget (2 * m) η ≤ 1 / 2)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : Function.Injective (actualPath m ‖β‖ u t) := by
  rw [actualPath, radial_path_identity]
  exact quotient_small_injective (by omega) _ (fun i h hh hhn =>
    (model_path_pair_le hm hmodel hη hz hE hp ht hh hhn i).trans hsmall)

theorem model_radial_price {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η ε : ℝ}
    (hmodel : NormalizedRelativeEdgeModel z σ α β u η) (hη : η ≤ 1 / 4)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hE : ExtremalEnergyBound.totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2)
    (hp : PolarBounds m u η) (hsmall : pairBudget (2 * m) η ≤ 1 / 2)
    (hgrad : ∀ t ∈ Set.Icc (0 : ℝ) 1, gradientDeviation (actualPath m ‖β‖ u t) ≤ ε) :
    Real.log (discriminant (actualPath m ‖β‖ u 1)) ≤
      Real.log (discriminant (actualPath m ‖β‖ u 0)) -
        (1 - 1 / ((2 * m : ℕ) : ℝ) - ε - 2 * Real.sqrt (sizeBudget (2 * m))) * actualMass m ‖β‖ u := by
  apply finite_price (by omega)
  · intro i
    exact sub_nonneg.mpr (model_radius_le_one (by omega) hmodel hz.1 i)
  · positivity
  · intro i
    have hs := Real.le_sqrt_of_sq_le (hp.angle_size i)
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hs
    norm_num at hs
    exact hs
  · intro t ht
    exact model_path_injective hm hmodel hη hz hE hp hsmall ht
  · exact hgrad

theorem eventual_model_radial_price {M : ℕ → ℕ} (hM : Tendsto M atTop atTop)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ (z : Points (2 * M k)) (σ : Equiv.Perm (Fin (2 * M k)))
      (α β : ℂ) (u : ℕ → ℂ),
      NormalizedRelativeEdgeModel z σ α β u (η k) → ExtremalNormalization.DiameterExtremal z →
      ExtremalEnergyBound.totalEnergy (2 * M k) u ≤ 32 * Real.pi ^ 2 →
      Real.log (discriminant (actualPath (M k) ‖β‖ u 1)) ≤
        Real.log (discriminant (actualPath (M k) ‖β‖ u 0)) -
          (1 - ε) * actualMass (M k) ‖β‖ u := by
  have hN : Tendsto (fun k => 2 * M k) atTop atTop := tendsto_atTop_mono (fun _ => by omega) hM
  have hg := eventual_model_path_gradient hM hη (show 0 < ε / 3 by linarith)
  have hi : Tendsto (fun k => 1 / ((2 * M k : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN :
        Tendsto (fun k => ((2 * M k : ℕ) : ℝ)) atTop atTop)
  have hs := (Real.continuous_sqrt.tendsto 0).comp (sizeBudget_tendsto hN)
  have hc : Tendsto (fun k => 1 / ((2 * M k : ℕ) : ℝ) + ε / 3 +
      2 * Real.sqrt (sizeBudget (2 * M k))) atTop (𝓝 (ε / 3)) := by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero, zero_add, add_zero] using
      (hi.add_const (ε / 3)).add (hs.const_mul 2)
  filter_upwards [hg, hM.eventually_ge_atTop 2,
    hη.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4),
    (pairBudget_tendsto hN hη).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2),
    (sizeBudget_tendsto hN).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4),
    hc.eventually_le_const (show ε / 3 < ε by linarith)] with k hk hm he hb hs hc
  intro z σ α β u hmodel hz hE
  have hp := model_polar_bounds hm hmodel hE hs
  have hprice := model_radial_price hm hmodel he hz hE hp hb (hk z σ α β u hmodel hz hE hp)
  have hmass : 0 ≤ actualMass (M k) ‖β‖ u := by
    unfold actualMass mass
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Finset.sum_nonneg (fun j _ => sub_nonneg.mpr (model_radius_le_one (by omega) hmodel hz.1 j))
  have hcoeff : 1 - ε ≤ 1 - 1 / ((2 * M k : ℕ) : ℝ) - ε / 3 -
      2 * Real.sqrt (sizeBudget (2 * M k)) := by linarith only [hc]
  have hmul := mul_le_mul_of_nonneg_right hcoeff hmass
  linarith only [hprice, hmul]

/-- Every growing family of genuine diameter maximizers admits actual coordinates
whose radial interpolation loses asymptotically the full radial mass. -/
theorem diameter_sequence_radial_price {M : ℕ → ℕ} (hM2 : ∀ k, 2 ≤ M k)
    (hM : Tendsto M atTop atTop) (z : ∀ k, Points (2 * M k))
    (hz : ∀ k, ExtremalNormalization.DiameterExtremal (z k)) :
    ∃ (σ : ∀ k, Equiv.Perm (Fin (2 * M k))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ), Tendsto η atTop (𝓝 0) ∧
      (∀ᶠ k in atTop, NormalizedRelativeEdgeModel (z k) (σ k) (α k) (β k) (u k) (η k)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        Real.log (discriminant (actualPath (M k) ‖β k‖ (u k) 1)) ≤
          Real.log (discriminant (actualPath (M k) ‖β k‖ (u k) 0)) -
            (1 - ε) * actualMass (M k) ‖β k‖ (u k) := by
  obtain ⟨σ, α, β, u, η, hη, _, _, hgood⟩ := diameter_sequence_polar_bounds hM2 hM z hz
  refine ⟨σ, α, β, u, η, hη, hgood.mono (fun _ h => h.1), ?_⟩
  intro ε hε
  filter_upwards [hgood, eventual_model_radial_price hM hη hε] with k hk hp
  exact hp (z k) (σ k) (α k) (β k) (u k) hk.1 (hz k) hk.2.1

end StructuralNote.ActualRadialPrice

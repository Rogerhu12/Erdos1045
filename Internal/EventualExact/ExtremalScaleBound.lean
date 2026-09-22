import EventualExact.LocalTaylorRemainder
import EventualExact.AntipodalDecomposition

/-! Discriminant maximality bounds the loss of the actual similarity scale. -/

namespace Erdos1045.EventualExact.ExtremalScaleBound

open Complex Configuration HullGeometry CommonLocalization ExtremalEnergyBound LocalTaylorRemainder
open scoped BigOperators
noncomputable section

theorem pairTerm_le_energyA (n : ℕ) (u : ℕ → ℂ) :
    pairTerm n u ≤ LocalDFT.energyA n u := by
  have hpoint (w : ℂ) : -(w * w).re ≤ normSq w := by
    have hh := (abs_le.mp (Complex.abs_re_le_norm (w * w))).1
    rw [norm_mul, ← pow_two, ← Complex.normSq_eq_norm_sq] at hh
    linarith
  have hs := Finset.sum_le_sum (s := (Finset.range n).erase 0) fun h _ =>
    Finset.sum_le_sum (s := Finset.range n) fun j _ => hpoint (LocalDFT.pairRatio n u j h)
  unfold pairTerm LocalDFT.energyA
  simp only [Complex.div_ofNat_re, Complex.re_sum]
  simp only [Finset.sum_neg_distrib] at hs
  linarith

theorem pair_gain_upper {n : ℕ} (hn : 4 ≤ n) (u : ℕ → ℂ)
    (hu : Function.Periodic u n)
    (hsim : (∑ j ∈ Finset.range n, u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖) :
    (∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n,
      2 * Real.log ‖1 + LocalDFT.pairRatio n u j h‖) / 2 ≤ 2 * LocalDFT.energyA n u := by
  have HF := ClosedFourier.orthogonality n (show 0 < n by omega)
  have hpair (h : ℕ) (hh : h ∈ (Finset.range n).erase 0) :
      (∑ j ∈ Finset.range n, 2 * Real.log ‖1 + LocalDFT.pairRatio n u j h‖) ≤
        -(∑ j ∈ Finset.range n, (LocalDFT.pairRatio n u j h ^ 2).re) +
          4 * η * ∑ j ∈ Finset.range n, normSq (LocalDFT.pairRatio n u j h) := by
    have hm := Finset.mem_erase.mp hh
    have hl := LocalMaximum.ratio_linear_sum_zero ClosedFourier.dftInversion
      (show 0 < n by omega) HF u hu hsim (by omega) (Finset.mem_range.mp hm.2)
    have hp := Finset.sum_le_sum (s := Finset.range n) (fun j _ =>
      LocalNonlinear.pair_log_upper LocalNonlinear.scalarLogTaylor hη hsmall
        (LocalMaximum.pair_ratio_bound ClosedFourier.geometricSine hn u hu hη hstep hh j))
    simpa [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hl, Complex.normSq_eq_norm_sq] using hp
  have hs := Finset.sum_le_sum (s := (Finset.range n).erase 0) hpair
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at hs
  have hP := pairTerm_le_energyA n u
  have hA := LocalMaximum.energyA_nonneg n u
  have hmul := mul_le_mul_of_nonneg_right hsmall hA
  unfold pairTerm at hP
  unfold LocalDFT.energyA at hP hA hmul ⊢
  simp only [Complex.div_ofNat_re, Complex.re_sum, ← pow_two] at hP
  simp only [← Finset.mul_sum]
  nlinarith

theorem perturbed_discriminant_gain {n : ℕ} (hn : 4 ≤ n) (u : ℕ → ℂ)
    (hu : Function.Periodic u n)
    (hsim : (∑ j ∈ Finset.range n, u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖) :
    Real.log (discriminant (fun i : Fin n => LocalObjective.perturbedVertices n u i)) -
      Real.log ((n : ℝ) ^ n) ≤ 2 * LocalDFT.energyA n u := by
  have hinj := LocalConfiguration.small_perturbation_injective ClosedFourier.geometricSine
    hn u hu hη hsmall hstep
  have hp := LocalConfiguration.logDistanceProduct_eq_sum (LocalObjective.perturbedVertices n u)
    (LocalConfiguration.periodic_of_perturbed (by omega) u hu)
  rw [← LocalConfiguration.logDiscriminant_eq_sum _ hinj] at hp
  have hregp : Function.Periodic (LocalObjective.regularVertices n) n := by
    intro j
    simp [LocalObjective.regularVertices, pow_add, LocalDFT.regularRoot_pow (by omega : 0 < n)]
  have he : (fun i : Fin n => LocalObjective.regularVertices n i) = regular n := by
    funext i
    exact LocalRigidity.root_power_eq_regular n i
  have hr := LocalConfiguration.logDistanceProduct_eq_sum (LocalObjective.regularVertices n) hregp
  have hreginj : Function.Injective (fun i : Fin n => LocalObjective.regularVertices n i) := by
    rw [he]
    exact LocalConfiguration.regular_injective hn ClosedFourier.geometricSine
  rw [← LocalConfiguration.logDiscriminant_eq_sum _ hreginj, he,
    ExtremalNormalization.provedGeometry.regular_discriminant n (by omega)] at hr
  have hdiff := LocalObjective.pair_log_difference ClosedFourier.geometricSine hn u hu hη hsmall hstep
  rw [hp, hr] at hdiff
  rw [hdiff]
  exact pair_gain_upper hn u hu hsim hη hsmall hstep

theorem model_log_scale_bound {n : ℕ} {z : Points n} {σ : Equiv.Perm (Fin n)}
    {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hn : 4 ≤ n) (hη : η ≤ 1 / 4)
    (hD : (n : ℝ) ^ n ≤ discriminant z) (hE : totalEnergy n u ≤ 32 * Real.pi ^ 2) :
    -(exponent n : ℝ) * Real.log ‖β‖ ≤ 64 * Real.pi ^ 2 := by
  let p : Points n := fun i => LocalObjective.perturbedVertices n u i
  have hinj : Function.Injective p := LocalConfiguration.small_perturbation_injective
    ClosedFourier.geometricSine hn u h.periodic h.error_nonneg hη h.relative_edges
  have hp := discriminant_pos p hinj
  have hb : 0 < ‖β‖ := norm_pos_iff.mpr h.scale_ne_zero
  have hrep : z ∘ σ = fun i => α + β * p i := funext h.coordinates
  have hscale : discriminant z = ‖β‖ ^ exponent n * discriminant p := by
    rw [← discriminant_perm z σ, hrep, discriminant_affine]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog := Real.log_le_log (pow_pos hnR n) hD
  rw [hscale, Real.log_mul (pow_pos hb _).ne' hp.ne', Real.log_pow] at hlog
  have hpair := perturbed_discriminant_gain hn u h.periodic h.similarity_zero
    h.error_nonneg hη h.relative_edges
  change Real.log (discriminant p) - Real.log ((n : ℝ) ^ n) ≤ _ at hpair
  simp only [Real.log_pow] at hlog hpair
  have hB := mul_nonneg hnR.le (LocalMaximum.energyB_nonneg n u)
  unfold totalEnergy at hE
  linarith

theorem scale_square_deficit_le {n : ℕ} (hn : 4 ≤ n) {b C : ℝ} (hb : 0 < b)
    (hC : 0 ≤ C) (hlog : -(exponent n : ℝ) * Real.log b ≤ C) :
    (n : ℝ) ^ 2 * (1 - b ^ 2) ≤ 4 * C := by
  by_cases hb1 : b ≤ 1
  · have hl : 0 ≤ -Real.log b := neg_nonneg.mpr (Real.log_nonpos hb.le hb1)
    have hs := Real.log_le_sub_one_of_pos (sq_pos_of_pos hb)
    rw [Real.log_pow] at hs
    norm_num at hs
    have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (n : ℝ))
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have he : (exponent n : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
      simp only [exponent, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    rw [he] at hlog
    have hratio : (n : ℝ) ^ 2 ≤ 2 * ((n : ℝ) * ((n : ℝ) - 1)) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hratio (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hl)
    nlinarith
  · have hdef : 1 - b ^ 2 ≤ 0 := by nlinarith
    exact (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hdef).trans (by positivity)

theorem model_scale_deficit_bound {n : ℕ} {z : Points n} {σ : Equiv.Perm (Fin n)}
    {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hn : 4 ≤ n) (hη : η ≤ 1 / 4)
    (hz : ExtremalNormalization.DiameterExtremal z) (hE : totalEnergy n u ≤ 32 * Real.pi ^ 2) :
    (n : ℝ) ^ 2 * (1 - ‖β‖ ^ 2) ≤ 256 * Real.pi ^ 2 := by
  have hlog := model_log_scale_bound h hn hη (hz.discriminant_ge (by omega)) hE
  have hh := scale_square_deficit_le hn (norm_pos_iff.mpr h.scale_ne_zero)
    (by positivity : 0 ≤ 64 * Real.pi ^ 2) hlog
  nlinarith

theorem model_matching_deficit_bound {m : ℕ} (hm : 2 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hη : η ≤ 1 / 4)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hE : totalEnergy (2 * m) u ≤ 32 * Real.pi ^ 2) :
    ‖β‖ ≤ 1 ∧
      (2 * m : ℝ) ^ 2 * (1 - ‖β‖ ^ 2) ≤ 256 * Real.pi ^ 2 ∧
      (2 * m : ℝ) * (∑ j, (1 - ‖AntipodalDecomposition.oddPart
        (FourierMultiplier.halfTurn (by omega)) (z ∘ σ) j‖)) ≤ 256 * Real.pi ^ 2 := by
  have hb := AntipodalDecomposition.normalized_model_scale_deficit hm h hz.1
  have hd := model_scale_deficit_bound h (by omega) hη hz hE
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hd
  exact ⟨hb.1, hd, hb.2.trans hd⟩

theorem norm_scale_lower_of_deficit {n : ℕ} (hn : 0 < n) {β : ℂ} {C : ℝ}
    (hb : ‖β‖ ≤ 1) (hdef : (n : ℝ) ^ 2 * (1 - ‖β‖ ^ 2) ≤ C) :
    1 - C / (n : ℝ) ^ 2 ≤ ‖β‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : ‖β‖ ^ 2 ≤ ‖β‖ := by nlinarith [norm_nonneg β]
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (n : ℝ))
  have hh : 1 - ‖β‖ ≤ C / (n : ℝ) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hnR)).2
    nlinarith
  linarith


open Filter
open scoped Topology

/-- The scale and actual antipodal matching deficits are uniformly bounded for
all growing even-order diameter-maximizing configurations. -/
theorem even_diameter_sequence_matching_bound {M : ℕ → ℕ} (hM2 : ∀ j, 2 ≤ M j)
    (hM : Tendsto M atTop atTop) (z : ∀ j, Points (2 * M j))
    (hz : ∀ j, ExtremalNormalization.DiameterExtremal (z j)) :
    ∃ (σ : ∀ j, Equiv.Perm (Fin (2 * M j))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ),
      Tendsto η atTop (𝓝 0) ∧ ∀ᶠ j in atTop,
        NormalizedRelativeEdgeModel (z j) (σ j) (α j) (β j) (u j) (η j) ∧
        totalEnergy (2 * M j) (u j) ≤ 32 * Real.pi ^ 2 ∧
        ‖β j‖ ≤ 1 ∧
        (2 * M j : ℝ) ^ 2 * (1 - ‖β j‖ ^ 2) ≤ 256 * Real.pi ^ 2 ∧
        (2 * M j : ℝ) * (∑ i, (1 - ‖AntipodalDecomposition.oddPart
          (FourierMultiplier.halfTurn (by have := hM2 j; omega)) (z j ∘ σ j) i‖)) ≤ 256 * Real.pi ^ 2 := by
  have hN4 (j) : 4 ≤ 2 * M j := by have := hM2 j; omega
  have hN : Tendsto (fun j => 2 * M j) atTop atTop :=
    tendsto_atTop_mono (fun _ => by omega) hM
  obtain ⟨σ, α, β, u, η, hη, hm⟩ := diameter_sequence_energy hN4 hN z hz
  refine ⟨σ, α, β, u, η, hη, ?_⟩
  filter_upwards [hm, hη.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
    with j hj hs
  exact ⟨hj.1, hj.2.2.2.1, model_matching_deficit_bound (hM2 j) hj.1 hs.le (hz j) hj.2.2.2.1⟩

end
end Erdos1045.EventualExact.ExtremalScaleBound

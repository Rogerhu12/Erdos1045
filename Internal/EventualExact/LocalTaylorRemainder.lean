import EventualExact.ExtremalEdgeBudget

/-! Uniform two-sided Taylor control for the actual local discriminant objective. -/

namespace Erdos1045.EventualExact.LocalTaylorRemainder

open Complex LocalNonlinear LocalMaximum
open scoped BigOperators
noncomputable section

theorem pair_log_lower {η : ℝ} (hsmall : η ≤ 1 / 4) {z : ℂ} (hz : ‖z‖ ≤ 2 * η) :
    2 * z.re - (z ^ 2).re - 4 * η * ‖z‖ ^ 2 ≤ 2 * Real.log ‖1 + z‖ := by
  have ht := (abs_le.mp (scalarLogTaylor z (by linarith))).1
  have hm := mul_le_mul_of_nonneg_right hz (sq_nonneg ‖z‖)
  nlinarith

theorem norm_one_add_upper {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    {z : ℂ} (hz : ‖z‖ ≤ η) :
    ‖1 + z‖ ≤ 1 + z.re + (1 + 2 * η) * z.im ^ 2 / 2 := by
  have hre := (Complex.abs_re_le_norm z).trans hz
  have hnorm : 1 - η ≤ ‖1 + z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-z)
    simp only [norm_one, norm_neg, sub_neg_eq_add] at h
    linarith
  have hdiff : 0 ≤ ‖1 + z‖ - (1 + z.re) := by
    have h := Complex.re_le_norm (1 + z)
    simp only [Complex.add_re, Complex.one_re] at h
    linarith
  have hfactor : 2 * (1 - η) ≤ ‖1 + z‖ + 1 + z.re := by
    linarith [(abs_le.mp hre).1]
  have hprod := mul_le_mul_of_nonneg_left hfactor hdiff
  have hexact := norm_one_add_remainder z
  have hmul := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 1 + 2 * η by positivity)
  have hcoeff : 0 ≤ η - 2 * η ^ 2 := by nlinarith
  have hrem := mul_nonneg hcoeff hdiff
  nlinarith

theorem perimeter_sum_upper {ι : Type*} [Fintype ι] {η : ℝ}
    (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4) (ρ : ι → ℂ)
    (hρ : ∀ i, ‖ρ i‖ ≤ η) (hlinear : ∑ i, (ρ i).re = 0) :
    (∑ i, ‖1 + ρ i‖) ≤ (Fintype.card ι : ℝ) + (1 + 2 * η) * imaginaryEnergy ρ / 2 := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => norm_one_add_upper hη hsmall (hρ i))
  simpa only [imaginaryEnergy, Finset.sum_add_distrib, ← Finset.sum_div,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    hlinear, add_zero] using hsum

theorem perimeter_log_upper {ι : Type*} [Fintype ι] [Nonempty ι] {η : ℝ}
    (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4) (ρ : ι → ℂ)
    (hρ : ∀ i, ‖ρ i‖ ≤ η) (hlinear : ∑ i, (ρ i).re = 0) :
    Real.log ((∑ i, ‖1 + ρ i‖) / Fintype.card ι) ≤
      (1 + 2 * η) * imaginaryEnergy ρ / (2 * Fintype.card ι) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hlo := perimeter_average_lower hη hsmall ρ hρ hlinear
  have hB := imaginaryEnergy_nonneg ρ
  have hpos : 0 < (∑ i, ‖1 + ρ i‖) / Fintype.card ι := by
    have hh : 0 ≤ imaginaryEnergy ρ / (2 * Fintype.card ι * (1 + η)) := by positivity
    linarith
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hupp := perimeter_sum_upper hη hsmall ρ hρ hlinear
  refine hlog.trans ?_
  apply (le_div_iff₀ (show 0 < 2 * (Fintype.card ι : ℝ) by positivity)).2
  field_simp [hn.ne']
  linarith


theorem gain_lower (HI : LocalDFT.ClassicalDFTInversion)
    (HS : LocalPhase.ClassicalGeometricSine)
    {n : ℕ} (hn : 4 ≤ n)
    (HF : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (u : ℕ → ℂ) (hu : Function.Periodic u n)
    (hsim : (∑ j ∈ Finset.range n, u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖) :
    -LocalDFT.positiveQuadratic n u -
      4 * η * (LocalDFT.energyA n u + (n : ℝ) * LocalDFT.energyB n u) ≤ gain n u := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hpair (h : ℕ) (hh : h ∈ (Finset.range n).erase 0) :
      -(∑ j ∈ Finset.range n, (LocalDFT.pairRatio n u j h ^ 2).re) -
          4 * η * (∑ j ∈ Finset.range n, normSq (LocalDFT.pairRatio n u j h)) ≤
        (∑ j ∈ Finset.range n, 2 * Real.log ‖1 + LocalDFT.pairRatio n u j h‖) := by
    have hm := Finset.mem_erase.mp hh
    have hl := ratio_linear_sum_zero HI hn0 HF u hu hsim (by omega) (Finset.mem_range.mp hm.2)
    have hp := Finset.sum_le_sum (s := Finset.range n) (fun j _ =>
      pair_log_lower hsmall (pair_ratio_bound HS hn u hu hη hstep hh j))
    simpa [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hl, Complex.normSq_eq_norm_sq] using hp
  have hpairall := Finset.sum_le_sum (s := (Finset.range n).erase 0) hpair
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at hpairall
  let : NeZero n := ⟨by omega⟩
  have hedgeLinear : (∑ j : Fin n, (LocalDFT.pairRatio n u j.val 1).re) = 0 := by
    calc
      _ = ∑ j ∈ Finset.range n, (LocalDFT.pairRatio n u j 1).re :=
        (Finset.sum_range (fun j => (LocalDFT.pairRatio n u j 1).re)).symm
      _ = 0 := ratio_linear_sum_zero HI hn0 HF u hu hsim (by omega) (by omega)
  have hedge := perimeter_log_upper hη hsmall
    (fun j : Fin n => LocalDFT.pairRatio n u j.val 1)
    (fun j => edge_ratio_bound hn u hstep j.val) hedgeLinear
  simp only [LocalNonlinear.imaginaryEnergy, Fintype.card_fin] at hedge
  have hImagFin : (∑ j : Fin n, (LocalDFT.pairRatio n u j.val 1).im ^ 2) =
      ∑ j ∈ Finset.range n, (LocalDFT.pairRatio n u j 1).im ^ 2 :=
    (Finset.sum_range (fun j => (LocalDFT.pairRatio n u j 1).im ^ 2)).symm
  have hNormFin : (∑ j : Fin n, ‖1 + LocalDFT.pairRatio n u j.val 1‖) =
      ∑ j ∈ Finset.range n, ‖1 + LocalDFT.pairRatio n u j 1‖ :=
    (Finset.sum_range (fun j => ‖1 + LocalDFT.pairRatio n u j 1‖)).symm
  rw [hImagFin, hNormFin] at hedge
  have hmult := mul_le_mul_of_nonneg_left hedge
    (show 0 ≤ (n : ℝ) * ((n : ℝ) - 1) by positivity)
  have hcancel : (n : ℝ) * ((n : ℝ) - 1) *
      ((1 + 2 * η) * LocalDFT.energyB n u / (2 * (n : ℝ))) =
      ((n : ℝ) - 1) / 2 * (1 + 2 * η) * LocalDFT.energyB n u := by field_simp
  change _ ≤ (n : ℝ) * ((n : ℝ) - 1) *
      ((1 + 2 * η) * LocalDFT.energyB n u / (2 * (n : ℝ))) at hmult
  rw [hcancel] at hmult
  have hB : 0 ≤ LocalDFT.energyB n u := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hηB := mul_nonneg hη hB
  have hnηB := mul_nonneg hnR.le hηB
  have hQ : LocalDFT.positiveQuadratic n u =
      (∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n,
        (LocalDFT.pairRatio n u j h ^ 2).re) / 2 +
        ((n : ℝ) - 1) / 2 * LocalDFT.energyB n u := by
    simp [LocalDFT.positiveQuadratic, Complex.div_ofNat_re, Complex.re_sum, pow_two]
  rw [hQ]
  unfold gain LocalDFT.energyA
  simp only [← Finset.mul_sum]
  nlinarith

theorem gain_remainder_bound {n : ℕ} (hn : 4 ≤ n) (u : ℕ → ℂ)
    (hu : Function.Periodic u n)
    (hsim : (∑ j ∈ Finset.range n, u j * (starRingEnd ℂ) (LocalPhase.regularRoot n ^ j)) = 0)
    {η : ℝ} (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4)
    (hstep : ∀ j, ‖u (j + 1) - u j‖ ≤ η * ‖LocalPhase.regularRoot n - 1‖) :
    |gain n u + LocalDFT.positiveQuadratic n u| ≤ 4 * η * ExtremalEnergyBound.totalEnergy n u := by
  have HF := ClosedFourier.orthogonality n (show 0 < n by omega)
  have hl := gain_lower ClosedFourier.dftInversion ClosedFourier.geometricSine hn HF u hu hsim hη hsmall hstep
  have hr := gain_upper ClosedFourier.dftInversion ClosedFourier.geometricSine scalarLogTaylor
    hn HF u hu hsim hη hsmall hstep
  apply abs_le.mpr
  unfold ExtremalEnergyBound.totalEnergy
  constructor <;> linarith

open Filter Configuration HullGeometry CommonLocalization ExtremalEnergyBound
open scoped Topology

/-- The quadratic term from the pair logarithms, with the ordered-pair factor 1/2. -/
def pairTerm (n : ℕ) (u : ℕ → ℂ) : ℝ :=
  -((∑ h ∈ (Finset.range n).erase 0, ∑ j ∈ Finset.range n,
      LocalDFT.pairRatio n u j h * LocalDFT.pairRatio n u j h) / 2 : ℂ).re

theorem positiveQuadratic_eq (n : ℕ) (u : ℕ → ℂ) :
    LocalDFT.positiveQuadratic n u = ((n : ℝ) - 1) * LocalDFT.energyB n u / 2 - pairTerm n u := by
  unfold LocalDFT.positiveQuadratic pairTerm
  ring

theorem actual_remainder_tendsto {N : ℕ → ℕ} (hN4 : ∀ j, 4 ≤ N j)
    (z : ∀ j, Points (N j)) (σ : ∀ j, Equiv.Perm (Fin (N j)))
    {α β : ℕ → ℂ} {u : ℕ → ℕ → ℂ} {η : ℕ → ℝ}
    (hη : Tendsto η atTop (𝓝 0))
    (hm : ∀ᶠ j in atTop, NormalizedRelativeEdgeModel (z j) (σ j) (α j) (β j) (u j) (η j) ∧
      totalEnergy (N j) (u j) ≤ 32 * Real.pi ^ 2) :
    Tendsto (fun j => objective (regular (N j)) - objective (z j ∘ σ j) -
      LocalDFT.positiveQuadratic (N j) (u j)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hbound : ∀ᶠ j in atTop,
      |objective (regular (N j)) - objective (z j ∘ σ j) -
        LocalDFT.positiveQuadratic (N j) (u j)| ≤ 128 * Real.pi ^ 2 * η j := by
    filter_upwards [hm, hη.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
      with j hj hs
    rw [model_deficit_eq hj.1 (hN4 j) hs.le,
      show -gain (N j) (u j) - LocalDFT.positiveQuadratic (N j) (u j) =
        -(gain (N j) (u j) + LocalDFT.positiveQuadratic (N j) (u j)) by ring, abs_neg]
    have hb := gain_remainder_bound (hN4 j) (u j) hj.1.periodic hj.1.similarity_zero
      hj.1.error_nonneg hs.le hj.1.relative_edges
    have hmul := mul_le_mul_of_nonneg_left hj.2
      (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) hj.1.error_nonneg)
    nlinarith
  have hlim : Tendsto (fun j => 128 * Real.pi ^ 2 * η j) atTop (𝓝 0) := by
    simpa only [mul_zero] using hη.const_mul (128 * Real.pi ^ 2)
  exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hbound hlim

/-- Equations (3.9)--(3.10) for actual diameter maximizers: bounded local energy,
the asymptotically sharp B-budget, and a vanishing two-sided Taylor remainder. -/
theorem diameter_sequence_expansion {N : ℕ → ℕ} (hN4 : ∀ j, 4 ≤ N j)
    (hN : Tendsto N atTop atTop) (z : ∀ j, Points (N j))
    (hz : ∀ j, ExtremalNormalization.DiameterExtremal (z j)) :
    ∃ (σ : ∀ j, Equiv.Perm (Fin (N j))) (α β : ℕ → ℂ)
      (u : ℕ → ℕ → ℂ) (η : ℕ → ℝ),
      Tendsto η atTop (𝓝 0) ∧
      (∀ᶠ j in atTop,
        NormalizedRelativeEdgeModel (z j) (σ j) (α j) (β j) (u j) (η j) ∧
        boundaryLength (z j ∘ σ j) ≤ hullPerimeter (z j) ∧
        totalEnergy (N j) (u j) ≤ 32 * Real.pi ^ 2) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
        (N j : ℝ) * LocalDFT.energyB (N j) (u j) ≤ 3 * Real.pi ^ 2 / 2 + ε) ∧
      Tendsto (fun j => objective (regular (N j)) - objective (z j ∘ σ j) -
        (((N j : ℝ) - 1) * LocalDFT.energyB (N j) (u j) / 2 - pairTerm (N j) (u j)))
        atTop (𝓝 0) := by
  obtain ⟨σ, α, β, u, η, hη, hm, hB⟩ := diameter_sequence_edge_energy hN4 hN z hz
  refine ⟨σ, α, β, u, η, hη, ?_, hB, ?_⟩
  · exact hm.mono fun _ hj => ⟨hj.1, hj.2.1, hj.2.2.1⟩
  · simpa only [positiveQuadratic_eq] using actual_remainder_tendsto hN4 z σ hη
      (hm.mono fun _ hj => ⟨hj.1, hj.2.2.1⟩)

end
end Erdos1045.EventualExact.LocalTaylorRemainder

import StructuralNote.FixedSchurChosenSecondBounds
import StructuralNote.FixedSchurQuadraticExpansion
import StructuralNote.FixedSchurFirstSourceSup
import StructuralNote.FixedSchurNormalInnerEnergy

/-! Normalized mean-square source and inverse bounds for the true second
derivative of the chosen fixed-Schur chart. -/

namespace StructuralNote.FixedSchurChosenSecondBounds

open Filter Complex Erdos1045.EventualExact FiniteBox SchurSpectrum SchurLiftBounds
open CommonDomainClosure CommonDomainRadius CommonFiberBounds CommonClosureEnergy
open CommonFiberNormalAverage
open CommonFiberCanonicalDirections CommonTangentialParameters
open FixedSchurData FixedSchurChart FixedSchurDomainBounds
open FixedSchurNormalExpansion FixedSchurRotatedPath FixedSchurRotatedCoefficients
open FixedSchurRotatedInverse FixedSchurDirectionMoments
open FixedSchurChosenLinearization FixedSchurChosenSecondMoments
open FixedSchurSecondSourceTools FixedSchurNormalInnerEnergy
open FixedSchurQuadraticExpansion FixedSchurFirstSourceSup
open CommonFiberNormalProjectionScaled
open scoped BigOperators Topology

noncomputable section

private theorem meanSquare_five_add_le {n : ℕ}
    (f₁ f₂ f₃ f₄ f₅ : Fin n → ℝ) :
    meanSquare (fun j => (((f₁ j + f₂ j) + f₃ j) + f₄ j) + f₅ j) ≤
      16 * (meanSquare f₁ + meanSquare f₂ + meanSquare f₃ +
        meanSquare f₄ + meanSquare f₅) := by
  have h₁₂ := meanSquare_add_le f₁ f₂
  have h₁₂₃ := meanSquare_add_le (fun j => f₁ j + f₂ j) f₃
  have h₁₂₃₄ := meanSquare_add_le (fun j => (f₁ j + f₂ j) + f₃ j) f₄
  have h₁₂₃₄₅ := meanSquare_add_le
    (fun j => ((f₁ j + f₂ j) + f₃ j) + f₄ j) f₅
  change meanSquare (fun j => f₁ j + f₂ j) ≤
    2 * meanSquare f₁ + 2 * meanSquare f₂ at h₁₂
  change meanSquare (fun j => (f₁ j + f₂ j) + f₃ j) ≤
    2 * meanSquare (fun j => f₁ j + f₂ j) + 2 * meanSquare f₃ at h₁₂₃
  change meanSquare (fun j => ((f₁ j + f₂ j) + f₃ j) + f₄ j) ≤
    2 * meanSquare (fun j => (f₁ j + f₂ j) + f₃ j) +
      2 * meanSquare f₄ at h₁₂₃₄
  change meanSquare (fun j => (((f₁ j + f₂ j) + f₃ j) + f₄ j) + f₅ j) ≤
    2 * meanSquare (fun j => ((f₁ j + f₂ j) + f₃ j) + f₄ j) +
      2 * meanSquare f₅ at h₁₂₃₄₅
  have hnonneg (f : Fin n → ℝ) : 0 ≤ meanSquare f := by
    unfold meanSquare
    positivity
  linarith only [h₁₂, h₁₂₃, h₁₂₃₄, h₁₂₃₄₅,
    hnonneg f₁, hnonneg f₂, hnonneg f₃, hnonneg f₄, hnonneg f₅]


set_option maxHeartbeats 2000000 in
theorem eventual_second_source_meanSquare : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (w : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      let E := pairEnergy (by omega) (fun j => (η j : ℂ))
      let A := pairEnergy (by omega) h
      let K := E + A
      meanSquare (secondSource (by omega) w θ η v h) ≤
        1000000000000000000 * (1 + Real.log (2 * m : ℝ)) * K ^ 2 /
          (2 * m : ℝ) := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hord : ∀ᶠ m : ℕ in atTop,
      10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      hnat.eventually eventual_order_bound
  filter_upwards [eventual_second_coefficient_bounds,
    eventual_chosen_first_moments, hord] with m hcoef hmom horder
  intro hm w θ η v h hdom hd
  dsimp only
  let N : ℝ := 2 * m
  let E := pairEnergy (by omega) (fun j => (η j : ℂ))
  let A := pairEnergy (by omega) h
  let K := E + A
  let d := angleDifference (by omega) η
  let u := angleAverage (by omega) η
  let U := firstRadial (by omega) w θ η v h
  let T := firstTangential (by omega) w θ η v h
  let V := rotationVelocity (by omega) w θ η v h
  let ell := 1 + Real.log N
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hell : 1 ≤ ell := by dsimp [ell]; linarith
  have hE : 0 ≤ E := by dsimp [E]; exact pairEnergy_nonneg (by omega) _
  have hA : 0 ≤ A := by dsimp [A]; exact pairEnergy_nonneg (by omega) _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hEK : E ≤ K := by dsimp [K]; linarith
  have hAK : A ≤ K := by dsimp [K]; linarith
  rcases hmom hm w θ η v h hdom hd with
    ⟨_hqms, _hqnorm, _hpms, _hpnorm, hUms, _hUnorm,
      hTms, _hTnorm, hVms, hVnorm⟩
  change meanSquare U ≤ 1600000 * K / N + 32 * N * A at hUms
  change meanSquare T ≤ 1600000 * K / N + 32 * N * A at hTms
  change meanSquare V ≤ 3300000 * K / N + 64 * N * A at hVms
  change ‖V‖ ^ 2 ≤ 7200200 * K + 64 * N ^ 2 * A at hVnorm
  have hKN : K / N ≤ N * K := by
    apply (div_le_iff₀ hNpos).2
    have hN2 : 1 ≤ N ^ 2 := by nlinarith
    nlinarith only [hN2, hK]
  have hUms' : meanSquare U ≤ 1600032 * N * K := by
    have h1 := mul_le_mul_of_nonneg_left hKN (by norm_num : (0 : ℝ) ≤ 1600000)
    have h1' : 1600000 * K / N ≤ 1600000 * (N * K) := by
      simpa only [mul_div_assoc] using h1
    have h2 := mul_le_mul_of_nonneg_left hAK
      (show 0 ≤ 32 * N by positivity)
    calc
      _ ≤ 1600000 * (N * K) + 32 * N * K := by
        exact hUms.trans (add_le_add h1' h2)
      _ = 1600032 * N * K := by ring
  have hTms' : meanSquare T ≤ 1600032 * N * K := by
    have h1 := mul_le_mul_of_nonneg_left hKN (by norm_num : (0 : ℝ) ≤ 1600000)
    have h1' : 1600000 * K / N ≤ 1600000 * (N * K) := by
      simpa only [mul_div_assoc] using h1
    have h2 := mul_le_mul_of_nonneg_left hAK
      (show 0 ≤ 32 * N by positivity)
    calc
      _ ≤ 1600000 * (N * K) + 32 * N * K := by
        exact hTms.trans (add_le_add h1' h2)
      _ = 1600032 * N * K := by ring
  have hVms' : meanSquare V ≤ 3300064 * N * K := by
    have h1 := mul_le_mul_of_nonneg_left hKN (by norm_num : (0 : ℝ) ≤ 3300000)
    have h1' : 3300000 * K / N ≤ 3300000 * (N * K) := by
      simpa only [mul_div_assoc] using h1
    have h2 := mul_le_mul_of_nonneg_left hAK
      (show 0 ≤ 64 * N by positivity)
    calc
      _ ≤ 3300000 * (N * K) + 64 * N * K := by
        exact hVms.trans (add_le_add h1' h2)
      _ = 3300064 * N * K := by ring
  have hVnorm' : ‖V‖ ^ 2 ≤ 7200264 * N ^ 2 * K := by
    have hKscale : K ≤ N ^ 2 * K := by
      have hN2 : 1 ≤ N ^ 2 := by nlinarith
      nlinarith only [hN2, hK]
    have h1 := mul_le_mul_of_nonneg_left hKscale (by norm_num : (0 : ℝ) ≤ 7200200)
    have h2 := mul_le_mul_of_nonneg_left hAK
      (show 0 ≤ 64 * N ^ 2 by positivity)
    calc
      _ ≤ 7200200 * (N ^ 2 * K) + 64 * N ^ 2 * K := by
        exact hVnorm.trans (add_le_add h1 h2)
      _ = 7200264 * N ^ 2 * K := by ring
  have hdms := angleDifference_meanSquare_le (show 0 < 2 * m by omega) η
  have hdnorm0 := angleDifference_pointwise_sq_le (show 0 < 2 * m by omega) η
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hdms hdnorm0
  change meanSquare d ≤ 8 * Real.pi ^ 2 * E / N ^ 3 at hdms
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hdms' : meanSquare d ≤ 128 * K / N ^ 3 := by
    calc
      _ ≤ 8 * Real.pi ^ 2 * E / N ^ 3 := hdms
      _ ≤ 128 * K / N ^ 3 := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hNpos.le 3)
        have h1 := mul_le_mul_of_nonneg_right hpi hE
        have h2 := mul_le_mul_of_nonneg_left hEK (by norm_num : (0 : ℝ) ≤ 128)
        nlinarith only [h1, h2]
  have hdnorm : ‖d‖ ^ 2 ≤ 128 * K / N ^ 2 := by
    apply norm_sq_le_of_pointwise _ (by positivity)
    intro j
    have hj := hdnorm0 j
    change d j ^ 2 ≤ 8 * Real.pi ^ 2 * E / N ^ 2 at hj
    apply hj.trans
    apply div_le_div_of_nonneg_right _ (sq_nonneg N)
    have h1 := mul_le_mul_of_nonneg_right hpi hE
    have h2 := mul_le_mul_of_nonneg_left hEK (by norm_num : (0 : ℝ) ≤ 128)
    nlinarith only [h1, h2]
  have hums := angleAverage_meanSquare_le (show 2 ≤ 2 * m by omega) η hd.2.1
  have hunorm0 := angleAverage_pointwise_sq_le (show 2 ≤ 2 * m by omega) η hd.2.1
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hums hunorm0
  change meanSquare u ≤ 4 * E / N ^ 2 at hums
  have hums' : meanSquare u ≤ 4 * K / N ^ 2 :=
    hums.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hEK (by norm_num)) (sq_nonneg N))
  have hunorm : ‖u‖ ^ 2 ≤ 12 * ell * K / N ^ 2 := by
    apply norm_sq_le_of_pointwise _ (by positivity)
    intro j
    have hj := hunorm0 j
    change u j ^ 2 ≤ 12 * Real.log N / N ^ 2 * E at hj
    calc
      _ ≤ 12 * Real.log N / N ^ 2 * E := hj
      _ ≤ 12 * ell * K / N ^ 2 := by
        have hl : Real.log N ≤ ell := by dsimp [ell]; linarith
        have hh := mul_le_mul hl hEK hE (by linarith : 0 ≤ ell)
        have hnum : 12 * Real.log N * E ≤ 12 * ell * K :=
          by nlinarith only [hh]
        calc
          12 * Real.log N / N ^ 2 * E =
              (12 * Real.log N * E) / N ^ 2 := by ring
          _ ≤ (12 * ell * K) / N ^ 2 :=
            div_le_div_of_nonneg_right hnum (sq_nonneg N)
          _ = 12 * ell * K / N ^ 2 := by ring
  have hL : (logOrder (2 * m) : ℝ) ≤ N := by
    change 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ N at horder
    have hL0 : 0 ≤ (logOrder (2 * m) : ℝ) := by positivity
    linarith
  let f₁ : Fin (2 * m) → ℝ := fun j =>
    patternSign w j / (2 * epsilon (2 * m)) *
      Real.cos (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2) * d j ^ 2
  let f₂ : Fin (2 * m) → ℝ := fun j => -2 * T j * u j
  let f₃ : Fin (2 * m) → ℝ := fun j => baseRadial (by omega) w θ v j * u j ^ 2
  let f₄ : Fin (2 * m) → ℝ := fun j =>
    let S := rotatedS (by omega) θ v (coordinate (by omega) w θ v) j
    patternSign w j * epsilon (2 * m) * S / H (epsilon (2 * m)) S *
      (2 * U j * u j + S * u j ^ 2)
  let f₅ : Fin (2 * m) → ℝ := fun j =>
    let S := rotatedS (by omega) θ v (coordinate (by omega) w θ v) j;
    -(4 * patternSign w j * epsilon (2 * m) / H (epsilon (2 * m)) S ^ 3 * V j ^ 2)
  have hsourceEq : secondSource (by omega) w θ η v h =
      fun j => (((f₁ j + f₂ j) + f₃ j) + f₄ j) + f₅ j := by
    funext j
    have hVj : V j = T j -
        baseRadial (by omega) w θ v j * u j := by rfl
    dsimp only [f₁, f₂, f₃, f₄, f₅]
    rw [hVj]
    dsimp only [secondSource, d, u, U, T]
    ring
  have hf₁dom : meanSquare f₁ ≤ (N ^ 2 / 8) ^ 2 *
      meanSquare (fun j => d j ^ 2) := by
    apply meanSquare_domination f₁ (fun j => d j ^ 2) (by positivity)
    intro j
    rcases hcoef hm w θ v hdom j with ⟨hc, _hr, _hS, _hH, _hmid, _hlast⟩
    have hc' : |patternSign w j / (2 * epsilon (2 * m)) *
          Real.cos (Real.pi / (2 * m : ℝ) +
            angleDifference (by omega) θ j / 2)| ≤ N ^ 2 / 8 := by
      simpa only [N, Nat.cast_mul, Nat.cast_ofNat] using hc
    dsimp [f₁]
    calc
      |_ * d j ^ 2| =
          |patternSign w j / (2 * epsilon (2 * m)) *
            Real.cos (Real.pi / (2 * m : ℝ) +
              angleDifference (by omega) θ j / 2)| * |d j ^ 2| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hc' (abs_nonneg _)
  have hf₁ : meanSquare f₁ ≤ 256 * ell * K ^ 2 / N := by
    have hsquare := square_meanSquare_le d
    calc
      _ ≤ (N ^ 2 / 8) ^ 2 * meanSquare (fun j => d j ^ 2) := hf₁dom
      _ ≤ (N ^ 2 / 8) ^ 2 * (‖d‖ ^ 2 * meanSquare d) :=
        mul_le_mul_of_nonneg_left hsquare (sq_nonneg _)
      _ ≤ (N ^ 2 / 8) ^ 2 *
          ((128 * K / N ^ 2) * (128 * K / N ^ 3)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul hdnorm hdms'
          (by unfold meanSquare; positivity) (by positivity)
      _ ≤ 256 * ell * K ^ 2 / N := by
        field_simp [ne_of_gt hNpos]
        have hEllK : K ^ 2 ≤ ell * K ^ 2 := by
          nlinarith only [hell, sq_nonneg K]
        nlinarith only [hEllK]
  have hTu := product_meanSquare_le u T
  have hUu := product_meanSquare_le u U
  have hf₂dom : meanSquare f₂ ≤ 4 * meanSquare (fun j => T j * u j) := by
    have hh := meanSquare_domination f₂ (fun j => T j * u j)
      (K := 2) (by norm_num) (fun j => by
        dsimp [f₂]
        have heq : |-2 * T j * u j| = 2 * |T j * u j| := by
          rw [show -2 * T j * u j = (-2) * (T j * u j) by ring, abs_mul]
          norm_num
        exact heq.le)
    norm_num at hh ⊢
    exact hh
  have hf₂ : meanSquare f₂ ≤ 100000000 * ell * K ^ 2 / N := by
    have hprod : meanSquare (fun j => T j * u j) ≤
        (12 * ell * K / N ^ 2) * (1600032 * N * K) := by
      calc
        _ = meanSquare (fun j => u j * T j) := by congr 2; funext j; ring
        _ ≤ ‖u‖ ^ 2 * meanSquare T := hTu
        _ ≤ _ := mul_le_mul hunorm hTms' (by unfold meanSquare; positivity) (by positivity)
    calc
      _ ≤ 4 * meanSquare (fun j => T j * u j) := hf₂dom
      _ ≤ 4 * ((12 * ell * K / N ^ 2) * (1600032 * N * K)) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ ≤ 100000000 * ell * K ^ 2 / N := by
        have hh : (76801536 : ℝ) ≤ 100000000 := by norm_num
        have hX : 0 ≤ ell * K ^ 2 / N := by positivity
        calc
          _ = 76801536 * (ell * K ^ 2 / N) := by
            field_simp [ne_of_gt hNpos]
            ring
          _ ≤ 100000000 * (ell * K ^ 2 / N) :=
            mul_le_mul_of_nonneg_right hh hX
          _ = _ := by ring
  have hf₃dom : meanSquare f₃ ≤ (5 / 2 : ℝ) ^ 2 *
      meanSquare (fun j => u j ^ 2) := by
    apply meanSquare_domination f₃ (fun j => u j ^ 2)
      (K := (5 / 2 : ℝ)) (by norm_num)
    intro j
    rcases hcoef hm w θ v hdom j with ⟨_hc, hr, _hS, _hH, _hmid, _hlast⟩
    dsimp [f₃]
    calc
      |_ * u j ^ 2| = |baseRadial (by omega) w θ v j| * |u j ^ 2| :=
        abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hr (abs_nonneg _)
  have huSquare := square_meanSquare_le u
  have hf₃ : meanSquare f₃ ≤ 1000 * ell * K ^ 2 / N := by
    calc
      _ ≤ (5 / 2 : ℝ) ^ 2 * meanSquare (fun j => u j ^ 2) := hf₃dom
      _ ≤ (5 / 2 : ℝ) ^ 2 * (‖u‖ ^ 2 * meanSquare u) :=
        mul_le_mul_of_nonneg_left huSquare (sq_nonneg _)
      _ ≤ (5 / 2 : ℝ) ^ 2 *
          ((12 * ell * K / N ^ 2) * (4 * K / N ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul hunorm hums'
          (by unfold meanSquare; positivity) (by positivity)
      _ ≤ 1000 * ell * K ^ 2 / N := by
        have hfrac : (300 : ℝ) / N ^ 4 ≤ 1000 / N := by
          field_simp [ne_of_gt hNpos]
          have hN3 : 1 ≤ N ^ 3 := by
            nlinarith [show 0 ≤ N ^ 2 by positivity]
          nlinarith
        calc
          _ = (300 / N ^ 4) * (ell * K ^ 2) := by ring
          _ ≤ (1000 / N) * (ell * K ^ 2) :=
            mul_le_mul_of_nonneg_right hfrac (by positivity)
          _ = _ := by ring
  have hf₄ : meanSquare f₄ ≤ 300000000 * ell * K ^ 2 / N := by
    let g₁ : Fin (2 * m) → ℝ := fun j => 2 * U j * u j
    let g₂ : Fin (2 * m) → ℝ := fun j =>
      rotatedS (by omega) θ v (coordinate (by omega) w θ v) j * u j ^ 2
    have hfdom : meanSquare f₄ ≤ meanSquare (fun j => g₁ j + g₂ j) := by
      have hh := meanSquare_domination f₄ (fun j => g₁ j + g₂ j)
        (K := 1) (by norm_num) (fun j => by
          rcases hcoef hm w θ v hdom j with
            ⟨_hc, _hr, _hS, _hH, hmid, _hlast⟩
          dsimp [f₄, g₁, g₂]
          rw [abs_mul]
          simpa only [one_mul] using
            mul_le_mul hmid le_rfl (abs_nonneg _) (by norm_num))
      norm_num at hh ⊢
      exact hh
    have hgadd := meanSquare_add_le g₁ g₂
    change meanSquare (fun j => g₁ j + g₂ j) ≤
      2 * meanSquare g₁ + 2 * meanSquare g₂ at hgadd
    have hg₁dom : meanSquare g₁ ≤ 4 * meanSquare (fun j => U j * u j) := by
      have hh := meanSquare_domination g₁ (fun j => U j * u j)
        (K := 2) (by norm_num) (fun j => by
          dsimp [g₁]
          have heq : |2 * U j * u j| = 2 * |U j * u j| := by
            rw [show 2 * U j * u j = 2 * (U j * u j) by ring, abs_mul]
            norm_num
          exact heq.le)
      norm_num at hh ⊢
      exact hh
    have hg₁ : meanSquare g₁ ≤ 100000000 * ell * K ^ 2 / N := by
      have hprod : meanSquare (fun j => U j * u j) ≤
          (12 * ell * K / N ^ 2) * (1600032 * N * K) := by
        calc
          _ = meanSquare (fun j => u j * U j) := by congr 2; funext j; ring
          _ ≤ ‖u‖ ^ 2 * meanSquare U := hUu
          _ ≤ _ := mul_le_mul hunorm hUms' (by unfold meanSquare; positivity) (by positivity)
      calc
        _ ≤ 4 * meanSquare (fun j => U j * u j) := hg₁dom
        _ ≤ 4 * ((12 * ell * K / N ^ 2) * (1600032 * N * K)) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
        _ ≤ 100000000 * ell * K ^ 2 / N := by
          have hh : (76801536 : ℝ) ≤ 100000000 := by norm_num
          have hX : 0 ≤ ell * K ^ 2 / N := by positivity
          calc
            _ = 76801536 * (ell * K ^ 2 / N) := by
              field_simp [ne_of_gt hNpos]
              ring
            _ ≤ 100000000 * (ell * K ^ 2 / N) :=
              mul_le_mul_of_nonneg_right hh hX
            _ = _ := by ring
    have hg₂dom : meanSquare g₂ ≤ (18 * N) ^ 2 *
        meanSquare (fun j => u j ^ 2) := by
      apply meanSquare_domination g₂ (fun j => u j ^ 2)
        (K := 18 * N) (by positivity)
      intro j
      rcases hcoef hm w θ v hdom j with ⟨_hc, _hr, hS, _hH, _hmid, _hlast⟩
      dsimp [g₂]
      calc
        |_ * u j ^ 2| =
            |rotatedS (by omega) θ v (coordinate (by omega) w θ v) j| *
              |u j ^ 2| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (hS.trans (mul_le_mul_of_nonneg_left hL (by norm_num))) (abs_nonneg _)
    have hg₂ : meanSquare g₂ ≤ 20000 * ell * K ^ 2 / N := by
      calc
        _ ≤ (18 * N) ^ 2 * meanSquare (fun j => u j ^ 2) := hg₂dom
        _ ≤ (18 * N) ^ 2 * (‖u‖ ^ 2 * meanSquare u) :=
          mul_le_mul_of_nonneg_left huSquare (sq_nonneg _)
        _ ≤ (18 * N) ^ 2 *
            ((12 * ell * K / N ^ 2) * (4 * K / N ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact mul_le_mul hunorm hums'
            (by unfold meanSquare; positivity) (by positivity)
        _ ≤ 20000 * ell * K ^ 2 / N := by
          have hfrac : (15552 : ℝ) / N ^ 2 ≤ 20000 / N := by
            field_simp [ne_of_gt hNpos]
            nlinarith
          calc
            _ = (15552 / N ^ 2) * (ell * K ^ 2) := by
              field_simp [ne_of_gt hNpos]
              ring
            _ ≤ (20000 / N) * (ell * K ^ 2) :=
              mul_le_mul_of_nonneg_right hfrac (by positivity)
            _ = _ := by ring
    calc
      _ ≤ meanSquare (fun j => g₁ j + g₂ j) := hfdom
      _ ≤ 2 * meanSquare g₁ + 2 * meanSquare g₂ := hgadd
      _ ≤ 2 * (100000000 * ell * K ^ 2 / N) +
          2 * (20000 * ell * K ^ 2 / N) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hg₁ (by norm_num))
          (mul_le_mul_of_nonneg_left hg₂ (by norm_num))
      _ ≤ 300000000 * ell * K ^ 2 / N := by
        have hh : (200040000 : ℝ) ≤ 300000000 := by norm_num
        have hX : 0 ≤ ell * K ^ 2 / N := by positivity
        calc
          _ = 200040000 * (ell * K ^ 2 / N) := by ring
          _ ≤ 300000000 * (ell * K ^ 2 / N) :=
            mul_le_mul_of_nonneg_right hh hX
          _ = _ := by ring
  have hf₅dom : meanSquare f₅ ≤ (32 / N ^ 2) ^ 2 *
      meanSquare (fun j => V j ^ 2) := by
    apply meanSquare_domination f₅ (fun j => V j ^ 2)
      (K := 32 / N ^ 2) (by positivity)
    intro j
    rcases hcoef hm w θ v hdom j with ⟨_hc, _hr, _hS, _hH, _hmid, hlast⟩
    dsimp [f₅]
    rw [abs_neg]
    calc
      |_ * V j ^ 2| =
          |4 * patternSign w j * epsilon (2 * m) /
            H (epsilon (2 * m))
              (rotatedS (by omega) θ v (coordinate (by omega) w θ v) j) ^ 3| *
            |V j ^ 2| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hlast (abs_nonneg _)
  have hVSquare := square_meanSquare_le V
  have hf₅ : meanSquare f₅ ≤ 30000000000000000 * ell * K ^ 2 / N := by
    calc
      _ ≤ (32 / N ^ 2) ^ 2 * meanSquare (fun j => V j ^ 2) := hf₅dom
      _ ≤ (32 / N ^ 2) ^ 2 * (‖V‖ ^ 2 * meanSquare V) :=
        mul_le_mul_of_nonneg_left hVSquare (sq_nonneg _)
      _ ≤ (32 / N ^ 2) ^ 2 *
          ((7200264 * N ^ 2 * K) * (3300064 * N * K)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact mul_le_mul hVnorm' hVms'
          (by unfold meanSquare; positivity) (by positivity)
      _ ≤ 30000000000000000 * ell * K ^ 2 / N := by
        have hc : (24331603985301504 : ℝ) ≤
            30000000000000000 * ell := by nlinarith
        have hX : 0 ≤ K ^ 2 / N := by positivity
        calc
          _ = 24331603985301504 * (K ^ 2 / N) := by
            field_simp [ne_of_gt hNpos]
            ring
          _ ≤ (30000000000000000 * ell) * (K ^ 2 / N) :=
            mul_le_mul_of_nonneg_right hc hX
          _ = _ := by ring
  rw [hsourceEq]
  calc
    _ ≤ 16 * (meanSquare f₁ + meanSquare f₂ + meanSquare f₃ +
        meanSquare f₄ + meanSquare f₅) := meanSquare_five_add_le _ _ _ _ _
    _ ≤ 16 * ((256 + 100000000 + 1000 + 300000000 +
        30000000000000000) * ell * K ^ 2 / N) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      calc
        _ ≤ 256 * ell * K ^ 2 / N +
            100000000 * ell * K ^ 2 / N +
            1000 * ell * K ^ 2 / N +
            300000000 * ell * K ^ 2 / N +
            30000000000000000 * ell * K ^ 2 / N := by
          exact add_le_add (add_le_add (add_le_add (add_le_add hf₁ hf₂) hf₃) hf₄) hf₅
        _ = _ := by ring
    _ ≤ 1000000000000000000 * ell * K ^ 2 / N := by
      have hh : 0 ≤ ell * K ^ 2 / N := by positivity
      ring_nf at hh ⊢
      nlinarith only [hh]

theorem eventual_chosen_second_meanSquare : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (w : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      let K := pairEnergy (by omega) (fun j => (η j : ℂ)) +
        pairEnergy (by omega) h
      meanSquare (chosenSecondDerivative (by omega) w θ η v h) ≤
        4000000000000000000 * (1 + Real.log (2 * m : ℝ)) * K ^ 2 /
          (2 * m : ℝ) := by
  filter_upwards [eventual_second_source_meanSquare,
    eventual_actual_solution_bounds, eventual_chosen_normalLinearizations] with
      m hsource hinv hlin
  intro hm w θ η v h hdom hd
  dsimp only
  let q := chosenSecondDerivative (by omega) w θ η v h
  let src := secondSource (by omega) w θ η v h
  have hqroot := (hinv hm w θ v hdom q).2.1
  rw [(hlin hm w θ η v h hdom hd).2] at hqroot
  change Real.sqrt (meanSquare q) ≤ 2 * Real.sqrt (meanSquare src) at hqroot
  have hq0 : 0 ≤ meanSquare q := by unfold meanSquare; positivity
  have hs0 : 0 ≤ meanSquare src := by unfold meanSquare; positivity
  have hqms := pow_le_pow_left₀ (Real.sqrt_nonneg _) hqroot 2
  rw [Real.sq_sqrt hq0, mul_pow, Real.sq_sqrt hs0] at hqms
  norm_num at hqms
  have hs := hsource hm w θ η v h hdom hd
  dsimp only at hs
  change meanSquare src ≤
    1000000000000000000 * (1 + Real.log (2 * m : ℝ)) *
      (pairEnergy (by omega) (fun j => (η j : ℂ)) +
        pairEnergy (by omega) h) ^ 2 / (2 * m : ℝ) at hs
  calc
    meanSquare q ≤ 4 * meanSquare src := hqms
    _ ≤ 4 * (1000000000000000000 * (1 + Real.log (2 * m : ℝ)) *
        (pairEnergy (by omega) (fun j => (η j : ℂ)) +
          pairEnergy (by omega) h) ^ 2 / (2 * m : ℝ)) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

theorem eventual_chosen_second_coarse : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (w : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      meanSquare (chosenSecondDerivative (by omega) w θ η v h) ≤
        (pairEnergy (by omega) (fun j => (η j : ℂ)) +
          pairEnergy (by omega) h) ^ 2 := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hreal : Tendsto (fun m : ℕ => (2 * m : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using
      tendsto_natCast_atTop_atTop.comp hnat
  have hinv : Tendsto (fun m : ℕ => 1 / (2 * m : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hreal
  have hlog : Tendsto
      (fun m : ℕ => Real.log (2 * m : ℝ) / (2 * m : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hreal
  have hbase : Tendsto
      (fun m : ℕ => (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ))
        atTop (𝓝 0) := by
    convert hinv.add hlog using 1
    · funext m
      ring
    · norm_num
  have hscale : Tendsto
      (fun m : ℕ => 4000000000000000000 *
        ((1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ))) atTop (𝓝 0) :=
    by simpa only [mul_zero] using hbase.const_mul 4000000000000000000
  filter_upwards [eventual_chosen_second_meanSquare,
    hscale.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with
      m hsecond hsmall
  intro hm w θ η v h hdom hd
  let K := pairEnergy (by omega) (fun j => (η j : ℂ)) +
    pairEnergy (by omega) h
  have hK : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg (pairEnergy_nonneg (by omega) _)
      (pairEnergy_nonneg (by omega) _)
  have hs := hsecond hm w θ η v h hdom hd
  dsimp only at hs
  change meanSquare (chosenSecondDerivative (by omega) w θ η v h) ≤
    4000000000000000000 * (1 + Real.log (2 * m : ℝ)) * K ^ 2 /
      (2 * m : ℝ) at hs
  have hfactor : 4000000000000000000 *
      (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) ≤ 1 := by
    calc
      _ = 4000000000000000000 *
          ((1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ)) := by ring
      _ ≤ 1 := hsmall.le
  calc
    _ ≤ 4000000000000000000 *
        (1 + Real.log (2 * m : ℝ)) / (2 * m : ℝ) * K ^ 2 := by
      convert hs using 1
      all_goals ring
    _ ≤ 1 * K ^ 2 := mul_le_mul_of_nonneg_right hfactor (sq_nonneg K)
    _ = _ := by dsimp [K]; ring


end
end StructuralNote.FixedSchurChosenSecondBounds

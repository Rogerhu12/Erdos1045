import StructuralNote.FixedSchurChosenSecondMoments

/-! Normalized source estimates and inverse bounds for the true second
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
open CommonFiberNormalProjectionScaled
open scoped BigOperators Topology

noncomputable section

private theorem sign_abs {m : ℕ} (hm : 0 < m) (w : SignPattern hm)
    (j : Fin (2 * m)) :
    |patternSign w j| = 1 := by
  rcases patternSign_is_sign w j with h | h <;> rw [h] <;> norm_num

theorem eventual_second_coefficient_bounds : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (w : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → ∀ j,
      let S := rotatedS (by omega) θ v (coordinate (by omega) w θ v) j
      let HH := H (epsilon (2 * m)) S
      |patternSign w j / (2 * epsilon (2 * m)) *
          Real.cos (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2)| ≤
          (2 * m : ℝ) ^ 2 / 8 ∧
      |baseRadial (by omega) w θ v j| ≤ (5 / 2 : ℝ) ∧
      |S| ≤ 18 * (logOrder (2 * m) : ℝ) ∧
      1 ≤ HH ∧
      |patternSign w j * epsilon (2 * m) * S / HH| ≤ 1 ∧
      |4 * patternSign w j * epsilon (2 * m) / HH ^ 3| ≤
        32 / (2 * m : ℝ) ^ 2 := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hord : ∀ᶠ m : ℕ in atTop,
      10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m :=
    by simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      hnat.eventually eventual_order_bound
  filter_upwards [eventual_actual_coefficients_small,
    eventual_coordinate_properties, eventual_radialCoefficient_bound,
    hord] with
      m hcoeff hcoord hrad horder
  intro hm w θ v hdom j
  dsimp only
  let S := rotatedS (by omega) θ v (coordinate (by omega) w θ v) j
  let HH := H (epsilon (2 * m)) S
  have hn : (0 : ℝ) < 2 * m := by positivity
  have hε : 0 < epsilon (2 * m) := epsilon_pos (show 2 ≤ 2 * m by omega)
  have hεle := epsilon_le (show 2 ≤ 2 * m by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hεle
  have hscale := (scale_bounds (show 2 ≤ 2 * m by omega)).2
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hscale
  have hq := (hcoord hm w θ v hdom).norm_le
  have hS : |S| ≤ 18 * (logOrder (2 * m) : ℝ) :=
    rotatedS_abs_le_log (by omega) θ v hdom _ hq j
  have hH : 1 ≤ HH := (hcoeff hm w θ v hdom j).2.2
  have hHpos : 0 < HH := lt_of_lt_of_le (by norm_num) hH
  have hsign := sign_abs (by omega) w j
  have hL : 144 * (logOrder (2 * m) : ℝ) ≤ (2 * m : ℝ) ^ 2 := by
    have ho : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m := by
      exact_mod_cast horder
    have hL0 : 0 ≤ (logOrder (2 * m) : ℝ) := by positivity
    have hLm : 144 * (logOrder (2 * m) : ℝ) ≤ 15 * (2 * m : ℝ) := by
      nlinarith only [ho, hL0]
    have hmlarge : (15 : ℝ) ≤ 2 * m := by linarith
    nlinarith
  have hεS : |epsilon (2 * m) * S| ≤ 1 := by
    rw [abs_mul, abs_of_pos hε]
    calc
      epsilon (2 * m) * |S| ≤
          (8 / (2 * m : ℝ) ^ 2) *
            (18 * (logOrder (2 * m) : ℝ)) :=
        mul_le_mul hεle hS (abs_nonneg _) (by positivity)
      _ = 144 * (logOrder (2 * m) : ℝ) / (2 * m : ℝ) ^ 2 := by ring
      _ ≤ 1 := (div_le_one (sq_pos_of_pos hn)).2 hL
  have hfirst : |patternSign w j / (2 * epsilon (2 * m)) *
        Real.cos (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2)| ≤
      (2 * m : ℝ) ^ 2 / 8 := by
    have hden : |patternSign w j / (2 * epsilon (2 * m))| =
        scale (2 * m) / 2 := by
      rw [abs_div, hsign, abs_mul, abs_of_pos hε]
      norm_num
      rw [epsilon_inv (show 2 ≤ 2 * m by omega)]
      ring
    rw [abs_mul, hden]
    calc
      (scale (2 * m) / 2) *
          |Real.cos (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2)| ≤
          (((2 * m : ℝ) ^ 2 / 4) / 2) * 1 :=
        mul_le_mul (div_le_div_of_nonneg_right hscale (by norm_num))
          (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
      _ = (2 * m : ℝ) ^ 2 / 8 := by ring
  have hmiddle : |patternSign w j * epsilon (2 * m) * S / HH| ≤ 1 := by
    rw [abs_div, abs_mul, abs_mul, hsign, one_mul, abs_of_pos hε,
      abs_of_pos hHpos]
    have hnum : epsilon (2 * m) * |S| ≤ 1 := by
      simpa only [abs_mul, abs_of_pos hε] using hεS
    calc
      epsilon (2 * m) * |S| / HH ≤ epsilon (2 * m) * |S| :=
        div_le_self (mul_nonneg hε.le (abs_nonneg _)) hH
      _ ≤ 1 := hnum
  have hlast : |4 * patternSign w j * epsilon (2 * m) / HH ^ 3| ≤
      32 / (2 * m : ℝ) ^ 2 := by
    rw [abs_div, abs_mul, abs_mul, hsign, abs_of_pos hε,
      abs_of_pos (pow_pos hHpos 3)]
    norm_num
    calc
      4 * epsilon (2 * m) / HH ^ 3 ≤ 4 * epsilon (2 * m) :=
        div_le_self (by positivity) (by exact one_le_pow₀ hH)
      _ ≤ 4 * (8 / (2 * m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hεle (by norm_num)
      _ = 32 / (2 * m : ℝ) ^ 2 := by ring
  exact ⟨hfirst, hrad hm w θ v hdom j, hS, hH, hmiddle, hlast⟩

private theorem mixed_sqrt_bound (N E A K x y : ℝ)
    (hN : 1 ≤ N) (hE : 0 ≤ E) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hEK : E ≤ K) (_hAK : A ≤ K) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxb : x ≤ 1600000 * K / N + 32 * N * A)
    (hyb : y ≤ 4 * E / N ^ 2) :
    Real.sqrt x * Real.sqrt y ≤
      3000 * K / N + 12 * Real.sqrt (A * E) / Real.sqrt N := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hrootN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hsN : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNpos.le
  have hAE : 0 ≤ A * E := mul_nonneg hA hE
  have hsAE : Real.sqrt (A * E) ^ 2 = A * E := Real.sq_sqrt hAE
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hsy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hxb0 : 0 ≤ 1600000 * K / N + 32 * N * A := by positivity
  have hxy := mul_le_mul hxb hyb hy hxb0
  have hxy' : x * y ≤
      6400000 * K ^ 2 / N ^ 3 + 128 * A * E / N := by
    calc
      x * y ≤ (1600000 * K / N + 32 * N * A) * (4 * E / N ^ 2) := hxy
      _ ≤ 6400000 * K ^ 2 / N ^ 3 + 128 * A * E / N := by
        have hKE : K * E ≤ K ^ 2 :=
          by simpa only [pow_two] using mul_le_mul_of_nonneg_left hEK hK
        have hN2 : 1 ≤ N ^ 2 := by nlinarith
        field_simp [ne_of_gt hNpos]
        nlinarith only [hKE, hN2, hA, hE]
  have htarget :
      6400000 * K ^ 2 / N ^ 3 + 128 * A * E / N ≤
        (3000 * K / N + 12 * Real.sqrt (A * E) / Real.sqrt N) ^ 2 := by
    field_simp [ne_of_gt hNpos, ne_of_gt hrootN]
    ring_nf
    rw [hsN, hsAE]
    have hN2 : N ≤ N ^ 2 := by nlinarith
    have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
    have hKN : K ^ 2 * N ≤ K ^ 2 * N ^ 2 :=
      mul_le_mul_of_nonneg_left hN2 hK2
    have hAEN : 0 ≤ A * E * N ^ 3 := by positivity
    have hcross : 0 ≤ K * N ^ 2 * Real.sqrt N * Real.sqrt (A * E) := by positivity
    nlinarith only [hKN, hAEN, hcross]
  have hsquare :
      (Real.sqrt x * Real.sqrt y) ^ 2 ≤
        (3000 * K / N + 12 * Real.sqrt (A * E) / Real.sqrt N) ^ 2 := by
    rw [mul_pow, hsx, hsy]
    exact hxy'.trans htarget
  have hleft : 0 ≤ Real.sqrt x * Real.sqrt y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hright : 0 ≤ 3000 * K / N +
      12 * Real.sqrt (A * E) / Real.sqrt N := by positivity
  exact (sq_le_sq₀ hleft hright).mp hsquare

set_option maxHeartbeats 800000 in
theorem eventual_second_source_l1 : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (w : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      let E := pairEnergy (by omega) (fun j => (η j : ℂ))
      let A := pairEnergy (by omega) h
      let K := E + A
      (∑ j, |secondSource (by omega) w θ η v h j|) / (2 * m : ℝ) ≤
        120000000 *
          (K / (2 * m : ℝ) + Real.sqrt (A * E) / Real.sqrt (2 * m : ℝ)) := by
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
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hE : 0 ≤ E := by dsimp [E]; exact pairEnergy_nonneg (by omega) _
  have hA : 0 ≤ A := by dsimp [A]; exact pairEnergy_nonneg (by omega) _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hEK : E ≤ K := by dsimp [K]; linarith
  have hAK : A ≤ K := by dsimp [K]; linarith
  rcases hmom hm w θ η v h hdom hd with
    ⟨_hqms, _hqnorm, _hpms, _hpnorm, hUms, _hUnorm,
      hTms, _hTnorm, hVms, _hVnorm⟩
  change meanSquare U ≤ 1600000 * K / N + 32 * N * A at hUms
  change meanSquare T ≤ 1600000 * K / N + 32 * N * A at hTms
  change meanSquare V ≤ 3300000 * K / N + 64 * N * A at hVms
  have hdms := angleDifference_meanSquare_le (show 0 < 2 * m by omega) η
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hdms
  change meanSquare d ≤ 8 * Real.pi ^ 2 * E / N ^ 3 at hdms
  have hums := angleAverage_meanSquare_le (show 2 ≤ 2 * m by omega) η hd.2.1
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hums
  change meanSquare u ≤ 4 * E / N ^ 2 at hums
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hdms' : meanSquare d ≤ 128 * E / N ^ 3 := by
    calc
      _ ≤ 8 * Real.pi ^ 2 * E / N ^ 3 := hdms
      _ ≤ 128 * E / N ^ 3 := by
        apply div_le_div_of_nonneg_right _ (pow_nonneg hNpos.le 3)
        have hh := mul_le_mul_of_nonneg_right hpi hE
        nlinarith only [hh]
  have hTmix : Real.sqrt (meanSquare T) * Real.sqrt (meanSquare u) ≤
      3000 * K / N + 12 * Real.sqrt (A * E) / Real.sqrt N :=
    mixed_sqrt_bound N E A K _ _ hN hE hA hK hEK hAK
      (by unfold meanSquare; positivity)
      (by unfold meanSquare; positivity) hTms hums
  have hUmix : Real.sqrt (meanSquare U) * Real.sqrt (meanSquare u) ≤
      3000 * K / N + 12 * Real.sqrt (A * E) / Real.sqrt N :=
    mixed_sqrt_bound N E A K _ _ hN hE hA hK hEK hAK
      (by unfold meanSquare; positivity)
      (by unfold meanSquare; positivity) hUms hums
  have hL : (logOrder (2 * m) : ℝ) ≤ N := by
    have hL0 : 0 ≤ (logOrder (2 * m) : ℝ) := by positivity
    change 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ N at horder
    linarith
  have hpoint (j : Fin (2 * m)) :
      |secondSource (by omega) w θ η v h j| ≤
        N ^ 2 / 8 * d j ^ 2 + 2 * |T j * u j| +
        (5 / 2 : ℝ) * u j ^ 2 +
        (2 * |U j * u j| + 18 * (logOrder (2 * m) : ℝ) * u j ^ 2) +
        32 / N ^ 2 * V j ^ 2 := by
    rcases hcoef hm w θ v hdom j with ⟨hc, hr, hS, _hH, hmid, hlast⟩
    let S := rotatedS (by omega) θ v (coordinate (by omega) w θ v) j
    let c := patternSign w j / (2 * epsilon (2 * m)) *
      Real.cos (Real.pi / (2 * m : ℝ) + angleDifference (by omega) θ j / 2)
    have h1 : |c * d j ^ 2| ≤ N ^ 2 / 8 * d j ^ 2 := by
      simp only [abs_mul, abs_pow, sq_abs]
      exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    have h2 : |2 * T j * u j| ≤ 2 * |T j * u j| := by
      rw [show 2 * T j * u j = 2 * (T j * u j) by ring, abs_mul]
      norm_num
    have h3 : |baseRadial (by omega) w θ v j * u j ^ 2| ≤
        (5 / 2 : ℝ) * u j ^ 2 := by
      simp only [abs_mul, abs_pow, sq_abs]
      exact mul_le_mul_of_nonneg_right hr (sq_nonneg _)
    have h4 : |patternSign w j * epsilon (2 * m) * S /
          H (epsilon (2 * m)) S * (2 * U j * u j + S * u j ^ 2)| ≤
        2 * |U j * u j| + 18 * (logOrder (2 * m) : ℝ) * u j ^ 2 := by
      rw [abs_mul]
      calc
        _ ≤ 1 * |2 * U j * u j + S * u j ^ 2| :=
          mul_le_mul hmid le_rfl (abs_nonneg _) (by norm_num)
        _ ≤ 1 * (|2 * U j * u j| + |S * u j ^ 2|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
        _ ≤ 2 * |U j * u j| +
            18 * (logOrder (2 * m) : ℝ) * u j ^ 2 := by
          simp only [abs_mul, abs_pow, sq_abs]
          norm_num
          have hsPart := mul_le_mul_of_nonneg_right hS (sq_nonneg (u j))
          nlinarith only [hsPart]
    have h5 : |4 * patternSign w j * epsilon (2 * m) /
          H (epsilon (2 * m)) S ^ 3 * V j ^ 2| ≤
        32 / N ^ 2 * V j ^ 2 := by
      simp only [abs_mul, abs_pow, sq_abs]
      exact mul_le_mul_of_nonneg_right hlast (sq_nonneg _)
    change |c * d j ^ 2 - 2 * T j * u j +
        baseRadial (by omega) w θ v j * u j ^ 2 +
        patternSign w j * epsilon (2 * m) * S / H (epsilon (2 * m)) S *
          (2 * U j * u j + S * u j ^ 2) -
        4 * patternSign w j * epsilon (2 * m) / H (epsilon (2 * m)) S ^ 3 * V j ^ 2| ≤ _
    have ha := abs_sub (c * d j ^ 2 - 2 * T j * u j +
      baseRadial (by omega) w θ v j * u j ^ 2 +
      patternSign w j * epsilon (2 * m) * S / H (epsilon (2 * m)) S *
        (2 * U j * u j + S * u j ^ 2))
      (4 * patternSign w j * epsilon (2 * m) / H (epsilon (2 * m)) S ^ 3 * V j ^ 2)
    have hb := abs_add_le (c * d j ^ 2 - 2 * T j * u j +
      baseRadial (by omega) w θ v j * u j ^ 2)
      (patternSign w j * epsilon (2 * m) * S / H (epsilon (2 * m)) S *
        (2 * U j * u j + S * u j ^ 2))
    have hc' := abs_add_le (c * d j ^ 2 - 2 * T j * u j)
      (baseRadial (by omega) w θ v j * u j ^ 2)
    have hd' := abs_sub (c * d j ^ 2) (2 * T j * u j)
    linarith only [ha, hb, hc', hd', h1, h2, h3, h4, h5]
  have hraw : (∑ j, |secondSource (by omega) w θ η v h j|) / N ≤
      N ^ 2 / 8 * meanSquare d +
      2 * ((∑ j, |T j * u j|) / N) +
      (5 / 2 : ℝ) * meanSquare u +
      (2 * ((∑ j, |U j * u j|) / N) +
        18 * (logOrder (2 * m) : ℝ) * meanSquare u) +
      32 / N ^ 2 * meanSquare V := by
    have havg := average_mono hpoint
    simp only [average_add, average_mul] at havg
    unfold average at havg
    simpa only [meanSquare, N, Nat.cast_mul, Nat.cast_ofNat] using havg
  have hTl1 : (∑ j, |T j * u j|) / N ≤
      Real.sqrt (meanSquare T) * Real.sqrt (meanSquare u) := by
    simpa only [N, Nat.cast_mul, Nat.cast_ofNat] using normalized_product_l1 T u
  have hUl1 : (∑ j, |U j * u j|) / N ≤
      Real.sqrt (meanSquare U) * Real.sqrt (meanSquare u) := by
    simpa only [N, Nat.cast_mul, Nat.cast_ofNat] using normalized_product_l1 U u
  have hVterm : 32 / N ^ 2 * meanSquare V ≤ 108000000 * K / N := by
    calc
      _ ≤ 32 / N ^ 2 * (3300000 * K / N + 64 * N * A) :=
        mul_le_mul_of_nonneg_left hVms (by positivity)
      _ ≤ 108000000 * K / N := by
        field_simp [ne_of_gt hNpos]
        have hN2 : 1 ≤ N ^ 2 := by nlinarith
        have hKN : K ≤ K * N ^ 2 := by nlinarith
        have hAN : A * N ^ 2 ≤ K * N ^ 2 :=
          mul_le_mul_of_nonneg_right hAK (sq_nonneg N)
        nlinarith only [hKN, hAN, hK]
  calc
    _ ≤ N ^ 2 / 8 * meanSquare d +
        2 * ((∑ j, |T j * u j|) / N) +
        (5 / 2 : ℝ) * meanSquare u +
        (2 * ((∑ j, |U j * u j|) / N) +
          18 * (logOrder (2 * m) : ℝ) * meanSquare u) +
        32 / N ^ 2 * meanSquare V := hraw
    _ ≤ N ^ 2 / 8 * (128 * E / N ^ 3) +
        2 * (3000 * K / N + 12 * Real.sqrt (A * E) / Real.sqrt N) +
        (5 / 2 : ℝ) * (4 * E / N ^ 2) +
        (2 * (3000 * K / N + 12 * Real.sqrt (A * E) / Real.sqrt N) +
          18 * (logOrder (2 * m) : ℝ) * (4 * E / N ^ 2)) +
        108000000 * K / N := by
      have hdB := mul_le_mul_of_nonneg_left hdms' (show 0 ≤ N ^ 2 / 8 by positivity)
      have hTB := mul_le_mul_of_nonneg_left (hTl1.trans hTmix) (by norm_num : (0 : ℝ) ≤ 2)
      have huB := mul_le_mul_of_nonneg_left hums (by norm_num : (0 : ℝ) ≤ 5 / 2)
      have hUB := mul_le_mul_of_nonneg_left (hUl1.trans hUmix) (by norm_num : (0 : ℝ) ≤ 2)
      have hL0 : 0 ≤ (logOrder (2 * m) : ℝ) := Nat.cast_nonneg _
      have hLcoef : 0 ≤ 18 * (logOrder (2 * m) : ℝ) :=
        mul_nonneg (by norm_num) hL0
      have hLuB := mul_le_mul_of_nonneg_left hums hLcoef
      linarith only [hdB, hTB, huB, hUB, hLuB, hVterm]
    _ ≤ 120000000 *
        (K / N + Real.sqrt (A * E) / Real.sqrt N) := by
      have hroot : 0 ≤ Real.sqrt (A * E) / Real.sqrt N := by positivity
      have hE1 : E / N ^ 2 ≤ K / N := by
        calc
          _ ≤ K / N ^ 2 := div_le_div_of_nonneg_right hEK (sq_nonneg _)
          _ ≤ K / N := by
            apply div_le_div_of_nonneg_left hK hNpos
            nlinarith
      have hEN : E / N ≤ K / N := div_le_div_of_nonneg_right hEK hNpos.le
      have hLN : (logOrder (2 * m) : ℝ) * E / N ^ 2 ≤ K / N := by
        have hLE := mul_le_mul hL hEK hE hNpos.le
        calc
          _ ≤ N * K / N ^ 2 := div_le_div_of_nonneg_right hLE (sq_nonneg _)
          _ = K / N := by field_simp [ne_of_gt hNpos]
      calc
        _ = 108012000 * K / N + 16 * E / N + 10 * E / N ^ 2 +
            72 * ((logOrder (2 * m) : ℝ) * E / N ^ 2) +
            48 * (Real.sqrt (A * E) / Real.sqrt N) := by
          field_simp [ne_of_gt hNpos]
          ring
        _ ≤ 108012098 * K / N +
            48 * (Real.sqrt (A * E) / Real.sqrt N) := by
          have h1 := mul_le_mul_of_nonneg_left hEN (by norm_num : (0 : ℝ) ≤ 16)
          have h2 := mul_le_mul_of_nonneg_left hE1 (by norm_num : (0 : ℝ) ≤ 10)
          have h3 := mul_le_mul_of_nonneg_left hLN (by norm_num : (0 : ℝ) ≤ 72)
          have hrest : 16 * (E / N) + 10 * (E / N ^ 2) +
              72 * ((logOrder (2 * m) : ℝ) * E / N ^ 2) ≤
              98 * (K / N) := by
            calc
              _ ≤ 16 * (K / N) + 10 * (K / N) + 72 * (K / N) :=
                add_le_add (add_le_add h1 h2) h3
              _ = 98 * (K / N) := by ring
          calc
            _ = 108012000 * (K / N) +
                (16 * (E / N) + 10 * (E / N ^ 2) +
                  72 * ((logOrder (2 * m) : ℝ) * E / N ^ 2)) +
                48 * (Real.sqrt (A * E) / Real.sqrt N) := by ring
            _ ≤ 108012000 * (K / N) + 98 * (K / N) +
                48 * (Real.sqrt (A * E) / Real.sqrt N) := by
              gcongr
            _ = _ := by ring
        _ ≤ 120000000 *
            (K / N + Real.sqrt (A * E) / Real.sqrt N) := by
          have hKN : 0 ≤ K / N := div_nonneg hK hNpos.le
          have h1 : 108012098 * (K / N) ≤ 120000000 * (K / N) :=
            mul_le_mul_of_nonneg_right (by norm_num) hKN
          have h2 : 48 * (Real.sqrt (A * E) / Real.sqrt N) ≤
              120000000 * (Real.sqrt (A * E) / Real.sqrt N) :=
            mul_le_mul_of_nonneg_right (by norm_num) hroot
          calc
            _ = 108012098 * (K / N) +
                48 * (Real.sqrt (A * E) / Real.sqrt N) := by ring
            _ ≤ 120000000 * (K / N) +
                120000000 * (Real.sqrt (A * E) / Real.sqrt N) := add_le_add h1 h2
            _ = _ := by ring

theorem eventual_chosen_second_l1 : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (w : SignPattern (by omega))
      (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v → Admissible (by omega) (η, h) →
      let E := pairEnergy (by omega) (fun j => (η j : ℂ))
      let A := pairEnergy (by omega) h
      let K := E + A
      (∑ j, |chosenSecondDerivative (by omega) w θ η v h j|) /
          (2 * m : ℝ) ≤
        240000000 *
          (K / (2 * m : ℝ) + Real.sqrt (A * E) / Real.sqrt (2 * m : ℝ)) := by
  filter_upwards [eventual_second_source_l1,
    eventual_actual_solution_bounds, eventual_chosen_normalLinearizations] with
      m hsource hinv hlin
  intro hm w θ η v h hdom hd
  dsimp only
  have hi := (hinv hm w θ v hdom
    (chosenSecondDerivative (by omega) w θ η v h)).1
  rw [(hlin hm w θ η v h hdom hd).2] at hi
  have hs := hsource hm w θ η v h hdom hd
  dsimp only at hs
  calc
    _ ≤ 2 * ((∑ j, |secondSource (by omega) w θ η v h j|) /
        (2 * m : ℝ)) := hi
    _ ≤ 2 * (120000000 *
        ((pairEnergy (by omega) (fun j => (η j : ℂ)) + pairEnergy (by omega) h) /
          (2 * m : ℝ) +
        Real.sqrt (pairEnergy (by omega) h *
          pairEnergy (by omega) (fun j => (η j : ℂ))) /
          Real.sqrt (2 * m : ℝ))) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

end
end StructuralNote.FixedSchurChosenSecondBounds

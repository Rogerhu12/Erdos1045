import StructuralNote.FixedSchurRationalWindowDomain
import StructuralNote.LensIncrementDerivatives
import EventualExact.PolarCenterNormalization

/-! Quantitative nondegeneracy of the rational semidiameter-angle chart on
the literal Section 11 single window.  This module treats the `x` coordinates;
the crossing-unit `y` coordinates and the rank-two closure derivative are
separate questions. -/

namespace StructuralNote.FixedSchurRationalWindowAngleChart

open Erdos1045 Erdos1045.EventualExact Complex Filter
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open RationalCommonConfiguration RationalAngleBranch RationalChart
open CommonDomainRadius CommonFiberGeometry
open FixedSchurRationalWindowEnergy FixedSchurRationalWindowDomain
open PolarCenterNormalization LensClosure LensIncrementDerivatives
open scoped BigOperators Topology
noncomputable section

/-- A base-edge-gauge angle parameter is controlled directly by the energy of
the half-periodic `x` column.  The distinguished value `x₀=0` removes the
constant mode. -/
theorem angleParameter_sq_le_energy {m : ℕ} (hm : 0 < m)
    (X : RationalConfiguration.Variables m → ℝ) (j : Fin m) :
    RationalConfiguration.angleParameter X j ^ 2 ≤
      48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 *
        pairEnergy (by omega)
          (fun k => (extendedAngleParameter hm X k : ℂ)) := by
  let c : Fin (2 * m) → ℂ := fun k => (extendedAngleParameter hm X k : ℂ)
  let μ : ℝ := (∑ k : Fin (2 * m), extendedAngleParameter hm X k) / (2 * m : ℝ)
  let z : Fin (2 * m) → ℂ := fun k => ((extendedAngleParameter hm X k - μ : ℝ) : ℂ)
  let j₀ : Fin (2 * m) := ⟨0, by omega⟩
  let i : Fin (2 * m) := CommonClosureEnergy.halfIndex j
  have hnR : (2 * m : ℝ) ≠ 0 := by
    exact_mod_cast (show 2 * m ≠ 0 by omega)
  have hmeanR : (∑ k, (extendedAngleParameter hm X k - μ)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    dsimp [μ]
    field_simp
    norm_num [Nat.cast_mul]
  have hmean : (∑ k, z k) = 0 := by
    change (∑ k, ((extendedAngleParameter hm X k - μ : ℝ) : ℂ)) = 0
    exact_mod_cast hmeanR
  have hzenergy : pairEnergy (by omega) z = pairEnergy (by omega) c := by
    have hzfun : z = fun k => c k - (μ : ℂ) := by
      funext k
      simp only [z, c, Complex.ofReal_sub]
    rw [hzfun]
    exact pairEnergy_sub_const (by omega) c (μ : ℂ)
  have hi := DiscreteSobolev.pointwise_sq_le (show 2 ≤ 2 * m by omega) z hmean i
  have hzero := DiscreteSobolev.pointwise_sq_le (show 2 ≤ 2 * m by omega) z hmean j₀
  rw [hzenergy] at hi hzero
  have hxi : extendedAngleParameter hm X i = RationalConfiguration.angleParameter X j := by
    simp [i, extendedAngleParameter, CommonClosureEnergy.halfIndex,
      Nat.mod_eq_of_lt j.isLt]
  have hxzero : extendedAngleParameter hm X j₀ = 0 := by
    simp [j₀, extendedAngleParameter, RationalConfiguration.angleParameter]
  have hsub : z i - z j₀ = (RationalConfiguration.angleParameter X j : ℂ) := by
    simp only [z, ← Complex.ofReal_sub]
    rw [hxi, hxzero]
    push_cast
    ring
  have htri := norm_sub_le (z i) (z j₀)
  have htrisq := pow_le_pow_left₀ (norm_nonneg (z i - z j₀)) htri 2
  have hsum : (‖z i‖ + ‖z j₀‖) ^ 2 ≤ 2 * ‖z i‖ ^ 2 + 2 * ‖z j₀‖ ^ 2 := by
    nlinarith [sq_nonneg (‖z i‖ - ‖z j₀‖)]
  have hi' : ‖z i‖ ^ 2 ≤
      12 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * pairEnergy (by omega) c := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hi
  have hzero' : ‖z j₀‖ ^ 2 ≤
      12 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * pairEnergy (by omega) c := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hzero
  calc
    RationalConfiguration.angleParameter X j ^ 2 = ‖z i - z j₀‖ ^ 2 := by
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ ≤ (‖z i‖ + ‖z j₀‖) ^ 2 := htrisq
    _ ≤ 2 * ‖z i‖ ^ 2 + 2 * ‖z j₀‖ ^ 2 := hsum
    _ ≤ 48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * pairEnergy (by omega) c := by
      calc
        _ ≤ 2 * (12 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 *
              pairEnergy (by omega) c) +
            2 * (12 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 *
              pairEnergy (by omega) c) :=
          add_le_add (mul_le_mul_of_nonneg_left hi' (by norm_num))
            (mul_le_mul_of_nonneg_left hzero' (by norm_num))
        _ = _ := by ring

private theorem angleWindowCoefficient_tendsto :
    Tendsto (fun n : ℕ =>
      6 * (logOrder n : ℝ) ^ 2 * Real.log n / (n : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have ht := (((isLittleO_log_rpow_rpow_atTop (3 : ℝ)
    (by norm_num : (0 : ℝ) < 2)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop).const_mul 96
  have ht' : Tendsto (fun n : ℕ =>
      96 * Real.log n ^ 3 / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_ofNat, mul_zero, mul_div_assoc] using ht
  apply squeeze_zero' ?_ ?_ ht'
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hlog : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have hL := CommonDomainRadius.logOrder_le hn
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (logOrder n)) hL 2
    have hnum : 6 * (logOrder n : ℝ) ^ 2 * Real.log n ≤
        96 * Real.log n ^ 3 := by
      nlinarith only [hsq, hlog, mul_nonneg
        (sub_nonneg.mpr hsq) hlog]
    exact div_le_div_of_nonneg_right hnum (sq_nonneg (n : ℝ))

/-- Eventually the literal selected window forces every rational semidiameter
coordinate into the manuscript's small `x` window. -/
theorem eventual_selectedWindow_angleParameter_small :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        ∀ j : Fin m,
          |RationalConfiguration.angleParameter X j| < 1 / (2 * m : ℝ) := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  have hsmall := (angleWindowCoefficient_tendsto.comp hnat).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hsmall] with m hsmall
  intro hm s X hwindow j
  let Ex := pairEnergy (by omega : 0 < 2 * m)
    (fun k => (extendedAngleParameter (by omega : 0 < m) X k : ℂ))
  let AR := pairEnergy (by omega : 0 < 2 * m)
    (rationalCenter (by omega : 0 < m) (rationalSign s) X -
      fixedReferenceCenter (by omega) s)
  let L : ℝ := logOrder (2 * m)
  have hAR0 : 0 ≤ AR := pairEnergy_nonneg _ _
  have hEx : Ex < L ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
    change Ex + AR < L ^ 2 / (8 * (2 * m : ℝ) ^ 2) at hwindow
    linarith
  have hlog : 0 < Real.log (2 * m : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < 2 * m by omega))
  have hfactor : 0 < 48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 := by
    positivity
  have hx := angleParameter_sq_le_energy (by omega : 0 < m) X j
  change RationalConfiguration.angleParameter X j ^ 2 ≤
    48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * Ex at hx
  have hx' : RationalConfiguration.angleParameter X j ^ 2 <
      (6 * L ^ 2 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2) *
        (1 / (2 * m : ℝ)) ^ 2 := by
    calc
      _ ≤ 48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 * Ex := hx
      _ < 48 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 *
          (L ^ 2 / (8 * (2 * m : ℝ) ^ 2)) :=
        mul_lt_mul_of_pos_left hEx hfactor
      _ = _ := by ring
  have hone : 6 * L ^ 2 * Real.log (2 * m : ℝ) / (2 * m : ℝ) ^ 2 < 1 := by
    simpa only [L, Function.comp_apply, Nat.cast_mul, Nat.cast_ofNat] using hsmall
  have hx'' : RationalConfiguration.angleParameter X j ^ 2 <
      (1 / (2 * m : ℝ)) ^ 2 := by
    have hr : 0 < (1 / (2 * m : ℝ)) ^ 2 := by
      apply sq_pos_of_pos
      positivity
    exact hx'.trans (by simpa only [one_mul] using mul_lt_mul_of_pos_right hone hr)
  exact (sq_lt_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hx'')

/-- The forward scalar angle coordinate has the exact directional derivative
used by the chart chain rule. -/
theorem angleLine_hasDerivAt (x h : ℝ) :
    HasDerivAt (fun t : ℝ => 2 * Real.arctan (x + t * h))
      (2 / (1 + x ^ 2) * h) 0 := by
  have haff : HasDerivAt (fun t : ℝ => x + t * h) h 0 := by
    simpa only [id_eq, zero_mul, add_zero, one_mul] using
      ((hasDerivAt_id (0 : ℝ)).mul_const h).const_add x
  have hout : HasDerivAt (fun u : ℝ => 2 * Real.arctan u)
      (2 / (1 + x ^ 2)) (x + 0 * h) := by
    simpa only [zero_mul, add_zero] using angle_hasDerivAt x
  change HasDerivAt
    ((fun u : ℝ => 2 * Real.arctan u) ∘ fun t : ℝ => x + t * h)
      (2 / (1 + x ^ 2) * h) 0
  exact hout.comp 0 haff

/-- The rational unit-circle coordinate has its actual complex directional
derivative, obtained through the exact angle representation. -/
theorem rotationLine_hasDerivAt (x h : ℝ) :
    HasDerivAt (fun t : ℝ => rotation (x + t * h))
      (rotation x * (((2 / (1 + x ^ 2) * h : ℝ) : ℂ) * I)) 0 := by
  have hu := unit_path_hasDerivAt (angleLine_hasDerivAt x h)
  simpa only [rotation_eq_unit_arctan, zero_mul, add_zero] using hu

theorem angle_inverse_exact (x : ℝ) :
    Real.tan ((2 * Real.arctan x) / 2) = x := by
  rw [show 2 * Real.arctan x / 2 = Real.arctan x by ring, Real.tan_arctan]

theorem angle_derivative_bounds {x : ℝ} (hx : |x| < 1) :
    1 < 2 / (1 + x ^ 2) ∧ 2 / (1 + x ^ 2) ≤ 2 := by
  have hx2 : x ^ 2 < 1 := by
    nlinarith [sq_abs x, (sq_lt_sq₀ (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1)).mpr hx]
  have hden : 0 < 1 + x ^ 2 := by positivity
  constructor
  · exact (lt_div_iff₀ hden).2 (by nlinarith)
  · exact (div_le_iff₀ hden).2 (by nlinarith [sq_nonneg x])

theorem angle_inverse_derivative_product (x : ℝ) :
    ((1 + x ^ 2) / 2) * (2 / (1 + x ^ 2)) = 1 := by
  have hden : 1 + x ^ 2 ≠ 0 := by positivity
  field_simp

private theorem diameter_close_reference {m : ℕ} (hm : 0 < m)
    (X : RationalConfiguration.Variables m → ℝ) (r : ℕ) :
    ‖RationalConfiguration.diameter hm X r - unit (Real.pi / m * r)‖ ≤
      2 * |RationalConfiguration.angleParameter X ⟨r % m, Nat.mod_lt _ hm⟩| := by
  rw [RationalConfiguration.diameter, rotation_eq_unit_arctan]
  have he : unit (Real.pi / m * r) *
      unit (2 * Real.arctan
        (RationalConfiguration.angleParameter X ⟨r % m, Nat.mod_lt _ hm⟩)) -
      unit (Real.pi / m * r) =
      unit (Real.pi / m * r) *
        (unit (2 * Real.arctan
          (RationalConfiguration.angleParameter X ⟨r % m, Nat.mod_lt _ hm⟩)) - 1) := by
    ring
  rw [he, norm_mul, norm_unit, one_mul]
  calc
    _ ≤ |2 * Real.arctan
        (RationalConfiguration.angleParameter X ⟨r % m, Nat.mod_lt _ hm⟩)| := by
      simpa only [unit, Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_zero] using
        norm_unit_sub_le (2 * Real.arctan
          (RationalConfiguration.angleParameter X ⟨r % m, Nat.mod_lt _ hm⟩)) 0
    _ ≤ 2 * |RationalConfiguration.angleParameter X ⟨r % m, Nat.mod_lt _ hm⟩| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left
        (abs_arctan_le (RationalConfiguration.angleParameter X
          ⟨r % m, Nat.mod_lt _ hm⟩)) (by norm_num)

/-- Small rational angle parameters keep every adjacent semidiameter chord
uniformly away from zero. -/
theorem diameter_sum_norm_gt_one {m : ℕ} (hm : 8 ≤ m)
    (X : RationalConfiguration.Variables m → ℝ)
    (hx : ∀ j : Fin m, |RationalConfiguration.angleParameter X j| <
      1 / (2 * m : ℝ)) (j : Fin m) :
    1 < ‖RationalConfiguration.diameter (by omega) X j +
      RationalConfiguration.diameter (by omega) X (j.val + 1)‖ := by
  let a : ℝ := Real.pi / m * j
  let b : ℝ := Real.pi / (2 * m)
  let e₀ : ℂ := unit (Real.pi / m * j)
  let e₁ : ℂ := unit (Real.pi / m * (j.val + 1))
  have hclose0 := diameter_close_reference (by omega : 0 < m) X j
  have hclose1 := diameter_close_reference (by omega : 0 < m) X (j.val + 1)
  have hclose0' :
      ‖RationalConfiguration.diameter (by omega) X j - e₀‖ ≤
        2 * |RationalConfiguration.angleParameter X
          ⟨j.val % m, Nat.mod_lt _ (by omega : 0 < m)⟩| := by
    simpa only [e₀] using hclose0
  have hclose1' :
      ‖RationalConfiguration.diameter (by omega) X (j.val + 1) - e₁‖ ≤
        2 * |RationalConfiguration.angleParameter X
          ⟨(j.val + 1) % m, Nat.mod_lt _ (by omega : 0 < m)⟩| := by
    simpa only [e₁, Nat.cast_add, Nat.cast_one] using hclose1
  have hx0 : |RationalConfiguration.angleParameter X
      ⟨j.val % m, Nat.mod_lt _ (by omega : 0 < m)⟩| < 1 / (2 * m : ℝ) := hx _
  have hx1 : |RationalConfiguration.angleParameter X
      ⟨(j.val + 1) % m, Nat.mod_lt _ (by omega : 0 < m)⟩| <
      1 / (2 * m : ℝ) := hx _
  have hdev : ‖(RationalConfiguration.diameter (by omega) X j +
        RationalConfiguration.diameter (by omega) X (j.val + 1)) - (e₀ + e₁)‖ <
      4 / (2 * m : ℝ) := by
    have ht := norm_add_le
      (RationalConfiguration.diameter (by omega) X j - e₀)
      (RationalConfiguration.diameter (by omega) X (j.val + 1) - e₁)
    have heq :
        (RationalConfiguration.diameter (by omega) X j +
            RationalConfiguration.diameter (by omega) X (j.val + 1)) - (e₀ + e₁) =
          (RationalConfiguration.diameter (by omega) X j - e₀) +
            (RationalConfiguration.diameter (by omega) X (j.val + 1) - e₁) := by ring
    rw [heq]
    calc
      _ ≤ ‖RationalConfiguration.diameter (by omega) X j - e₀‖ +
          ‖RationalConfiguration.diameter (by omega) X (j.val + 1) - e₁‖ := ht
      _ ≤ 2 * |RationalConfiguration.angleParameter X
            ⟨j.val % m, Nat.mod_lt _ (by omega : 0 < m)⟩| +
          2 * |RationalConfiguration.angleParameter X
            ⟨(j.val + 1) % m, Nat.mod_lt _ (by omega : 0 < m)⟩| :=
        add_le_add hclose0' hclose1'
      _ < 4 / (2 * m : ℝ) := by
        have hsum :
            2 * |RationalConfiguration.angleParameter X
                ⟨j.val % m, Nat.mod_lt _ (by omega : 0 < m)⟩| +
              2 * |RationalConfiguration.angleParameter X
                ⟨(j.val + 1) % m, Nat.mod_lt _ (by omega : 0 < m)⟩| <
              4 * (1 / (2 * m : ℝ)) := by
          linarith
        simpa only [div_eq_mul_inv, one_mul] using hsum
  have hrefEq : e₀ + e₁ = unit (a + b) * (2 * Real.cos b : ℝ) := by
    have hleft : a + b - b = Real.pi / m * j := by ring
    have hright : a + b + b = Real.pi / m * (j.val + 1) := by
      dsimp [a, b]
      field_simp
      ring
    simpa only [e₀, e₁, hleft, hright] using unit_pair (a + b) b
  have hb : 0 < b ∧ b < 1 / 4 := by
    constructor
    · dsimp [b]
      positivity
    · dsimp [b]
      have hmR : (8 : ℝ) ≤ m := by exact_mod_cast hm
      have hpi := Real.pi_lt_four
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * m)).2
      nlinarith
  have hcos : (31 / 32 : ℝ) < Real.cos b := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := b)
    have hb2 : b ^ 2 < (1 / 4 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hb.1.le (by norm_num : (0 : ℝ) ≤ 1 / 4)).2 hb.2
    nlinarith [hc, hb2]
  have href : (31 / 16 : ℝ) < ‖e₀ + e₁‖ := by
    rw [hrefEq, norm_mul, norm_unit, one_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  have hsmall : 4 / (2 * m : ℝ) ≤ 1 / 4 := by
    have hmR : (8 : ℝ) ≤ m := by exact_mod_cast hm
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m)).2
    nlinarith
  have hreverse := norm_sub_norm_le (e₀ + e₁)
    (RationalConfiguration.diameter (by omega) X j +
      RationalConfiguration.diameter (by omega) X (j.val + 1))
  rw [show (e₀ + e₁) -
      (RationalConfiguration.diameter (by omega) X j +
        RationalConfiguration.diameter (by omega) X (j.val + 1)) =
      -((RationalConfiguration.diameter (by omega) X j +
        RationalConfiguration.diameter (by omega) X (j.val + 1)) - (e₀ + e₁)) by ring,
    norm_neg] at hreverse
  linarith

/-- The semidiameter part of the rational chart is quantitatively regular on
the actual selected window: coordinates are small, every adjacent chord is
nondegenerate, and the forward coordinate derivative is uniformly invertible. -/
theorem eventual_selectedWindow_angle_chart :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        (∀ j : Fin m,
          |RationalConfiguration.angleParameter X j| < 1 / (2 * m : ℝ) ∧
          1 < 2 / (1 + RationalConfiguration.angleParameter X j ^ 2) ∧
          2 / (1 + RationalConfiguration.angleParameter X j ^ 2) ≤ 2 ∧
          Real.tan ((2 * Real.arctan
            (RationalConfiguration.angleParameter X j)) / 2) =
              RationalConfiguration.angleParameter X j) ∧
        (∀ j : Fin m, 1 < ‖RationalConfiguration.diameter (by omega) X j +
          RationalConfiguration.diameter (by omega) X (j.val + 1)‖) := by
  filter_upwards [eventual_selectedWindow_angleParameter_small] with m hsmall
  intro hm s X hwindow
  have hx := hsmall (by omega) s X hwindow
  constructor
  · intro j
    have hx1 : |RationalConfiguration.angleParameter X j| < 1 :=
      (hx j).trans (by
        have hmR : (8 : ℝ) ≤ m := by exact_mod_cast hm
        apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * m)).2
        linarith)
    exact ⟨hx j, (angle_derivative_bounds hx1).1,
      (angle_derivative_bounds hx1).2, angle_inverse_exact _⟩
  · exact diameter_sum_norm_gt_one hm X hx

end
end StructuralNote.FixedSchurRationalWindowAngleChart

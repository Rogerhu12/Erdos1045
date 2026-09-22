import EventualExact.ExplicitLocalization
import StructuralNote.ExplicitNumericalBounds
import StructuralNote.ExplicitLocalNumerical

/-! A deliberately coarse binary bound for the explicit localization threshold. -/

namespace Erdos1045.EventualExact.ExplicitLocalizationNumerical

open ExteriorClassical FaberSampling PhysicalForceBudget GapRigidityLimit
open ExplicitInitial ExplicitLocalization ExplicitThreshold
open StructuralNote.ExplicitNumericalBounds
noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 65536

private theorem two_pow_mono {a b : ℕ} (h : a ≤ b) :
    (2 : ℝ) ^ a ≤ 2 ^ b :=
  pow_le_pow_right₀ (by norm_num) h

private theorem mul_le_two_pow {x y : ℝ} {a b : ℕ}
    (_hx₀ : 0 ≤ x) (hy₀ : 0 ≤ y)
    (hx : x ≤ (2 : ℝ) ^ a) (hy : y ≤ (2 : ℝ) ^ b) :
    x * y ≤ (2 : ℝ) ^ (a + b) := by
  calc
    x * y ≤ 2 ^ a * 2 ^ b := mul_le_mul hx hy hy₀ (by positivity)
    _ = 2 ^ (a + b) := by rw [pow_add]

private theorem add_le_two_pow_succ {x y : ℝ} {a : ℕ}
    (hx : x ≤ (2 : ℝ) ^ a) (hy : y ≤ (2 : ℝ) ^ a) :
    x + y ≤ (2 : ℝ) ^ (a + 1) := by
  calc
    x + y ≤ 2 ^ a + 2 ^ a := add_le_add hx hy
    _ = 2 ^ (a + 1) := by rw [pow_succ]; ring

private theorem div_le_two_pow {x y : ℝ} {a b : ℕ}
    (_hx₀ : 0 ≤ x) (hx : x ≤ (2 : ℝ) ^ a)
    (hy : 1 / (2 : ℝ) ^ b ≤ y) :
    x / y ≤ (2 : ℝ) ^ (a + b) := by
  have hy₀ : 0 < y := (by positivity : 0 < 1 / (2 : ℝ) ^ b).trans_le hy
  apply (div_le_iff₀ hy₀).2
  calc
    x ≤ 2 ^ a := hx
    _ = 2 ^ (a + b) * (1 / 2 ^ b) := by
      rw [pow_add]
      field_simp
    _ ≤ 2 ^ (a + b) * y := mul_le_mul_of_nonneg_left hy (by positivity)

private theorem majorant_le_two_pow {C : ℝ} {k : ℕ}
    (hC : |C| ≤ (2 : ℝ) ^ k) : majorant C ≤ 2 ^ (k + 1) := by
  have hc : ⌈|C|⌉₊ ≤ 2 ^ k := Nat.ceil_le.mpr (by exact_mod_cast hC)
  have hp : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_pow k 2 (by decide)
  unfold majorant
  rw [pow_succ]
  omega

private theorem inverse_le_two_pow {C ε : ℝ} {k : ℕ}
    (hC : C / ε ≤ (2 : ℝ) ^ k) : inverseThreshold C ε ≤ 2 ^ (k + 1) := by
  have hc : ⌈C / ε⌉₊ ≤ 2 ^ k := Nat.ceil_le.mpr (by exact_mod_cast hC)
  have hp : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_pow k 2 (by decide)
  unfold inverseThreshold
  rw [pow_succ]
  omega

private theorem inverseSqrt_le_two_pow {C ε : ℝ} {k : ℕ}
    (hC : (C / ε) ^ 2 ≤ (2 : ℝ) ^ k) :
    inverseSqrtThreshold C ε ≤ 2 ^ (k + 1) := by
  have hc : ⌈(C / ε) ^ 2⌉₊ ≤ 2 ^ k := Nat.ceil_le.mpr (by exact_mod_cast hC)
  have hp : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_pow k 2 (by decide)
  unfold inverseSqrtThreshold
  conv_rhs => rw [pow_succ]
  omega

private theorem decay_le_two_pow {C ε : ℝ} {a b : ℕ}
    (hC : |C| ≤ (2 : ℝ) ^ a) (hε : |1 / ε| ≤ (2 : ℝ) ^ b) :
    decayThreshold C ε ≤ 2 ^ (8 * (a + b + 73)) := by
  have ha := majorant_le_two_pow hC
  have hb := majorant_le_two_pow hε
  have hnum : (2 : ℕ) * 81 ^ 10 ≤ 2 ^ 71 := by norm_num
  have hprod : 2 * majorant C * 81 ^ 10 * majorant (1 / ε) ≤
      2 ^ (a + b + 73) := by
    calc
      _ = (2 * 81 ^ 10) * majorant C * majorant (1 / ε) := by ring
      _ ≤ 2 ^ 71 * 2 ^ (a + 1) * 2 ^ (b + 1) := by gcongr
      _ = 2 ^ (a + b + 73) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
  have hp : 2 ≤ (2 : ℕ) ^ (8 * (a + b + 73)) := by
    change 2 ^ 1 ≤ 2 ^ (8 * (a + b + 73))
    exact pow_le_pow_right₀ (by decide) (by omega)
  unfold decayThreshold
  apply max_le hp
  have hh := Nat.pow_le_pow_left hprod 8
  rw [← pow_mul, Nat.mul_comm (a + b + 73) 8] at hh
  exact hh

theorem radiusScale_bound : radiusScale ≤ 100000 := by
  have hlog₀ : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at h ⊢
    exact h
  have hp : Real.pi * Real.log 4 ≤ 4 * 3 :=
    mul_le_mul Real.pi_lt_four.le hlog hlog₀ (by norm_num)
  unfold radiusScale initialEnergy
  rw [max_le_iff]
  constructor
  · norm_num
  · nlinarith only [hp]

theorem exp_radiusScale_bound :
    Real.exp radiusScale ≤ (2 : ℝ) ^ 200000 :=
  exp_le_two_pow radiusScale_bound

private theorem exp_twice_radiusScale_bound :
    Real.exp (2 * radiusScale) ≤ (2 : ℝ) ^ 400000 := by
  apply exp_le_two_pow (k := 200000)
  exact (mul_le_mul_of_nonneg_left radiusScale_bound (by norm_num)).trans_eq (by norm_num)

private theorem angleSeparation_lower :
    1 / (2 : ℝ) ^ 200005 ≤ angleSeparation := by
  have hr : 1 ≤ radiusScale := le_max_left _ _
  have hden : 32 * Real.exp radiusScale ≤ (2 : ℝ) ^ 200005 := by
    calc
      _ ≤ 32 * 2 ^ 200000 := mul_le_mul_of_nonneg_left exp_radiusScale_bound (by norm_num)
      _ = 2 ^ 200005 := by rw [show 200005 = 5 + 200000 by norm_num, pow_add]; norm_num
  unfold angleSeparation
  apply (div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ 200005)
    (by positivity : 0 < 32 * Real.exp radiusScale)).2
  calc
    1 * (32 * Real.exp radiusScale) ≤ 1 * 2 ^ 200005 := by gcongr
    _ ≤ radiusScale * 2 ^ 200005 := by gcongr

theorem samplingConstant_bound :
    samplingConstant ≤ (2 : ℝ) ^ 200010 := by
  let δ := min angleSeparation Real.pi
  have hδ₀ : 0 < δ := lt_min angleSeparation_pos Real.pi_pos
  have hLδ : 1 / (2 : ℝ) ^ 200005 ≤ δ := by
    apply le_min angleSeparation_lower
    have hL1 : 1 / (2 : ℝ) ^ 200005 ≤ 1 := by
      apply (div_le_one (by positivity : 0 < (2 : ℝ) ^ 200005)).2
      exact one_le_pow₀ (by norm_num)
    exact hL1.trans (by nlinarith [Real.pi_gt_three])
  have hfrac : 8 / δ ≤ (2 : ℝ) ^ 200008 := by
    exact div_le_two_pow (by norm_num) (by norm_num : (8 : ℝ) ≤ 2 ^ 3) hLδ
  have hδ : δ ≤ (2 : ℝ) ^ 200008 := by
    have hδ4 : δ ≤ 4 := (min_le_right _ _).trans Real.pi_lt_four.le
    exact hδ4.trans (two_pow_mono (show 2 ≤ 200008 by omega) |>.trans' (by norm_num : (4 : ℝ) ≤ 2 ^ 2))
  unfold samplingConstant
  change 8 / δ + δ ≤ _
  exact (add_le_two_pow_succ hfrac hδ).trans (two_pow_mono (by omega))

private theorem faberRadial_bound :
    FaberSampling.radialConstant radiusScale ≤ 16 := by
  have hr : 1 ≤ radiusScale := le_max_left _ _
  have hratio₀ : 0 ≤ (1 + radiusScale) / radiusScale := by positivity
  have hratio : (1 + radiusScale) / radiusScale ≤ 2 := by
    apply (div_le_iff₀ radiusScale_pos).2
    nlinarith only [hr]
  have hcube := pow_le_pow_left₀ hratio₀ hratio 3
  unfold FaberSampling.radialConstant
  apply max_le <;> nlinarith only [hcube]

theorem matrixErrorConstant_bound :
    matrixErrorConstant ≤ (2 : ℝ) ^ 600019 := by
  unfold matrixErrorConstant ExteriorClassical.matrixConstant
  calc
    32 * Real.exp (2 * radiusScale) * samplingConstant *
        FaberSampling.radialConstant radiusScale ≤
      32 * 2 ^ 400000 * 2 ^ 200010 * 16 := by
        gcongr
        · unfold FaberSampling.radialConstant; positivity
        · exact samplingConstant_pos.le
        · exact exp_twice_radiusScale_bound
        · exact samplingConstant_bound
        · exact faberRadial_bound
    _ = 2 ^ 600019 := by
      rw [show 600019 = 5 + 400000 + 200010 + 4 by norm_num]
      simp only [pow_add]
      norm_num

theorem energyConstant_bound :
    energyConstant ≤ (2 : ℝ) ^ 600040 := by
  unfold energyConstant
  have hpi : 18 * Real.pi ≤ (2 : ℝ) ^ 7 := by
    nlinarith [Real.pi_lt_four]
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 18 * Real.pi) hpi 2
  calc
    16 * matrixErrorConstant * (18 * Real.pi) ^ 2 ≤
        16 * 2 ^ 600019 * (2 ^ 7) ^ 2 := by
      gcongr
      exact matrixErrorConstant_bound
    _ = 2 ^ 600037 := by
      rw [show 600037 = 4 + 600019 + 7 * 2 by norm_num, pow_add, pow_add, pow_mul]
      norm_num
    _ ≤ 2 ^ 600040 := two_pow_mono (by omega)

private theorem sqrt_energyConstant_bound :
    Real.sqrt energyConstant ≤ (2 : ℝ) ^ 300020 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · calc
      energyConstant ≤ 2 ^ 600040 := energyConstant_bound
      _ = (2 ^ 300020) ^ 2 := by rw [← pow_mul]

theorem radialCoefficient_bound :
    radialCoefficient ≤ (2 : ℝ) ^ 300023 := by
  unfold radialCoefficient
  calc
    6 * Real.sqrt energyConstant ≤ 2 ^ 3 * 2 ^ 300020 := by
      exact mul_le_mul (by norm_num) sqrt_energyConstant_bound (Real.sqrt_nonneg _) (by norm_num)
    _ = 2 ^ 300023 := by rw [← pow_add]

private theorem sqrt_six_sqrt_energy_bound :
    Real.sqrt (6 * Real.sqrt energyConstant) ≤ (2 : ℝ) ^ 150012 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · calc
      6 * Real.sqrt energyConstant ≤ 2 ^ 3 * 2 ^ 300020 := by
        exact mul_le_mul (by norm_num) sqrt_energyConstant_bound (Real.sqrt_nonneg _) (by norm_num)
      _ = 2 ^ 300023 := by rw [← pow_add]
      _ ≤ 2 ^ 300024 := two_pow_mono (by omega)
      _ = (2 ^ 150012) ^ 2 := by rw [← pow_mul]

theorem geometricConstant_bound :
    geometricConstant ≤ (2 : ℝ) ^ 150018 := by
  unfold geometricConstant
  calc
    48 * Real.sqrt (6 * Real.sqrt energyConstant) ≤ 2 ^ 6 * 2 ^ 150012 := by
      exact mul_le_mul (by norm_num) sqrt_six_sqrt_energy_bound (Real.sqrt_nonneg _) (by norm_num)
    _ = 2 ^ 150018 := by rw [← pow_add]

private theorem angularSeparation_lower :
    1 / (2 : ℝ) ^ 200006 ≤ angularSeparation := by
  have hr : 1 ≤ radiusScale := le_max_left _ _
  have hden : 64 * Real.exp radiusScale ≤ (2 : ℝ) ^ 200006 := by
    calc
      _ ≤ 64 * 2 ^ 200000 := mul_le_mul_of_nonneg_left exp_radiusScale_bound (by norm_num)
      _ = 2 ^ 200006 := by rw [show 200006 = 6 + 200000 by norm_num, pow_add]; norm_num
  unfold angularSeparation physicalSeparation
  rw [div_div]
  apply (div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ 200006)
    (by positivity : 0 < 8 * Real.exp radiusScale * 8)).2
  calc
    1 * (8 * Real.exp radiusScale * 8) = 64 * Real.exp radiusScale := by ring
    _ ≤ 2 ^ 200006 := hden
    _ ≤ radiusScale * 2 ^ 200006 :=
      by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hr (show 0 ≤ (2 : ℝ) ^ 200006 by positivity)

private theorem radialForce_bound :
    PhysicalForceBudget.radialConstant angularSeparation ≤
      (2 : ℝ) ^ 200011 := by
  unfold PhysicalForceBudget.radialConstant
  have hnum : 2 * Real.pi ^ 2 ≤ (2 : ℝ) ^ 5 := by
    have hp := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le 2
    norm_num at hp ⊢
    linarith only [hp]
  exact div_le_two_pow (by positivity) hnum angularSeparation_lower

private theorem angularForce_bound :
    PhysicalForceBudget.angularConstant angularSeparation ≤
      (2 : ℝ) ^ 200015 := by
  unfold PhysicalForceBudget.angularConstant
  have hpi4 : Real.pi ^ 4 ≤ (4 : ℝ) ^ 4 := by gcongr; exact Real.pi_lt_four.le
  have hnum : 2 * Real.pi ^ 4 ≤ (2 : ℝ) ^ 9 := by
    norm_num at hpi4 ⊢
    linarith only [hpi4]
  exact div_le_two_pow (by positivity) hnum angularSeparation_lower

theorem forceConstant_bound :
    PhysicalForceBudget.forceConstant angularSeparation ≤
      (2 : ℝ) ^ 200017 := by
  have hrad := radialForce_bound.trans (two_pow_mono (show 200011 ≤ 200015 by omega))
  have hang := angularForce_bound
  have hsum : PhysicalForceBudget.radialConstant angularSeparation +
      PhysicalForceBudget.angularConstant angularSeparation ≤ (2 : ℝ) ^ 200016 :=
    add_le_two_pow_succ hrad hang
  have hone : (1 : ℝ) ≤ 2 ^ 200016 := one_le_pow₀ (by norm_num)
  unfold PhysicalForceBudget.forceConstant
  simpa only [add_assoc] using add_le_two_pow_succ hone hsum

theorem rigidityBudget_bound :
    rigidityBudget ≤ (2 : ℝ) ^ 700072 := by
  have hF₀ : 0 ≤ PhysicalForceBudget.forceConstant angularSeparation :=
    PhysicalForceBudget.forceConstant_nonneg angularSeparation_pos
  have hC₀ : 0 ≤ geometricConstant := geometricConstant_nonneg
  have hprod : PhysicalForceBudget.forceConstant angularSeparation * geometricConstant ≤
      (2 : ℝ) ^ 350035 :=
    mul_le_two_pow hF₀ hC₀ forceConstant_bound geometricConstant_bound
  have hsq := pow_le_pow_left₀ (mul_nonneg hF₀ hC₀) hprod 2
  have hsq' : (PhysicalForceBudget.forceConstant angularSeparation) ^ 2 *
      geometricConstant ^ 2 ≤ (2 : ℝ) ^ 700070 := by
    calc
      _ = (PhysicalForceBudget.forceConstant angularSeparation * geometricConstant) ^ 2 := by ring
      _ ≤ (2 ^ 350035) ^ 2 := hsq
      _ = 2 ^ 700070 := by rw [← pow_mul]
  have hprod' := hprod.trans (two_pow_mono (show 350035 ≤ 700070 by omega))
  have hsum : PhysicalForceBudget.forceConstant angularSeparation * geometricConstant +
      PhysicalForceBudget.forceConstant angularSeparation ^ 2 * geometricConstant ^ 2 ≤
      (2 : ℝ) ^ 700071 := add_le_two_pow_succ hprod' hsq'
  have hone : (1 : ℝ) ≤ 2 ^ 700071 := one_le_pow₀ (by norm_num)
  unfold rigidityBudget PhysicalForceBudget.rigidityBudgetConstant
  simpa only [add_assoc] using add_le_two_pow_succ hone hsum

theorem gapCoefficient_bound :
    gapCoefficient ≤ (2 : ℝ) ^ 3500393 := by
  have hC₀ : 0 ≤ rigidityBudget := rigidityBudget_nonneg
  have hpi2 : 3 * Real.pi ^ 2 ≤ (2 : ℝ) ^ 6 := by
    have hp := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le 2
    norm_num at hp ⊢
    linarith only [hp]
  have hterm := mul_le_two_pow (by positivity : 0 ≤ 3 * Real.pi ^ 2) hC₀
    hpi2 rigidityBudget_bound
  have htwo : (2 : ℝ) ≤ 2 ^ 700078 := by
    calc
      (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ 700078 := two_pow_mono (by omega)
  have hinner : 2 + 3 * Real.pi ^ 2 * rigidityBudget ≤
      (2 : ℝ) ^ 700079 := add_le_two_pow_succ htwo hterm
  have hinner₀ : 0 ≤ 2 + 3 * Real.pi ^ 2 * rigidityBudget := by positivity
  have hcube := pow_le_pow_left₀ hinner₀ hinner 3
  have hcube' : (2 + 3 * Real.pi ^ 2 * rigidityBudget) ^ 3 ≤
      (2 : ℝ) ^ 2100237 := by
    calc
      _ ≤ (2 ^ 700079) ^ 3 := hcube
      _ = 2 ^ 2100237 := by rw [← pow_mul]
  have hsq := pow_le_pow_left₀ hC₀ rigidityBudget_bound 2
  have hsq' : rigidityBudget ^ 2 ≤ (2 : ℝ) ^ 1400144 := by
    calc
      _ ≤ (2 ^ 700072) ^ 2 := hsq
      _ = 2 ^ 1400144 := by rw [← pow_mul]
  have hcoef : 54 * Real.pi ^ 3 ≤ (2 : ℝ) ^ 12 := by
    have hpi3 : Real.pi ^ 3 ≤ (4 : ℝ) ^ 3 := by gcongr; exact Real.pi_lt_four.le
    norm_num at hpi3 ⊢
    linarith only [hpi3]
  unfold gapCoefficient GapRigidityLimit.rigidityConstant
  calc
    54 * Real.pi ^ 3 * (2 + 3 * Real.pi ^ 2 * rigidityBudget) ^ 3 * rigidityBudget ^ 2 ≤
      2 ^ 12 * 2 ^ 2100237 * 2 ^ 1400144 := by gcongr
    _ = 2 ^ 3500393 := by
      rw [show 3500393 = 12 + 2100237 + 1400144 by norm_num, pow_add, pow_add]

theorem coarseThreshold_bound :
    coarseThreshold ≤ (2 : ℕ) ^ 600030 := by
  have hlog : 2 * Real.log 4 ≤ (2 : ℝ) ^ 600029 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    have hsmall : 2 * Real.log 4 ≤ 8 := by norm_num at h ⊢; linarith only [h]
    calc
      2 * Real.log 4 ≤ 8 := hsmall
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ 2 ^ 600029 := two_pow_mono (by omega)
  have hpi : 18 * Real.pi ≤ (2 : ℝ) ^ 7 := by nlinarith [Real.pi_lt_four]
  have hmul := mul_le_two_pow matrixErrorConstant_nonneg (by positivity : 0 ≤ 18 * Real.pi)
    matrixErrorConstant_bound hpi
  have hmain : 4 * matrixErrorConstant * (18 * Real.pi) ≤
      (2 : ℝ) ^ 600028 := by
    simpa only [mul_assoc] using
      (mul_le_two_pow (by norm_num) (mul_nonneg matrixErrorConstant_nonneg (by positivity))
        (by norm_num : (4 : ℝ) ≤ 2 ^ 2) hmul)
  have hmax : max (2 * Real.log 4) (4 * matrixErrorConstant * (18 * Real.pi)) ≤
      (2 : ℝ) ^ 600029 := max_le hlog (hmain.trans (two_pow_mono (by omega)))
  have hceil : ⌈max (2 * Real.log 4) (4 * matrixErrorConstant * (18 * Real.pi))⌉₊ ≤
      (2 : ℕ) ^ 600029 := Nat.ceil_le.mpr (by exact_mod_cast hmax)
  unfold coarseThreshold
  apply max_le
  · exact (show 4 ≤ (2 : ℕ) ^ 2 by norm_num) |>.trans
      (pow_le_pow_right₀ (by decide) (show 2 ≤ 600030 by omega))
  · exact hceil.trans (pow_le_pow_right₀ (by decide) (show 600029 ≤ 600030 by omega))

private theorem epsilon_dyadic_lower {ε : ℝ} (hε : (1 : ℝ) / 10 ^ 20 ≤ ε) :
    1 / (2 : ℝ) ^ 80 ≤ ε := by
  have hpNat : (10 : ℕ) ^ 20 ≤ 2 ^ 80 := by
    exact (pow10_le_pow2 20).trans_eq (by norm_num)
  have hp : (10 : ℝ) ^ 20 ≤ 2 ^ 80 := by exact_mod_cast hpNat
  have hinv : 1 / (2 : ℝ) ^ 80 ≤ 1 / 10 ^ 20 := by
    apply (div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ 80)
      (by positivity : 0 < (10 : ℝ) ^ 20)).2
    simpa using hp
  exact hinv.trans hε

theorem edgeTarget_lower {ε : ℝ} (hε : (1 : ℝ) / 10 ^ 20 ≤ ε) :
    1 / (2 : ℝ) ^ 82 ≤ edgeTarget ε := by
  have he := epsilon_dyadic_lower hε
  unfold edgeTarget
  apply le_min
  · apply (div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ 82) (by norm_num : (0 : ℝ) < 2)).2
    simpa using two_pow_mono (show 1 ≤ 82 by omega)
  · calc
      1 / (2 : ℝ) ^ 82 = (1 / 2 ^ 80) / 4 := by
        rw [show 82 = 80 + 2 by norm_num, pow_add]
        norm_num
      _ ≤ ε / 4 := div_le_div_of_nonneg_right he (by norm_num)

theorem gapTarget_lower {ε : ℝ} (hε : (1 : ℝ) / 10 ^ 20 ≤ ε) :
    1 / (2 : ℝ) ^ 88 ≤ gapTarget ε := by
  have hedge := edgeTarget_lower hε
  have hden : 10 * Real.pi ≤ (2 : ℝ) ^ 6 := by nlinarith [Real.pi_lt_four]
  have hden₀ : 0 < 10 * Real.pi := by positivity
  unfold gapTarget
  apply (div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ 88) hden₀).2
  calc
    1 * (10 * Real.pi) ≤ 2 ^ 6 := by simpa using hden
    _ = (1 / 2 ^ 82) * 2 ^ 88 := by
      rw [show 88 = 82 + 6 by norm_num, pow_add]
      field_simp
    _ ≤ edgeTarget ε * 2 ^ 88 := mul_le_mul_of_nonneg_right hedge (by positivity)

theorem radialTarget_lower {ε : ℝ} (hε : (1 : ℝ) / 10 ^ 20 ≤ ε) :
    1 / (2 : ℝ) ^ 91 ≤ radialTarget ε := by
  have hedge := edgeTarget_lower hε
  have hden : 104 * Real.pi ≤ (2 : ℝ) ^ 9 := by nlinarith [Real.pi_lt_four]
  have hden₀ : 0 < 104 * Real.pi := by positivity
  unfold radialTarget
  apply (div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ 91) hden₀).2
  calc
    1 * (104 * Real.pi) ≤ 2 ^ 9 := by simpa using hden
    _ = (1 / 2 ^ 82) * 2 ^ 91 := by
      rw [show 91 = 82 + 9 by norm_num, pow_add]
      field_simp
    _ ≤ edgeTarget ε * 2 ^ 91 := mul_le_mul_of_nonneg_right hedge (by positivity)

theorem localizationThreshold_bound {ε : ℝ}
    (hε : (1 : ℝ) / 10 ^ 20 ≤ ε) :
    localizationThreshold ε ≤ (2 : ℕ) ^ 100000000 := by
  have hεpos : 0 < ε := (by positivity : 0 < (1 : ℝ) / 10 ^ 20).trans_le hε
  have hradT := radialTarget_lower hε
  have hgapT := gapTarget_lower hε
  have hradTpos := radialTarget_pos hεpos
  have hgapTpos := gapTarget_pos hεpos
  have hradSqLower : 1 / (2 : ℝ) ^ 182 ≤ (radialTarget ε) ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (2 : ℝ) ^ 91) hradT 2
    calc
      1 / (2 : ℝ) ^ 182 = (1 / 2 ^ 91) ^ 2 := by
        rw [show 182 = 91 * 2 by norm_num, pow_mul]
        field_simp
      _ ≤ _ := hh
  have hgapCubeLower : 1 / (2 : ℝ) ^ 264 ≤ (gapTarget ε) ^ 3 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (2 : ℝ) ^ 88) hgapT 3
    calc
      1 / (2 : ℝ) ^ 264 = (1 / 2 ^ 88) ^ 3 := by
        rw [show 264 = 88 * 3 by norm_num, pow_mul]
        field_simp
      _ ≤ _ := hh
  have hquarter : radialCoefficient / (1 / 4) ≤ (2 : ℝ) ^ 300025 := by
    exact div_le_two_pow radialCoefficient_nonneg radialCoefficient_bound
      (by norm_num : (1 : ℝ) / 2 ^ 2 ≤ 1 / 4)
  have hradial : radialCoefficient / (radialTarget ε) ^ 2 ≤
      (2 : ℝ) ^ 300205 :=
    div_le_two_pow radialCoefficient_nonneg radialCoefficient_bound hradSqLower
  have hgeoPi : geometricConstant * Real.pi ≤ (2 : ℝ) ^ 150020 := by
    exact mul_le_two_pow geometricConstant_nonneg Real.pi_pos.le geometricConstant_bound
      (by nlinarith [Real.pi_lt_four] : Real.pi ≤ (2 : ℝ) ^ 2)
  have hgeoPiSq : (geometricConstant * Real.pi / 1) ^ 2 ≤
      (2 : ℝ) ^ 300040 := by
    have hh := pow_le_pow_left₀ (mul_nonneg geometricConstant_nonneg Real.pi_pos.le) hgeoPi 2
    simpa only [div_one] using hh.trans_eq (by rw [← pow_mul])
  have hgapRecip : |1 / (gapTarget ε) ^ 3| ≤ (2 : ℝ) ^ 264 := by
    rw [abs_of_pos (one_div_pos.mpr (pow_pos hgapTpos 3))]
    exact div_le_two_pow (by norm_num) (by norm_num : (1 : ℝ) ≤ 2 ^ 0) hgapCubeLower
  have hcoarse : coarseThreshold ≤ 2 ^ 100000000 :=
    coarseThreshold_bound.trans (pow_le_pow_right₀ (by decide) (by omega))
  have hq : inverseThreshold radialCoefficient (1 / 4) ≤ 2 ^ 100000000 :=
    (inverse_le_two_pow hquarter).trans (pow_le_pow_right₀ (by decide) (by omega))
  have hr : inverseThreshold radialCoefficient ((radialTarget ε) ^ 2) ≤ 2 ^ 100000000 :=
    (inverse_le_two_pow hradial).trans (pow_le_pow_right₀ (by decide) (by omega))
  have hs : inverseSqrtThreshold (geometricConstant * Real.pi) 1 ≤ 2 ^ 100000000 :=
    (inverseSqrt_le_two_pow hgeoPiSq).trans (pow_le_pow_right₀ (by decide) (by omega))
  have hg : decayThreshold geometricConstant 1 ≤ 2 ^ 100000000 := by
    have hh := decay_le_two_pow (C := geometricConstant) (ε := 1) (a := 150018) (b := 0)
      (by simpa [abs_of_nonneg geometricConstant_nonneg] using geometricConstant_bound)
      (by norm_num : |(1 : ℝ) / 1| ≤ 2 ^ 0)
    exact hh.trans (pow_le_pow_right₀ (by decide) (by norm_num))
  have hgap : decayThreshold gapCoefficient ((gapTarget ε) ^ 3) ≤
      2 ^ 100000000 := by
    have hh := decay_le_two_pow (C := gapCoefficient) (ε := (gapTarget ε) ^ 3)
      (a := 3500393) (b := 264)
      (by simpa [abs_of_nonneg gapCoefficient_nonneg] using gapCoefficient_bound) hgapRecip
    exact hh.trans (pow_le_pow_right₀ (by decide) (by norm_num))
  unfold localizationThreshold
  exact max_le hcoarse (max_le hq (max_le hr (max_le hs (max_le hg hgap))))

end
end Erdos1045.EventualExact.ExplicitLocalizationNumerical

namespace StructuralNote.ExplicitLocalizationNumerical

open Erdos1045.EventualExact
open ExplicitPressureNumerical ExplicitLocalNumerical

/-- The full physical-localization threshold at the strong-coordinate edge tolerance
is already below a modest binary cutoff. -/
theorem localizationThreshold_le_binaryCutoff :
    ExplicitLocalization.localizationThreshold ExplicitStrongBudget.edgeTolerance ≤
      (2 : ℕ) ^ 100000000 :=
  Erdos1045.EventualExact.ExplicitLocalizationNumerical.localizationThreshold_bound
    edgeTolerance_lower

/-- Numerical bridge used by the final assembly. -/
theorem localizationThreshold_le_concrete :
    ExplicitLocalization.localizationThreshold ExplicitStrongBudget.edgeTolerance ≤
      ExplicitPressureNumerical.concreteThreshold := by
  have hexp : 100000000 ≤ (10 : ℕ) ^ 120 := by
    change 10 ^ 8 ≤ 10 ^ 120
    exact Nat.pow_le_pow_right (by decide) (by norm_num)
  have hp : (2 : ℕ) ^ 100000000 ≤ 2 ^ (10 ^ 120) :=
    pow_le_pow_right₀ (by decide) hexp
  unfold ExplicitPressureNumerical.concreteThreshold
  exact localizationThreshold_le_binaryCutoff.trans hp

end StructuralNote.ExplicitLocalizationNumerical

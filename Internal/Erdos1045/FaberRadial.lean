import Erdos1045.FaberSampling

namespace Erdos1045.FaberSampling

open scoped BigOperators
noncomputable section

/-- The standard differentiated geometric-series identity, independently of
the polygon, Faber coefficients, and sampling points. -/
def ClassicalGeometricMoment : Prop := ∀ q : ℝ, 0 ≤ q → q < 1 →
  HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ 2 * q ^ (k + 1))
    (q * (1 + q) / (1 - q) ^ 3)

def radialRatio (n : ℕ) (τ : ℝ) : ℝ := n / ((n : ℝ) + τ)

def radialWeight (n : ℕ) (τ : ℝ) (k : ℕ) : ℝ := radialRatio n τ ^ (2 * k)

def radialConstant (τ : ℝ) : ℝ := max 1 (2 * ((1 + τ) / τ) ^ 3)

theorem radialRatio_pos {n : ℕ} (hn : 0 < n) {τ : ℝ} (hτ : 0 < τ) :
    0 < radialRatio n τ := by unfold radialRatio; positivity

theorem radialRatio_lt_one {n : ℕ} (hn : 0 < n) {τ : ℝ} (hτ : 0 < τ) :
    radialRatio n τ < 1 := by
  unfold radialRatio
  apply (div_lt_one (by positivity)).2
  linarith

theorem radialWeight_nonneg {n k : ℕ} {τ : ℝ} (hn : 0 < n) (hτ : 0 < τ) :
    0 ≤ radialWeight n τ k := pow_nonneg (radialRatio_pos hn hτ).le _

theorem radialWeight_le_one {n k : ℕ} {τ : ℝ} (hn : 0 < n) (hτ : 0 < τ) :
    radialWeight n τ k ≤ 1 := by
  exact pow_le_one₀ (radialRatio_pos hn hτ).le (radialRatio_lt_one hn hτ).le

theorem radial_moment_bound (classicalMoment : ClassicalGeometricMoment)
    {n : ℕ} (hn : 0 < n) {τ : ℝ} (hτ : 0 < τ) (m : ℕ) :
    moment (radialWeight n τ) m ≤ radialConstant τ * (n : ℝ) ^ 3 := by
  let q := radialRatio n τ
  have hq0 : 0 < q := radialRatio_pos hn hτ
  have hq1 : q < 1 := radialRatio_lt_one hn hτ
  have hseries := classicalMoment q hq0.le hq1
  have hpartial : moment (radialWeight n τ) m ≤ q * (1 + q) / (1 - q) ^ 3 := by
    calc
      moment (radialWeight n τ) m ≤
          ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) ^ 2 * q ^ (k + 1) := by
        apply Finset.sum_le_sum
        intro k _
        have hp0 := pow_nonneg hq0.le (k + 1)
        have hp1 := pow_le_one₀ hq0.le hq1.le (n := k + 1)
        have hp : q ^ (2 * (k + 1)) ≤ q ^ (k + 1) := by
          rw [mul_comm 2, pow_mul]
          nlinarith
        exact mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ ≤ q * (1 + q) / (1 - q) ^ 3 :=
        (hseries.summable.sum_le_tsum _ (fun k _ => by positivity)).trans_eq hseries.tsum_eq
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnτ : (n : ℝ) + τ ≠ 0 := by positivity
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hinv : (1 - q)⁻¹ = ((n : ℝ) + τ) / τ := by
    dsimp [q, radialRatio]
    field_simp
    simp [hτ0]
  have hratio : ((n : ℝ) + τ) / τ ≤ (n : ℝ) * ((1 + τ) / τ) := by
    apply (div_le_iff₀ hτ).2
    have heq : (n : ℝ) * ((1 + τ) / τ) * τ = (n : ℝ) * (1 + τ) := by field_simp
    rw [heq]
    nlinarith
  have hcube := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((n : ℝ) + τ) / τ) hratio 3
  have hnum : q * (1 + q) ≤ 2 := by nlinarith [sq_nonneg (1 - q)]
  calc
    moment (radialWeight n τ) m ≤ q * (1 + q) / (1 - q) ^ 3 := hpartial
    _ = (q * (1 + q)) * (((n : ℝ) + τ) / τ) ^ 3 := by
      rw [div_eq_mul_inv, ← inv_pow, hinv]
    _ ≤ 2 * ((n : ℝ) * ((1 + τ) / τ)) ^ 3 :=
      mul_le_mul hnum hcube (by positivity) (by norm_num)
    _ = (2 * ((1 + τ) / τ) ^ 3) * (n : ℝ) ^ 3 := by ring
    _ ≤ radialConstant τ * (n : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

theorem radial_inner_sum_le (classicalMoment : ClassicalGeometricMoment)
    {n : ℕ} (hn : 0 < n) {τ : ℝ} (hτ : 0 < τ) (m : ℕ) :
    (∑ k ∈ Finset.range m, coupling n (radialWeight n τ) k m) ≤
      2 * radialConstant τ * (n : ℝ) ^ 2 * (m : ℝ) ^ 2 :=
  inner_sum_le hn (fun _ => radialWeight_nonneg hn hτ)
    (fun _ => radialWeight_le_one hn hτ) (le_max_left _ _)
    (radial_moment_bound classicalMoment hn hτ) m

/-- The loss on retaining modes at most `n` is uniformly bounded by `exp(2τ)`. -/
theorem radial_unweight {n k : ℕ} (hn : 0 < n) {τ : ℝ} (hτ : 0 < τ) (hk : k ≤ n) :
    1 ≤ Real.exp (2 * τ) * radialWeight n τ k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq := radialRatio_pos hn hτ
  have hinv : (radialRatio n τ)⁻¹ = ((n : ℝ) + τ) / n := by
    unfold radialRatio
    rw [inv_div]
  have hlog := Real.one_sub_inv_le_log_of_pos hq
  rw [hinv] at hlog
  have hloglower : -τ / n ≤ Real.log (radialRatio n τ) := by
    have hid : 1 - ((n : ℝ) + τ) / n = -τ / n := by field_simp; ring
    rwa [hid] at hlog
  have hmult := mul_le_mul_of_nonneg_left hloglower (show 0 ≤ (2 : ℝ) * k by positivity)
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hkt : (k : ℝ) * τ / n ≤ τ := by
    apply (div_le_iff₀ hn').2
    nlinarith
  have hlogpow : -2 * τ ≤ Real.log (radialRatio n τ ^ (2 * k)) := by
    rw [Real.log_pow]
    push_cast
    simp only [div_eq_mul_inv] at hmult hkt
    nlinarith
  have hlo := (Real.le_log_iff_exp_le (pow_pos hq (2 * k))).1 hlogpow
  have hm := mul_le_mul_of_nonneg_left hlo (Real.exp_pos (2 * τ)).le
  have hexp : Real.exp (2 * τ) * Real.exp (-2 * τ) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hexp] at hm
  exact hm

end

end Erdos1045.FaberSampling

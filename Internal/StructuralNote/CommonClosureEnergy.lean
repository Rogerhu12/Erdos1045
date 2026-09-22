import StructuralNote.CommonClosureExistence
import EventualExact.DiscreteSobolev

/-! Actual energy bounds imply uniform small closure roots. The energy ball used
here, A(theta), A(v) <= 1/n, eventually contains the manuscript's common domain. -/

namespace StructuralNote.CommonClosureEnergy

open Erdos1045.EventualExact Complex
open FiniteFourierLift SchurSpectrum LensClosure CommonClosureExistence
open scoped BigOperators
noncomputable section

theorem pointwise_of_small_energy {n : ℕ} (hn : 2 ≤ n) (c : Fin n → ℂ)
    (hmean : ∑ j, c j = 0) (hA : pairEnergy (by omega) c ≤ 1 / n) (j : Fin n) :
    ‖c j‖ ≤ 4 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlog : Real.log n ≤ n := by linarith [Real.log_le_sub_one_of_pos hnR]
  have hsq := DiscreteSobolev.pointwise_sq_le hn c hmean j
  have hAB : 12 * Real.log n / (n : ℝ) ^ 2 * pairEnergy (by omega) c ≤
      12 / (n : ℝ) ^ 2 := by
    calc
      _ ≤ 12 * Real.log n / (n : ℝ) ^ 2 * (1 / n) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      _ ≤ 12 * (n : ℝ) / (n : ℝ) ^ 2 * (1 / n) := by gcongr
      _ = _ := by field_simp
  have ht : ‖c j‖ ^ 2 ≤ (4 / (n : ℝ)) ^ 2 := by
    have hb := hsq.trans hAB
    rw [div_pow]
    norm_num
    exact hb.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity))
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ht

theorem difference_sq_of_energy {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ) (j : Fin n) :
    (n : ℝ) ^ 2 * ‖difference hn c j‖ ^ 2 ≤ 8 * Real.pi ^ 2 * pairEnergy hn c := by
  have hj : normSq (difference hn c j) ≤ ∑ k, normSq (difference hn c k) :=
    Finset.single_le_sum (fun k _ => normSq_nonneg _) (Finset.mem_univ j)
  rw [normSq_eq_norm_sq] at hj
  exact (mul_le_mul_of_nonneg_left hj (sq_nonneg _)).trans (DiscreteEnergy.difference_energy_le hn c)

theorem difference_of_small_energy {n : ℕ} (hn : 0 < n) (c : Fin n → ℂ)
    (hA : pairEnergy hn c ≤ 1 / n) (j : Fin n) : ‖difference hn c j‖ ≤ 10 / n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have ha1 : pairEnergy hn c ≤ 1 := hA.trans (by simpa using one_div_le_one_div_of_le (by norm_num) hnR)
  have hsq := difference_sq_of_energy hn c j
  have hpi : Real.pi ^ 2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hpi' : Real.pi ^ 2 < 12 := by nlinarith [Real.pi_lt_d4, Real.pi_pos]
  have hh : (n : ℝ) ^ 2 * ‖difference hn c j‖ ^ 2 ≤ 100 := by
    have hb := mul_le_mul_of_nonneg_left ha1 (by positivity : 0 ≤ 8 * Real.pi ^ 2)
    nlinarith only [hsq, hb, hpi']
  apply (le_div_iff₀ hnpos).mpr
  nlinarith [mul_nonneg (norm_nonneg (difference hn c j)) hnpos.le]

def angleAverage {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (j : Fin n) : ℝ :=
  (θ j + θ (successor hn j)) / 2

def angleDifference {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (j : Fin n) : ℝ :=
  θ (successor hn j) - θ j

theorem angleAverage_le {n : ℕ} (hn : 2 ≤ n) (θ : Fin n → ℝ)
    (hmean : ∑ j, (θ j : ℂ) = 0)
    (hA : pairEnergy (by omega) (fun j => (θ j : ℂ)) ≤ 1 / n) (j : Fin n) :
    |angleAverage (by omega) θ j| ≤ 4 / n := by
  have h₁ := pointwise_of_small_energy hn (fun j => (θ j : ℂ)) hmean hA j
  have h₂ := pointwise_of_small_energy hn (fun j => (θ j : ℂ)) hmean hA (successor (by omega) j)
  simp only [Complex.norm_real, Real.norm_eq_abs] at h₁ h₂
  dsimp [angleAverage]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := abs_add_le (θ j) (θ (successor (by omega) j))
  linarith

theorem angleDifference_le {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
    (hA : pairEnergy hn (fun j => (θ j : ℂ)) ≤ 1 / n) (j : Fin n) :
    |angleDifference hn θ j| ≤ 10 / n := by
  have h := difference_of_small_energy hn (fun j => (θ j : ℂ)) hA j
  simpa only [angleDifference, difference, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] using h

def halfIndex {m : ℕ} (j : Fin m) : Fin (2 * m) := ⟨j, by omega⟩

def phase {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (j : Fin m) : ℝ :=
  midpoint m j + angleAverage (by omega) θ (halfIndex j)

def halfAngle {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (j : Fin m) : ℝ :=
  Real.pi / (2 * m) + angleDifference (by omega) θ (halfIndex j) / 2

theorem exists_unique_energy_root {m : ℕ} (hm : 128 ≤ m)
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ) (ν σ : Fin m → ℝ)
    (hmean : ∑ j, (θ j : ℂ) = 0)
    (hθ : pairEnergy (by omega) (fun j => (θ j : ℂ)) ≤ 1 / (2 * m))
    (hv : pairEnergy (by omega) v ≤ 1 / (2 * m))
    (hν : ∀ j, |ν j| ≤ ‖difference (by omega) v (halfIndex j)‖)
    (hclosed : (∑ j, unit (midpoint m j) * ((ν j : ℂ) * I)) = 0)
    (hσ : ∀ j, |σ j| ≤ 1) :
    ∃! ξ : ℂ, ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2 ∧
      closure (phase (by omega) θ) (fun j => 2 * Real.cos (halfAngle (by omega) θ j)) σ ν ξ = 0 := by
  have hmR : (128 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < 2 * m := by positivity
  have hθ' : pairEnergy (by omega) (fun j => (θ j : ℂ)) ≤ 1 / ((2 * m : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hθ
  have hv' : pairEnergy (by omega) v ≤ 1 / ((2 * m : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hv
  apply exists_unique_geometric_root (by omega) (phase (by omega) θ)
    (halfAngle (by omega) θ) σ ν (e := 4 / (2 * m)) (d := 9 / (2 * m)) (h := 10 / (2 * m))
  · positivity
  · apply (div_le_iff₀ hnR).mpr; linarith
  · exact hσ
  · intro j
    simpa only [phase, add_sub_cancel_left, Nat.cast_mul, Nat.cast_ofNat] using
      angleAverage_le (by omega) θ hmean hθ' (halfIndex j)
  · intro j
    have h := angleDifference_le (by omega) θ hθ' (halfIndex j)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    have hp : |Real.pi / (2 * m : ℝ)| = Real.pi / (2 * m) := abs_of_pos (by positivity)
    unfold halfAngle
    calc
      _ ≤ |Real.pi / (2 * m : ℝ)| + |angleDifference (by omega) θ (halfIndex j) / 2| := abs_add_le _ _
      _ = Real.pi / (2 * m) + |angleDifference (by omega) θ (halfIndex j)| / 2 := by rw [hp, abs_div]; norm_num
      _ ≤ Real.pi / (2 * m) + (10 / (2 * m)) / 2 := by gcongr
      _ ≤ _ := by
        apply (le_of_mul_le_mul_right ?_ hnR)
        field_simp
        linarith [Real.pi_lt_four]
  · intro j
    have h := difference_of_small_energy (by omega) v hv' (halfIndex j)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    exact (hν j).trans h
  · exact hclosed
  · have h₁ : (4 : ℝ) / (2 * m) ≤ 1 / 64 := by apply (div_le_iff₀ hnR).mpr; linarith
    have h₂ : (10 : ℝ) / (2 * m) ≤ 5 / 128 := by apply (div_le_iff₀ hnR).mpr; linarith
    have h₃ : (1024 : ℝ) / (2 * m) ^ 2 ≤ 1 / 64 := by
      apply (div_le_iff₀ (sq_pos_of_pos hnR)).mpr
      nlinarith
    linarith
  · field_simp
    norm_num

end
end StructuralNote.CommonClosureEnergy

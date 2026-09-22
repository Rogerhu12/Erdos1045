import EventualExact.CoarseFeketeFamilyProved

/-! Explicit constants and finite-dimension coarse exterior localization.
The constants below are formulae, not witnesses extracted from eventual assertions.
The deliberately large expressions are never numerically evaluated. -/

namespace Erdos1045.FaberFourier
open MeasureTheory Set
open scoped BigOperators
noncomputable section

/-- The concrete constant already produced by the interval sampling proof. -/
theorem circle_sampling_explicit {γ : ℝ} (hγ : 0 < γ) {n : ℕ}
    (hn : 0 < n) (θ : Fin n → ℝ) (hsep : Separated θ γ) :
    H1Sampling θ (8 / min γ Real.pi + min γ Real.pi) := by
  let δ := min γ Real.pi
  have hδ : 0 < δ := lt_min hγ Real.pi_pos
  intro f
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let L := δ / (4 * n)
  have hL : 0 < L := div_pos hδ (by positivity)
  have hLn : L * (4 * n) = δ := div_mul_cancel₀ δ (by positivity)
  have hδπ : δ ≤ Real.pi := min_le_right _ _
  have hδγ : δ ≤ γ := min_le_left _ _
  have hLπ : L ≤ Real.pi := by
    nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hn1)]
  have hLγ : 4 * L ≤ γ / n := by
    apply (le_div_iff₀ hn0).mpr
    nlinarith [hLn]
  let a : Fin n → ℝ := fun j => if θ j ≤ Real.pi then θ j else θ j - L
  let b : Fin n → ℝ := fun j => a j + L
  have hlen (j : Fin n) : b j - a j = L := by dsimp [b]; ring
  have hnode (j : Fin n) : θ j ∈ Icc (a j) (b j) := by
    dsimp [a, b]
    split_ifs <;> constructor <;> linarith
  have hsub (j : Fin n) : Ioc (a j) (b j) ⊆ Ioc 0 (2 * Real.pi) := by
    have hrange := hsep.1 j
    intro x hx
    dsimp [a, b] at hx
    split_ifs at hx with hθ <;> constructor <;> linarith [hrange.1, hrange.2, hx.1, hx.2]
  have hdis : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hxi' : |θ i - x| ≤ L := by
      apply abs_le.mpr
      constructor <;> linarith [(hnode i).1, (hnode i).2, hlen i, hxi.1, hxi.2]
    have hxj' : |x - θ j| ≤ L := by
      apply abs_le.mpr
      constructor <;> linarith [(hnode j).1, (hnode j).2, hlen j, hxj.1, hxj.2]
    have hfar : γ / n ≤ |θ i - θ j| := (hsep.2 i j hij).trans (min_le_left _ _)
    have htriangle := abs_sub_le (θ i) x (θ j)
    linarith
  have hb := f.sampling_of_intervals θ a b hL hlen hnode hsub hdis
  have hE : 0 ≤ energy f.value := integral_nonneg fun x => sq_nonneg _
  have hD : 0 ≤ energy f.weakDerivative := integral_nonneg fun x => sq_nonneg _
  have heq : (2 / L) * energy f.value + 2 * L * energy f.weakDerivative =
      (8 / δ) * ((n : ℝ) * energy f.value) + (δ / 2) * (energy f.weakDerivative / n) := by
    dsimp [L]
    field_simp
    ring
  rw [heq] at hb
  apply hb.trans
  have hC1 : 8 / δ ≤ 8 / δ + δ := le_add_of_nonneg_right hδ.le
  have hC2 : δ / 2 ≤ 8 / δ + δ := by
    have : 0 ≤ 8 / δ := by positivity
    linarith
  calc
    (8 / δ) * ((n : ℝ) * energy f.value) + (δ / 2) * (energy f.weakDerivative / n) ≤
        (8 / δ + δ) * ((n : ℝ) * energy f.value) +
          (8 / δ + δ) * (energy f.weakDerivative / n) :=
      add_le_add (mul_le_mul_of_nonneg_right hC1 (mul_nonneg hn0.le hE))
        (mul_le_mul_of_nonneg_right hC2 (div_nonneg hD hn0.le))
    _ = _ := by ring

end
end Erdos1045.FaberFourier

namespace Erdos1045.EventualExact.ExplicitInitial

open Configuration HullGeometry ExteriorClassical ExteriorBoundary MatrixDefect GlobalProof
noncomputable section

/-- Initial Laurent energy budget. -/
def initialEnergy : ℝ := 18 * Real.pi * Real.log 4

/-- A radial scale sufficient for the proved Hölder constant 4. -/
def radiusScale : ℝ := max 1 (16 * (4 : ℝ) ^ 2 * initialEnergy)

def angleSeparation : ℝ := radiusScale / (32 * Real.exp radiusScale)

def samplingConstant : ℝ :=
  8 / min angleSeparation Real.pi + min angleSeparation Real.pi

def matrixErrorConstant : ℝ := matrixConstant samplingConstant radiusScale

def capacityConstant : ℝ := 16 * matrixErrorConstant * (18 * Real.pi)

def energyConstant : ℝ := 16 * matrixErrorConstant * (18 * Real.pi) ^ 2

def errorConstant : ℝ := matrixErrorConstant * energyConstant

/-- An arithmetic threshold sufficient for the complete coarse bootstrap. -/
def coarseThreshold : ℕ :=
  max 4 ⌈max (2 * Real.log 4) (4 * matrixErrorConstant * (18 * Real.pi))⌉₊

theorem radiusScale_pos : 0 < radiusScale :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem angleSeparation_pos : 0 < angleSeparation := by
  unfold angleSeparation
  exact div_pos radiusScale_pos (by positivity)

theorem samplingConstant_pos : 0 < samplingConstant := by
  have hδ := lt_min angleSeparation_pos Real.pi_pos
  unfold samplingConstant
  positivity

theorem matrixErrorConstant_nonneg : 0 ≤ matrixErrorConstant :=
  matrixConstant_nonneg samplingConstant_pos.le

theorem capacityConstant_nonneg : 0 ≤ capacityConstant := by
  unfold capacityConstant
  exact mul_nonneg (mul_nonneg (by norm_num) matrixErrorConstant_nonneg) (by positivity)

theorem energyConstant_nonneg : 0 ≤ energyConstant := by
  unfold energyConstant
  exact mul_nonneg (mul_nonneg (by norm_num) matrixErrorConstant_nonneg) (sq_nonneg _)

theorem errorConstant_nonneg : 0 ≤ errorConstant :=
  mul_nonneg matrixErrorConstant_nonneg energyConstant_nonneg

theorem coarseThreshold_conditions {n : ℕ} (hn : coarseThreshold ≤ n) :
    4 ≤ n ∧ 2 * Real.log 4 ≤ (n : ℝ) ∧
      4 * matrixErrorConstant * (18 * Real.pi) ≤ (n : ℝ) := by
  have h := (max_le_iff.mp hn).2
  have hr := Nat.ceil_le.mp h
  exact ⟨(max_le_iff.mp hn).1, (le_max_left _ _).trans hr, (le_max_right _ _).trans hr⟩

/-- The Laurent Hölder bound has the fixed constant 4 for every exterior model. -/
theorem holder_four {n : ℕ} {z : Points n} (d : ExteriorData z)
    (u v : ℂ) (hu : 1 ≤ ‖u‖) (hv : 1 ≤ ‖v‖) :
    ‖laurent d.coefficient u - laurent d.coefficient v‖ ≤
      4 * Real.sqrt d.energySquared * Real.sqrt ‖u - v‖ := by
  rw [d.parseval_identity]
  exact ClosedSeries.laurent_holder_bound d.coefficient d.sobolev u v hu hv

/-- Separation, sampling and matrix control at a specified finite dimension. -/
theorem initial_matrix_estimates {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hn : 4 ≤ n)
    (hinj : Function.Injective z) (hF : Fekete z)
    (hΔ : (n : ℝ) ^ n ≤ discriminant z) (hlarge : 2 * Real.log 4 ≤ (n : ℝ)) :
    (1 / 2 : ℝ) ≤ d.capacity ∧
      FaberFourier.H1Sampling (fun i : Fin n => d.angles.angle i) samplingConstant ∧
      frobSq d.errorMatrix ≤ matrixErrorConstant * (n : ℝ) ^ 2 * d.energySquared := by
  let B := classicalBackground_proved.toClassicalAnalysis
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hc := d.initial_capacity_half B.circle B.hadamard HF (by omega) hΔ hlarge
  have he : (n : ℝ) * d.energySquared ≤ initialEnergy :=
    d.initial_energy_bound B.circle B.hadamard HF (by omega) hΔ
  have hA : 16 * (4 : ℝ) ^ 2 * initialEnergy ≤ radiusScale := le_max_right _ _
  have hr : 1 < 1 + radiusScale / (n : ℝ) := by
    linarith [div_pos radiusScale_pos hnR]
  have hsep := d.separated HF B.level (by omega) hinj hF
    (by norm_num : (0 : ℝ) ≤ 4) radiusScale_pos hc he hA (holder_four d)
  have hs := FaberFourier.circle_sampling_explicit angleSeparation_pos hn0 _ hsep
  have hq := d.quotient_half hn0 radiusScale_pos he hA
    (fun i t => d.quotient_sq_bound (by norm_num : (0 : ℝ) ≤ 4) hc (holder_four d) hr i t)
  exact ⟨hc, hs, d.faber_error_bound HF B.series B.fourier B.moment
    hn0 radiusScale_pos samplingConstant_pos.le hc hs hq⟩

/-- Effective capacity, inverse-square energy, and unnormalized matrix-error bounds. -/
theorem coarse_bounds {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hn : coarseThreshold ≤ n)
    (hinj : Function.Injective z) (hF : Fekete z)
    (hΔ : (n : ℝ) ^ n ≤ discriminant z) :
    (1 / 2 : ℝ) ≤ d.capacity ∧
      FaberFourier.H1Sampling (fun i : Fin n => d.angles.angle i) samplingConstant ∧
      (n : ℝ) ^ 2 * (1 - d.capacity) ≤ capacityConstant ∧
      (n : ℝ) ^ 2 * d.energySquared ≤ energyConstant ∧
      frobSq d.errorMatrix ≤ errorConstant := by
  let B := classicalBackground_proved.toClassicalAnalysis
  obtain ⟨hn4, hncap, hnboot⟩ := coarseThreshold_conditions hn
  obtain ⟨hc, hs, hR⟩ := initial_matrix_estimates d HF hn4 hinj hF hΔ hncap
  have hb := d.bootstrap_bound B.circle B.matrix hn4 hΔ matrixErrorConstant_nonneg hR hnboot
  refine ⟨hc, hs, hb.1, hb.2, hR.trans ?_⟩
  have hm := mul_le_mul_of_nonneg_left hb.2 matrixErrorConstant_nonneg
  simpa only [energyConstant, errorConstant, mul_assoc] using hm

/-- An effective version of the energy conclusion used by the existing family API. -/
theorem inverse_square_energy {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hn : coarseThreshold ≤ n)
    (hinj : Function.Injective z) (hF : Fekete z)
    (hΔ : (n : ℝ) ^ n ≤ discriminant z) :
    (n : ℝ) ^ 2 * d.energySquared ≤ energyConstant :=
  (coarse_bounds d HF hn hinj hF hΔ).2.2.2.1

end
end Erdos1045.EventualExact.ExplicitInitial

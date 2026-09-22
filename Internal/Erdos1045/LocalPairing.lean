import Erdos1045.LocalCoercivity
import Mathlib.Tactic

/-!
# Summing all paired Fourier blocks, including fixed points

An involution is used on the whole frequency set. Dividing the sum of its
two-entry blocks by two handles both two-element orbits and self-paired modes.
The second complex entry is conjugated throughout.
-/

namespace Erdos1045.LocalPairing

open Complex
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem sum_involution (p : ι → ι) (hp : Function.Involutive p) (f : ι → ℝ) :
    (∑ i, f (p i)) = ∑ i, f i := by
  exact Equiv.sum_comp (Equiv.ofBijective p hp.bijective) f

def energyA (n : ℝ) (a : ι → ℝ) (x : ι → ℂ) : ℝ :=
  n / 2 * ∑ i, a i * normSq (x i)

def energyB (n : ℝ) (p : ι → ι) (x : ι → ℂ) : ℝ :=
  n / 2 * ((∑ i, normSq (x i)) + (∑ i, x i * x (p i)).re)

def quadratic (n : ℝ) (p : ι → ι) (r : ι → ℝ) (x : ι → ℂ) : ℝ :=
  n / 4 * ((n - 1) * (∑ i, normSq (x i)) +
    ∑ i, (n - 1 - 2 * r i) * (x i * x (p i)).re)

theorem quadratic_eq_cross_form (n : ℝ) (p : ι → ι) (r : ι → ℝ) (x : ι → ℂ) :
    quadratic n p r x =
      -n / 2 * (∑ i, r i * (x i * x (p i)).re) + (n - 1) / 2 * energyB n p x := by
  unfold quadratic energyB
  simp_rw [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  rw [Complex.re_sum]
  ring

theorem quadratic_eq_half_sum_blocks (n : ℝ) (p : ι → ι)
    (hp : Function.Involutive p) (r : ι → ℝ) (x : ι → ℂ) :
    quadratic n p r x =
      (∑ i, LocalCoercivity.blockEnergy n (r i) (x i) ((starRingEnd ℂ) (x (p i)))) / 2 := by
  have hi := sum_involution p hp (fun i => normSq (x i))
  have hterm (i : ι) : LocalCoercivity.blockEnergy n (r i) (x i)
      ((starRingEnd ℂ) (x (p i))) =
      n / 4 * ((n - 1) * (normSq (x i) + normSq (x (p i))) +
        2 * ((n - 1 - 2 * r i) * (x i * x (p i)).re)) := by
    simp [LocalCoercivity.blockEnergy, normSq_add, normSq_sub, normSq_conj]
    ring_nf
    simp
  simp_rw [hterm]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, hi]
  unfold quadratic
  ring

theorem energy_eq_half_sum_blocks (n : ℝ) (p : ι → ι)
    (hp : Function.Involutive p) (a : ι → ℝ) (x : ι → ℂ) :
    energyA n a x + n * energyB n p x =
      (∑ i, LocalCoercivity.weightedEnergy n (a i) (a (p i))
        (x i) ((starRingEnd ℂ) (x (p i)))) / 2 := by
  have hi := sum_involution p hp (fun i => normSq (x i))
  have ha := sum_involution p hp (fun i => a i * normSq (x i))
  have hterm (i : ι) : LocalCoercivity.weightedEnergy n (a i) (a (p i))
      (x i) ((starRingEnd ℂ) (x (p i))) =
      n / 2 * (a i * normSq (x i) + a (p i) * normSq (x (p i))) +
        n ^ 2 / 2 * (normSq (x i) + normSq (x (p i)) + 2 * (x i * x (p i)).re) := by
    simp [LocalCoercivity.weightedEnergy, normSq_add, normSq_conj]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hi, ha, ← Complex.re_sum]
  unfold energyA energyB
  ring

/-- Full spectral coercivity follows by summing the verified block inequality.
The coefficient bounds here are numerical hypotheses, proved for the actual
sine coefficients in `LocalTrigonometry`; they are not classical inputs. -/
theorem spectral_coercivity {n : ℝ} (hn : 4 ≤ n) (p : ι → ι)
    (hp : Function.Involutive p) (r a : ι → ℝ) (x : ι → ℂ)
    (hr : ∀ i, 0 ≤ r i) (hupper : ∀ i, r i ≤ (5 / 6 : ℝ) * (n - 1))
    (hsym : ∀ i, r (p i) = r i) (ha : ∀ i, a i ≤ 9 * r i) :
    (energyA n a x + n * energyB n p x) / 64 ≤ quadratic n p r x := by
  have hpoint (i : ι) :
      LocalCoercivity.weightedEnergy n (a i) (a (p i))
          (x i) ((starRingEnd ℂ) (x (p i))) / 64 ≤
        LocalCoercivity.blockEnergy n (r i) (x i) ((starRingEnd ℂ) (x (p i))) := by
    have hap : a (p i) ≤ 9 * r i := by simpa [hsym] using ha (p i)
    have hw := LocalCoercivity.weightedEnergy_le_control
      (show 0 ≤ n by linarith) (ha i) hap (x i) ((starRingEnd ℂ) (x (p i)))
    have hc := LocalCoercivity.blockEnergy_coercive hn (hr i) (hupper i)
      (x i) ((starRingEnd ℂ) (x (p i)))
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  rw [← Finset.sum_div] at hsum
  rw [energy_eq_half_sum_blocks n p hp a x, quadratic_eq_half_sum_blocks n p hp r x]
  linarith

/-- The isolated `k=2` mode is stronger than the general block estimate. -/
theorem isolated_mode_coercivity {n s q : ℝ} (hn : 3 ≤ n) (hs : 1 ≤ s)
    (hq : 0 ≤ q) :
    (n * (n - 2) * q + n ^ 2 / 2 * s ^ 2 * q) / 6 ≤
      n * (n - 1) / 4 * s ^ 2 * q := by
  have hs2 : 1 ≤ s ^ 2 := by nlinarith
  have hbase : 4 * (n - 2) ≤ (4 * n - 6) * s ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hbase (show 0 ≤ n * q by positivity)
  nlinarith

end

end Erdos1045.LocalPairing

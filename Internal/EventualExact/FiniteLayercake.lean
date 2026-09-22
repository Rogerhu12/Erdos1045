import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! A finite layer-cake argument, with ordinary bounded interval integrals. -/

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace Erdos1045.EventualExact.FiniteLayercake

theorem intervalIntegrable_indicator (f : ℝ → ℝ) {a b c : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable ((Iic c).indicator f) volume a b :=
  ⟨hf.1.indicator measurableSet_Iic, hf.2.indicator measurableSet_Iic⟩

theorem integral_linear_indicator {R a : ℝ} (ha : 0 ≤ a) (hR : a ≤ R) :
    (∫ t in (0 : ℝ)..R, (Iic a).indicator (fun t : ℝ => 2 * t) t) = a ^ 2 := by
  classical
  have he := intervalIntegral.integral_indicator (μ := volume) (f := fun t : ℝ => 2 * t)
    (show a ∈ Icc 0 R from ⟨ha, hR⟩)
  change (∫ t in (0 : ℝ)..R, (Iic a).indicator (fun t : ℝ => 2 * t) t) =
    ∫ t in (0 : ℝ)..a, 2 * t at he
  rw [he]
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

theorem integral_const_indicator {R a : ℝ} (ha : 0 ≤ a) (hR : a ≤ R) (b : ℝ) :
    (∫ t in (0 : ℝ)..R, (Iic a).indicator (fun _ : ℝ => b) t) = a * b := by
  classical
  have he := intervalIntegral.integral_indicator (μ := volume) (f := fun _ : ℝ => b)
    (show a ∈ Icc 0 R from ⟨ha, hR⟩)
  change (∫ t in (0 : ℝ)..R, (Iic a).indicator (fun _ : ℝ => b) t) =
    ∫ t in (0 : ℝ)..a, b at he
  rw [he, intervalIntegral.integral_const]
  simp

/-- Integrating a truncated weak estimate yields a strong square-sum estimate. -/
theorem square_sum_of_truncated_weak {ι : Type*} (S : Finset ι) (M f : ι → ℝ)
    (hM : ∀ i ∈ S, 0 ≤ M i) (hf : ∀ i ∈ S, 0 ≤ f i)
    (hweak : ∀ t : ℝ, 0 ≤ t →
      t * (S.filter (fun i => t ≤ M i)).card ≤ 4 * ∑ i ∈ S, if t ≤ 2 * f i then f i else 0) :
    (∑ i ∈ S, M i ^ 2) ≤ 16 * ∑ i ∈ S, f i ^ 2 := by
  classical
  let R := (∑ i ∈ S, (M i + 2 * f i)) + 1
  have hterm (i : ι) (hi : i ∈ S) : 0 ≤ M i + 2 * f i := by
    linarith [hM i hi, hf i hi]
  have hR : 0 ≤ R := by
    have hs := Finset.sum_nonneg hterm
    dsimp [R]
    linarith
  have hMR (i : ι) (hi : i ∈ S) : M i ≤ R := by
    have h := Finset.single_le_sum hterm hi
    dsimp [R]
    linarith [hf i hi]
  have hfR (i : ι) (hi : i ∈ S) : 2 * f i ≤ R := by
    have h := Finset.single_le_sum hterm hi
    dsimp [R]
    linarith [hM i hi]
  let L (t : ℝ) := ∑ i ∈ S, (Iic (M i)).indicator (fun t : ℝ => 2 * t) t
  let G (t : ℝ) := 8 * ∑ i ∈ S, (Iic (2 * f i)).indicator (fun _ : ℝ => f i) t
  have hLi (i : ι) : IntervalIntegrable ((Iic (M i)).indicator (fun t : ℝ => 2 * t)) volume 0 R :=
    intervalIntegrable_indicator _ ((show Continuous (fun t : ℝ => 2 * t) by fun_prop).intervalIntegrable 0 R)
  have hGi (i : ι) : IntervalIntegrable ((Iic (2 * f i)).indicator (fun _ : ℝ => f i)) volume 0 R :=
    intervalIntegrable_indicator _ (continuous_const.intervalIntegrable 0 R)
  have hL : IntervalIntegrable L volume 0 R := by
    have he : L = ∑ i ∈ S, (Iic (M i)).indicator (fun t : ℝ => 2 * t) := by
      funext t
      simp only [L, Finset.sum_apply]
    rw [he]
    exact IntervalIntegrable.sum S (fun i _ => hLi i)
  have hG : IntervalIntegrable G volume 0 R := by
    simpa only [G, Finset.sum_apply] using (IntervalIntegrable.sum S (fun i _ => hGi i)).const_mul 8
  have hpoint (t : ℝ) (ht : t ∈ Icc 0 R) : L t ≤ G t := by
    have hw := hweak t ht.1
    have hLe : L t = 2 * (t * (S.filter (fun i => t ≤ M i)).card) := by
      dsimp [L]
      simp only [Set.indicator_apply, Set.mem_Iic]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    have hGe : G t = 8 * ∑ i ∈ S, if t ≤ 2 * f i then f i else 0 := by
      simp only [G, Set.indicator_apply, Set.mem_Iic]
    rw [hLe, hGe]
    linarith
  have hi := intervalIntegral.integral_mono_on hR hL hG hpoint
  have hLint : (∫ t in (0 : ℝ)..R, L t) = ∑ i ∈ S, M i ^ 2 := by
    rw [show L = (fun t => ∑ i ∈ S, (Iic (M i)).indicator (fun t : ℝ => 2 * t) t) from rfl,
      intervalIntegral.integral_finsetSum (fun i _ => hLi i)]
    exact Finset.sum_congr rfl (fun i hi => integral_linear_indicator (hM i hi) (hMR i hi))
  have hGint : (∫ t in (0 : ℝ)..R, G t) = 16 * ∑ i ∈ S, f i ^ 2 := by
    rw [show G = (fun t => 8 * ∑ i ∈ S,
      (Iic (2 * f i)).indicator (fun _ : ℝ => f i) t) from rfl,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun i _ => hGi i)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_indicator (by linarith [hf i hi] : 0 ≤ 2 * f i) (hfR i hi)]
    ring
  rwa [hLint, hGint] at hi

end Erdos1045.EventualExact.FiniteLayercake

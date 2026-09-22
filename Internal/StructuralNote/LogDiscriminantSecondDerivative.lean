import EventualExact.AngularObjectiveCurvature
import EventualExact.LogDiscriminantGradient

/-! The exact second derivative of the original logarithmic discriminant
along an arbitrary twice differentiable collision-free configuration path. -/

namespace StructuralNote.LogDiscriminantSecondDerivative

open Erdos1045 Erdos1045.EventualExact Complex Configuration Filter
open scoped BigOperators Topology ComplexConjugate
noncomputable section

def first {n : ℕ} (z v : Fin n → ℂ) : ℝ :=
  ∑ i, ∑ j, ((v i - v j) / (z i - z j)).re

def second {n : ℕ} (z v a : Fin n → ℂ) : ℝ :=
  ∑ i, ∑ j, ((a i - a j) / (z i - z j) - ((v i - v j) / (z i - z j)) ^ 2).re

theorem eventually_injective {n : ℕ} {z : ℝ → Fin n → ℂ} {x : ℝ}
    (hc : ∀ j, ContinuousAt (fun s => z s j) x) (hi : Function.Injective (z x)) :
    ∀ᶠ s in 𝓝 x, Function.Injective (z s) := by
  have hp (i j : Fin n) : ∀ᶠ s in 𝓝 x, i ≠ j → z s i ≠ z s j := by
    by_cases hij : i = j
    · exact Eventually.of_forall (by simp [hij])
    · have hn := ((hc i).sub (hc j)).eventually_ne (sub_ne_zero.mpr (hi.ne hij))
      filter_upwards [hn] with s hs
      exact fun _ => sub_ne_zero.mp hs
  have hall := Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j => hp i j))
  filter_upwards [hall] with s hs
  intro i j hij
  by_contra hne
  exact hs i j hne hij

theorem log_norm_hasDerivAt {f : ℝ → ℂ} {v : ℂ} {x : ℝ}
    (hf : HasDerivAt f v x) (hne : f x ≠ 0) :
    HasDerivAt (fun s => Real.log ‖f s‖) (v / f x).re x := by
  have hd := (AngularObjectiveCurvature.log_norm_sq_hasDerivAt hf hne).div_const 2
  simpa only [Real.log_pow, Nat.cast_ofNat, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hd

theorem log_hasDerivAt {n : ℕ} {z : ℝ → Fin n → ℂ} {v : Fin n → ℂ} {x : ℝ}
    (hz : ∀ j, HasDerivAt (fun s => z s j) (v j) x) (hi : Function.Injective (z x)) :
    HasDerivAt (fun s => Real.log (discriminant (z s))) (first (z x) v) x := by
  have hdj (i j : Fin n) : HasDerivAt (fun s => Real.log ‖z s i - z s j‖)
      ((v i - v j) / (z x i - z x j)).re x := by
    by_cases hij : i = j
    · subst j
      simpa only [sub_self, zero_div, zero_re, norm_zero, Real.log_zero] using hasDerivAt_const x (0 : ℝ)
    · exact log_norm_hasDerivAt ((hz i).sub (hz j)) (sub_ne_zero.mpr (hi.ne hij))
  have hd := HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    HasDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hdj i j))
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_injective (fun j => (hz j).continuousAt) hi] with s hs
  exact LocalConfiguration.logDiscriminant_eq_sum (z s) hs

theorem first_hasDerivAt {n : ℕ} {z v : ℝ → Fin n → ℂ} {a : Fin n → ℂ} {x : ℝ}
    (hz : ∀ j, HasDerivAt (fun s => z s j) (v x j) x)
    (hv : ∀ j, HasDerivAt (fun s => v s j) (a j) x) (hi : Function.Injective (z x)) :
    HasDerivAt (fun s => first (z s) (v s)) (second (z x) (v x) a) x := by
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  by_cases hij : i = j
  · subst j
    simpa only [sub_self, zero_div, zero_pow (by norm_num : 2 ≠ 0), zero_re] using
      hasDerivAt_const x (0 : ℝ)
  · have hne := sub_ne_zero.mpr (hi.ne hij)
    have hd := ((hv i).sub (hv j)).div ((hz i).sub (hz j)) hne
    apply (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd).congr_deriv
    change (((a i - a j) * (z x i - z x j) - (v x i - v x j) * (v x i - v x j)) /
      (z x i - z x j) ^ 2).re =
        ((a i - a j) / (z x i - z x j) - ((v x i - v x j) / (z x i - z x j)) ^ 2).re
    congr 1
    field_simp [hne]

/-- This is the derivative of the actual first derivative, not merely a formal
quadratic expression. The acceleration term is retained. -/
theorem log_second_derivative {n : ℕ} {z v : ℝ → Fin n → ℂ} {a : Fin n → ℂ} {x : ℝ}
    (hz : ∀ᶠ s in 𝓝 x, ∀ j, HasDerivAt (fun r => z r j) (v s j) s)
    (hv : ∀ j, HasDerivAt (fun s => v s j) (a j) x) (hi : Function.Injective (z x)) :
    HasDerivAt (deriv (fun s => Real.log (discriminant (z s)))) (second (z x) (v x) a) x := by
  have hx := hz.self_of_nhds
  apply (first_hasDerivAt hx hv hi).congr_of_eventuallyEq
  filter_upwards [hz, eventually_injective (fun j => (hx j).continuousAt) hi] with s hs hsi
  exact (log_hasDerivAt hs hsi).deriv

end
end StructuralNote.LogDiscriminantSecondDerivative

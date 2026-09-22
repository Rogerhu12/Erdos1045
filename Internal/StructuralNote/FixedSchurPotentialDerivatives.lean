import StructuralNote.FixedSchurConfigurationDerivatives
import EventualExact.QuadraticStability

/-! The actual second derivative of the free pair potential on an affine path. -/

namespace StructuralNote.FixedSchurPotentialDerivatives

open Complex Filter Erdos1045 Erdos1045.EventualExact SchurSpectrum QuadraticStability
open FixedSchurChosenPath FixedSchurConfigurationDerivatives
open scoped BigOperators Topology

noncomputable section

theorem ratio_hasDerivAt {n : ℕ} (hn : 0 < n)
    {c : ℝ → Fin n → ℂ} {v : Fin n → ℂ} {t : ℝ}
    (hc : ∀ j, HasDerivAt (fun r => c r j) (v j) t) (k : ℕ × ℕ) :
    HasDerivAt (fun r => ratio hn (c r) k) (ratio hn v k) t := by
  unfold ratio LocalDFT.pairRatio periodize
  exact ((hc _).sub (hc _)).div_const _

theorem potential_hasDerivAt {n : ℕ} (hn : 0 < n)
    {c : ℝ → Fin n → ℂ} {v : Fin n → ℂ} {t : ℝ}
    (hc : ∀ j, HasDerivAt (fun r => c r j) (v j) t) :
    HasDerivAt (fun r => pairPotential hn (c r))
      (-(∑ k ∈ pairs n, (ratio hn (c t) k * ratio hn v k).re)) t := by
  have hd (k : ℕ × ℕ) := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    ((ratio_hasDerivAt hn hc k).pow 2)
  have hs := (HasDerivAt.fun_sum (fun k (_ : k ∈ pairs n) => hd k)).neg.div_const 2
  simp only [pairPotential_sum]
  apply hs.congr_deriv
  have he (a b : ℂ) : ((2 : ℂ) * a ^ (2 - 1) * b).re = 2 * (a * b).re := by
    norm_num [Complex.mul_re]
    ring
  simp only [Complex.reCLM_apply, Nat.cast_ofNat, he, ← Finset.mul_sum]
  ring

theorem affine_potential_second {m : ℕ} (hm : 0 < m)
    (θ η : Fin (2 * m) → ℝ) (v h : Fin (2 * m) → ℂ) :
    HasDerivAt (deriv (fun t => pairPotential (by omega)
      (chosenParameterPath θ η v h t).2)) (2 * pairPotential (by omega) h) 0 := by
  have hd (k : ℕ × ℕ) := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((ratio_hasDerivAt (by omega) (parameter_center_hasDerivAt θ η v h · 0) k).mul_const
      (ratio (by omega) h k))
  have hs := (HasDerivAt.fun_sum (fun k (_ : k ∈ pairs (2 * m)) => hd k)).neg
  have he : -(∑ k ∈ pairs (2 * m), (ratio (by omega) h k * ratio (by omega) h k).re) =
      2 * pairPotential (by omega) h := by
    rw [pairPotential_sum]
    simp only [pow_two]
    ring
  simp only [Complex.reCLM_apply] at hs
  rw [he] at hs
  apply hs.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t =>
    (potential_hasDerivAt (by omega) (parameter_center_hasDerivAt θ η v h · t)).deriv)

end
end StructuralNote.FixedSchurPotentialDerivatives

import Erdos1045.KernelFourier
import Erdos1045.ClosedOrthogonality

/-! Elementary Fourier identities are proved here, not retained as inputs. -/

namespace Erdos1045.KernelWeights

open scoped BigOperators
noncomputable section

theorem circlePowerSum_gram (n : ℕ) (θ : ℕ → ℝ) (k : ℕ) :
    ‖circlePowerSum n θ k‖ ^ 2 =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        Real.cos ((k : ℝ) * (θ i - θ j)) := by
  have hn (z : ℂ) : ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hn]
  unfold circlePowerSum
  simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]
  rw [← Complex.exp_add]
  have harg : -((((k : ℝ) * θ i : ℝ) : ℂ) * Complex.I) +
      (((k : ℝ) * θ j : ℝ) : ℂ) * Complex.I =
      ((-((k : ℝ) * (θ i - θ j)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]

theorem grid_cos_sum {n : ℕ} (H : LocalFourier.ClassicalOrthogonality n
    (LocalPhase.regularRoot n)) (k : ℕ) :
    (∑ j ∈ Finset.range n, Real.cos ((k : ℝ) * (2 * Real.pi * j / n))) =
      if n ∣ k then (n : ℝ) else 0 := by
  have hp (j : ℕ) : LocalPhase.regularRoot n ^ (j * k) =
      Complex.exp ((((k : ℝ) * (2 * Real.pi * j / n) : ℝ) : ℂ) * Complex.I) := by
    unfold LocalPhase.regularRoot
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h := congrArg Complex.re (H.sum_pow k)
  simp only [Complex.re_sum, hp, Complex.exp_ofReal_mul_I_re] at h
  simpa only [apply_ite, Complex.natCast_re, Complex.zero_re] using h

theorem cosine_sampling_of_orthogonality {n : ℕ} (hn : 0 < n)
    (H : LocalFourier.ClassicalOrthogonality n (LocalPhase.regularRoot n))
    (a : ℕ → ℝ) (ha : Summable a) :
    ((∑ j ∈ Finset.range n, ∑' k, a k * Real.cos ((k : ℝ) * (2 * Real.pi * j / n))) / n) =
      ∑' q, a (q * n) := by
  have hs (j : ℕ) : Summable (fun k =>
      a k * Real.cos ((k : ℝ) * (2 * Real.pi * j / n))) :=
    summable_mul_cos ha.abs _
  rw [← Summable.tsum_finsetSum (fun j _ => hs j), ← tsum_div_const]
  simp_rw [← Finset.mul_sum, grid_cos_sum H]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    (∑' k, (a k * if n ∣ k then (n : ℝ) else 0) / n) =
        ∑' k, if n ∣ k then a k else 0 := by
      apply tsum_congr
      intro k
      split_ifs <;> simp [hn0]
    _ = ∑' q, a (q * n) := by
      have hinj : Function.Injective (fun q : ℕ => q * n) :=
        fun _ _ h => Nat.eq_of_mul_eq_mul_right hn h
      have hsupport : Function.support (fun k => if n ∣ k then a k else 0) ⊆
          Set.range (fun q : ℕ => q * n) := by
        intro k hk
        have hd : n ∣ k := by
          by_contra h
          exact hk (by simp [h])
        obtain ⟨q, rfl⟩ := hd
        exact ⟨q, Nat.mul_comm _ _⟩
      simpa using (hinj.tsum_eq hsupport).symm

/-- Both generic cosine Fourier formulas now follow from proved identities. -/
theorem classicalCosineFourier : ClassicalCosineFourier where
  gram := circlePowerSum_gram
  sampling := fun n hn a ha =>
    cosine_sampling_of_orthogonality hn (ClosedFourier.orthogonality n hn) a ha

end
end Erdos1045.KernelWeights

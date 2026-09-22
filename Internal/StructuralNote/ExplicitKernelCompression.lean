import StructuralNote.ExplicitKernelRateIdentification
import StructuralNote.FiniteCompressionBackgroundUniform
import StructuralNote.FiniteCompressionGeometric

/-! Explicit finite-compression consequences of the quantitative kernel signs. -/

namespace StructuralNote.ExplicitKernelCompression

open Real Set Finset Erdos1045.EventualExact FourierMultiplier FiniteBox
open ExplicitKernelRateIdentification
open FixedDualClassificationKernelSignsPropagation FixedDualClassificationKernelSignsFinal
open FiniteCompressionKernelGeometry FiniteCompressionBackgroundUniform
open FiniteCompressionConvolutionBase FiniteCompressionArcPartition
open FiniteCompressionRanked FiniteCompressionEnergy
open FixedDualClassificationFinite
open scoped BigOperators
noncomputable section

/-- The complete kernel geometry interface with the concrete margin `1/50`. -/
theorem explicit_kernelAt_geometry :
    ∀ m ≥ compressionKernelSignsThreshold,
      (∀ j L R : ℕ, j ≤ L → L ≤ R →
        Real.pi / 4 ≤ compressionAngle m (L - j) →
        compressionAngle m (R - j) ≤ 5 * Real.pi / 12 →
        MonotoneOn (kernelAt m j) (Set.Icc L R) ∧
          kernelAt m j R ≤ -(1 : ℝ) / 50) ∧
      (∀ j L R : ℕ, L ≤ R → R ≤ j + m →
        Real.pi / 4 ≤ compressionAngle m (j + m - R) →
        compressionAngle m (j + m - L) ≤ 5 * Real.pi / 12 →
        MonotoneOn (kernelAt m j) (Set.Icc L R) ∧
          (1 : ℝ) / 50 ≤ kernelAt m j L) ∧
      (∀ j s : ℕ, s ≤ j → compressionAngle m (j - s) ≤ Real.pi / 12 →
        0 ≤ kernelAt m j s) := by
  intro m hm
  have hsign := explicit_compressionKernelSigns m hm
  have hmargin := explicit_cross_negative_margin m hm
  constructor
  · intro j L R hjL hLR hL hR
    refine ⟨cross_monotone_on hsign hjL hLR hL hR, ?_⟩
    rw [kernelAt_eq_gridKernel_of_le' (hjL.trans hLR)]
    apply hmargin (R - j)
    · exact hL.trans (angle_mono (Nat.sub_le_sub_right hLR j))
    · exact hR
  constructor
  · intro j L R hLR hRj hR hL
    refine ⟨reflected_cross_monotone_on hsign hLR hRj hR hL, ?_⟩
    have hLj : L ≤ j + m := hLR.trans hRj
    rw [kernelAt_eq_neg_gridKernel_of_le_add hLj]
    have hmarg := hmargin (j + m - L)
      (hR.trans (angle_mono (by omega : j + m - R ≤ j + m - L))) hL
    linarith
  · intro j s hsj hangle
    exact left_near_nonneg hsign hsj hangle

/-- The half-circle background drops by the concrete amount `4/25 /(2m)`. -/
theorem explicit_background_drop :
    ∀ m ≥ compressionKernelSignsThreshold, ∀ (hm : 0 < m)
      (b : Fin (2 * m) → ℝ), b ∈ Q hm → ∀ j : ℕ, BackgroundArcs hm b j →
      (4 / 25 : ℝ) / (2 * m : ℕ) ≤ operator (2 * m) b (site hm j) -
        operator (2 * m) b (site hm (j + 1)) := by
  intro m hmThreshold hm b hb j arcs
  have hkernel := explicit_kernelAt_geometry m hmThreshold
  have hforward := hkernel.1 j arcs.left₁ arcs.right₁ arcs.site_le_first
    arcs.first_nonempty arcs.first_angle_lo arcs.first_angle_hi
  have hbackward := hkernel.2.1 j arcs.left₂ arcs.right₂ arcs.second_nonempty
    arcs.second_le_antipode arcs.second_angle_lo arcs.second_angle_hi
  have hnear := hkernel.2.2 j arcs.jump arcs.jump_le_site arcs.near_angle
  have hfmargin : kernelAt m j arcs.right₁ ≤ -((1 : ℝ) / 50) := by
    linarith [hforward.2]
  have hA := amplitude_ge_one (show 2 ≤ 2 * m by omega)
  have hg := operator_step_le (δ := (1 : ℝ) / 50) hm b hb.1
    (by linarith : 0 ≤ amplitude (2 * m)) hb.2
    arcs.start_le arcs.jump_lt arcs.first_nonempty arcs.separated arcs.second_nonempty
    arcs.last_lt arcs.outside arcs.jump_left arcs.jump_right arcs.first_left arcs.first_right
    arcs.second_left arcs.second_right hnear hforward.1 hbackward.1 hfmargin
    ((by norm_num : (0 : ℝ) ≤ 1 / 50).trans hbackward.2)
  have hscale : (4 / 25 : ℝ) / (2 * m : ℕ) ≤
      8 * amplitude (2 * m) * (1 / 50 : ℝ) / (2 * m : ℕ) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hA (by norm_num : (0 : ℝ) ≤ 1 / 50)]
  linarith

theorem explicit_background_predecessor_drop :
    ∀ m ≥ compressionKernelSignsThreshold, ∀ (hm : 0 < m)
      (b : Fin (2 * m) → ℝ), b ∈ Q hm → ∀ k : ℕ, 0 < k →
      BackgroundArcs hm b (k - 1) →
      (4 / 25 : ℝ) / (2 * m : ℕ) ≤
        operator (2 * m) b (site hm (k - 1)) - operator (2 * m) b (site hm k) := by
  intro m hmThreshold hm b hb k hk arcs
  simpa only [Nat.sub_add_cancel hk] using
    explicit_background_drop m hmThreshold hm b hb (k - 1) arcs

/-- The self-kernel is antitone on every admissible near arc at the same cutoff. -/
theorem explicit_near_antitone :
    ∀ m ≥ compressionKernelSignsThreshold, ∀ N : ℕ,
      2 * Real.pi * N / (2 * m : ℝ) ≤ Real.pi / 12 →
      AntitoneOn (FiniteCompressionRanked.gridKernel (2 * m)) (Set.Icc 1 N) := by
  intro m hm N hN i hi j hj hij
  rw [FiniteCompressionGeometric.gridKernel_eq,
    FiniteCompressionGeometric.gridKernel_eq]
  apply near_antitone (explicit_compressionKernelSigns m hm) hij
  have hangle : (j : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤
      (N : ℝ) * (2 * Real.pi / (2 * m : ℕ)) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hj.2) (by positivity)
  have he : (N : ℝ) * (2 * Real.pi / (2 * m : ℕ)) =
      2 * Real.pi * N / (2 * m : ℝ) := by push_cast; ring
  rw [he] at hangle
  exact hangle.trans hN

end
end StructuralNote.ExplicitKernelCompression

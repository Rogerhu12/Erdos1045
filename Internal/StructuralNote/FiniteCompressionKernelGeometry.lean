import StructuralNote.FiniteCompressionConvolutionBase
import StructuralNote.FixedDualClassificationKernelSignsFinal
import StructuralNote.FiniteCompressionGeometric

/-! Natural-coordinate geometry of the actual finite compression kernel.

The sign and margin statements for `gridKernel` are proved in the fixed-dual
coordinates.  This file transports them to `kernelAt`, where the coordinates
are the natural site indices used by the convolution argument.
-/

namespace StructuralNote.FiniteCompressionKernelGeometry

open Real Filter Set Erdos1045.EventualExact FourierMultiplier
open FiniteCompressionConvolutionBase
open FixedDualClassificationKernel
open FixedDualClassificationKernelSignsPropagation
open FixedDualClassificationKernelSignsFinal
open scoped Topology
noncomputable section

def compressionAngle (m r : ℕ) : ℝ :=
  (r : ℝ) * (2 * Real.pi / (2 * m : ℕ))

theorem angle_mono {m r s : ℕ} (hrs : r ≤ s) :
    compressionAngle m r ≤ compressionAngle m s := by
  unfold compressionAngle
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hrs) (by positivity)

theorem kernelAt_eq_gridKernel_of_le {m j s : ℕ} (hsj : s ≤ j) :
    kernelAt m j s = gridKernel m (j - s) := by
  unfold kernelAt FixedDualClassificationKernelSignsPropagation.gridKernel
  rw [Nat.cast_sub hsj]
  congr 1
  push_cast
  ring

theorem kernelAt_eq_gridKernel_of_le' {m j s : ℕ} (hjs : j ≤ s) :
    kernelAt m j s = gridKernel m (s - j) := by
  unfold kernelAt FixedDualClassificationKernelSignsPropagation.gridKernel
  rw [show ((j : ℝ) - s) = -((s - j : ℕ) : ℝ) by
    rw [Nat.cast_sub hjs]
    ring]
  rw [show 2 * Real.pi * (-((s - j : ℕ) : ℝ)) / (2 * m : ℕ) =
      -(((s - j : ℕ) : ℝ) * (2 * Real.pi / (2 * m : ℕ))) by
    ring, FixedDualClassificationKernel.finiteKernel_even]

theorem kernelAt_eq_neg_gridKernel_of_le_add {m j s : ℕ} (hs : s ≤ j + m) :
    kernelAt m j s = -gridKernel m (j + m - s) := by
  by_cases hm : m = 0
  · subst m
    simp [kernelAt, FixedDualClassificationKernelSignsPropagation.gridKernel,
      FixedDualClassificationKernel.finiteKernel]
  unfold kernelAt FixedDualClassificationKernelSignsPropagation.gridKernel
  have hsub : (j : ℝ) - s = ((j + m - s : ℕ) : ℝ) - m := by
    rw [Nat.cast_sub hs, Nat.cast_add]
    ring
  rw [hsub]
  have hangle :
      2 * Real.pi * (((j + m - s : ℕ) : ℝ) - m) / (2 * m : ℕ) =
        ((j + m - s : ℕ) : ℝ) * (2 * Real.pi / (2 * m : ℕ)) - Real.pi := by
    push_cast
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.pos_of_ne_zero hm))
    field_simp [hmR]
  rw [hangle, finiteKernel_sub_pi]

theorem cross_le {m r s : ℕ} (h : CompressionKernelSigns m) (hrs : r ≤ s)
    (hr : Real.pi / 4 ≤ compressionAngle m r)
    (hs : compressionAngle m s ≤ 5 * Real.pi / 12) :
    gridKernel m r ≤ gridKernel m s := by
  revert hs
  induction s, hrs using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ s hrs ih =>
      intro hs
      have hrs_angle : compressionAngle m r ≤ compressionAngle m s := angle_mono hrs
      have hlow : Real.pi / 4 ≤ compressionAngle m s := hr.trans hrs_angle
      have hstep := h.2.2.2 s hlow hs
      have hpred : compressionAngle m s ≤ compressionAngle m (s + 1) := angle_mono (by omega)
      exact (ih (hpred.trans hs)).trans hstep.le

theorem cross_monotone_on {m j L R : ℕ} (h : CompressionKernelSigns m)
    (hjL : j ≤ L) (_hLR : L ≤ R)
    (hL : Real.pi / 4 ≤ compressionAngle m (L - j))
    (hR : compressionAngle m (R - j) ≤ 5 * Real.pi / 12) :
    MonotoneOn (kernelAt m j) (Set.Icc L R) := by
  intro x hx y hy hxy
  have hjx : j ≤ x := hjL.trans hx.1
  have hjy : j ≤ y := hjL.trans hy.1
  rw [kernelAt_eq_gridKernel_of_le' hjx,
    kernelAt_eq_gridKernel_of_le' hjy]
  apply cross_le h (by omega)
  · exact hL.trans (angle_mono (Nat.sub_le_sub_right hx.1 j))
  · exact (angle_mono (Nat.sub_le_sub_right hy.2 j)).trans hR

theorem reflected_cross_monotone_on {m j L R : ℕ} (h : CompressionKernelSigns m)
    (_hLR : L ≤ R) (hRj : R ≤ j + m)
    (hR : Real.pi / 4 ≤ compressionAngle m (j + m - R))
    (hL : compressionAngle m (j + m - L) ≤ 5 * Real.pi / 12) :
    MonotoneOn (kernelAt m j) (Set.Icc L R) := by
  intro x hx y hy hxy
  have hxL : L ≤ x := hx.1
  have hxR : x ≤ R := hx.2
  have hyR : y ≤ R := hy.2
  have hxj : x ≤ j + m := hxR.trans hRj
  have hyv : y ≤ j + m := hyR.trans hRj
  rw [kernelAt_eq_neg_gridKernel_of_le_add hxj,
    kernelAt_eq_neg_gridKernel_of_le_add hyv]
  apply neg_le_neg
  apply cross_le h (by omega)
  · exact hR.trans (angle_mono (by omega : j + m - R ≤ j + m - y))
  · exact (angle_mono (by omega : j + m - x ≤ j + m - L)).trans hL

theorem left_near_nonneg {m j s : ℕ} (h : CompressionKernelSigns m)
    (hsj : s ≤ j) (hangle : compressionAngle m (j - s) ≤ Real.pi / 12) :
    0 ≤ kernelAt m j s := by
  rw [kernelAt_eq_gridKernel_of_le hsj]
  exact (h.1 (j - s) hangle).le

theorem eventually_forward_kernelAt_geometry : ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ m : ℕ in atTop, ∀ j L R : ℕ, j ≤ L → L ≤ R →
      Real.pi / 4 ≤ compressionAngle m (L - j) →
      compressionAngle m (R - j) ≤ 5 * Real.pi / 12 →
      MonotoneOn (kernelAt m j) (Set.Icc L R) ∧
        kernelAt m j R ≤ -δ := by
  obtain ⟨δ, hδ, hmargin⟩ := eventually_cross_negative_margin
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [eventually_compressionKernelSigns, hmargin] with m hsign hmargin
  intro j L R hjL hLR hL hR
  have hmono : MonotoneOn (kernelAt m j) (Set.Icc L R) := by
    intro x hx y hy hxy
    have hjx : j ≤ x := hjL.trans hx.1
    have hjy : j ≤ y := hjL.trans hy.1
    rw [kernelAt_eq_gridKernel_of_le' hjx,
      kernelAt_eq_gridKernel_of_le' hjy]
    apply cross_le hsign (by omega)
    · exact hL.trans (angle_mono (Nat.sub_le_sub_right hx.1 j))
    · exact (angle_mono (Nat.sub_le_sub_right hy.2 j)).trans hR
  constructor
  · exact hmono
  · rw [kernelAt_eq_gridKernel_of_le' (hjL.trans hLR)]
    apply hmargin (R - j)
    · change Real.pi / 4 ≤ compressionAngle m (R - j)
      exact hL.trans (angle_mono (Nat.sub_le_sub_right hLR j))
    · change compressionAngle m (R - j) ≤ 5 * Real.pi / 12
      exact hR

theorem eventually_backward_kernelAt_geometry : ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ m : ℕ in atTop, ∀ j L R : ℕ, L ≤ R → R ≤ j + m →
      Real.pi / 4 ≤ compressionAngle m (j + m - R) →
      compressionAngle m (j + m - L) ≤ 5 * Real.pi / 12 →
      MonotoneOn (kernelAt m j) (Set.Icc L R) ∧
        δ ≤ kernelAt m j L := by
  obtain ⟨δ, hδ, hmargin⟩ := eventually_cross_negative_margin
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [eventually_compressionKernelSigns, hmargin] with m hsign hmargin
  intro j L R hLR hRj hR hL
  have hmono : MonotoneOn (kernelAt m j) (Set.Icc L R) := by
    intro x hx y hy hxy
    have hxL : L ≤ x := hx.1
    have hxR : x ≤ R := hx.2
    have hyR : y ≤ R := hy.2
    have hxj : x ≤ j + m := hxR.trans hRj
    have hyv : y ≤ j + m := hyR.trans hRj
    rw [kernelAt_eq_neg_gridKernel_of_le_add hxj,
      kernelAt_eq_neg_gridKernel_of_le_add hyv]
    apply neg_le_neg
    apply cross_le hsign (by omega)
    · exact hR.trans (angle_mono (by omega : j + m - R ≤ j + m - y))
    · exact (angle_mono (by omega : j + m - x ≤ j + m - L)).trans hL
  constructor
  · exact hmono
  · have hLj : L ≤ j + m := by omega
    rw [kernelAt_eq_neg_gridKernel_of_le_add hLj]
    have hmarg := hmargin (j + m - L)
      (by
        change Real.pi / 4 ≤ compressionAngle m (j + m - L)
        exact hR.trans (angle_mono (by omega : j + m - R ≤ j + m - L)))
      (by
        change compressionAngle m (j + m - L) ≤ 5 * Real.pi / 12
        exact hL)
    linarith

theorem eventually_near_kernelAt_nonneg :
    ∀ᶠ m : ℕ in atTop, ∀ j s : ℕ, s ≤ j →
      compressionAngle m (j - s) ≤ Real.pi / 12 → 0 ≤ kernelAt m j s := by
  filter_upwards [eventually_compressionKernelSigns] with m hsign
  intro j s hsj hangle
  rw [kernelAt_eq_gridKernel_of_le hsj]
  exact (hsign.1 (j - s) hangle).le

theorem eventually_kernelAt_geometry : ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ m : ℕ in atTop,
      (∀ j L R : ℕ, j ≤ L → L ≤ R →
        Real.pi / 4 ≤ compressionAngle m (L - j) →
        compressionAngle m (R - j) ≤ 5 * Real.pi / 12 →
        MonotoneOn (kernelAt m j) (Set.Icc L R) ∧
          kernelAt m j R ≤ -δ) ∧
      (∀ j L R : ℕ, L ≤ R → R ≤ j + m →
        Real.pi / 4 ≤ compressionAngle m (j + m - R) →
        compressionAngle m (j + m - L) ≤ 5 * Real.pi / 12 →
        MonotoneOn (kernelAt m j) (Set.Icc L R) ∧
          δ ≤ kernelAt m j L) ∧
      (∀ j s : ℕ, s ≤ j → compressionAngle m (j - s) ≤ Real.pi / 12 →
        0 ≤ kernelAt m j s) := by
  obtain ⟨δ, hδ, hforward⟩ := eventually_forward_kernelAt_geometry
  obtain ⟨δ', hδ', hbackward⟩ := eventually_backward_kernelAt_geometry
  have hδcommon : 0 < min δ δ' := lt_min hδ hδ'
  refine ⟨min δ δ', hδcommon, ?_⟩
  filter_upwards [hforward, hbackward, eventually_near_kernelAt_nonneg] with m hf hb hp
  constructor
  · intro j L R hjL hLR hL hR
    have h := hf j L R hjL hLR hL hR
    constructor
    · exact h.1
    · exact h.2.trans (by linarith [min_le_left δ δ'])
  constructor
  · intro j L R hLR hRj hR hL
    have h := hb j L R hLR hRj hR hL
    constructor
    · exact h.1
    · exact (min_le_right δ δ').trans h.2
  · exact hp

end
end StructuralNote.FiniteCompressionKernelGeometry

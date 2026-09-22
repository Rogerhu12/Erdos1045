import StructuralNote.CommonFiberNormalAverage
import StructuralNote.CommonFiberInnerReconstruction
import StructuralNote.MatchingActivityRadialProjection

/-! The exact half-circle pairing of the actual normal error, with its
weighted absolute-average bound. -/

namespace StructuralNote.CommonFiberNormalPairing

open Erdos1045.EventualExact FourierMultiplier SchurLift SchurSpectrum LensClosure Filter
open CommonClosureEnergy CommonTangentialParameters CommonFiberDifferentialEstimate
open CommonFiberGeometry CommonFiberSmooth CommonFiberCanonical CommonFiberInnerReconstruction
open CommonFiberNormalProjectionScaled CommonFiberNormalAverage
open scoped BigOperators Topology
noncomputable section

theorem antiperiodic_pairing_average {m : ℕ} (hm : 0 < m) (g q : Fin (2 * m) → ℝ)
    (hg : FiniteBox.Antiperiodic hm g) (hq : FiniteBox.Antiperiodic hm q) :
    finitePairing g q / (2 * m : ℝ) =
      average (fun j : Fin m => g (halfIndex j) * q (halfIndex j)) := by
  have hs := MatchingActivityRadialProjection.real_half_sum hm (fun j => g j * q j)
    (fun j => by rw [hg j, hq j, neg_mul_neg])
  unfold finitePairing
  rw [hs]
  unfold average
  ring

theorem weighted_average_abs_le {m : ℕ} (g e : Fin m → ℝ) (G : ℝ)
    (hg : ∀ j, |g j| ≤ G) :
    |average (fun j => g j * e j)| ≤ G * average (fun j => |e j|) := by
  have hs : |∑ j, g j * e j| ≤ ∑ j, G * |e j| := by
    apply (Finset.abs_sum_le_sum_abs (fun j : Fin m => g j * e j) Finset.univ).trans
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hg j) (abs_nonneg (e j))
  rw [← Finset.mul_sum] at hs
  unfold average
  rw [abs_div, show |(m : ℝ)| = m from abs_of_nonneg (Nat.cast_nonneg m)]
  exact (div_le_div_of_nonneg_right hs (Nat.cast_nonneg m)).trans_eq (by ring)

theorem actual_normal_pairing {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (g : Fin (2 * m) → ℝ)
    (hg : FiniteBox.Antiperiodic hm g)
    (hz : LensClosure.closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j))
      σ (coordinates hm v) ξ = 0) :
    finitePairing g (constraint (by omega) (center hm θ v σ ξ) - boxInput hm σ) / (2 * m : ℝ) -
      (∑ j : Fin m, g (halfIndex j) * σ j * angleDifference (by omega) θ (halfIndex j)) =
        average (fun j => g (halfIndex j) * normalError hm θ v σ ξ j) := by
  have hc := constraint_halfTurn hm (center hm θ v σ ξ) (center_halfPeriodic hm θ v σ ξ hz)
  have hq : FiniteBox.Antiperiodic hm (constraint (by omega) (center hm θ v σ ξ) - boxInput hm σ) := by
    intro j
    simp only [Pi.sub_apply, hc j, boxInput_antiperiodic hm σ j]
    ring
  rw [antiperiodic_pairing_average hm g _ hg hq]
  have he (j : Fin m) :
      g (halfIndex j) * normalError hm θ v σ ξ j =
        g (halfIndex j) * (constraint (by omega) (center hm θ v σ ξ) - boxInput hm σ) (halfIndex j) -
          (m : ℝ) * (g (halfIndex j) * σ j * angleDifference (by omega) θ (halfIndex j)) := by
    simp only [normalError, Pi.sub_apply, boxInput]
    rw [show antiWord hm σ (halfIndex j) = σ j from antiWord_halfIndex hm σ j]
    ring
  simp_rw [he]
  simp only [average, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

theorem actual_normal_pairing_error {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (g : Fin (2 * m) → ℝ)
    (hg : FiniteBox.Antiperiodic hm g)
    (hz : LensClosure.closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j))
      σ (coordinates hm v) ξ = 0) (G : ℝ) (hG : ∀ j, |g j| ≤ G) :
    |finitePairing g (constraint (by omega) (center hm θ v σ ξ) - boxInput hm σ) / (2 * m : ℝ) -
      (∑ j : Fin m, g (halfIndex j) * σ j * angleDifference (by omega) θ (halfIndex j))| ≤
        G * average (fun j => |normalError hm θ v σ ξ j|) := by
  rw [actual_normal_pairing hm θ v σ ξ g hg hz]
  exact weighted_average_abs_le _ _ G (fun j => hG (halfIndex j))

theorem eventual_canonical_normal_pairing : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (σ : Fin m → ℝ) (x : FreeParameters m) (g : Fin (2 * m) → ℝ),
      (∀ j, |σ j| ≤ 1) → x ∈ domain hm → FiniteBox.Antiperiodic hm g →
      finitePairing g (constraint (by omega) (centerAt hm σ x) - boxInput hm σ) / (2 * m : ℝ) -
        (∑ j : Fin m, g (halfIndex j) * σ j * angleDifference (by omega) x.1 (halfIndex j)) =
          average (fun j => g (halfIndex j) * normalError hm x.1 x.2 σ (root hm σ x) j) := by
  filter_upwards [eventual_size_conditions] with m hs hm σ x g hσ hx hg
  exact actual_normal_pairing hm x.1 x.2 σ (root hm σ x) g hg
    (root_spec hs.1 σ x hs.2.1 hσ hx).2

end
end StructuralNote.CommonFiberNormalPairing

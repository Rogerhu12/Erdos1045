import FinitePerimeterIntervals
import FinitePerimeterCut

namespace ExteriorReduction.Reinhardt
open Complex Set
open Erdos1045.Configuration Erdos1045.HullGeometry
noncomputable section

def normalRightEndpoint {n : ℕ} (z : Points n) (i : Fin n) : ℝ := by
  classical
  exact if (strictNormalAngles z i).Nonempty then sSup (strictNormalAngles z i) else Real.pi

def foldEndpoint (t : ℝ) : ℝ := if t ≤ 0 then t else t - Real.pi

def widthEndpoints {n : ℕ} (z : Points n) : Finset ℝ :=
  Finset.univ.image (fun i => foldEndpoint (normalRightEndpoint z i))

theorem normalRightEndpoint_mem {n : ℕ} (z : Points n) (i : Fin n)
    (hne : ∃ j, z j ≠ z i) (hcut : (-1 : ℂ) ∉ strictNormalCone z i) :
    normalRightEndpoint z i ∈ Ioc (-Real.pi) Real.pi := by
  have hs := strictNormalAngles_subset z i hne hcut
  unfold normalRightEndpoint
  split_ifs with hi
  · obtain ⟨t, ht⟩ := hi
    refine ⟨(hs ht).1.trans_le (le_csSup ⟨Real.pi, fun _ hx => (hs hx).2.le⟩ ht), ?_⟩
    exact csSup_le ⟨t, ht⟩ (fun _ hx => (hs hx).2.le)
  · exact ⟨by linarith [Real.pi_pos], le_rfl⟩

theorem foldEndpoint_mem {t : ℝ} (ht : t ∈ Ioc (-Real.pi) Real.pi) :
    foldEndpoint t ∈ Ioc (-Real.pi) 0 := by
  unfold foldEndpoint
  split_ifs with h
  · exact ⟨ht.1, h⟩
  · constructor <;> linarith [ht.1, ht.2]

theorem widthEndpoints_card_le {n : ℕ} (z : Points n) : (widthEndpoints z).card ≤ n := by
  classical
  exact (Finset.card_image_le).trans (by simp)

theorem widthEndpoints_mem {n : ℕ} (z : Points n) (hne : ∃ i j, z i ≠ z j)
    (hcut : ∀ i, (-1 : ℂ) ∉ strictNormalCone z i) :
    ∀ t ∈ widthEndpoints z, t ∈ Ioc (-Real.pi) 0 := by
  intro t ht
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
  exact foldEndpoint_mem (normalRightEndpoint_mem z i (other_point_of_nontrivial z hne i) (hcut i))

theorem zero_mem_widthEndpoints {n : ℕ} (hn : 0 < n) (z : Points n)
    (hne : ∃ i j, z i ≠ z j) (hcut : ∀ i, (-1 : ℂ) ∉ strictNormalCone z i) :
    0 ∈ widthEndpoints z := by
  have hs (i) := strictNormalAngles_subset z i (other_point_of_nontrivial z hne i) (hcut i)
  obtain ⟨i, hi, he⟩ := endpoint_eq_cell_sup (strictNormalAngles z)
    (fun i t ht => (hs i ht).2.le)
    (strictNormalAngles_closure_cover hn z ⟨by linarith [Real.pi_pos], le_rfl⟩)
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  simp [normalRightEndpoint, hi, he, foldEndpoint, not_le.mpr Real.pi_pos]

theorem support_fixed_between_endpoints {n : ℕ} (hn : 0 < n) (z : Points n)
    (hne : ∃ i j, z i ≠ z j) (hcut : ∀ i, (-1 : ℂ) ∉ strictNormalCone z i)
    {a b : ℝ} (hab : a < b) (ha : -Real.pi ≤ a) (hb : b ≤ Real.pi)
    (hend : ∀ i, normalRightEndpoint z i ∉ Ioo a b) :
    ∃ i, EqOn (support z)
      (fun t => (z i * Complex.exp (-((t : ℂ) * Complex.I))).re) (Icc a b) := by
  have hs (i) := strictNormalAngles_subset z i (other_point_of_nontrivial z hne i) (hcut i)
  obtain ⟨i, hi⟩ := interval_covered_by_cell (strictNormalAngles z)
    (fun i => strictNormalAngles_ordConnected z i (other_point_of_nontrivial z hne i) (hcut i))
    (fun i => ⟨Real.pi, fun _ ht => (hs i ht).2.le⟩) hab
    (fun _ ht => strictNormalAngles_closure_cover hn z ⟨ha.trans ht.1.le, ht.2.le.trans hb⟩)
    (fun i hne => by simpa [normalRightEndpoint, hne] using hend i)
  have he := (support_eq_on_strictNormalAngles z i (other_point_of_nontrivial z hne i) (hcut i)).mono hi
  have hh := he.closure (support_continuous z) (by fun_prop)
  rw [closure_Ioo hab.ne] at hh
  exact ⟨i, hh⟩

theorem projection_add_pi (v : ℂ) (t : ℝ) :
    (v * Complex.exp (-(((t + Real.pi : ℝ) : ℂ) * Complex.I))).re =
      -(v * Complex.exp (-((t : ℂ) * Complex.I))).re := by
  rw [point_projection, point_projection, Real.cos_add_pi, Real.sin_add_pi]
  ring

/-- Between folded normal endpoints, the width is one actual difference-vector
projection. This retains the original diameter bound. -/
theorem width_fixed_between_endpoints {n : ℕ} (hn : 0 < n) (z : Points n)
    (hne : ∃ i j, z i ≠ z j) (hcut : ∀ i, (-1 : ℂ) ∉ strictNormalCone z i)
    {a b : ℝ} (hab : a < b) (ha : -Real.pi ≤ a) (hb : b ≤ 0)
    (hend : ∀ t ∈ widthEndpoints z, t ∉ Ioo a b) :
    ∃ i j, EqOn (width z)
      (fun t => ((z i - z j) * Complex.exp (-((t : ℂ) * Complex.I))).re) (Icc a b) := by
  have hmem (i : Fin n) : foldEndpoint (normalRightEndpoint z i) ∈ widthEndpoints z :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨i, hi⟩ := support_fixed_between_endpoints hn z hne hcut hab ha
    (hb.trans Real.pi_pos.le) (by
      intro i ht
      have he : foldEndpoint (normalRightEndpoint z i) = normalRightEndpoint z i :=
        if_pos (ht.2.le.trans hb)
      exact hend _ (hmem i) (by simpa only [he] using ht))
  obtain ⟨j, hj⟩ := support_fixed_between_endpoints hn z hne hcut
    (show a + Real.pi < b + Real.pi by linarith)
    (show -Real.pi ≤ a + Real.pi by linarith [Real.pi_pos])
    (show b + Real.pi ≤ Real.pi by linarith) (by
      intro j ht
      have hp : 0 < normalRightEndpoint z j := by linarith [ht.1]
      have he : foldEndpoint (normalRightEndpoint z j) = normalRightEndpoint z j - Real.pi :=
        if_neg (not_le.mpr hp)
      apply hend _ (hmem j)
      rw [he]
      constructor <;> linarith [ht.1, ht.2])
  refine ⟨i, j, fun t ht => ?_⟩
  have ht' : t + Real.pi ∈ Icc (a + Real.pi) (b + Real.pi) := by
    constructor <;> linarith [ht.1, ht.2]
  rw [width, hi ht, hj ht']
  dsimp only
  rw [projection_add_pi, sub_mul, Complex.sub_re]
  ring

#print axioms width_fixed_between_endpoints
end
end ExteriorReduction.Reinhardt


import Erdos1045.CyclicAngles
import Erdos1045.ExteriorBoundary
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Selecting and ordering finitely many boundary preimages does not require
injectivity of the boundary extension. Distinct images suffice. -/

namespace ExteriorReduction

open Complex Metric Set
open Erdos1045.ExteriorBoundary Erdos1045.CyclicAngles
open scoped Topology
noncomputable section

theorem exists_angle_Ico_of_norm_one {u : ℂ} (hu : ‖u‖ = 1) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 2 * Real.pi ∧ unit t = u := by
  have he : unit (arg u) = u := by
    simpa [unit, hu] using Complex.norm_mul_exp_arg_mul_I u
  by_cases h : 0 ≤ arg u
  · exact ⟨arg u, h, (arg_le_pi u).trans_lt (by linarith [Real.pi_pos]), he⟩
  · refine ⟨arg u + 2 * Real.pi, ?_, ?_, ?_⟩
    · linarith [neg_pi_lt_arg u, Real.pi_pos]
    · linarith
    · rw [unit, Complex.ofReal_add, add_mul, Complex.exp_add]
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.exp_two_pi_mul_I,
        mul_one]
      exact he

theorem exists_perm_strictMono {n : ℕ} {a : Fin n → ℝ}
    (ha : Function.Injective a) : ∃ σ : Equiv.Perm (Fin n), StrictMono (a ∘ σ) := by
  classical
  let s : Finset ℝ := Finset.univ.image a
  have hs : s.card = n := by simp [s, Finset.card_image_of_injective _ ha]
  let e : Fin n ≃ s := Equiv.ofBijective
    (fun i => ⟨a i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun i j h => ha (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
      exact ⟨i, Subtype.ext hi⟩⟩
  let σ := (s.orderIsoOfFin hs).toEquiv.trans e.symm
  refine ⟨σ, ?_⟩
  have he (i : Fin n) : a (σ i) = s.orderEmbOfFin hs i := by
    exact congrArg Subtype.val (e.apply_symm_apply (s.orderIsoOfFin hs i))
  simpa only [Function.comp_def, he] using (s.orderEmbOfFin hs).strictMono

def finiteAngleIndex {n : ℕ} (hn : 0 < n) (i : ℤ) : Fin n :=
  ⟨(i % (n : ℤ)).toNat, by
    have h0 := Int.emod_nonneg i (show (n : ℤ) ≠ 0 by omega)
    have h1 := Int.emod_lt_of_pos i (show (0 : ℤ) < n by omega)
    omega⟩

@[simp] theorem finiteAngleIndex_val {n : ℕ} (hn : 0 < n) (i : ℤ) :
    ((finiteAngleIndex hn i).val : ℤ) = i % (n : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

def periodicAngle {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (i : ℤ) : ℝ :=
  a (finiteAngleIndex hn i) + (i / (n : ℤ) : ℤ) * (2 * Real.pi)

theorem periodicAngle_fin {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (i : Fin n) :
    periodicAngle hn a i = a i := by
  have hq : (i : ℤ) / (n : ℤ) = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  have hr : finiteAngleIndex hn i = i := by
    apply Fin.ext
    simp [finiteAngleIndex, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ i) (by omega : (i : ℤ) < n)]
  simp [periodicAngle, hq, hr]

theorem periodicAngle_period {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (i : ℤ) :
    periodicAngle hn a (i + n) = periodicAngle hn a i + 2 * Real.pi := by
  have hr : finiteAngleIndex hn (i + n) = finiteAngleIndex hn i := by
    apply Fin.ext
    simp [finiteAngleIndex, Int.add_emod_right]
  have hdiv : (i + (n : ℤ)) / (n : ℤ) = i / (n : ℤ) + 1 := by
    simpa using Int.add_mul_ediv_right i 1 (show (n : ℤ) ≠ 0 by omega)
  simp only [periodicAngle, hr, hdiv,
    Int.cast_add, Int.cast_one]
  ring

theorem periodicAngle_strictMono {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ}
    (ha : StrictMono a) (hrange : ∀ i, 0 ≤ a i ∧ a i < 2 * Real.pi) :
    StrictMono (periodicAngle hn a) := by
  intro i j hij
  have hnz : (0 : ℤ) < n := by omega
  have hq : i / (n : ℤ) ≤ j / (n : ℤ) := Int.ediv_le_ediv hnz hij.le
  by_cases he : i / (n : ℤ) = j / (n : ℤ)
  · have hr : i % (n : ℤ) < j % (n : ℤ) := by
      have hi := Int.emod_add_mul_ediv i (n : ℤ)
      have hj := Int.emod_add_mul_ediv j (n : ℤ)
      nlinarith
    have hai : finiteAngleIndex hn i < finiteAngleIndex hn j := by
      change (finiteAngleIndex hn i).val < (finiteAngleIndex hn j).val
      exact_mod_cast (show ((finiteAngleIndex hn i).val : ℤ) <
        ((finiteAngleIndex hn j).val : ℤ) by simpa only [finiteAngleIndex_val] using hr)
    simpa only [periodicAngle, he, add_lt_add_iff_right] using ha hai
  · have hq' : ((i / (n : ℤ) : ℤ) : ℝ) + 1 ≤ ((j / (n : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast (show i / (n : ℤ) + 1 ≤ j / (n : ℤ) by omega)
    have hi := (hrange (finiteAngleIndex hn i)).2
    have hj := (hrange (finiteAngleIndex hn j)).1
    have hmul := mul_le_mul_of_nonneg_right hq' (show 0 ≤ 2 * Real.pi by positivity)
    dsimp [periodicAngle]
    nlinarith

def anglesOfFinite {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : StrictMono a) (hrange : ∀ i, 0 ≤ a i ∧ a i < 2 * Real.pi) : Angles n where
  angle := periodicAngle hn a
  increasing := periodicAngle_strictMono hn ha hrange
  period := periodicAngle_period hn a

theorem ordered_boundary_preimages {n : ℕ} (hn : 0 < n) {z : Fin n → ℂ}
    (hz : Function.Injective z) {F : ℂ → ℂ}
    (hpre : ∀ i, ∃ u ∈ sphere (0 : ℂ) 1, F u = z i) :
    ∃ (σ : Equiv.Perm (Fin n)) (a : Angles n),
      (∀ i : Fin n, 0 ≤ a.angle i ∧ a.angle i < 2 * Real.pi) ∧
      ∀ i : Fin n, F (unit (a.angle i)) = z (σ i) := by
  choose u hu hFu using hpre
  have hu' (i : Fin n) : ‖u i‖ = 1 := mem_sphere_zero_iff_norm.mp (hu i)
  choose t ht0 ht1 ht using fun i => exists_angle_Ico_of_norm_one (hu' i)
  have hti : Function.Injective t := by
    intro i j hij
    apply hz
    rw [← hFu i, ← hFu j, ← ht i, ← ht j, hij]
  obtain ⟨σ, hσ⟩ := exists_perm_strictMono hti
  let a := anglesOfFinite hn (t ∘ σ) hσ (fun i => ⟨ht0 (σ i), ht1 (σ i)⟩)
  have ha (i : Fin n) : a.angle i = t (σ i) := periodicAngle_fin hn (t ∘ σ) i
  refine ⟨σ, a, fun i => ?_, fun i => ?_⟩
  · rw [ha]
    exact ⟨ht0 _, ht1 _⟩
  · rw [ha, ht, hFu]

#print axioms ordered_boundary_preimages

end
end ExteriorReduction

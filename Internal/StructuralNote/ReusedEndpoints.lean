import EventualExact.AllOrderPerimeterExact

/-! Previously proved geometric theorems, connected to the literal maxima in
(1.1) and (1.2). These use the previous proof of localization, not the new
capacity/Sturm route. They certify reuse, not completion of §§2–3. -/

noncomputable section
namespace StructuralNote

open Erdos1045 Erdos1045.Configuration Erdos1045.HullGeometry
open Erdos1045.EventualExact
open Erdos1045.GlobalProof

def diameterValues (n : ℕ) : Set ℝ :=
  {x | ∃ z : Points n, DiameterAtMost 2 z ∧ discriminant z = x}

def perimeterValues (n : ℕ) : Set ℝ :=
  {x | ∃ z : Points n, hullPerimeter z ≤ 2 * Real.pi ∧ discriminant z = x}

/-- The actual supremum over diameter-two configurations, not a proposed formula. -/
def M (n : ℕ) : ℝ := sSup (diameterValues n)

/-- The actual supremum over perimeter-at-most-two-pi configurations. -/
def W (n : ℕ) : ℝ := sSup (perimeterValues n)

theorem supremum_eq_of_attained_bound {S : Set ℝ} {a : ℝ}
    (ha : a ∈ S) (hupper : ∀ x ∈ S, x ≤ a) : sSup S = a := by
  apply le_antisymm
  · exact csSup_le ⟨a, ha⟩ hupper
  · exact le_csSup ⟨a, hupper⟩ ha

theorem eventual_odd_maximum :
    ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n ≥ n₀, Odd n →
      M n = (n : ℝ) ^ n / Real.cos (Real.pi / (2 * n)) ^ (n * (n - 1)) := by
  obtain ⟨n₀, hn₀, h⟩ := AllOrderPerimeterExact.eventual_odd_diameter_two_exact
  refine ⟨n₀, hn₀, fun n hn hodd => ?_⟩
  obtain ⟨hu, ⟨hc, hv⟩, _⟩ := h n hn hodd
  apply supremum_eq_of_attained_bound
  · exact ⟨diameterTwoRegular n, hc, hv⟩
  · rintro x ⟨z, hz, rfl⟩
    exact hu z hz

theorem eventual_odd_maximizer_regular :
    ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n ≥ n₀, Odd n → ∀ z : Points n,
      DiameterAtMost 2 z → discriminant z = M n → Configuration.IsRegular z := by
  obtain ⟨n₀, hn₀, h⟩ := AllOrderPerimeterExact.eventual_odd_diameter_two_exact
  obtain ⟨n₁, _, hM⟩ := eventual_odd_maximum
  refine ⟨max n₀ n₁, le_trans hn₀ (le_max_left _ _), fun n hn hodd z hz he => ?_⟩
  exact (h n (le_trans (le_max_left _ _) hn) hodd).2.2 z hz
    (he.trans (hM n (le_trans (le_max_right _ _) hn) hodd))

theorem eventual_perimeter_maximum :
    ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n ≥ n₀,
      W n = (n : ℝ) ^ n *
        (Real.pi / (n * Real.sin (Real.pi / n))) ^ (n * (n - 1)) := by
  let H := Erdos1045.classicalBackground_proved.toClassicalAnalysis.geometry
  obtain ⟨n₀, hn₀, hreg⟩ := AllOrderPerimeter.large_perimeter_extremizers_regular
  refine ⟨n₀, hn₀, fun n hn => ?_⟩
  have hn3 : 3 ≤ n := by omega
  have heq : perimeterMaximum n = (n : ℝ) ^ n *
      (Real.pi / (n * Real.sin (Real.pi / n))) ^ (n * (n - 1)) := by
    simp only [perimeterMaximum, circlePerimeter, exponent]
    ring
  rw [← heq]
  apply supremum_eq_of_attained_bound
  · exact ⟨perimeterRegular n, (perimeterRegular_perimeter H hn3).le,
      perimeterRegular_discriminant H hn3⟩
  · rintro x ⟨z, hz, rfl⟩
    exact perimeter_bound_of_regular_extremals H hn3 (hreg n hn) z hz

theorem eventual_perimeter_maximizer_regular :
    ∃ n₀ : ℕ, 4 ≤ n₀ ∧ ∀ n ≥ n₀, ∀ z : Points n,
      hullPerimeter z ≤ 2 * Real.pi → discriminant z = W n →
        Configuration.IsRegular z := by
  let H := Erdos1045.classicalBackground_proved.toClassicalAnalysis.geometry
  obtain ⟨n₀, hn₀, hreg⟩ := AllOrderPerimeter.large_perimeter_extremizers_regular
  refine ⟨n₀, hn₀, fun n hn z hz he => hreg n hn z ⟨hz, ?_⟩⟩
  have hb : BddAbove (perimeterValues n) := by
    refine ⟨perimeterMaximum n, ?_⟩
    rintro x ⟨w, hw, rfl⟩
    exact perimeter_bound_of_regular_extremals H (by omega) (hreg n hn) w hw
  intro w hw
  rw [he]
  exact le_csSup hb ⟨w, hw, rfl⟩

end StructuralNote

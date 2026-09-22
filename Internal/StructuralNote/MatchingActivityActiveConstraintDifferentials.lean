import StructuralNote.MatchingActivityActualChartSelection
import StructuralNote.MatchingActivityCrossingVariationDerivative

/-! The ambient first differentials of the actual matching and selected
crossing squared-distance constraints. -/

namespace StructuralNote.MatchingActivityActiveConstraintDifferentials

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization
open FiniteFourierLift FourierMultiplier
open CommonClosureEnergy MatchingActivityActualChartSelection
open MatchingActivityCrossingVariationDerivative
open scoped BigOperators

noncomputable section

def realPairing {n : ℕ} (A U : Points n) : ℝ :=
  ∑ j, inner ℝ (A j) (U j)

def edgeConstraint {n : ℕ} (x : Points n) (p q : Fin n) : ℝ :=
  ‖x p - x q‖ ^ 2

def edgeDifferential {n : ℕ} (x U : Points n) (p q : Fin n) : ℝ :=
  2 * inner ℝ (x p - x q) (U p - U q)

def edgeGradient {n : ℕ} (x : Points n) (p q : Fin n) : Points n :=
  Pi.single p (2 * (x p - x q)) + Pi.single q (-2 * (x p - x q))

theorem edgeConstraint_hasDerivAt {n : ℕ} {x : ℝ → Points n}
    {U : Points n} {t : ℝ} (p q : Fin n)
    (hx : ∀ j, HasDerivAt (fun s => x s j) (U j) t) :
    HasDerivAt (fun s => edgeConstraint (x s) p q)
      (edgeDifferential (x t) U p q) t := by
  have hz := (hx p).sub (hx q)
  exact hz.norm_sq

def matchingFirst {m : ℕ} (i : Fin m) : Fin (2 * m) := halfIndex i

def matchingSecond {m : ℕ} (hm : 0 < m) (i : Fin m) : Fin (2 * m) :=
  halfTurn hm (halfIndex i)

def matchingConstraint {m : ℕ} (hm : 0 < m) (x : Points (2 * m))
    (i : Fin m) : ℝ := edgeConstraint x (matchingFirst i) (matchingSecond hm i)

def matchingGradient {m : ℕ} (hm : 0 < m) (x : Points (2 * m))
    (i : Fin m) : Points (2 * m) := edgeGradient x (matchingFirst i) (matchingSecond hm i)

def selectedFirst {m : ℕ} (hm : 0 < m) (s : Fin m → ℝ) (i : Fin m) : Fin (2 * m) :=
  if s i = 1 then successor (by omega) (halfIndex i) else halfIndex i

def selectedSecond {m : ℕ} (hm : 0 < m) (s : Fin m → ℝ) (i : Fin m) : Fin (2 * m) :=
  if s i = 1 then halfTurn hm (halfIndex i)
  else halfTurn hm (successor (by omega) (halfIndex i))

def selectedConstraint {m : ℕ} (hm : 0 < m) (s : Fin m → ℝ)
    (x : Points (2 * m)) (i : Fin m) : ℝ :=
  edgeConstraint x (selectedFirst hm s i) (selectedSecond hm s i)

def selectedGradient {m : ℕ} (hm : 0 < m) (s : Fin m → ℝ)
    (x : Points (2 * m)) (i : Fin m) : Points (2 * m) :=
  edgeGradient x (selectedFirst hm s i) (selectedSecond hm s i)

theorem matchingConstraint_hasDerivAt {m : ℕ} (hm : 0 < m)
    {x : ℝ → Points (2 * m)} {U : Points (2 * m)} {t : ℝ} (i : Fin m)
    (hx : ∀ j, HasDerivAt (fun a => x a j) (U j) t) :
    HasDerivAt (fun a => matchingConstraint hm (x a) i)
      (edgeDifferential (x t) U (matchingFirst i) (matchingSecond hm i)) t := by
  exact edgeConstraint_hasDerivAt _ _ hx

theorem selectedConstraint_hasDerivAt {m : ℕ} (hm : 0 < m)
    (s : Fin m → ℝ) {x : ℝ → Points (2 * m)} {U : Points (2 * m)}
    {t : ℝ} (i : Fin m)
    (hx : ∀ j, HasDerivAt (fun a => x a j) (U j) t) :
    HasDerivAt (fun a => selectedConstraint hm s (x a) i)
      (edgeDifferential (x t) U (selectedFirst hm s i) (selectedSecond hm s i)) t := by
  exact edgeConstraint_hasDerivAt _ _ hx

end
end StructuralNote.MatchingActivityActiveConstraintDifferentials

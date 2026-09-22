import EventualExact.LensClosureLinear

/-! Exact first and second derivatives of the actual lens increment. The second
formula retains the acceleration of the implicit closure correction. -/

namespace StructuralNote.LensIncrementDerivatives

open Erdos1045.EventualExact Complex LensClosure
noncomputable section

def heightSlope (t : ℝ) : ℝ := -t / Lens.height t

def heightCurvature (t : ℝ) : ℝ := -4 / Lens.height t ^ 3

theorem height_pos {t : ℝ} (ht : t ^ 2 < 4) : 0 < Lens.height t := by
  exact Real.sqrt_pos.mpr (by linarith)

theorem heightSlope_hasDerivAt {t : ℝ} (ht : t ^ 2 < 4) :
    HasDerivAt heightSlope (heightCurvature t) t := by
  have hh := height_hasDerivAt ht
  have hp := height_pos ht
  have hs := Lens.height_sq ht.le
  have hd := (hasDerivAt_id t).neg.div hh hp.ne'
  change HasDerivAt heightSlope
    ((-1 * Lens.height t - -t * (-t / Lens.height t)) / Lens.height t ^ 2) t at hd
  apply hd.congr_deriv
  unfold heightCurvature
  field_simp
  nlinarith only [hs]

def body (L σ t : ℝ) : ℂ := ((σ * Lens.width L t : ℝ) : ℂ) + (t : ℂ) * I

def bodyVelocity (L' σ t t' : ℝ) : ℂ :=
  ((σ * (heightSlope t * t' - L') : ℝ) : ℂ) + (t' : ℂ) * I

def bodyAcceleration (L'' σ t t' t'' : ℝ) : ℂ :=
  ((σ * (heightCurvature t * t' ^ 2 + heightSlope t * t'' - L'') : ℝ) : ℂ) + (t'' : ℂ) * I

theorem body_hasDerivAt {L t : ℝ → ℝ} {x L' t' : ℝ} (σ : ℝ)
    (hL : HasDerivAt L L' x) (ht : HasDerivAt t t' x) (hsmall : t x ^ 2 < 4) :
    HasDerivAt (fun s => body (L s) σ (t s)) (bodyVelocity L' σ (t x) t') x := by
  have hh := (height_hasDerivAt hsmall).comp x ht
  exact (((hh.sub hL).const_mul σ).ofReal_comp).add (ht.ofReal_comp.mul_const I)

theorem bodyVelocity_hasDerivAt {L' t t' : ℝ → ℝ} {x L'' t₁ t₂ : ℝ} (σ : ℝ)
    (hL : HasDerivAt L' L'' x) (ht : HasDerivAt t t₁ x)
    (ht' : HasDerivAt t' t₂ x) (ht₁ : t' x = t₁) (hsmall : t x ^ 2 < 4) :
    HasDerivAt (fun s => bodyVelocity (L' s) σ (t s) (t' s))
      (bodyAcceleration L'' σ (t x) t₁ t₂) x := by
  have hh := (heightSlope_hasDerivAt hsmall).comp x ht
  have hd := (((hh.mul ht').sub hL).const_mul σ).ofReal_comp.add (ht'.ofReal_comp.mul_const I)
  change HasDerivAt (fun s => bodyVelocity (L' s) σ (t s) (t' s)) _ x at hd
  apply hd.congr_deriv
  simp only [bodyAcceleration, Function.comp_apply, ht₁]
  push_cast
  ring

def incrementVelocity (α L σ t α' L' t' : ℝ) : ℂ :=
  unit α * ((α' : ℂ) * I * body L σ t + bodyVelocity L' σ t t')

def incrementAcceleration (α L σ t α' L' t' α'' L'' t'' : ℝ) : ℂ :=
  unit α * (((α'' : ℂ) * I - (α' : ℂ) ^ 2) * body L σ t +
    2 * (α' : ℂ) * I * bodyVelocity L' σ t t' + bodyAcceleration L'' σ t t' t'')

theorem unit_path_hasDerivAt {α : ℝ → ℝ} {x α' : ℝ} (hα : HasDerivAt α α' x) :
    HasDerivAt (fun s => unit (α s)) (unit (α x) * ((α' : ℂ) * I)) x := by
  exact (hα.ofReal_comp.mul_const I).cexp

theorem increment_hasDerivAt {α L t : ℝ → ℝ} {x α' L' t' : ℝ} (σ : ℝ)
    (hα : HasDerivAt α α' x) (hL : HasDerivAt L L' x) (ht : HasDerivAt t t' x)
    (hsmall : t x ^ 2 < 4) :
    HasDerivAt (fun s => LensClosure.increment (α s) (L s) σ (t s))
      (incrementVelocity (α x) (L x) σ (t x) α' L' t') x := by
  have hd := (unit_path_hasDerivAt hα).mul (body_hasDerivAt σ hL ht hsmall)
  change HasDerivAt (fun s => LensClosure.increment (α s) (L s) σ (t s)) _ x at hd
  apply hd.congr_deriv
  unfold incrementVelocity
  ring

theorem incrementVelocity_hasDerivAt {α L t α' L' t' : ℝ → ℝ}
    {x a₁ l₁ t₁ a₂ l₂ t₂ : ℝ} (σ : ℝ)
    (hα : HasDerivAt α a₁ x) (hL : HasDerivAt L l₁ x) (ht : HasDerivAt t t₁ x)
    (hα' : HasDerivAt α' a₂ x) (hL' : HasDerivAt L' l₂ x) (ht' : HasDerivAt t' t₂ x)
    (ha₁ : α' x = a₁) (hl₁ : L' x = l₁) (ht₁ : t' x = t₁) (hsmall : t x ^ 2 < 4) :
    HasDerivAt (fun s => incrementVelocity (α s) (L s) σ (t s) (α' s) (L' s) (t' s))
      (incrementAcceleration (α x) (L x) σ (t x) a₁ l₁ t₁ a₂ l₂ t₂) x := by
  have hb := body_hasDerivAt σ hL ht hsmall
  have hv := bodyVelocity_hasDerivAt σ hL' ht ht' ht₁ hsmall
  have hd := (unit_path_hasDerivAt hα).mul (((hα'.ofReal_comp.mul_const I).mul hb).add hv)
  change HasDerivAt
    (fun s => incrementVelocity (α s) (L s) σ (t s) (α' s) (L' s) (t' s)) _ x at hd
  apply hd.congr_deriv
  simp only [incrementAcceleration, Pi.add_apply, Pi.mul_apply, ha₁, hl₁, ht₁]
  ring_nf
  simp only [I_sq]
  ring

end
end StructuralNote.LensIncrementDerivatives

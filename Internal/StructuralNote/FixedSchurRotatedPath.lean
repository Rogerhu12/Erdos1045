import StructuralNote.FixedSchurRotatedAlgebra
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Actual one- and two-variable chain rules for the rotated selected chord. -/

namespace StructuralNote.FixedSchurRotatedPath

open Filter
open scoped Topology

noncomputable section

def r (q p b : ℝ) : ℝ :=
  q * Real.cos b + p * Real.sin b

def s (q p b : ℝ) : ℝ :=
  p * Real.cos b - q * Real.sin b

def L (a : ℝ) : ℝ := 2 * Real.cos a

def H (ε y : ℝ) : ℝ := Real.sqrt (4 - (ε * y) ^ 2)

def alpha (ε σ b y : ℝ) : ℝ :=
  Real.cos b - σ * ε * (y / H ε y) * Real.sin b

def beta (ε σ b y : ℝ) : ℝ :=
  Real.sin b + σ * ε * (y / H ε y) * Real.cos b

theorem hasDerivAt_r_path {q p b : ℝ → ℝ} {q' p' u : ℝ} {t : ℝ}
    (hq : HasDerivAt q q' t) (hp : HasDerivAt p p' t)
    (hb : HasDerivAt b u t) :
    HasDerivAt (fun z : ℝ => r (q z) (p z) (b z))
      (q' * Real.cos (b t) + p' * Real.sin (b t) +
        s (q t) (p t) (b t) * u) t := by
  have hc := (Real.hasDerivAt_cos (b t)).comp t hb
  have hs := (Real.hasDerivAt_sin (b t)).comp t hb
  have hq' := hq.mul hc
  have hp' := hp.mul hs
  have hsum := hq'.add hp'
  apply hsum.congr_deriv
  dsimp [r, s]
  ring

theorem hasDerivAt_s_path {q p b : ℝ → ℝ} {q' p' u : ℝ} {t : ℝ}
    (hq : HasDerivAt q q' t) (hp : HasDerivAt p p' t)
    (hb : HasDerivAt b u t) :
    HasDerivAt (fun z : ℝ => s (q z) (p z) (b z))
      (p' * Real.cos (b t) - q' * Real.sin (b t) -
        r (q t) (p t) (b t) * u) t := by
  have hc := (Real.hasDerivAt_cos (b t)).comp t hb
  have hs := (Real.hasDerivAt_sin (b t)).comp t hb
  have hp' := hp.mul hc
  have hq' := hq.mul hs
  have hsub := hp'.sub hq'
  apply hsub.congr_deriv
  dsimp [r, s]
  ring

theorem hasDerivAt_L_path {a : ℝ → ℝ} {e : ℝ} {t : ℝ}
    (ha : HasDerivAt a (e / 2) t) :
    HasDerivAt (fun z : ℝ => L (a z))
      (-Real.sin (a t) * e) t := by
  have hc := (Real.hasDerivAt_cos (a t)).comp t ha
  have h := (hasDerivAt_const t (2 : ℝ)).mul hc
  apply h.congr_deriv
  dsimp [L]
  ring

theorem hasDerivAt_H_path {ε : ℝ} {y : ℝ → ℝ}
    {y' : ℝ} {t : ℝ}
    (hs : HasDerivAt y y' t)
    (hH : 0 < H ε (y t)) :
    HasDerivAt (fun z : ℝ => H ε (y z))
      (-(ε ^ 2 * y t * y') / H ε (y t)) t := by
  have hy : HasDerivAt y y' t := hs
  have harg : HasDerivAt (fun z : ℝ => 4 - (ε * y z) ^ 2)
      (-2 * ε ^ 2 * y t * y') t := by
    have he : HasDerivAt (fun z : ℝ => ε * y z) (ε * y') t := by
      have hmul := (hasDerivAt_const t ε).mul hy
      have hmul' : HasDerivAt (fun z : ℝ => ε * y z)
          (0 * y t + ε * y') t := by
        apply hmul.congr_of_eventuallyEq
        filter_upwards [] with z
        simp
      exact hmul'.congr_deriv (by ring)
    have he2 := he.pow 2
    have hfour := (hasDerivAt_const t (4 : ℝ)).sub he2
    apply hfour.congr_deriv
    ring
  have hinner : 0 < 4 - (ε * y t) ^ 2 := by
    have hh := (Real.sqrt_pos).mp hH
    simpa only [H] using hh
  have hsqrt := harg.sqrt hinner.ne'
  apply hsqrt.congr_deriv
  dsimp [H]
  field_simp [hinner.ne']

theorem rotated_first_derivative
    {q p a b : ℝ → ℝ} {ε σ e u q' p' : ℝ} {t : ℝ}
    (hε : 0 < ε) (hσ : σ = 1 ∨ σ = -1)
    (hq : HasDerivAt q q' t) (hp : HasDerivAt p p' t)
    (ha : HasDerivAt a (e / 2) t) (hb : HasDerivAt b u t)
    (hH : 0 < H ε (s (q t) (p t) (b t)))
    (hid : ∀ᶠ z in 𝓝 t,
      r (q z) (p z) (b z) + σ / ε *
          (L (a z) - H ε (s (q z) (p z) (b z))) = 0) :
    alpha ε σ (b t) (s (q t) (p t) (b t)) * q' +
        beta ε σ (b t) (s (q t) (p t) (b t)) * p' =
      σ / ε * Real.sin (a t) * e -
        (L (a t) / H ε (s (q t) (p t) (b t))) *
          s (q t) (p t) (b t) * u := by
  have hrad := hasDerivAt_r_path hq hp hb
  have htang := hasDerivAt_s_path hq hp hb
  have hheight := hasDerivAt_H_path
    (y := fun z : ℝ => s (q z) (p z) (b z))
    (y' := p' * Real.cos (b t) - q' * Real.sin (b t) -
      r (q t) (p t) (b t) * u) htang hH
  have hlength := hasDerivAt_L_path ha
  have hbranch := hrad.add
    ((hasDerivAt_const t (σ / ε)).mul (hlength.sub hheight))
  have hid' :
      ((fun z : ℝ => r (q z) (p z) (b z)) +
        (fun _ : ℝ => σ / ε) *
          ((fun z : ℝ => L (a z)) -
            (fun z : ℝ => H ε (s (q z) (p z) (b z))))) =ᶠ[𝓝 t]
        (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hid] with z hz
    simpa only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply] using hz
  have hzero := hbranch.congr_of_eventuallyEq hid'.symm
  have hderiv := hzero.unique (hasDerivAt_const t (0 : ℝ))
  have hσsq : σ ^ 2 = 1 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hid0 : r (q t) (p t) (b t) + σ / ε *
      (L (a t) - H ε (s (q t) (p t) (b t))) = 0 := hid.self_of_nhds
  have hrel : ε * r (q t) (p t) (b t) + σ *
      (L (a t) - H ε (s (q t) (p t) (b t))) = 0 := by
    calc
      ε * r (q t) (p t) (b t) + σ *
          (L (a t) - H ε (s (q t) (p t) (b t))) =
          ε * (r (q t) (p t) (b t) + σ / ε *
            (L (a t) - H ε (s (q t) (p t) (b t)))) := by
              field_simp [hε.ne']
      _ = 0 := by rw [hid0, mul_zero]
  have hrel' : σ * (ε * r (q t) (p t) (b t)) +
      (L (a t) - H ε (s (q t) (p t) (b t))) = 0 := by
    calc
      σ * (ε * r (q t) (p t) (b t)) +
          (L (a t) - H ε (s (q t) (p t) (b t))) =
          σ * (ε * r (q t) (p t) (b t) + σ *
            (L (a t) - H ε (s (q t) (p t) (b t)))) +
            (1 - σ ^ 2) *
              (L (a t) - H ε (s (q t) (p t) (b t))) := by ring
      _ = 0 := by rw [hrel, hσsq]; ring
  have hratio : σ * ε / H ε (s (q t) (p t) (b t)) *
      r (q t) (p t) (b t) =
      1 - L (a t) / H ε (s (q t) (p t) (b t)) := by
    field_simp [ne_of_gt hH]
    nlinarith [hrel']
  simp only [zero_mul, zero_add] at hderiv
  have hderiv' := hderiv
  field_simp [hε.ne', ne_of_gt hH] at hderiv'
  have hrel_mul := congrArg
    (fun z : ℝ => z * s (q t) (p t) (b t) * u) hrel'
  dsimp [alpha, beta]
  field_simp [hε.ne', ne_of_gt hH]
  nlinarith [hderiv', hrel_mul]

end
end StructuralNote.FixedSchurRotatedPath

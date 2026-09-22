import StructuralNote.FixedSchurRotatedPath
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Genuine second differentiation of the rotated selected-chord constraint. -/

namespace StructuralNote.FixedSchurRotatedSecondPath

open Filter
open StructuralNote.FixedSchurRotatedPath
open scoped Topology

noncomputable section

def radialPath (q p b : ℝ → ℝ) (z : ℝ) : ℝ :=
  r (q z) (p z) (b z)

def tangentialPath (q p b : ℝ → ℝ) (z : ℝ) : ℝ :=
  s (q z) (p z) (b z)

def UPath (q₁ p₁ b : ℝ → ℝ) (z : ℝ) : ℝ :=
  r (q₁ z) (p₁ z) (b z)

def TPath (q₁ p₁ b : ℝ → ℝ) (z : ℝ) : ℝ :=
  s (q₁ z) (p₁ z) (b z)

def constraintPath (ε σ : ℝ) (q p a b : ℝ → ℝ) (z : ℝ) : ℝ :=
  radialPath q p b z + σ / ε *
    (L (a z) - H ε (tangentialPath q p b z))

def firstResidual (ε σ e u : ℝ) (q p a b q₁ p₁ : ℝ → ℝ) (z : ℝ) : ℝ :=
  UPath q₁ p₁ b z + tangentialPath q p b z * u +
    σ / ε *
      (-Real.sin (a z) * e +
        ε ^ 2 * tangentialPath q p b z *
          (TPath q₁ p₁ b z - radialPath q p b z * u) /
            H ε (tangentialPath q p b z))

theorem hasDerivAt_constraint_first {ε σ e u : ℝ}
    {q p a b q₁ p₁ : ℝ → ℝ} {z : ℝ}
    (hq : HasDerivAt q (q₁ z) z) (hp : HasDerivAt p (p₁ z) z)
    (ha : HasDerivAt a (e / 2) z) (hb : HasDerivAt b u z)
    (hH : 0 < H ε (tangentialPath q p b z)) (hε : ε ≠ 0) :
    HasDerivAt (fun w : ℝ => constraintPath ε σ q p a b w)
      (firstResidual ε σ e u q p a b q₁ p₁ z) z := by
  have hrad := hasDerivAt_r_path hq hp hb
  have htang := hasDerivAt_s_path hq hp hb
  have hheight := hasDerivAt_H_path htang hH
  have hlength := hasDerivAt_L_path ha
  have hbranch := hrad.add
    ((hasDerivAt_const z (σ / ε)).mul (hlength.sub hheight))
  apply hbranch.congr_deriv
  dsimp [constraintPath, firstResidual, radialPath, tangentialPath,
    UPath, TPath, r, s]
  field_simp [hε, ne_of_gt hH]
  ring_nf

private theorem hasDerivAt_UPath {q₁ p₁ b : ℝ → ℝ}
    {q₂ p₂ u : ℝ} {t : ℝ}
    (hq₁ : HasDerivAt q₁ q₂ t) (hp₁ : HasDerivAt p₁ p₂ t)
    (hb : HasDerivAt b u t) :
    HasDerivAt (fun z : ℝ => UPath q₁ p₁ b z)
      (q₂ * Real.cos (b t) + p₂ * Real.sin (b t) +
        TPath q₁ p₁ b t * u) t := by
  simpa only [UPath, TPath] using hasDerivAt_r_path hq₁ hp₁ hb

private theorem hasDerivAt_TPath {q₁ p₁ b : ℝ → ℝ}
    {q₂ p₂ u : ℝ} {t : ℝ}
    (hq₁ : HasDerivAt q₁ q₂ t) (hp₁ : HasDerivAt p₁ p₂ t)
    (hb : HasDerivAt b u t) :
    HasDerivAt (fun z : ℝ => TPath q₁ p₁ b z)
      (p₂ * Real.cos (b t) - q₂ * Real.sin (b t) -
        UPath q₁ p₁ b t * u) t := by
  simpa only [UPath, TPath] using hasDerivAt_s_path hq₁ hp₁ hb

theorem rotated_second_derivative
    {ε σ e u q₂ p₂ : ℝ} {q p a b q₁ p₁ : ℝ → ℝ} {t : ℝ}
    (hε : 0 < ε) (hσ : σ = 1 ∨ σ = -1)
    (hq : ∀ᶠ z in 𝓝 t, HasDerivAt q (q₁ z) z)
    (hp : ∀ᶠ z in 𝓝 t, HasDerivAt p (p₁ z) z)
    (hq₁ : HasDerivAt q₁ q₂ t) (hp₁ : HasDerivAt p₁ p₂ t)
    (ha : ∀ᶠ z in 𝓝 t, HasDerivAt a (e / 2) z)
    (hb : ∀ᶠ z in 𝓝 t, HasDerivAt b u z)
    (hH : ∀ᶠ z in 𝓝 t, 0 < H ε (tangentialPath q p b z))
    (hid : ∀ᶠ z in 𝓝 t, constraintPath ε σ q p a b z = 0) :
    alpha ε σ (b t) (tangentialPath q p b t) * q₂ +
        beta ε σ (b t) (tangentialPath q p b t) * p₂ =
      σ / (2 * ε) * Real.cos (a t) * e ^ 2 -
        2 * TPath q₁ p₁ b t * u +
        radialPath q p b t * u ^ 2 +
        σ * ε * tangentialPath q p b t /
            H ε (tangentialPath q p b t) *
          (2 * UPath q₁ p₁ b t * u +
            tangentialPath q p b t * u ^ 2) -
        4 * σ * ε /
            H ε (tangentialPath q p b t) ^ 3 *
          (TPath q₁ p₁ b t - radialPath q p b t * u) ^ 2 := by
  have hσsq : σ ^ 2 = 1 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hq0 := hq.self_of_nhds
  have hp0 := hp.self_of_nhds
  have ha0 := ha.self_of_nhds
  have hb0 := hb.self_of_nhds
  have hH0 := hH.self_of_nhds
  have hrad := hasDerivAt_r_path hq0 hp0 hb0
  have htang := hasDerivAt_s_path hq0 hp0 hb0
  have hheight := hasDerivAt_H_path htang hH0
  have hlength := hasDerivAt_L_path ha0
  have hfirst := hasDerivAt_constraint_first (σ := σ) hq0 hp0 ha0 hb0
    hH0 hε.ne'
  have hUF := hasDerivAt_UPath hq₁ hp₁ hb0
  have hTF := hasDerivAt_TPath hq₁ hp₁ hb0
  have hS1 := htang
  have hR1 := hrad
  have hS1Path : HasDerivAt
      (fun z : ℝ => TPath q₁ p₁ b z - radialPath q p b z * u)
      ((p₂ * Real.cos (b t) - q₂ * Real.sin (b t) -
          UPath q₁ p₁ b t * u) -
        (q₁ t * Real.cos (b t) + p₁ t * Real.sin (b t) +
          tangentialPath q p b t * u) * u) t := by
    have hmul := hR1.mul_const u
    have hsub := hTF.sub hmul
    have hsub' : HasDerivAt
        (fun z : ℝ => TPath q₁ p₁ b z - radialPath q p b z * u)
        ((p₂ * Real.cos (b t) - q₂ * Real.sin (b t) -
            UPath q₁ p₁ b t * u) -
          (q₁ t * Real.cos (b t) + p₁ t * Real.sin (b t) +
            tangentialPath q p b t * u) * u) t := by
      apply hsub.congr_of_eventuallyEq
      filter_upwards [] with z
      simp [radialPath, TPath]
    exact hsub'.congr_deriv (by
      dsimp [radialPath, tangentialPath, UPath, TPath, r, s])
  have hSPath := hS1
  have hHpath := hheight
  have hprod : HasDerivAt
      (fun z : ℝ => tangentialPath q p b z *
        (TPath q₁ p₁ b z - radialPath q p b z * u))
      ((p₁ t * Real.cos (b t) - q₁ t * Real.sin (b t) -
          radialPath q p b t * u) *
          (TPath q₁ p₁ b t - radialPath q p b t * u) +
        tangentialPath q p b t *
          ((p₂ * Real.cos (b t) - q₂ * Real.sin (b t) -
            UPath q₁ p₁ b t * u) -
            (q₁ t * Real.cos (b t) + p₁ t * Real.sin (b t) +
              tangentialPath q p b t * u) * u)) t := by
    have h := hSPath.mul hS1Path
    have h' : HasDerivAt
        (fun z : ℝ => tangentialPath q p b z *
          (TPath q₁ p₁ b z - radialPath q p b z * u))
        ((p₁ t * Real.cos (b t) - q₁ t * Real.sin (b t) -
            radialPath q p b t * u) *
            (TPath q₁ p₁ b t - radialPath q p b t * u) +
          tangentialPath q p b t *
            ((p₂ * Real.cos (b t) - q₂ * Real.sin (b t) -
              UPath q₁ p₁ b t * u) -
              (q₁ t * Real.cos (b t) + p₁ t * Real.sin (b t) +
                tangentialPath q p b t * u) * u)) t := by
      apply h.congr_of_eventuallyEq
      filter_upwards [] with z
      simp [radialPath, tangentialPath, TPath]
    exact h'.congr_deriv (by
      dsimp [radialPath, tangentialPath, UPath, TPath, r, s])
  have hquot : HasDerivAt
      (fun z : ℝ => tangentialPath q p b z *
        (TPath q₁ p₁ b z - radialPath q p b z * u) /
          H ε (tangentialPath q p b z))
      (((p₁ t * Real.cos (b t) - q₁ t * Real.sin (b t) -
          radialPath q p b t * u) *
          (TPath q₁ p₁ b t - radialPath q p b t * u) +
        tangentialPath q p b t *
          ((p₂ * Real.cos (b t) - q₂ * Real.sin (b t) -
            UPath q₁ p₁ b t * u) -
            (q₁ t * Real.cos (b t) + p₁ t * Real.sin (b t) +
              tangentialPath q p b t * u) * u)) /
          H ε (tangentialPath q p b t) -
        (tangentialPath q p b t *
          (TPath q₁ p₁ b t - radialPath q p b t * u)) /
          H ε (tangentialPath q p b t) ^ 2 *
          (-(ε ^ 2 * tangentialPath q p b t *
            (TPath q₁ p₁ b t - radialPath q p b t * u)) /
            H ε (tangentialPath q p b t))) t := by
    have h := hprod.div hHpath (ne_of_gt hH0)
    exact h.congr_deriv (by
      dsimp [radialPath, tangentialPath, UPath, TPath, r, s]
      field_simp [ne_of_gt hH0])
  have hsin : HasDerivAt
      (fun z : ℝ => -Real.sin (a z) * e)
      (-Real.cos (a t) * (e / 2) * e) t := by
    have hs := (Real.hasDerivAt_sin (a t)).comp t ha0
    have hneg := (hasDerivAt_const t (-1 : ℝ)).mul hs
    have hmul := hneg.mul_const e
    have hmul' : HasDerivAt (fun z : ℝ => -Real.sin (a z) * e)
        ((0 * (Real.sin ∘ a) t + (-1) *
          (Real.cos (a t) * (e / 2))) * e) t := by
      apply hmul.congr_of_eventuallyEq
      filter_upwards [] with z
      simp
    exact hmul'.congr_deriv (by ring)
  have hsumprod := hsin.add
    ((hasDerivAt_const t (ε ^ 2)).mul hquot)
  have hG := hUF.add ((hSPath.mul_const u).add
    ((hasDerivAt_const t (σ / ε)).mul hsumprod))
  have hGpath := hG.congr_of_eventuallyEq
    (f₁ := fun z : ℝ => firstResidual ε σ e u q p a b q₁ p₁ z) (by
      filter_upwards [] with z
      simp [firstResidual, UPath, tangentialPath, radialPath, TPath]
      ring)
  have hderivFirst : (deriv (fun z : ℝ => constraintPath ε σ q p a b z)) =ᶠ[𝓝 t]
      (fun z : ℝ => firstResidual ε σ e u q p a b q₁ p₁ z) := by
    filter_upwards [hq, hp, ha, hb, hH] with z hzq hzp hza hzb hzH
    exact (hasDerivAt_constraint_first (σ := σ) hzq hzp hza hzb
      hzH hε.ne').deriv
  have hderivZero : (deriv (fun z : ℝ => constraintPath ε σ q p a b z)) =ᶠ[𝓝 t]
      (fun _ : ℝ => (0 : ℝ)) := by
    have hidEq : (fun z : ℝ => constraintPath ε σ q p a b z) =ᶠ[𝓝 t]
        (fun _ : ℝ => (0 : ℝ)) := hid
    simpa only [deriv_const'] using hidEq.deriv
  have hfirstZero :
      (fun z : ℝ => firstResidual ε σ e u q p a b q₁ p₁ z) =ᶠ[𝓝 t]
      (fun _ : ℝ => (0 : ℝ)) := hderivFirst.symm.trans hderivZero
  have hGzero := hGpath.congr_of_eventuallyEq hfirstZero.symm
  have hsecond := hGzero.unique (hasDerivAt_const t (0 : ℝ))
  simp only [zero_mul, zero_add] at hsecond
  have hsecond' :
      q₂ * Real.cos (b t) + p₂ * Real.sin (b t) +
          TPath q₁ p₁ b t * u +
          (TPath q₁ p₁ b t - radialPath q p b t * u) * u +
          σ / ε *
            (-Real.cos (a t) * (e / 2) * e + ε ^ 2 *
              (((TPath q₁ p₁ b t - radialPath q p b t * u) ^ 2 +
                  tangentialPath q p b t *
                    ((p₂ * Real.cos (b t) - q₂ * Real.sin (b t)) -
                      2 * UPath q₁ p₁ b t * u -
                      tangentialPath q p b t * u ^ 2)) /
                    H ε (tangentialPath q p b t) +
                ε ^ 2 * tangentialPath q p b t ^ 2 *
                    (TPath q₁ p₁ b t - radialPath q p b t * u) ^ 2 /
                  H ε (tangentialPath q p b t) ^ 3)) = 0 := by
    calc
      _ = q₂ * Real.cos (b t) + p₂ * Real.sin (b t) +
          TPath q₁ p₁ b t * u +
          ((p₁ t * Real.cos (b t) - q₁ t * Real.sin (b t) -
              r (q t) (p t) (b t) * u) * u +
            σ / ε *
              (-Real.cos (a t) * (e / 2) * e + ε ^ 2 *
                (((p₁ t * Real.cos (b t) - q₁ t * Real.sin (b t) -
                        radialPath q p b t * u) *
                      (TPath q₁ p₁ b t - radialPath q p b t * u) +
                    tangentialPath q p b t *
                      ((p₂ * Real.cos (b t) - q₂ * Real.sin (b t) -
                          UPath q₁ p₁ b t * u) -
                        (q₁ t * Real.cos (b t) +
                          p₁ t * Real.sin (b t) +
                          tangentialPath q p b t * u) * u)) /
                    H ε (tangentialPath q p b t) -
                  tangentialPath q p b t *
                      (TPath q₁ p₁ b t - radialPath q p b t * u) /
                    H ε (tangentialPath q p b t) ^ 2 *
                    (-(ε ^ 2 * tangentialPath q p b t *
                        (TPath q₁ p₁ b t - radialPath q p b t * u)) /
                      H ε (tangentialPath q p b t))))) := by
            dsimp [radialPath, tangentialPath, UPath, TPath, r, s]
            field_simp [hε.ne', ne_of_gt hH0]
            ring
      _ = 0 := hsecond
  have hHsq : H ε (tangentialPath q p b t) ^ 2 +
      (ε * tangentialPath q p b t) ^ 2 = 4 := by
    have hinner : 0 ≤ 4 - (ε * tangentialPath q p b t) ^ 2 := by
      have hh := (Real.sqrt_pos).mp hH0
      simpa only [H] using hh.le
    dsimp [H]
    rw [Real.sq_sqrt hinner]
    ring
  have hHsq_mul := congrArg
    (fun z : ℝ => z *
      (TPath q₁ p₁ b t - radialPath q p b t * u) ^ 2) hHsq
  have hHsq_scaled := congrArg (fun z : ℝ => 2 * σ * ε ^ 2 * z) hHsq_mul
  dsimp [alpha, beta]
  field_simp [hε.ne', ne_of_gt hH0] at hsecond' ⊢
  ring_nf at hsecond' hHsq_scaled ⊢
  linarith [hsecond', hHsq_scaled, hσsq]

end
end StructuralNote.FixedSchurRotatedSecondPath

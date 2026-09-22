import StructuralNote.FixedSchurRemainderPath

/-! L2 aggregation of the actual scalar Schur Hessian along finite families. -/

namespace StructuralNote.FixedSchurRemainderHessianSum

open StructuralNote.FixedSchurRemainderScalar
open StructuralNote.FixedSchurRemainderSecond
open StructuralNote.FixedSchurRemainderPath
open scoped BigOperators Topology

noncomputable section

def l2Norm {ι : Type*} [Fintype ι] (f : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖f i‖ ^ 2)

theorem l2Norm_sq {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    l2Norm f ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  dsimp [l2Norm]
  rw [Real.sq_sqrt]
  positivity

theorem l2_sum_mul_le {ι : Type*} [Fintype ι] (f g : ι → ℂ) :
    ∑ i, ‖f i‖ * ‖g i‖ ≤ l2Norm f * l2Norm g := by
  simpa only [l2Norm] using
    (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i => ‖f i‖) (fun i => ‖g i‖))

theorem sum_norm_R_hessian_le {ι : Type*} [Fintype ι]
    (u x du dx ddu ddx : ι → ℂ) {U X : ℝ}
    (hU : 0 ≤ U) (hUquarter : U ≤ 1 / 4)
    (hX : 0 ≤ X) (hXquarter : X ≤ 1 / 4)
    (hu : ∀ i, ‖u i‖ ≤ U) (hx : ∀ i, ‖x i‖ ≤ X) :
    ∑ i, ‖Ruu (u i) (x i) * (du i) ^ 2 +
        2 * Rux (u i) (x i) * du i * dx i +
        Rxx (u i) (x i) * (dx i) ^ 2 +
        Ru (u i) (x i) * ddu i + Rx (u i) (x i) * ddx i‖ ≤
      32 * (X + U ^ 2) * l2Norm du ^ 2 +
        64 * U * l2Norm du * l2Norm dx +
        128 * U ^ 2 * l2Norm dx ^ 2 +
        32 * (X + U ^ 2) * l2Norm u * l2Norm ddu +
        32 * U * l2Norm u * l2Norm ddx := by
  have hpoint (i : ι) :
      ‖Ruu (u i) (x i) * (du i) ^ 2 +
          2 * Rux (u i) (x i) * du i * dx i +
          Rxx (u i) (x i) * (dx i) ^ 2 +
          Ru (u i) (x i) * ddu i + Rx (u i) (x i) * ddx i‖ ≤
        32 * (X + U ^ 2) * ‖du i‖ ^ 2 +
          64 * U * ‖du i‖ * ‖dx i‖ +
          128 * U ^ 2 * ‖dx i‖ ^ 2 +
          32 * (X + U ^ 2) * ‖u i‖ * ‖ddu i‖ +
          32 * U * ‖u i‖ * ‖ddx i‖ := by
    have hi := norm_R_velocity_deriv_le
      (u := u i) (x := x i) (du := du i) (dx := dx i)
      (ddu := ddu i) (ddx := ddx i)
      (hu i |>.trans hUquarter) (hx i |>.trans hXquarter)
    have hu2 : ‖u i‖ ^ 2 ≤ U ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg (u i)) (hu i) 2
    have hxi : ‖x i‖ + ‖u i‖ ^ 2 ≤ X + U ^ 2 := by
      nlinarith [hx i, hu2]
    have hux : ‖u i‖ ^ 2 ≤ U * ‖u i‖ := by
      have h := mul_le_mul_of_nonneg_right (hu i) (norm_nonneg (u i))
      nlinarith
    have hdu0 : 0 ≤ ‖du i‖ := norm_nonneg _
    have hdx0 : 0 ≤ ‖dx i‖ := norm_nonneg _
    have hddu0 : 0 ≤ ‖ddu i‖ := norm_nonneg _
    have hddx0 : 0 ≤ ‖ddx i‖ := norm_nonneg _
    have h1 :
        32 * (‖x i‖ + ‖u i‖ ^ 2) * ‖du i‖ ^ 2 ≤
          32 * (X + U ^ 2) * ‖du i‖ ^ 2 := by
      have h := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hxi (sq_nonneg (‖du i‖)))
        (by norm_num : (0 : ℝ) ≤ 32)
      simpa only [mul_assoc] using h
    have h2 :
        64 * ‖u i‖ * ‖du i‖ * ‖dx i‖ ≤
          64 * U * ‖du i‖ * ‖dx i‖ := by
      calc
        64 * ‖u i‖ * ‖du i‖ * ‖dx i‖ =
            64 * (‖u i‖ * (‖du i‖ * ‖dx i‖)) := by ring
        _ ≤ 64 * (U * (‖du i‖ * ‖dx i‖)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hu i) (mul_nonneg hdu0 hdx0))
            (by norm_num : (0 : ℝ) ≤ 64)
        _ = 64 * U * ‖du i‖ * ‖dx i‖ := by ring
    have h3 :
        128 * ‖u i‖ ^ 2 * ‖dx i‖ ^ 2 ≤
          128 * U ^ 2 * ‖dx i‖ ^ 2 := by
      have h := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hu2 (sq_nonneg (‖dx i‖)))
        (by norm_num : (0 : ℝ) ≤ 128)
      simpa only [mul_assoc] using h
    have h4 :
        32 * ‖u i‖ * (‖x i‖ + ‖u i‖ ^ 2) * ‖ddu i‖ ≤
          32 * (X + U ^ 2) * ‖u i‖ * ‖ddu i‖ := by
      calc
        32 * ‖u i‖ * (‖x i‖ + ‖u i‖ ^ 2) * ‖ddu i‖ =
            32 * ((‖x i‖ + ‖u i‖ ^ 2) * (‖u i‖ * ‖ddu i‖)) := by ring
        _ ≤ 32 * ((X + U ^ 2) * (‖u i‖ * ‖ddu i‖)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hxi (mul_nonneg (norm_nonneg _) hddu0))
            (by norm_num : (0 : ℝ) ≤ 32)
        _ = 32 * (X + U ^ 2) * ‖u i‖ * ‖ddu i‖ := by ring
    have h5 :
        32 * ‖u i‖ ^ 2 * ‖ddx i‖ ≤
          32 * U * ‖u i‖ * ‖ddx i‖ := by
      calc
        32 * ‖u i‖ ^ 2 * ‖ddx i‖ =
            32 * (‖u i‖ ^ 2 * ‖ddx i‖) := by ring
        _ ≤ 32 * (U * ‖u i‖ * ‖ddx i‖) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hux hddx0)
            (by norm_num : (0 : ℝ) ≤ 32)
        _ = 32 * U * ‖u i‖ * ‖ddx i‖ := by ring
    calc
      _ ≤ 32 * (‖x i‖ + ‖u i‖ ^ 2) * ‖du i‖ ^ 2 +
          64 * ‖u i‖ * ‖du i‖ * ‖dx i‖ +
          128 * ‖u i‖ ^ 2 * ‖dx i‖ ^ 2 +
          32 * ‖u i‖ * (‖x i‖ + ‖u i‖ ^ 2) * ‖ddu i‖ +
          32 * ‖u i‖ ^ 2 * ‖ddx i‖ := hi
      _ ≤ 32 * (X + U ^ 2) * ‖du i‖ ^ 2 +
          64 * U * ‖du i‖ * ‖dx i‖ +
          128 * U ^ 2 * ‖dx i‖ ^ 2 +
          32 * (X + U ^ 2) * ‖u i‖ * ‖ddu i‖ +
          32 * U * ‖u i‖ * ‖ddx i‖ := by
        nlinarith [h1, h2, h3, h4, h5]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun i _ => hpoint i)
  have hdecomp :
      ∑ i, (32 * (X + U ^ 2) * ‖du i‖ ^ 2 +
          64 * U * ‖du i‖ * ‖dx i‖ +
          128 * U ^ 2 * ‖dx i‖ ^ 2 +
          32 * (X + U ^ 2) * ‖u i‖ * ‖ddu i‖ +
          32 * U * ‖u i‖ * ‖ddx i‖) =
        32 * (X + U ^ 2) * (∑ i, ‖du i‖ ^ 2) +
          64 * U * (∑ i, ‖du i‖ * ‖dx i‖) +
          128 * U ^ 2 * (∑ i, ‖dx i‖ ^ 2) +
          32 * (X + U ^ 2) * (∑ i, ‖u i‖ * ‖ddu i‖) +
          32 * U * (∑ i, ‖u i‖ * ‖ddx i‖) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
  rw [hdecomp] at hsum
  have hc_du_dx := l2_sum_mul_le du dx
  have hc_u_ddu := l2_sum_mul_le u ddu
  have hc_u_ddx := l2_sum_mul_le u ddx
  have hsq_du := l2Norm_sq du
  have hsq_dx := l2Norm_sq dx
  have hcoef : 0 ≤ X + U ^ 2 := add_nonneg hX (sq_nonneg U)
  calc
    ∑ i, ‖Ruu (u i) (x i) * (du i) ^ 2 +
        2 * Rux (u i) (x i) * du i * dx i +
        Rxx (u i) (x i) * (dx i) ^ 2 +
        Ru (u i) (x i) * ddu i + Rx (u i) (x i) * ddx i‖ ≤
      32 * (X + U ^ 2) * (∑ i, ‖du i‖ ^ 2) +
        64 * U * (∑ i, ‖du i‖ * ‖dx i‖) +
        128 * U ^ 2 * (∑ i, ‖dx i‖ ^ 2) +
        32 * (X + U ^ 2) * (∑ i, ‖u i‖ * ‖ddu i‖) +
        32 * U * (∑ i, ‖u i‖ * ‖ddx i‖) := hsum
    _ ≤ 32 * (X + U ^ 2) * l2Norm du ^ 2 +
        64 * U * (l2Norm du * l2Norm dx) +
        128 * U ^ 2 * l2Norm dx ^ 2 +
        32 * (X + U ^ 2) * (l2Norm u * l2Norm ddu) +
        32 * U * (l2Norm u * l2Norm ddx) := by
      rw [hsq_du, hsq_dx]
      have h2 : 0 ≤ U ^ 2 := sq_nonneg U
      have h64U : 0 ≤ (64 : ℝ) * U := mul_nonneg (by norm_num) hU
      have hu1 := mul_le_mul_of_nonneg_left hc_du_dx h64U
      have hu2' := mul_le_mul_of_nonneg_left hc_u_ddu (by positivity : (0 : ℝ) ≤ 32 * (X + U ^ 2))
      have h32U : 0 ≤ (32 : ℝ) * U := mul_nonneg (by norm_num) hU
      have hu3 := mul_le_mul_of_nonneg_left hc_u_ddx h32U
      nlinarith
    _ = 32 * (X + U ^ 2) * l2Norm du ^ 2 +
        64 * U * l2Norm du * l2Norm dx +
        128 * U ^ 2 * l2Norm dx ^ 2 +
        32 * (X + U ^ 2) * l2Norm u * l2Norm ddu +
        32 * U * l2Norm u * l2Norm ddx := by ring

theorem hasDerivAt_sum_R_path {ι : Type*} [Fintype ι]
    {u x : ℝ → ι → ℂ} {du dx : ι → ℂ} {t : ℝ}
    (hu : ∀ i, HasDerivAt (fun s : ℝ => u s i) (du i) t)
    (hx : ∀ i, HasDerivAt (fun s : ℝ => x s i) (dx i) t)
    (hU : ∀ i, ‖u t i‖ ≤ 1 / 4)
    (hX : ∀ i, ‖x t i‖ ≤ 1 / 4) :
    HasDerivAt
      (fun s : ℝ => ∑ i, R (u s i) (x s i))
      (∑ i, (Ru (u t i) (x t i) * du i +
        Rx (u t i) (x t i) * dx i)) t := by
  apply HasDerivAt.fun_sum
  intro i _
  exact hasDerivAt_R_path (hu i) (hx i) (hU i) (hX i)

theorem hasDerivAt_sum_R_velocity {ι : Type*} [Fintype ι]
    {u x du dx : ℝ → ι → ℂ} {ddu ddx : ι → ℂ} {t : ℝ}
    (hu : ∀ i, HasDerivAt (fun s : ℝ => u s i) (du t i) t)
    (hx : ∀ i, HasDerivAt (fun s : ℝ => x s i) (dx t i) t)
    (hdu : ∀ i, HasDerivAt (fun s : ℝ => du s i) (ddu i) t)
    (hdx : ∀ i, HasDerivAt (fun s : ℝ => dx s i) (ddx i) t)
    (hU : ∀ i, ‖u t i‖ ≤ 1 / 4)
    (hX : ∀ i, ‖x t i‖ ≤ 1 / 4) :
    HasDerivAt
      (fun s : ℝ => ∑ i, (Ru (u s i) (x s i) * du s i +
          Rx (u s i) (x s i) * dx s i))
      (∑ i, (Ruu (u t i) (x t i) * (du t i) ^ 2 +
          2 * Rux (u t i) (x t i) * du t i * dx t i +
          Rxx (u t i) (x t i) * (dx t i) ^ 2 +
          Ru (u t i) (x t i) * ddu i +
          Rx (u t i) (x t i) * ddx i)) t := by
  apply HasDerivAt.fun_sum
  intro i _
  exact hasDerivAt_R_velocity (hu i) (hx i) (hdu i) (hdx i) (hU i) (hX i)

end
end StructuralNote.FixedSchurRemainderHessianSum

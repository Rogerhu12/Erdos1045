import Erdos1045.ClosedMatrixSpectral
import Erdos1045.MatrixFrobeniusDirect

/-! Direct matrix-defect transfer uses one-matrix spectral bounds and Gram
perturbation. It does not compare or match two singular-value lists. -/

namespace Erdos1045.MatrixDefect

open scoped BigOperators ComplexOrder Matrix
open LogDefect MatrixStability
noncomputable section

theorem eigenvalue_pos_direct {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (i : Fin n) :
    0 < eigenvalue A i := by
  have hp : 0 < ∏ j, eigenvalue A j := by
    rw [prod_eigenvalue_eq_detSq]
    exact (detSq_pos_iff A).2 hA
  have hi := Finset.prod_ne_zero_iff.mp hp.ne' i (Finset.mem_univ i)
  exact lt_of_le_of_ne (eigenvalue_nonneg A i) hi.symm

theorem det_ne_zero_of_eigenvalue_pos_direct {n : ℕ} (A : Mat n)
    (hA : ∀ i, 0 < eigenvalue A i) : A.det ≠ 0 := by
  apply (detSq_pos_iff A).1
  rw [← prod_eigenvalue_eq_detSq]
  exact Finset.prod_pos fun i _ => hA i

theorem defect_eq_total_direct {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) :
    defect A = total Finset.univ (eigenvalue A) := by
  rw [total_eq_trace_sub_card_sub_log_prod Finset.univ (eigenvalue A)
    (fun i _ => eigenvalue_pos_direct A hA i)]
  rw [sum_eigenvalue_eq_frobSq, prod_eigenvalue_eq_detSq]
  simp [defect]

theorem defect_nonneg_direct {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) : 0 ≤ defect A := by
  rw [defect_eq_total_direct A hA]
  exact total_nonneg Finset.univ _ (fun i _ => eigenvalue_pos_direct A hA i)

theorem eigenvalue_bounds_direct {n : ℕ} (A : Mat n) (hA : A.det ≠ 0)
    {C : ℝ} (hC : defect A ≤ C) (i : Fin n) :
    Real.exp (-C - 1) ≤ eigenvalue A i ∧ eigenvalue A i ≤ 2 * C + 2 := by
  rw [defect_eq_total_direct A hA] at hC
  exact coordinate_bounds_of_total_le Finset.univ _
    (fun j _ => eigenvalue_pos_direct A hA j) hC (Finset.mem_univ i)

theorem gram_deviation_bound_direct {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) :
    frobSq (gram A - 1) ≤ (4 * defect A + 6) * defect A := by
  rw [gram_deviation_eq, defect_eq_total_direct A hA]
  exact deviation_le_self_bound Finset.univ _ (fun i _ => eigenvalue_pos_direct A hA i)

theorem eigenvalue_conjTranspose_direct {n : ℕ} (A : Mat n) :
    eigenvalue A.conjTranspose = eigenvalue A := by
  unfold eigenvalue
  apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).2
  simp only [Matrix.conjTranspose_conjTranspose]
  exact Matrix.charpoly_mul_comm _ _

theorem gram_sub_scalar_posSemidef {n : ℕ} (A : Mat n) {a : ℝ}
    (ha : ∀ i, a ≤ eigenvalue A i) :
    (gram A - (a : ℂ) • (1 : Mat n)).PosSemidef := by
  let hA := Matrix.isHermitian_conjTranspose_mul_self A
  let e := Unitary.conjStarAlgAut ℂ (Mat n) hA.eigenvectorUnitary
  let D : Mat n := Matrix.diagonal (fun i => (eigenvalue A i : ℂ))
  have hG : gram A = e D := hA.spectral_theorem
  have hsub : gram A - (a : ℂ) • (1 : Mat n) = e (D - (a : ℂ) • 1) := by
    rw [map_sub, map_smul, map_one, ← hG]
  have hd : D - (a : ℂ) • (1 : Mat n) =
      Matrix.diagonal (fun i => ((eigenvalue A i - a : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [D, hij]
  rw [hsub]
  change ((hA.eigenvectorUnitary : Mat n) * _ * star (hA.eigenvectorUnitary : Mat n)).PosSemidef
  apply (Matrix.IsUnit.posSemidef_star_right_conjugate_iff
    (show IsUnit (hA.eigenvectorUnitary : Mat n) from Unitary.isUnit_coe)).2
  rw [hd, Matrix.posSemidef_diagonal_iff]
  intro i
  exact_mod_cast sub_nonneg.mpr (ha i)

theorem re_star_dotProduct_self {n : ℕ} (x : Fin n → ℂ) :
    (star x ⬝ᵥ x).re = vectorEnergy x := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.re_sum, Complex.ofReal_re, vectorEnergy]

theorem gram_quadratic_eq_vectorEnergy {n : ℕ} (A : Mat n) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (gram A *ᵥ x)).re = vectorEnergy (A *ᵥ x) := by
  rw [gram, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    re_star_dotProduct_self]

theorem vectorEnergy_lower_of_eigenvalue_lower {n : ℕ} (A : Mat n) {a : ℝ}
    (ha : ∀ i, a ≤ eigenvalue A i) (x : Fin n → ℂ) :
    a * vectorEnergy x ≤ vectorEnergy (A *ᵥ x) := by
  have h := (gram_sub_scalar_posSemidef A ha).re_dotProduct_nonneg x
  change 0 ≤ (star x ⬝ᵥ ((gram A - (a : ℂ) • (1 : Mat n)) *ᵥ x)).re at h
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  rw [gram_quadratic_eq_vectorEnergy, re_star_dotProduct_self] at h
  linarith

theorem eigenvector_vectorEnergy_one {n : ℕ} (A : Mat n) (i : Fin n) :
    vectorEnergy ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorBasis i) = 1 := by
  let x := (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorBasis i
  have hx : ‖x‖ = 1 := (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorBasis.orthonormal.1 i
  have he := EuclideanSpace.norm_sq_eq x
  rw [hx, one_pow] at he
  simpa only [vectorEnergy, Complex.normSq_eq_norm_sq] using he.symm

theorem eigenvector_gram_energy {n : ℕ} (A : Mat n) (i : Fin n) :
    vectorEnergy (A *ᵥ (Matrix.isHermitian_conjTranspose_mul_self A).eigenvectorBasis i) =
      eigenvalue A i := by
  rw [← gram_quadratic_eq_vectorEnergy]
  exact (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues_eq i |>.symm

/-- A one-vector Rayleigh argument gives invertibility of the perturbed matrix;
there is no matching of eigenvalues belonging to different matrices. -/
theorem eigenvalue_lower_of_small_frob {n : ℕ} (A V : Mat n) (hA : A.det ≠ 0)
    {C : ℝ} (hC : defect A ≤ C) (hsmall : frobSq (A - V) ≤ lowerScale C)
    (i : Fin n) : lowerScale C ≤ eigenvalue V i := by
  let x : Fin n → ℂ := (Matrix.isHermitian_conjTranspose_mul_self V).eigenvectorBasis i
  have hx : vectorEnergy x = 1 := eigenvector_vectorEnergy_one V i
  have hAx := vectorEnergy_lower_of_eigenvalue_lower A
    (fun j => (eigenvalue_bounds_direct A hA hC j).1) x
  have he := vectorEnergy_mulVec_le (A - V) x
  have hsum := vectorEnergy_add_le (V *ᵥ x) ((A - V) *ᵥ x)
  have hadd : (V *ᵥ x) + ((A - V) *ᵥ x) = A *ᵥ x := by
    rw [← Matrix.add_mulVec]
    congr 1
    abel
  rw [hadd, show vectorEnergy (V *ᵥ x) = eigenvalue V i from
    eigenvector_gram_energy V i] at hsum
  rw [hx, mul_one] at hAx he
  unfold lowerScale at hsmall ⊢
  linarith

theorem eigenvalue_le_frobSq {n : ℕ} (A : Mat n) (i : Fin n) :
    eigenvalue A i ≤ frobSq A := by
  rw [← sum_eigenvalue_eq_frobSq]
  exact Finset.single_le_sum (fun j _ => eigenvalue_nonneg A j) (Finset.mem_univ i)

theorem gram_frobSq_le_sq {n : ℕ} (E : Mat n) : frobSq (gram E) ≤ frobSq E ^ 2 := by
  have h := frobSq_mul_le_of_eigenvalue_le E.conjTranspose E (b := frobSq E)
    (fun i => by rw [eigenvalue_conjTranspose_direct]; exact eigenvalue_le_frobSq E i)
  simpa [gram, pow_two] using h

theorem gram_perturbation_bound {n : ℕ} (A V : Mat n) {b : ℝ}
    (hb : ∀ i, eigenvalue A i ≤ b) (hone : frobSq (A - V) ≤ 1) :
    frobSq (gram V - gram A) ≤ (8 * b + 2) * frobSq (A - V) := by
  let E := A - V
  let X := A.conjTranspose * E
  have hX : frobSq X ≤ b * frobSq E :=
    frobSq_mul_le_of_eigenvalue_le A.conjTranspose E
      (fun i => by rw [eigenvalue_conjTranspose_direct]; exact hb i)
  have hid : gram V - gram A = -(X + X.conjTranspose) + gram E := by
    dsimp [X, E, gram]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_sub]
    noncomm_ring
  have h₁ := frobSq_add_le (-(X + X.conjTranspose)) (gram E)
  have h₂ := frobSq_add_le X X.conjTranspose
  have h₃ := gram_frobSq_le_sq E
  have he0 := frobSq_nonneg E
  have he1 : frobSq E ≤ 1 := hone
  rw [hid]
  simp only [frobSq_neg, frobSq_conjTranspose] at h₁ h₂
  nlinarith [mul_nonneg he0 (sub_nonneg.mpr he1)]

def directStabilityConstant (C : ℝ) : ℝ := (32 * C + 36) / lowerScale C

theorem directStabilityConstant_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ directStabilityConstant C := by
  unfold directStabilityConstant
  exact div_nonneg (by linarith) (lowerScale_pos C).le

/-- The dimension-independent nonlinear transfer is proved by Gram perturbation,
Rayleigh lower bounds, and the scalar logarithmic inequality. -/
theorem direct_transfer {n : ℕ} (A V : Mat n) (hA : A.det ≠ 0)
    {C : ℝ} (hC : defect A ≤ C)
    (hsmall : frobSq (A - V) ≤ lowerScale C) (hone : frobSq (A - V) ≤ 1) :
    V.det ≠ 0 ∧ 0 ≤ defect V ∧
      defect V ≤ directStabilityConstant C * (defect A + frobSq (A - V)) := by
  have hlow := eigenvalue_lower_of_small_frob A V hA hC hsmall
  have hVpos (i : Fin n) : 0 < eigenvalue V i := (lowerScale_pos C).trans_le (hlow i)
  have hV := det_ne_zero_of_eigenvalue_pos_direct V hVpos
  have hD := defect_nonneg_direct A hA
  have hC0 := hD.trans hC
  refine ⟨hV, defect_nonneg_direct V hV, ?_⟩
  have hchi : defect V ≤ frobSq (gram V - 1) / lowerScale C := by
    rw [defect_eq_total_direct V hV, gram_deviation_eq, total, deviation,
      Finset.sum_div]
    exact Finset.sum_le_sum (fun i _ => chi_le_sub_one_sq_div_lower (lowerScale_pos C) (hlow i))
  have hdiff := gram_perturbation_bound A V
    (fun i => (eigenvalue_bounds_direct A hA hC i).2) hone
  have hG := gram_deviation_bound_direct A hA
  have hadd : gram V - 1 = (gram A - 1) + (gram V - gram A) := by abel
  have htri := frobSq_add_le (gram A - 1) (gram V - gram A)
  rw [← hadd] at htri
  have hbound : frobSq (gram V - 1) ≤
      (32 * C + 36) * (defect A + frobSq (A - V)) := by
    have hCD := mul_le_mul_of_nonneg_right hC hD
    have hCD0 := mul_nonneg hC0 hD
    nlinarith [frobSq_nonneg (A - V)]
  exact hchi.trans ((div_le_div_of_nonneg_right hbound (lowerScale_pos C).le).trans_eq
    (by unfold directStabilityConstant; ring))

end
end Erdos1045.MatrixDefect

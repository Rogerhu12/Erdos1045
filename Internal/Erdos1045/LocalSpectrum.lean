import Erdos1045.LocalTrigonometry
import Erdos1045.LocalPairing
import Erdos1045.LocalFourier
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The actual sine spectrum and the uniform Hessian bound

The paired index is `r=k-1`, and its involution is `r ↦ n-r`. Every numerical
coefficient condition is proved from the explicit trigonometric definitions.
No assertion of local maximality or Hessian positivity is an input.
-/

namespace Erdos1045.LocalSpectrum

open Complex
open scoped BigOperators
noncomputable section

abbrev PairedModes (n : ℕ) := ↥(Finset.Ico 2 (n - 1))

def pairedPartner {n : ℕ} (i : PairedModes n) : PairedModes n :=
  ⟨n - i.val, by have hi := i.property; simp only [Finset.mem_Ico] at hi ⊢; omega⟩

theorem pairedPartner_involutive (n : ℕ) :
    Function.Involutive (pairedPartner (n := n)) := by
  intro i
  apply Subtype.ext
  have hi := i.property
  simp only [Finset.mem_Ico] at hi
  change n - (n - i.val) = i.val
  omega

theorem partner_agrees {n : ℕ} (i : PairedModes n) :
    LocalFourier.partner n i.val = (pairedPartner i).val := by
  have hi := i.property
  simp only [Finset.mem_Ico] at hi
  simp [LocalFourier.partner, pairedPartner, show i.val ≠ 0 by omega]

def sine {n : ℕ} (i : PairedModes n) : ℝ :=
  LocalTrigonometry.mode (n : ℝ) (i.val + 1 : ℝ)

def ratio {n : ℕ} (i : PairedModes n) : ℝ :=
  LocalTrigonometry.pairRatio (n : ℝ) (i.val + 1 : ℝ)

def weight {n : ℕ} (i : PairedModes n) : ℝ :=
  LocalTrigonometry.leftWeight (n : ℝ) (i.val + 1 : ℝ)

def amplitude {n : ℕ} (b : ℕ → ℂ) (i : PairedModes n) : ℂ :=
  (sine i : ℂ) * b i.val

theorem index_real_bounds {n : ℕ} (i : PairedModes n) :
    (3 : ℝ) ≤ (i.val : ℝ) + 1 ∧ (i.val : ℝ) + 1 ≤ (n : ℝ) - 1 := by
  have hi := i.property
  simp only [Finset.mem_Ico] at hi
  constructor
  · exact_mod_cast (show 3 ≤ i.val + 1 by omega)
  · have h : (i.val : ℝ) + 2 ≤ (n : ℝ) := by
      exact_mod_cast (show i.val + 2 ≤ n by omega)
    linarith

theorem sine_pos {n : ℕ} (hn : 4 ≤ n) (i : PairedModes n) : 0 < sine i := by
  have hi := index_real_bounds i
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  exact LocalTrigonometry.mode_pos (by linarith) (by linarith) (by linarith)

theorem partner_real_index {n : ℕ} (i : PairedModes n) :
    ((pairedPartner i).val : ℝ) + 1 = (n : ℝ) + 2 - ((i.val : ℝ) + 1) := by
  have hi := i.property
  simp only [Finset.mem_Ico] at hi
  change ((n - i.val : ℕ) : ℝ) + 1 = _
  rw [Nat.cast_sub (show i.val ≤ n by omega)]
  ring

theorem sine_partner {n : ℕ} (hn : 4 ≤ n) (i : PairedModes n) :
    sine (pairedPartner i) = LocalTrigonometry.mode (n : ℝ) ((i.val : ℝ) + 1 - 2) := by
  unfold sine
  rw [partner_real_index, LocalTrigonometry.paired_mode_eq]
  exact_mod_cast (show n ≠ 0 by omega)

theorem ratio_partner {n : ℕ} (hn : 4 ≤ n) (i : PairedModes n) :
    ratio (pairedPartner i) = ratio i := by
  unfold ratio
  rw [partner_real_index, LocalTrigonometry.pairRatio_reflect]
  exact_mod_cast (show n ≠ 0 by omega)

theorem coefficient_bounds {n : ℕ} (hn : 4 ≤ n) (i : PairedModes n) :
    0 < ratio i ∧ ratio i ≤ (5 / 6 : ℝ) * ((n : ℝ) - 1) ∧ weight i ≤ 9 * ratio i := by
  have hi := index_real_bounds i
  exact LocalTrigonometry.all_mode_bounds (by exact_mod_cast hn) hi.1 hi.2

theorem amplitude_normSq {n : ℕ} (b : ℕ → ℂ) (i : PairedModes n) :
    normSq (amplitude b i) = sine i ^ 2 * normSq (b i.val) := by
  simp [amplitude, normSq_mul, normSq_ofReal, pow_two]

theorem amplitude_cross_re {n : ℕ} (b : ℕ → ℂ) (i : PairedModes n) :
    (amplitude b i * amplitude b (pairedPartner i)).re =
      (sine i * sine (pairedPartner i)) * (b i.val * b (pairedPartner i).val).re := by
  simp [amplitude, mul_re, mul_im]
  ring

theorem weighted_amplitude {n : ℕ} (hn : 4 ≤ n) (b : ℕ → ℂ) (i : PairedModes n) :
    weight i * normSq (amplitude b i) =
      ((i.val : ℝ) + 1) * ((n : ℝ) - ((i.val : ℝ) + 1)) * normSq (b i.val) := by
  rw [amplitude_normSq]
  unfold weight LocalTrigonometry.leftWeight
  change _ / sine i ^ 2 * (sine i ^ 2 * _) = _
  have hs : sine i ≠ 0 := (sine_pos hn i).ne'
  field_simp

theorem ratio_amplitude_cross {n : ℕ} (hn : 4 ≤ n) (b : ℕ → ℂ) (i : PairedModes n) :
    ratio i * (amplitude b i * amplitude b (pairedPartner i)).re =
      ((i.val : ℝ) - 1) * ((n : ℝ) - ((i.val : ℝ) + 1)) *
        (b i.val * b (pairedPartner i).val).re := by
  rw [amplitude_cross_re]
  have hs : sine i ≠ 0 := (sine_pos hn i).ne'
  have hp : sine (pairedPartner i) ≠ 0 := (sine_pos hn (pairedPartner i)).ne'
  unfold ratio LocalTrigonometry.pairRatio
  rw [← sine_partner hn]
  change _ / (sine i * sine (pairedPartner i)) * _ = _
  field_simp
  ring

/-- The complete paired-mode coercivity, with the paper's actual coefficients. -/
theorem paired_spectral_coercivity {n : ℕ} (hn : 4 ≤ n) (b : ℕ → ℂ) :
    (LocalPairing.energyA (n : ℝ) weight (amplitude (n := n) b) +
        (n : ℝ) * LocalPairing.energyB (n : ℝ) pairedPartner (amplitude (n := n) b)) / 64 ≤
      LocalPairing.quadratic (n : ℝ) pairedPartner ratio (amplitude (n := n) b) := by
  exact LocalPairing.spectral_coercivity (by exact_mod_cast hn)
    pairedPartner (pairedPartner_involutive n) ratio weight (amplitude b)
    (fun i => (coefficient_bounds hn i).1.le)
    (fun i => (coefficient_bounds hn i).2.1) (ratio_partner hn)
    (fun i => (coefficient_bounds hn i).2.2)

/-- The isolated second mode, using its actual sine ratio. -/
theorem isolated_spectral_coercivity {n : ℕ} (hn : 4 ≤ n) (b : ℂ) :
    ((n : ℝ) * ((n : ℝ) - 2) * normSq b +
        (n : ℝ) ^ 2 / 2 * LocalTrigonometry.mode (n : ℝ) 2 ^ 2 * normSq b) / 64 ≤
      (n : ℝ) * ((n : ℝ) - 1) / 4 * LocalTrigonometry.mode (n : ℝ) 2 ^ 2 * normSq b := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have he := LocalPairing.isolated_mode_coercivity (by linarith : (3 : ℝ) ≤ n)
    (LocalTrigonometry.second_mode_ge_one hnR) (normSq_nonneg b)
  have hnonneg : 0 ≤ (n : ℝ) * ((n : ℝ) - 2) * normSq b +
      (n : ℝ) ^ 2 / 2 * LocalTrigonometry.mode (n : ℝ) 2 ^ 2 * normSq b := by
    have hn2 : 0 ≤ (n : ℝ) - 2 := by linarith
    have hnorm := normSq_nonneg b
    positivity
  linarith

/-- Splitting the two normalized-away modes and the isolated second mode. -/
theorem sum_modes {R : Type*} [AddCommGroup R] {n : ℕ} (hn : 4 ≤ n)
    (f : ℕ → R) (hzero : f 0 = 0) (hlast : f (n - 1) = 0) :
    (∑ r ∈ Finset.range n, f r) = f 1 + ∑ i : PairedModes n, f i.val := by
  have hI := Finset.sum_Ico_eq_sub f (show 2 ≤ n - 1 by omega)
  have htotal : (∑ r ∈ Finset.range n, f r) =
      (∑ r ∈ Finset.range (n - 1), f r) + f (n - 1) := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using
      Finset.sum_range_succ f (n - 1)
  have htwo : (∑ r ∈ Finset.range 2, f r) = f 0 + f 1 := by
    simp [Finset.sum_range_succ]
  rw [Finset.sum_coe_sort, hI, htotal, hlast, htwo, hzero]
  abel

def fullAmplitude (n : ℕ) (b : ℕ → ℂ) (r : ℕ) : ℂ :=
  (LocalTrigonometry.mode (n : ℝ) (r + 1 : ℝ) : ℂ) * b r

def fullA (n : ℕ) (b : ℕ → ℂ) : ℝ :=
  (n : ℝ) / 2 * ∑ r ∈ Finset.range n,
    ((r : ℝ) + 1) * ((n : ℝ) - ((r : ℝ) + 1)) * normSq (b r)

def fullB (n : ℕ) (b : ℕ → ℂ) : ℝ :=
  (n : ℝ) / 2 *
    ((∑ r ∈ Finset.range n, normSq (fullAmplitude n b r)) +
      ∑ r ∈ Finset.range n,
        (fullAmplitude n b r * fullAmplitude n b (LocalFourier.partner n r)).re)

def fullQ (n : ℕ) (b : ℕ → ℂ) : ℝ :=
  -(n : ℝ) / 2 * (∑ r ∈ Finset.range n,
    ((r : ℝ) - 1) * ((n : ℝ) - ((r : ℝ) + 1)) *
      (b r * b (LocalFourier.partner n r)).re) + ((n : ℝ) - 1) / 2 * fullB n b

theorem fullA_split {n : ℕ} (hn : 4 ≤ n) (b : ℕ → ℂ)
    (hzero : b 0 = 0) (hlast : b (n - 1) = 0) :
    fullA n b = (n : ℝ) * ((n : ℝ) - 2) * normSq (b 1) +
      LocalPairing.energyA (n : ℝ) weight (amplitude (n := n) b) := by
  unfold fullA
  rw [sum_modes hn _ (by simp [hzero]) (by simp [hlast])]
  have hi : (∑ i : PairedModes n,
      ((i.val : ℝ) + 1) * ((n : ℝ) - ((i.val : ℝ) + 1)) * normSq (b i.val)) =
      ∑ i : PairedModes n, weight i * normSq (amplitude b i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact (weighted_amplitude hn b i).symm
  rw [hi]
  unfold LocalPairing.energyA
  norm_num
  ring

theorem fullB_split {n : ℕ} (hn : 4 ≤ n) (b : ℕ → ℂ)
    (hzero : b 0 = 0) (hlast : b (n - 1) = 0) :
    fullB n b = (n : ℝ) / 2 * LocalTrigonometry.mode (n : ℝ) 2 ^ 2 * normSq (b 1) +
      LocalPairing.energyB (n : ℝ) pairedPartner (amplitude (n := n) b) := by
  have ha0 : fullAmplitude n b 0 = 0 := by simp [fullAmplitude, hzero]
  have halast : fullAmplitude n b (n - 1) = 0 := by simp [fullAmplitude, hlast]
  have hp1 : LocalFourier.partner n 1 = n - 1 := by simp [LocalFourier.partner]
  unfold fullB
  rw [sum_modes hn _ (by simp [ha0]) (by simp [halast])]
  rw [sum_modes hn _ (by simp [ha0]) (by simp [halast])]
  rw [hp1, halast]
  have hnorm : normSq (fullAmplitude n b 1) =
      LocalTrigonometry.mode (n : ℝ) 2 ^ 2 * normSq (b 1) := by
    simp [fullAmplitude, normSq_mul, normSq_ofReal, pow_two]
    norm_num
  rw [hnorm]
  simp only [mul_zero, zero_re, zero_add]
  have hcross : (∑ i : PairedModes n,
      (fullAmplitude n b i.val * fullAmplitude n b (LocalFourier.partner n i.val)).re) =
      (∑ i : PairedModes n, amplitude b i * amplitude b (pairedPartner i)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [partner_agrees]
    rfl
  rw [hcross]
  change _ = _ + (n : ℝ) / 2 *
    ((∑ i : PairedModes n, normSq (fullAmplitude n b i.val)) + _)
  ring

theorem fullQ_split {n : ℕ} (hn : 4 ≤ n) (b : ℕ → ℂ)
    (hzero : b 0 = 0) (hlast : b (n - 1) = 0) :
    fullQ n b = (n : ℝ) * ((n : ℝ) - 1) / 4 *
        LocalTrigonometry.mode (n : ℝ) 2 ^ 2 * normSq (b 1) +
      LocalPairing.quadratic (n : ℝ) pairedPartner ratio (amplitude (n := n) b) := by
  unfold fullQ
  rw [sum_modes hn _ (by simp [hzero]) (by simp [hlast]), fullB_split hn b hzero hlast]
  have hi : (∑ i : PairedModes n,
      ((i.val : ℝ) - 1) * ((n : ℝ) - ((i.val : ℝ) + 1)) *
        (b i.val * b (LocalFourier.partner n i.val)).re) =
      ∑ i : PairedModes n, ratio i * (amplitude b i * amplitude b (pairedPartner i)).re := by
    apply Finset.sum_congr rfl
    intro i _
    rw [partner_agrees]
    exact (ratio_amplitude_cross hn b i).symm
  rw [hi, LocalPairing.quadratic_eq_cross_form]
  norm_num
  ring

/-- Uniform inequality (6.5), for the complete actual finite sine spectrum.
The assumptions merely remove the translation and similarity modes. -/
theorem full_spectral_coercivity {n : ℕ} (hn : 4 ≤ n) (b : ℕ → ℂ)
    (hzero : b 0 = 0) (hlast : b (n - 1) = 0) :
    (fullA n b + (n : ℝ) * fullB n b) / 64 ≤ fullQ n b := by
  rw [fullA_split hn b hzero hlast, fullB_split hn b hzero hlast,
    fullQ_split hn b hzero hlast]
  have hp := paired_spectral_coercivity hn b
  have hi := isolated_spectral_coercivity hn (b 1)
  nlinarith

end

end Erdos1045.LocalSpectrum

import EventualExact.AllOrderFine

/-! Every sufficiently large perimeter extremizer is regular, without a parity restriction. -/

namespace Erdos1045.EventualExact.AllOrderPerimeter

open Configuration HullGeometry ExteriorClassical GlobalProof CoarseFekete Filter
open scoped Topology
noncomputable section

/-- The original exterior ordering retains its proved boundary-perimeter bound. -/
theorem family_eventually_regular (s : Family)
    (hmax : ∀ j, PerimeterExtremal (s.size j) (s.points j)) :
    ∀ᶠ j in atTop, Configuration.IsRegular (s.points j) := by
  let B := classicalBackground_proved.toClassicalAnalysis
  obtain ⟨C, K, D, hC, hK, hD, hb⟩ := s.coarse_control B
  exact ExteriorLocalBridge.eventually_regular_of_eventual_bounds
    B.geometry ClosedSeries.laurentAnalysis ClosedFourier.dftInversion
    ClosedFourier.geometricSine LocalNonlinear.scalarLogTaylor
    s.size_ge s.size_tendsto s.points hmax s.data
    (fun j => ClosedFourier.orthogonality (s.size j) (by have := s.size_ge j; omega))
    (s.circleEnergy_tendsto_zero B hmax) (hb.mono fun _ h => h.1) K
    (hb.mono fun _ h => h.2.2.1)

theorem perimeter_sequence_eventually_regular {N : ℕ → ℕ}
    (hN4 : ∀ j, 4 ≤ N j) (hN : Tendsto N atTop atTop) (z : ∀ j, Points (N j))
    (hz : ∀ j, PerimeterExtremal (N j) (z j)) :
    ∀ᶠ j in atTop, Configuration.IsRegular (z j) := by
  classical
  let B := classicalBackground_proved.toClassicalAnalysis
  have hmodel (j : ℕ) : ∃ σ : Equiv.Perm (Fin (N j)), Nonempty
      {d : ExteriorData (z j ∘ σ) // FaberIdentities d} :=
    classicalBackground_proved.exterior.model (N j) (by have := hN4 j; omega) (z j)
      (perimeterExtremal_injective B.geometry (by have := hN4 j; omega) (hz j))
      (perimeterExtremal_perimeter_eq B.geometry (by have := hN4 j; omega) (hz j))
      (fun w hw => perimeterExtremal_dominates_hull B.geometry (hz j) w hw)
  choose σ hdata using hmodel
  let chosen (j : ℕ) := Classical.choice (hdata j)
  have hmax (j : ℕ) : PerimeterExtremal (N j) (z j ∘ σ j) :=
    perimeterExtremal_perm B.geometry (hz j) (σ j)
  let s : Family :=
    { size := N
      size_ge := hN4
      size_tendsto := hN
      points := fun j => z j ∘ σ j
      injective := fun j => perimeterExtremal_injective B.geometry (by have := hN4 j; omega) (hmax j)
      fekete := fun j w hw => perimeterExtremal_dominates_hull B.geometry (hmax j) w hw
      discriminant_ge := fun j =>
        perimeterExtremal_discriminant_ge B.geometry (by have := hN4 j; omega) (hmax j)
      data := fun j => (chosen j).val
      identities := fun j => (chosen j).property }
  exact (family_eventually_regular s hmax).mono fun j hj =>
    isRegular_of_perm (z j) (σ j) hj

/-- Uniform eventual uniqueness modulo similarity and relabeling. -/
theorem large_perimeter_extremizers_regular :
    ∃ M : ℕ, 4 ≤ M ∧ ∀ n : ℕ, M ≤ n →
      ∀ z : Points n, PerimeterExtremal n z → Configuration.IsRegular z := by
  classical
  by_contra! hbad
  have hchoose (j : ℕ) : ∃ n : ℕ, max 4 j ≤ n ∧
      ∃ z : Points n, PerimeterExtremal n z ∧ ¬ Configuration.IsRegular z :=
    hbad (max 4 j) (le_max_left _ _)
  choose N hN z hz hnonreg using hchoose
  have hN4 (j : ℕ) : 4 ≤ N j := (le_max_left _ _).trans (hN j)
  have hNj (j : ℕ) : j ≤ N j := (le_max_right _ _).trans (hN j)
  have hNtop : Tendsto N atTop atTop := tendsto_atTop_mono hNj tendsto_id
  obtain ⟨j, hj⟩ := (perimeter_sequence_eventually_regular hN4 hNtop z hz).exists
  exact hnonreg j hj

theorem large_perimeter_maximum_attained_regular :
    ∃ M : ℕ, 4 ≤ M ∧ ∀ n : ℕ, M ≤ n →
      (∃ z : Points n, PerimeterExtremal n z) ∧
      ∀ z : Points n, PerimeterExtremal n z → Configuration.IsRegular z := by
  obtain ⟨M, hM, h⟩ := large_perimeter_extremizers_regular
  refine ⟨M, hM, fun n hn => ⟨?_, h n hn⟩⟩
  exact exists_perimeterExtremal classicalBackground_proved.toClassicalAnalysis.geometry (by omega)

end
end Erdos1045.EventualExact.AllOrderPerimeter

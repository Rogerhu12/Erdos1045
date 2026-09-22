import Erdos1045.Internal.Maxima
import Erdos1045.Internal.KKT
import Erdos1045.ExplicitProof
import Erdos1045.ExplicitRegularProof

/-! The five public conclusions, stated at their proved thresholds. -/

namespace Erdos1045

theorem diameter_characterization : Statement.DiameterCharacterization := by
  intro n hn
  by_cases hodd : Odd n
  · have hN : Statement.regularThreshold ≤ n := by
      simpa only [Statement.diameterThreshold, if_pos hodd] using hn
    obtain ⟨hvalue, hexists, hregular, hunique⟩ := explicit_odd n hN hodd
    refine ⟨hexists, hunique, fun _ => ⟨hvalue, hregular⟩, ?_⟩
    intro m hnm
    rcases hodd with ⟨k, hk⟩
    omega
  · obtain ⟨m, hm⟩ := (Nat.even_or_odd n).resolve_right hodd
    have hnm : n = 2 * m := by omega
    clear hm
    subst n
    have hN : Statement.evenThreshold ≤ 2 * m := by
      simpa only [Statement.diameterThreshold, if_neg hodd] using hn
    obtain ⟨hexists, hunique, hgeometry, ⟨cert⟩⟩ := explicit_even m hN
    have hm3 := cert.large
    have hatt := StructuralNote.RewrittenMaxima.diameterExtremal_iff_attains
      (show 0 < 2 * m by omega)
    refine ⟨?_, ?_, fun ho => (hodd ho).elim, ?_⟩
    · obtain ⟨z, hz⟩ := hexists
      exact ⟨z, (hatt z).1 hz⟩
    · intro z w hz hDz hw hDw
      exact hunique z w ((hatt z).2 ⟨hz, hDz⟩) ((hatt w).2 ⟨hw, hDw⟩)
    · intro k hk z hz
      have hkm : k = m := by omega
      subst k
      exact hgeometry z hz

theorem algebraic_certificate : Statement.Algebraic.CertificateAboveThreshold :=
  fun m hn => (explicit_even m hn).2.2.2

/-- The diameter and perimeter characterizations, parity limits, algebraic
certificate and positive KKT theorem. Each finite-order conclusion carries
its proved threshold directly. -/
theorem main : Statement.Claims :=
  ⟨diameter_characterization, explicit_perimeter, Statement.normalized_limits,
    algebraic_certificate, Statement.KKT.unique_positive_kkt⟩

end Erdos1045

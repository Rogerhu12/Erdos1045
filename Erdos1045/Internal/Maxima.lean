import Erdos1045.Statement
import StructuralNote.RewrittenMain

open StructuralNote

/-! Proof adapters for the Mathlib-only public perimeter and limit statements. -/

namespace Erdos1045.Statement

theorem normalized_limits : NormalizedLimits :=
  RewrittenMain.normalized_limits

end Erdos1045.Statement

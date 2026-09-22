import Lean

/-!
Local diagnostic: compare the exact constant graph of the advertised statement
in separate compiled environments. This is not Comparator's exported-proof
replay and does not replace NanoDa or its sandbox. The recursive comparison
criterion follows Comparator.Compare (Lean FRO, Apache-2.0).
-/

open Lean
deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstantInfo

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← importModules #[{ module := `Challenge }] {}
  let solution ← importModules #[{ module := `Solution }] {}
  let explicitDefinitions : Array Name := #[
    `Erdos1045.Statement.evenThreshold,
    `Erdos1045.Statement.regularThreshold,
    `Erdos1045.Statement.diameterThreshold,
    `Erdos1045.Statement.DiameterCharacterization,
    `Erdos1045.Statement.PerimeterCharacterization,
    `Erdos1045.Statement.Algebraic.CertificateAboveThreshold,
    `Erdos1045.Statement.KKT.UniquePositiveKKT]
  for name in explicitDefinitions do
    let some a := challenge.find? name
      | throw <| IO.userError s!"Explicit definition missing from Challenge: {name}"
    let some b := solution.find? name
      | throw <| IO.userError s!"Explicit definition missing from Solution: {name}"
    unless a == b do
      throw <| IO.userError s!"Explicit definition differs: {name}"
  IO.println s!"EXPLICIT_SURFACE_DEFINITIONS_MATCH_PASS: {explicitDefinitions.size} definitions"
  let target := `Erdos1045.main
  let some cc := challenge.find? target
    | throw <| IO.userError "Public theorem missing from Challenge"
  let some sc := solution.find? target
    | throw <| IO.userError "Public theorem missing from Solution"
  unless cc.isTheorem && sc.isTheorem && cc.type == sc.type && cc.levelParams == sc.levelParams do
    throw <| IO.userError "Public theorem types do not match"
  let mut work := cc.type.getUsedConstants
  let mut seen : Std.HashSet Name := {}
  while !work.isEmpty do
    let name := work.back!
    work := work.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some a := challenge.find? name
      | throw <| IO.userError s!"Challenge is missing {name}"
    let some b := solution.find? name
      | throw <| IO.userError s!"Solution is missing {name}"
    unless a == b do
      throw <| IO.userError s!"Statement dependency differs: {name}"
    work := work ++ a.type.getUsedConstants
    if let some value := a.value? (allowOpaque := true) then
      work := work ++ value.getUsedConstants
    if let .inductInfo info := a then
      work := work ++ info.ctors.toArray
  IO.println s!"STATEMENT_GRAPH_MATCH_PASS: {seen.size} dependency constants"

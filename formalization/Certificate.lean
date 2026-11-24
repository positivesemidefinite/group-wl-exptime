import GroupWL.AllAxioms

/-! Build-time check of the main declaration and its exact closed type.
Importing GroupWL.AllAxioms first runs the audit of the project declarations. -/

run_cmd do
  let env ← Lean.getEnv
  let some (.thmInfo proof) := env.find? `GroupWL.Statement.manuscriptClaim_proved
    | throwError "Missing theorem GroupWL.Statement.manuscriptClaim_proved"
  unless proof.levelParams.isEmpty && proof.type == Lean.mkConst `GroupWL.Statement.ManuscriptClaim do
    throwError "The declaration does not have the expected closed type"

#print axioms GroupWL.Statement.manuscriptClaim_proved

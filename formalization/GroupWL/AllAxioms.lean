import GroupWL
import Lean.Util.CollectAxioms

/-! Audit every declaration in the project namespace, including definitions
and generated auxiliary proofs. An unexpected logical axiom is a build error. -/
set_option maxHeartbeats 0

run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (name, _) in env.constants.toList do
    if (`GroupWL).isPrefixOf name || name.toString.startsWith "_private.GroupWL." then
      let axioms ← Lean.collectAxioms name
      for a in axioms do
        unless allowed.contains a do
          throwError "Unexpected axiom {a} in {name}"
      checked := checked+1
  Lean.logInfo m!"Audited {checked} GroupWL declarations: only propext, Classical.choice, Quot.sound."

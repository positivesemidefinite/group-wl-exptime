# EXPTIME-completeness of group Weisfeiler–Leman identification and equivalence

For every fixed odd prime `p`, all three versions of group Weisfeiler–Leman refinement have the following two EXPTIME-complete decision problems. The dimension `k ≥ 1` is part of the input, in binary or unary. A group on the input is given by all coefficients of an alternating bilinear map over the field of order `p`.

- **Identification.** Does `k`-WL distinguish the given group from every nonisomorphic finite group? Hardness holds on class-two groups of exponent `p` with center equal to the commutator subgroup.
- **Equivalence.** Do two given groups have the same WL colors with the same multiplicities? The hardness reduction produces nonisomorphic pairs on every input.

Completeness uses deterministic polynomial-time many-one reductions on bit strings. Dimensions in a tensor description are recorded in unary. The bases describe the input and do not name elements in the WL game. Versions I and II extend joint replacement-vector refinement to dimension one. Version III uses graph WL on the multiplication gadget and compares colors on tuples of group elements, with ordinary neighbor refinement at dimension one.

## Build and verify

Install Lean's toolchain manager [elan](https://github.com/leanprover/elan) and Git. From this repository's root, run:

```sh
lake exe cache get
lake build
```

The toolchain file selects Lean 4.30.0. The lockfile pins mathlib and its transitive dependencies. The first command fetches the prebuilt mathlib cache. The default build compiles the project, checks that its main declaration is a theorem of exactly the closed type below, and audits every public and private declaration in the project namespace. The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

```lean
import GroupWL.ManuscriptCertification

#check (GroupWL.Statement.manuscriptClaim_proved : GroupWL.Statement.ManuscriptClaim)
#print axioms GroupWL.Statement.manuscriptClaim_proved
```

## Proof entry points

| File | Contents |
| --- | --- |
| [Statement.lean](GroupWL/Statement.lean) | Group encoding, decision languages, restricted reductions and theorem statement |
| [Refinement.lean](GroupWL/Refinement.lean) | The three refinements and identification among all finite groups |
| [Complexity.lean](GroupWL/Complexity.lean) | One-tape deterministic machine model and complexity definitions |
| [Completeness.lean](GroupWL/Completeness.lean) | Upper bounds and reduction of the full claim to construction of the output words |
| [CircuitTensorPipelineBounded.lean](GroupWL/MachinePrograms/CircuitTensorPipelineBounded.lean) | One polynomially bounded program producing both tensor coefficient arrays and the WL dimension |
| [CircuitWriterReduction.lean](GroupWL/MachinePrograms/CircuitWriterReduction.lean) | Composition of the tensor writer with the source circuit compiler |
| [ManuscriptCertification.lean](GroupWL/ManuscriptCertification.lean) | The closed main theorem |
| [SingleObstruction.lean](GroupWL/SingleObstruction.lean) | Nonisomorphic groups indistinguishable in all three versions at any prescribed dimension |
| [Certificate.lean](Certificate.lean) | Exact theorem-type check and axiom-audit entry point |

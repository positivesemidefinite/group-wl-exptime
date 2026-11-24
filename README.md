# EXPTIME-completeness of group Weisfeiler–Leman identification and equivalence

[Read the paper (PDF)](manuscript/group_wl.pdf) · [LaTeX source](manuscript/group_wl.tex) · [Lean formalization](formalization/README.md)

Fix an odd prime \(p\). Given a finite group described by a dense alternating
tensor over the field of order \(p\), and a dimension \(k\), deciding whether
\(k\)-dimensional Weisfeiler–Leman refinement identifies the group among all
finite groups is EXPTIME-complete. Deciding whether two such groups are
indistinguishable by refinement is also EXPTIME-complete. Both results hold
for all three versions of group Weisfeiler–Leman refinement and for either
binary or unary encoding of \(k\).

## Verify the proof

With [elan](https://github.com/leanprover/elan) and Git installed, run these
commands from the repository root:

```sh
cd formalization
lake exe cache get
lake build
```

The build checks the [main theorem](formalization/GroupWL/ManuscriptCertification.lean)
and audits its axioms. The [unboundedness corollary](formalization/GroupWL/SingleObstruction.lean)
is also formalized.

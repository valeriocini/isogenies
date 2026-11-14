# Source and local changes

`Torsion/Identities.lean` and `Torsion/EDS.lean` are adapted from
https://github.com/lana-agents/iut at commit
`553076af459e7a401bfee63a4607814d1c854477` (LANA Project, Apache 2.0).
The accompanying `LICENSE` is copied from that commit.

Initial local change: remap the `Iut.Torsion.Identities` import to
`IsogenyAttack.Vendor.Iut.Torsion.Identities`. These modules retain the
upstream namespace and copyright notices. Any additional compatibility
changes are recorded below.

`Torsion/Count.lean` and `Torsion/Divisible.lean` are adapted from the same
commit. `Count` replaces characteristic zero by nonzero `2` and nonzero
index in the field. Its Wronskian nonvanishing proof is replaced by the
characteristic-independent coefficient proof in
`IsogenyAttack/TorsionPolynomialBounds.lean`. `Divisible` retains the
`a₁ = a₃ = 0` surjectivity theorem in characteristic different from two
and omits the unrelated completion-of-the-square extension. These changes
are proved against the pinned local mathlib; no geometric conclusions are
added as assumptions.

Lean/mathlib 4.36 compatibility: the point-image equivalence in `Count`
uses an explicit existential `change` before the image-membership proof.
This replaces a simplification rule whose matching behavior changed.

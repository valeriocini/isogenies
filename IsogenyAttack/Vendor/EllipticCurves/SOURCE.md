# Source and local changes

`Torsion/AbelianStructure.lean` is copied from
https://github.com/lana-agents/elliptic-curves at commit
`e70086a9c442dcfe76152fa03777091c50985d43` (LANA Project, Apache 2.0).
The accompanying `LICENSE` is copied from that commit.

This module proves a finite abelian group classification statement against
mathlib and imports no external elliptic-curve geometry.

Compatibility change for mathlib 4.30: in `zmultiples_sum_of_one_eq_top`,
replace the unavailable `ZMod.prodEquivPi_apply` rewrite by the general
`map_one` property of the ring equivalence.

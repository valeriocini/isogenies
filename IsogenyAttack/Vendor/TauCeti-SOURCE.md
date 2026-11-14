# TauCeti dependency

Repository: https://github.com/TauCetiProject/TauCeti

Frozen commit: `a7aa188e650fba2aaa9a62178202af132a5515e0`.
License: Apache 2.0; a copy is retained as `TauCeti-LICENSE`.

TauCeti is an external Lake dependency, not a copied or renamed local theorem
interface. Its sources construct rational-function/function-field isogenies,
Vélu elliptic quotients, relative Frobenius, dual isogenies, and geometric
supersingularity. The local wrappers prove the correspondence with the point
subgroups and Hasse locus used by this project.

No mathematical TauCeti source was modified. Its exact matching mathlib and
Lean revisions are pinned by the delivered toolchain and dependency manifest.
All project and imported TauCeti declarations are covered by `AuditAll.lean`;
the imported source closure is also scanned in `audit/`.

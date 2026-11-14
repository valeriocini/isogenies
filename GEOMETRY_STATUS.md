# Mathematical scope and verification boundary

The final experiment uses genuine elliptic curves and algebraic maps. The earlier
missing geometry-to-sampler connections have been supplied by dedicated modules;
they are no longer arbitrary target maps or hypotheses asserting the desired
probability bound. The exact final build and transitive axiom-audit outcome is
recorded in `verification.log`, rather than inferred from an earlier checkpoint
or a declaration count.

## Completed mathematical chain

1. **Actual torsion and kernel classification.** Prime-to-characteristic
   `E[d] ≃+ ZMod d × ZMod d`, actual finite subgroup/HNF classification, and
   exactly `σ₁(d)` order-`d` kernels are derived. Independently chosen bases at
   different degrees are handled by recoding the stripped subgroup.
2. **Intrinsic scalar content and actual factorization.** If a separable raw
   map has kernel `S` and degree `d`, the HNF content `m` is maximal among
   positive divisors of `d` whose full torsion lies in `S`. The actual scalar
   image `[m]S` is cyclic, of cardinality `d/m²`. `ScalarStripGeometry` transports
   the full-torsion inclusion into TauCeti's geometric kernel convention and
   proves equality of quotient j-invariants. `CyclicComponent` constructs an
   actual map `χ` to the original raw codomain, with `χ ∘ [m] = φ`, actual
   point kernel `[m]S`, degree `d/m²`, and separability. Unrestricted geometric
   p-primary torsion is not used to define maximal content.
3. **Genuine supersingularity and stationary masses.** Supersingularity is
   trivial geometric p-torsion. The Hasse criterion identifies its geometric
   j-locus with the finite separable Hasse-polynomial locus. Actual coordinate
   automorphism counts and Legendre/Montgomery fiber counts give stationary
   mass `24/((p-1)*|Aut(E)|) ≤ 12/(p-1)` for each supersingular class.
4. **Finite-field normalized models.** Supersingular j and every supersingular
   normalized Montgomery parameter lie in the constructed p²-element field.
   `FiniteMontgomerySampler` identifies the geometric parameter locus with
   actual supersingular coefficients over that field and transports the exact
   uniform law. This is stronger than descent of j alone.
5. **Maximality and rational morphisms.** For `p ≡ 3 mod 4`, the normalized
   supersingular Montgomery models have p²-Frobenius `[-p]` and `(p+1)²` rational
   points. `MontgomeryLegendre` provides an actual isogeny comparison and the
   negative scalar identity. `IsogenyDescent` proves unique finite-field descent
   for an arbitrary geometric isogeny commuting with Frobenius, then applies it
   to common scalar Frobenius. `MontgomeryMorphismDescent` specializes this to
   the source models. Rational map types and base-change/sampler equivalences
   are collected in `RationalMapSampler`, `RationalTargetMembership`, and
   `RationalRawSampler`; `RationalAttack.signed_gap_lower` states the bound
   directly for the actual rational-map laws.
6. **Actual raw-morphism counting and complete sample spaces.** Vélu quotients
   have the input subgroup as actual point kernel and its cardinality as degree.
   Quotient uniqueness gives precisely twelve raw morphisms per kernel across
   normalized Montgomery targets, including exceptional j-invariants. At a
   fixed target the multiplicity is its automorphism count, independently of
   the kernel. `RawDegreeSampler` and `RawTargetSampler` implement these finite
   laws on raw maps. `RawTargetGeometry` proves that an invertible degree makes
   separability automatic, so the bounded sampler omits no actual isogeny.
   Its observations and those in `RawDegreeGeometry` are the degrees of actual
   same-target cyclic components.
7. **Printed weights and the attack probability.** The arithmetic proves
   `W(d) ≥ σ₁(d)` and `∑_(d≤B) W(d) ≤ 4B²`. Explicit disjoint HNF families give
   the degree-first lower bound; counting possible short-degree target classes
   gives the target-first upper bound. `RawSamplerAttack` combines these for
   two possibly different source curves, initially discarding all raw-degree-B
   outputs as a conservative lower bound. `SourceEndpoint` retains the valid
   noncyclic endpoint outputs, proves failure is exactly `C=B`, and transfers
   the bound by pointwise inclusion of accepting events. `RawExperiments` proves
   signed common-context averaging and reduction of any positive hint count
   to its first observed hint.
8. **Actual pushing and continuation.** `IsogenyPush` derives coprime kernel
   transport from actual dual-isogeny identities, constructs commuting quotient
   squares and cyclic splittings, and proves that Algorithm 6's first exposed
   degree is preserved. `HintContinuation` supplies actual cyclic maps of every
   positive invertible degree and finite uniform continuation laws. A
   cyclic-component degree `C<B` gives a positive complementary degree in
   Algorithm 5, even when the sampled raw degree is `d=B`.
9. **Public extraction and composed cost.** `ResponseCutoff` proves that the
   integer cutoff is exactly `2^ceil(log₂(sqrt p))`. `PublicObservation` and
   `PublicFullAttack` prove the decoder-plus-binary-test semantics and charged
   polynomial work bound, including failure and randomized valid encodings.
   `EndToEnd.full_attack_certificate` is the public finite certificate with
   actual finite-field source coefficients and a common context law.
   `PushedEncoding.sourceDegreeChannel` derives the required observation from
   actual Algorithm 6 outputs, and `TranscriptEncoding` allows arbitrary fresh
   later challenges/hints while the first slot retains its degree.
   `EndToEndFamilies.family_advantage_not_negligible` proves nonnegligibility
   for the encoded, source-completed experiment.

## Exact experiment being certified

For prime `p ≥ 49`, `p ≡ 3 mod 4`, use normalized supersingular Montgomery
models over `F_(p²)`. Put `B = 2^(Nat.clog 4 p)`, choose `s ≥ 784` with
`8*s² ≤ B`, and accept a nonfailure degree `C` exactly when `4*s²*C ≤ B`.
The signed difference, degree first minus target first, is at least
`1/(1024*s³)`.

The degree-first distribution chooses `d` from `[1,B]` with the source's printed
weight, then samples raw degree-d morphisms uniformly. Its actual cyclic-component
degree `C` determines completion: **only `C=B` returns failure**, precisely the
zero-complementary-degree case. All `C<B` outputs are retained, including valid
noncyclic raw maps with `d=B`. The strict raw-degree endpoint rejection occurs
only inside the conservative lower-bound proof. The target-first law samples
its actual finite-field target first and fails on an empty connecting fiber
**without resampling or conditioning the target**. Both laws retain their full
normalizers. Later outputs, hints, or representation randomness may be added
without altering the first optional degree. Failures remain observable failures;
there is no silent rejection/resampling step.

These are explicit totalizations of the source experiments. The literal printed
Algorithm 5 can request complementary degree zero with positive probability,
as proved in `Endpoint`; its uncompleted partial program is not asserted to be
a total probability distribution. Nor is reachability of every target silently
assumed. `SourceEndpoint.source_event_le_completion` also proves that replacing
only the `C=B` failure by arbitrary outputs cannot decrease acceptance if all
valid outputs and the original law are retained. Conditioning or resampling is
not such a completion and needs a separate comparison theorem.

The public-key curve and first challenge codomain may differ. The theorem
quantifies over any common finite context law choosing them, so it applies to a
key-generation/challenge law satisfying those model conditions without needing
to verify one concrete implementation of key generation. Only the first hint is
examined. For multiple fresh challenges, the first challenge belongs to the
common context; later challenge/hint generation is a continuation preserving
the first observation.

## Explicit external interfaces and nonclaims

The degree decoder is the public representation interface of Definition 2.11:
it must return the actual represented degree in polynomial work. Randomized
encodings are permitted, but must decode to the genuine observed optional
degree. No scalar-stripping correctness, target identity, stationary mass,
raw-map counting result, or distinguishing bound is assumed by that interface.

The binary arithmetic and the cost composition are proved in a charged
Boolean/list model. A concrete higher-dimensional isogeny validator, the complete
SQIsign software implementation, and a Turing-machine simulation of that work
model are outside this certificate. Sampling laws are finite mathematical laws;
the proof does not assert that all their raw-map enumeration procedures are
efficient algorithms available to the adversary.

For an asymptotic polynomial-time conclusion, decoder work bounds must be
uniform across the family, and public representation lengths and `log p` must
be polynomially bounded in the security parameter. With `s=n+784`,
the degree threshold hypothesis must hold eventually; `p(n) ≥ 2^n` suffices,
and `ResponseCutoff` proves the needed growth estimate. The resulting lower
bound `1/(1024*(n+784)^3)` is nonnegligible. The theorem concerns hint
distinguishability, not signature forgery or endomorphism-ring recovery.

## Trust and reproducibility

Lean `4.36.0-rc1`, mathlib commit
`2cabef97b63d3275776b8b060d802de6a6fa1055`, and TauCeti commit
`a7aa188e650fba2aaa9a62178202af132a5515e0` are pinned. `scripts/check.sh` builds
all project modules and runs the declaration-wide transitive axiom audit, whose
allowlist is exactly `propext`, `Classical.choice`, and `Quot.sound`.
`verification.log` records the actual integrated result; `audit/` contains source
scans. The independent `scripts/check-kernel.sh` replay is recorded separately
in `kernel-verification.log`; an incomplete replay is not reported as passed.

Adapted LANA and TauCeti materials retain attribution and licenses under
`IsogenyAttack/Vendor/`. Genuine rational-function and function-field isogeny
constructions come from the pinned TauCeti dependency. No proof hole or added
axiom stands for an unfinished mathematical conclusion.

# SQIsign degree-distinguishing certificate

This project formalizes a public degree distinguisher for the raw-isogeny hint
laws in the supplied August 1, 2025 revision of *A Complete Security Proof of
SQIsign*. The final experiments use actual elliptic curves, actual algebraic
isogenies, and their actual cyclic-component degrees. Their target map is the
constructed quotient curve; it is not an unspecified subgroup-to-target interface.

The theorem concerns **explicitly failure-completed experiments**. It does not
assert that the partial sampling instructions printed in the source were already
total. The exact conventions and mathematical scope are below and in
[GEOMETRY_STATUS.md](GEOMETRY_STATUS.md). The final build and audit results are
recorded in `verification.log`.

## Precise theorem

Let `p ≥ 49` be prime with `p ≡ 3 mod 4`, let

```text
B = 2^(Nat.clog 4 p) = 2^ceil(log₂(sqrt(p))),
s ≥ 784,     8*s² ≤ B,     L = floor(B/(4*s²)).
```

The two source curves are supersingular normalized Montgomery equations
`y² = x³ + A*x² + x` over `F_(p²)`. They may differ: the degree-first source is
the public-key curve, whereas the target-first source is the first challenge
codomain. A common finite public-context law may choose both curves arbitrarily.

- **Degree first:** choose `d` in `[1,B]` with weight
  `W(d) = ∏_(ell^a || d) (ell+1)^a`, then uniformly choose an actual degree-`d`
  morphism to any supersingular normalized Montgomery equation, retaining its
  target coefficient. Compute its actual cyclic-component degree `C`; return
  failure **only when `C=B`**, the zero-complementary-degree case. Every valid
  `C<B` is retained, including noncyclic raw maps of sampled degree `d=B`.
- **Target first:** choose a supersingular normalized Montgomery coefficient
  uniformly over `F_(p²)`, then uniformly choose an actual connecting morphism
  of degree `<B`. An empty fiber returns failure **without resampling the
  target**. On success expose the cyclic-component degree.
- **Public test:** reject failure; otherwise extract the first exposed
  component's degree `C` and accept exactly when `4*s²*C ≤ B`.

The signed acceptance difference, degree first minus target first, is at least
`1/(1024*s³)`. The bound survives common-context averaging, any positive number
of hints when only the first is read, and randomized continuations or valid
representations preserving that first optional degree. Later hint generation
must not discard or resample the already observed first outcome. Protocol
failure is distinct from an invalid representation string.

Raw morphisms, including their target equations, are counted separately. The
sampler does not identify maps up to post-isomorphism or sample representation
strings uniformly. Exact multiplicity theorems prove that raw morphism sampling
induces the required kernel laws. For these normalized models and
`p ≡ 3 mod 4`, parameter and morphism descent identify the geometric calculation
with maps defined over `F_(p²)`.

## Entry points and module map

The principal public theorem is `EndToEnd.full_attack_certificate`: it combines
the literal response cutoff, two finite-field source families, a common public
context, the signed probability bound, and a polynomial charged-work bound for
decoding and testing. `PublicFullAttack.finite_attack` is the corresponding
fixed-context theorem for the conservative interior model. `SourceEndpoint`
transfers its bound to the source observation retaining all valid endpoint maps.
`RawExperiments.signedGap_lower` and
`RawExperiments.signedGap_eq_one_hint` handle any positive hint count.
`RationalAttack.signed_gap_lower` states the bound on the literal rational-map
laws over the p²-element field. `PushedEncoding.sourceDegreeChannel` supplies
the public channel from actual Algorithm 6 outputs; `TranscriptEncoding` permits
arbitrary fresh later challenges and hints.
`EndToEndFamilies.family_advantage_not_negligible` gives the asymptotic
nonnegligibility result for the encoded source-completed experiments.

| Modules | Mathematical role |
|---|---|
| `Kernels`, `LatticeKernels`, `EllipticKernels` | HNF classification, actual rank-two torsion, exact `σ₁(d)` subgroup counts, scalar content |
| `Weights`, `Attack`, `FullArithmeticAttack` | Printed weights, `W(d) ≥ σ₁(d)`, normalizer at most `4B²`, explicit signed gap and asymptotics |
| `HasseSupersingular`, `StationaryIdentification`, `MontgomeryStationary` | Genuine supersingularity and the exact stationary geometric-class law |
| `MontgomeryDescent`, `FiniteMontgomerySampler` | Normalized parameter descent and uniform actual finite-field targets |
| `MontgomeryLegendre`, `IsogenyDescent`, `MontgomeryMorphismDescent` | Negative scalar Frobenius and unique rational descent of actual isogenies |
| `VeluQuotient`, `ScalarStripGeometry`, `CyclicComponent` | Actual quotient curves and same-target scalar factorization with cyclic residual kernel |
| `IsogenySampler`, `RawDegreeSampler`, `RawTargetSampler` | Actual raw morphism sample spaces, multiplicities, and exact finite probability laws |
| `RawDegreeGeometry`, `RawTargetGeometry` | All bounded maps occur; observations are genuine cyclic-component degrees |
| `RationalMapSampler`, `RationalTargetMembership`, `RationalRawSampler`, `RationalAttack` | Rational map spaces, exact sampler transport, and the signed bound on literal finite-field laws |
| `IsogenyPush`, `HintContinuation` | Actual dual-isogeny push, cyclic splitting, positive complementary degrees, and degree preservation |
| `RawSamplerAttack`, `RawExperiments` | Conservative interior lower bound, two-source averaging, first-hint reduction |
| `SourceEndpoint` | Retain all `C<B` outcomes, fail exactly at `C=B`, and transfer the bound by pointwise monotonicity |
| `ResponseCutoff`, `PublicObservation`, `PublicFullAttack`, `EndToEnd` | Exact source cutoff, public decoder interface, and composed public attack certificate |
| `PushedEncoding`, `TranscriptEncoding`, `EndToEndFamilies` | Concrete push-to-encoding bridge, unrestricted later hints, and encoded-family nonnegligibility |

`GEOMETRY_STATUS.md` explains these bridges and the boundary of the result.
The exposition with a precise theorem and proof is in `../exposition/`.

## Representation and efficiency scope

Definition 2.11 of the source specifies a polynomial-time public validator that
returns a represented isogeny's domain, codomain, and actual degree. The
certificate's `PolynomialDegreeDecoder` retains the degree, includes its
polynomial work guarantee, and requires correct decoding on supplied valid
representations. `EncodingChannel` permits arbitrary finite randomized encodings
with that property. No distinguishing-probability premise is included in these
interfaces.

The binary test and the composition of decoder cost with test cost are verified
in an explicit charged Boolean/list computation model. The project does not
implement a concrete higher-dimensional isogeny validator, verify a particular
SQIsign binary, or provide a Turing-machine simulation of that model.
For the security-parameter conclusion, the decoder must have uniform polynomial
work bounds across the family, and efficient representation lengths and `log p`
must be polynomially bounded in the parameter. Taking `s=n+784` gives
inverse-polynomial advantage whenever `8*(n+784)² ≤ B` eventually; exponential
characteristic growth `p(n) ≥ 2^n` is a sufficient condition proved by
`ResponseCutoff`. The finite theorem itself has no asymptotic growth assumption.

## Build and audit

The completed integrated run checked **89 source modules and both audits**.
The transitive axiom audit covered **10,868 project and imported TauCeti
declarations**; the source scan checked 91 project files and 472 imported
TauCeti modules. Both passed. The exact run is recorded in `verification.log`
and the source-scan reports in `audit/`.

| Dependency | Pinned revision |
|---|---|
| Lean | `4.36.0-rc1` |
| mathlib | `2cabef97b63d3275776b8b060d802de6a6fa1055` |
| TauCeti | `a7aa188e650fba2aaa9a62178202af132a5515e0` |

In the workspace, build every project source in dependency order and run both
axiom audits with the saved local toolchain and dependency cache:

```sh
sh scripts/check.sh
```

A fresh kernel replay of the assembled module and imported declarations is a
separate, potentially expensive check:

```sh
sh scripts/check-kernel.sh
```

For an extracted source archive with Lean/elan installed and dependencies
available:

```sh
lake exe cache get
lake build
lake env lean IsogenyAttack/Audit.lean
lake env lean IsogenyAttack/AuditAll.lean
```

`AuditAll.lean` checks transitive axiom dependencies of declarations in the
imported project and TauCeti modules. Its permitted axioms are exactly `propext`,
`Classical.choice`, and `Quot.sound`; proof holes, custom axioms, and
`native_decide` proofs are excluded. Use `verification.log` for the integrated
build and audit outcome, `kernel-verification.log` for the separate fresh replay,
and `audit/` for dependency-source scans. An interrupted or incomplete fresh
replay is not a passed replay. No stale declaration count is used as evidence of
the final build.

Source archives exclude toolchains, caches, and build products. The toolchain,
frozen dependency manifest, project sources, scripts, and reports are retained.
Adapted LANA and TauCeti materials retain attribution and Apache 2.0 licenses
under `IsogenyAttack/Vendor/`.

## Source and interpretation

The supplied source PDF is the August 1, 2025 revision of ePrint 2025/379,
SHA-256 `dd5b653e2d22a03a18748c0de057cf188441349bffba7ce39ea429b69ecf4f61`.

The result is a hint-distinguishing attack, not a signature forgery or key
recovery. `Endpoint.odd_split_zero_complement_probability_pos` proves the literal
source's positive-probability zero-complement problem; the theorem resolves it
with failure only at cyclic-component degree `C=B`. Empty target fibers are
also handled explicitly. `SourceEndpoint` proves that any non-resampling
completion of that sole zero-complement case can only increase acceptance,
provided all valid `C<B` outputs and the original sampling law are retained.
Conditioning on success, target resampling, or a different sampling convention
is a different experiment and needs its own comparison theorem.

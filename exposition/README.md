# Degree distinguisher: mathematical exposition

`main.tex` is the editable short exposition; `main.pdf` is its rendered form.
The final four-page PDF was compiled and all four pages visually checked on
14 November 2026; its final compilation has no unresolved-reference or layout warnings.
It gives a precise finite theorem and proof for actual raw isogenies between
supersingular normalized Montgomery equations over `F_(p²)`, with the source's
exact rounded response cutoff.

The theorem states a signed acceptance gap of at least `1/(1024*s³)` for
`p ≥ 49`, `p ≡ 3 mod 4`, `s ≥ 784`, and `8*s² ≤ B`. It permits distinct
public-key and challenge source curves, a common public-context law, and any
positive hint count when the test reads the first hint. Degree extraction uses
the polynomial public representation interface of Definition 2.11.

The experiments are explicitly completed with failure: only cyclic-component
degree `C=B` fails on the degree-first side, because its complementary degree
is zero. Valid noncyclic raw maps with sampled degree `d=B` and `C<B` are retained.
An empty target fiber fails without resampling its target.
The theorem does not claim that the source's uncompleted partial instructions
already define total distributions. The proof also covers arbitrary
non-resampling completions of the sole zero-complement case: retaining all
valid outputs can only increase the accepting probability. It counts actual
morphisms with target
coefficients retained, not representation strings or post-isomorphism classes.

Build the document with either:

```sh
tectonic main.tex
```

or two runs of `pdflatex main.tex`. The final rendered document should be checked
for references and layout after any source edit.

The source analyzed is the supplied August 1, 2025 revision of
*A Complete Security Proof of SQIsign*, IACR ePrint 2025/379.
The PDF at `../original_repo/2025-379.pdf` has SHA-256:

```text
dd5b653e2d22a03a18748c0de057cf188441349bffba7ce39ea429b69ecf4f61
```

The companion Lean project is in `../lean_certificate/`. Its module map and build
commands are in `../lean_certificate/README.md`; mathematical scope, failure
conventions, and representation assumptions are detailed in
`../lean_certificate/GEOMETRY_STATUS.md`. Use `../lean_certificate/verification.log`
for the final integrated build and axiom-audit result.

The certificate includes actual torsion and kernel classification, the Hasse
criterion, normalized model and morphism descent, raw-map multiplicities,
same-target cyclic components, exact probability bounds, and a public binary
test with composed charged-work bounds. It does not supply a concrete HD
representation validator or a Turing-machine verification of that work model.
The asymptotic claim additionally requires uniform polynomial decoder bounds,
polynomial public input lengths, and the stated parameter-growth condition.
`EndToEnd.full_attack_certificate` and
`EndToEndFamilies.family_advantage_not_negligible` are the principal finite and
asymptotic declarations. `RationalAttack.signed_gap_lower` presents the bound
on literal finite-field rational-map laws; `PushedEncoding` and
`TranscriptEncoding` connect actual pushes and arbitrary later hints to the
first public observation.

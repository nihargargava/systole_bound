# Third-Party Code Attributions

This project includes selected, modified Lean code from the sources below. These are copied source slices. Original copyright and provenance headers are retained in the relevant files.

## Licenses at a glance

- Apache-2.0 applies to the listed Apache-licensed sources. The complete license is in [`LICENSE`](LICENSE); source-specific license files are kept beside vendored code when needed.
- The directed-topology slice from Directed-Topology-Lean-4 is MIT-licensed. Its license is retained at `Vendored/ClassicalVanKampen/LICENSE-MIT`.
- DifferentialGeometry's upstream `NOTICE` is retained at `Vendored/DifferentialGeometry/NOTICE`.

## Code sources

- **PalomarTemplate** — [source](https://github.com/PalomarRegistry/PalomarTemplate), commit `2891de4c48955af824969a263d31b25e7a9a1406`. Authors: PalomarTemplate contributors. Apache-2.0. The unchanged verification script is `scripts/verify-comparator.sh`.

- **Classical van Kampen** — [source](https://github.com/Arthur742Ramos/classical-svk-lean), commit `874680e16db88b4a41daadf56eafbac79fd2f748`; author: Arthur Freitas Ramos, copyright 2026; Apache-2.0. The fundamental-groupoid open-cover pushout dependency slice is under `Vendored/ClassicalVanKampen/`. Its 34-module directed-topology dependency closure is by Dominique Lawson (copyright 2023), from [Directed-Topology-Lean-4](https://github.com/Dominique-Lawson/Directed-Topology-Lean-4), commit `009529606c66d37ef93b4b81b8587f71ce4d2c56`, MIT-licensed. Both license texts are retained beside the code. Imports, namespaces, and compatibility syntax were adapted; the upstream unfinished `Challenge.lean` and any assumed van Kampen result are excluded.

- **ProCGroups** — [source](https://github.com/n-yamaguchi-0729/ProCGroups), v2.0.0, commit `5299e13f185d524c90710d41e2e9e4f4d4fce470`; Naganori Yamaguchi and contributors; Apache-2.0. The discrete/free-group Reidemeister–Schreier and Tietze slice is in `Vendored/ProCGroups/`. Two compatibility edits are documented in `Vendored/ProCGroups/README.md` and the affected source files. The upstream license is retained at `Vendored/ProCGroups/LICENSE`.

- **RiemannDynamics** — [source](https://github.com/will1491/RiemannDynamics), commit `b3fa37cc0f18a23ea66b654ea3f73eb472129010`; Will (Ziang) Li; Apache-2.0. Selected hyperbolic polygon, Dirichlet-domain, compact-covering, polygon-rank, and disc-automorphism code is in `Vendored/RiemannDynamics/`. The selected sources preserve their headers and identify original paths. Imports and namespaces were adapted; unrelated Mumford, RMT4, and Carleson dependencies were excluded. `Geometry/DirichletFanAngles.lean` adapts the cited fan angle-splitting argument.

- **DifferentialGeometry** — [source](https://github.com/qinz1yang/differential-geometry), commit `777299070a5529e96345e0033979706fd00c7e62`; DifferentialGeometry contributors; Apache-2.0. The two Mathlib-only deck-group modules are combined in `Vendored/DifferentialGeometry/DeckGroup.lean`; the upstream `NOTICE` is retained. Imports and namespace were adapted without changing theorem contracts.

- **Tau Ceti: universal cover** — [source](https://github.com/TauCetiProject/TauCeti), commit `4d898cf1e30951c7c13845c1ef043ad9415b6aca`; Kim Morrison and Tau Ceti contributors, with original copyright headers retained; Apache-2.0. The selected topology and based-path universal-cover modules are in `Vendored/TauCeti/`. The files preserve acknowledgements of Mathlib drafts, including PR #38292. Import paths and several pinned-Mathlib API names were adjusted. Native adapters in `Geometry/` apply this code to the project surface; lifting results use Mathlib directly where available.

- **Tau Ceti: matrix normalization and group extensions** — [source](https://github.com/TauCetiProject/TauCeti), commit `04648565a5156f3ff447d3a662949bdaa89b864b`; Chris Birkbeck and Tau Ceti contributors; Apache-2.0. Selected projective-special-linear normalization and group-extension/cohomology modules are in `Vendored/TauCeti/`. Original headers and the AINTLIB attribution are retained. The code provides general splitting/cohomology results; it does not assert that this project's surface holonomy obstruction vanishes.

- **Poincare-Conjecture / DoCarmo geometry** — [source](https://github.com/frenzymath/Poincare-Conjecture), commit `5a9e2acd61c33320a2e6232e502d2189385f5157`; Axel Delaval and contributors; Apache-2.0. The selected smooth-curvature, Cartan–Hadamard, and covering-metric dependency closure is in `Vendored/DoCarmo/`. Original headers are retained, imports are localized, and pinned-toolchain compatibility/lint changes are noted in affected sources. `Geometry/ExponentialGlobalVelocityDifferential.lean` adapts the cited DoCarmo exponential differential argument. The upstream source credits OpenGA for part of its Riemannian infrastructure.

- **sum_product** — [source](https://github.com/mathlib-initiative/sum_product), commit `80e4127a67742659d521466204c6d2d7e0ca2b3f`; Formal Frontier Team; Apache-2.0. The extracted convolution-density, Fourier/characteristic-function, and zero-point inversion results are in `CookMagyar/Vendor/SumProduct/ConvolutionDensity.lean`; the upstream header is retained.

- **PrimeNumberTheoremAnd** — [source](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), commit `c39a751132c88b6e8080b74c74023fd95b3d8be0`; Alex Kontorovich and PNT+ contributors; Apache-2.0. The selected strong-PNT dependency slice is under `Vendored/PrimeNumberTheoremAnd/`; original per-file attribution is retained. Pinned-Mathlib compatibility edits are proof-preserving. The upstream StrongPNT header credits `math-inc/strongpnt`; no separate checkout was copied. This slice supplies the principal Chebyshev-ψ estimate, not the arithmetic-progression/nonprincipal-character input.

## Local adaptations

- Lean imports, namespaces, and APIs were adjusted to this project's module layout and pinned toolchain.
- Adaptation details are recorded in the relevant vendored source headers or local README files.
- No upstream package dependency is added by these source copies.

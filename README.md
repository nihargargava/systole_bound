# Systolic growth in every genus

This repository contains a Lean proof that the largest possible systole of a
closed oriented hyperbolic surface grows at least logarithmically with its
genus. Writing `Sys(g)` for the supremum of these systoles, the result is

\[
\liminf_{g\to\infty}\frac{\operatorname{Sys}(g)}{\log g}\geq\frac43.
\]

This is a formal verification of a theorem that is going to appear in an upcoming preprint to be written by Yifei Chai, Nihar Gargava and Minkun Liu.

## Read the proof

The main result and its assembly are developed in
[`MainTheorem.lean`](MainTheorem.lean), with the final reduction in
[`Core/Reduction.lean`](Core/Reduction.lean).

The proof is organized around three ingredients:

- **Arithmetic surfaces:** `BuserSarnak/` constructs surfaces with large systole.
- **Prime-cube decomposition:** `CookMagyar/` supplies the arithmetic
  representation estimates used to cover every sufficiently large genus.
- **Surface gluing:** `Geometry/` joins the surfaces while retaining a uniform
  systole lower bound and constructs the required hyperbolic metric.

`Core/` contains shared definitions and the final reduction; `SurfaceGroup/`
contains finite-presentation results. `Vendored/` holds only external Lean
code used by the proof. Its sources, licenses, and local adaptations are
listed in [`Code-Attribution.md`](Code-Attribution.md).

## Build and check

Run these commands from the repository root. The Lean and Mathlib versions
are pinned in `lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean Solution.lean
bash scripts/verify-comparator.sh
```

`lake build` checks the project. The Comparator script checks the formalized
main result with Lean's kernel and the bundled independent proof checkers.

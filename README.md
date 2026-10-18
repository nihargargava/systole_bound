# Systolic growth in every genus


This repository contains a Lean proof that the largest possible systole of a
closed oriented hyperbolic surface grows at least logarithmically with its
genus. Writing `Sys(g)` for the supremum of these systoles, the result is

$$
\liminf_{g\to\infty}\frac{\mathrm{Sys}(g)}{\log g}\geq\frac43.
$$
This is based on the onging work of Yifei Cai, Nihar Gargava and Mingkun Liu.
The above result improves on previous results of Petri-Liu, Katz-Sabourau and Cai.


The autoformalization was done with the help of Codex running various version of ChatGPT.
Most of the code was written by ChaGPT 6.1 Sol with various proof outlines written by ChatGPT Astra 6.0.
The proof itself was based on a candidate construction given by ChatGPT 5.6.
The formalization took >7 days of agents working in total over a period of a few weeks. 

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

## Palomar submission

This repository has been verified by the Palomar project. 
What this means is that some robots agree that the claimed theorem is indeed what has been formalized by the code.



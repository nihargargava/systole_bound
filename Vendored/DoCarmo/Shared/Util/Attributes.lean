module

/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/shared/Shared/Util/Attributes.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes and upstream package-option restoration.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Mathlib.Tactic.Common
public import Vendored.DoCarmo.Shared.Util.Linter

@[expose] public section

-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000


/-!
# Riemannian simp attributes — declarations

Pure attribute registration, intentionally without imports of lemmas
that consume the attributes. This file is imported by lemma sites
(e.g., `Metric.lean`) to make `[metric_simp]` available as a
tag, and by downstream proof code to invoke `simp [metric_simp]`.

Splitting attribute registration from lemma sites avoids a circular
import (lemma sites need the attribute declared; a Tactic-level docs
file would otherwise need to import the lemma sites for documentation
context).
-/

/-- Simp set for `metricInner` algebra normalisation: bilinearity, sign
rules, zero / neg / sub / self_nonneg. Tagged on the lemmas in
`Metric.lean`; downstream proofs can invoke
`simp only [metric_simp]` for routine inner-product calculations. -/
register_simp_attr metric_simp

/-- Simp set for `riemannCurvature` algebra normalisation: definitional
unfold ($R(X,Y)Z = \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X,Y]} Z$),
Lie-bracket antisymmetry under `covDeriv`, and connection-direction
linearity rewrites. Tagged on lemmas in `Connection.lean` (Bianchi section);
downstream proofs invoke `simp only [riem_simp]` to normalise curvature
expressions before `abel` / `ring` / further reasoning. -/
register_simp_attr riem_simp


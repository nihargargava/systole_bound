module

/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/shared/Shared/Util/Linter.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes and upstream package-option restoration.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public meta import Vendored.DoCarmo.Shared.Util.Linter.AnchorPurity
public meta import Vendored.DoCarmo.Shared.Util.Linter.MathTag
public meta import Vendored.DoCarmo.Shared.Util.Linter.Naming

public meta section

-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000


/-!
# Shared fitness-function linter set

Aggregates the three Shared Lean-native linters and registers them
as a single linter set `linter.shared`. Use

```
set_option linter.shared false
```

at the top of a file to silence all three Shared linters at once
(e.g. for temporary experimentation); individual linters can also be
toggled in isolation via their own options
(`linter.shared.mathTag`, `linter.shared.anchorPurity`,
`linter.shared.naming`).

See CLAUDE.md "Fitness functions" for the full design and the per-
linter docstrings for the rule each one enforces.
-/

/-- The Shared fitness-function linter set, bundling `mathTag`,
`anchorPurity`, and `naming`. -/
register_linter_set linter.shared :=
  linter.shared.mathTag
  linter.shared.anchorPurity
  linter.shared.naming


module

/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Jacobi/Geodesics.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes and upstream package-option restoration.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.Equation
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Exponential.Defs

@[expose] public section

-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain the upstream overlapping finite-dimensional instance binders.
set_option linter.overlappingInstances false


/-!
# Geodesics and the exponential map — Jacobi-port aliases

Ported into DoCarmoLib from the Morgan–Tian / Poincaré Ch.1, §1.2 development
(toward `cor:dc-ch5-2-5`). Provides the `Riemannian.Jacobi`-namespace aliases of
DoCarmoLib's geodesic and exponential-map interfaces that the ported Jacobi-field
manifold layer is written against.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A curve `γ : ℝ → M` is a **geodesic** of `g` if `∇_{γ̇} γ̇ = 0`
everywhere. Alias of `Riemannian.Geodesic.IsGeodesic`. -/
abbrev IsGeodesic (g : Riemannian.RiemannianMetric I M) (γ : ℝ → M) : Prop :=
  Riemannian.Geodesic.IsGeodesic (I := I) g γ

/-- **Math.** A curve `γ : ℝ → M` is a **geodesic** of `g` on the set `s ⊆ ℝ`
if `∇_{γ̇} γ̇ = 0` at every `t ∈ s`. Alias of
`Riemannian.Geodesic.IsGeodesicOn`. -/
abbrev IsGeodesicOn (g : Riemannian.RiemannianMetric I M) (γ : ℝ → M)
    (s : Set ℝ) : Prop :=
  Riemannian.Geodesic.IsGeodesicOn (I := I) g γ s

/-- **Math.** The **exponential map** at `p ∈ M`, `exp_p(v) = γ_v(1)`. Alias of
`Riemannian.Exponential.expMap`. -/
abbrev expMap (g : Riemannian.RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) : M :=
  Riemannian.Exponential.expMap (I := I) g p v

/-- **Math.** The maximal domain `O_p ⊆ T_pM` of `expMap g p`. Alias of
`Riemannian.Exponential.expDomain`. -/
abbrev expDomain (g : Riemannian.RiemannianMetric I M) (p : M) :
    Set (TangentSpace I p) :=
  Riemannian.Exponential.expDomain (I := I) g p

end Riemannian.Jacobi

end

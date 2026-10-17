module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Topology.Order.LiminfLimsup

@[expose] public section

/-!
# Systolic growth: independent mathematical statement

For each genus `g`, `Sys g` is the supremum of the systoles of closed
oriented hyperbolic surfaces of genus `g`. The result to be compared is
`4 / 3 ≤ liminf (fun g ↦ Sys g / Real.log g) atTop`.

The definitions below use only mathlib. They describe surfaces as compact
quotients of the Poincaré upper half-plane by free discrete groups of
orientation-preserving isometries. The marking records the genus through
the ordinary presentation of the fundamental group of an oriented surface.
-/

open Filter Set UpperHalfPlane
open scoped MatrixGroups Pointwise UpperHalfPlane commutatorElement

namespace SystolicGrowth

/-- The two generators associated with each of the `g` handles. -/
abbrev SurfaceGenerator (g : ℕ) := Fin g × Bool

/-- The ordered product of the handle commutators. -/
def surfaceRelator (g : ℕ) : FreeGroup (SurfaceGenerator g) :=
  (List.ofFn fun i : Fin g ↦
    ⁅FreeGroup.of (i, false), FreeGroup.of (i, true)⁆).prod

/-- The standard fundamental group of a closed oriented surface of genus `g`:
the free group on the handle generators modulo their product of commutators. -/
abbrev SurfaceGroup (g : ℕ) := PresentedGroup ({surfaceRelator g} : Set _)

/-- A closed oriented hyperbolic surface of genus `g`, represented by its
discrete group of deck transformations on the Poincaré upper half-plane.
Freeness excludes fixed points, compactness makes the surface closed, and
the marking identifies its fundamental group with the genus-`g` surface group. -/
structure ClosedHyperbolicSurface (g : ℕ) where
  /-- The orientation-preserving deck transformations. -/
  deckGroup : Subgroup SL(2, ℝ)
  /-- Discreteness in the ambient Lie group. -/
  discrete : IsDiscrete (deckGroup : Set SL(2, ℝ))
  /-- Only the identity fixes a point of the upper half-plane. -/
  free : ∀ γ : deckGroup, ∀ z : ℍ, γ • z = z → γ = 1
  /-- The quotient surface is compact. -/
  compactQuotient :
    IsCompact (Set.univ : Set (MulAction.orbitRel.Quotient deckGroup ℍ))
  /-- An isomorphism with the usual genus-`g` fundamental group. -/
  marking : deckGroup ≃* SurfaceGroup g

namespace ClosedHyperbolicSurface

/-- All displacements by nonidentity deck transformations. Taking the
infimum also takes the infimum over points on their translation axes. -/
def translationLengths {g : ℕ} (X : ClosedHyperbolicSurface g) : Set ℝ :=
  { length | ∃ γ : X.deckGroup, γ ≠ 1 ∧ ∃ z : ℍ, length = dist z (γ • z) }

/-- The systole: the infimum of the nontrivial deck-transformation displacements. -/
noncomputable def systole {g : ℕ} (X : ClosedHyperbolicSurface g) : ℝ :=
  sInf X.translationLengths

end ClosedHyperbolicSurface

/-- The systoles realized by closed oriented hyperbolic surfaces of genus `g`. -/
def systoleSpectrum (g : ℕ) : Set ℝ :=
  Set.range (fun X : ClosedHyperbolicSurface g ↦ X.systole)

/-- The supremum of the systoles in genus `g`. No assertion that this
supremum is attained is needed for the asymptotic theorem. -/
noncomputable def Sys (g : ℕ) : ℝ :=
  sSup (systoleSpectrum g)

/-- The supremal systole grows at least as fast as `(4 / 3) * log g`
in the limit over all genera. This independent statement is proved by
the corresponding declaration in `Solution.lean`. -/
theorem systolic_growth_lower_bound :
    (4 / 3 : ℝ) ≤ liminf (fun g : ℕ ↦ Sys g / Real.log g) atTop := by
  -- Authorized statement-only placeholder; never imported by the proof development.
  sorry

end SystolicGrowth

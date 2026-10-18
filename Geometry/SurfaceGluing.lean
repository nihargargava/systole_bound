module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ExerciseGeometryFoundation
public import Geometry.GluingConformalSmoothSolution

@[expose] public section

/-!
# Constructed geometric input

The polygon and area calculations in `ExerciseGeometryFoundation` prepare
chains of surfaces. The smooth conformal construction supplies a hyperbolic
metric and a faithful surface-group action with the target systole lower
bound. This file forms the quotient surface and constructs the geometric
input to the final theorem.
-/

-- Use mathlib-style docstrings, not the imported DoCarmo documentation tags.
set_option linter.shared.mathTag false

open Filter MeasureTheory Set UpperHalfPlane
open scoped BigOperators ENNReal MatrixGroups Pointwise Topology UpperHalfPlane ContinuousMap

namespace SystolicGrowth

/-- A prepared chain determines a hyperbolic surface-group action
with the target displacement lower bound. The conformal curvature equation
supplies a smooth metric of curvature `-1`; its nonnegative solution preserves
the lower bound. Marked holonomy and its lift supply the faithful action
and compact fundamental set. -/
noncomputable def hyperbolicChainAction {C : ℝ} {g n : ℕ}
    (hn : 2 ≤ n) (genera : Fin n → ℕ)
    (X : ∀ i, ClosedHyperbolicSurface (genera i))
    (hsum : (∑ i, genera i) = g)
    (P : ExerciseGluingPreparation C g n genera X) :
    ExerciseLiftedChainOutput g (targetSystole C g) :=
  P.gluedConformalLiftedChainOutput hn hsum

/-- The faithful image defines a marked closed hyperbolic surface. -/
noncomputable def ExerciseLiftedChainOutput.surface {g : ℕ} {L : ℝ}
    (O : ExerciseLiftedChainOutput g L) : ClosedHyperbolicSurface g where
  deckGroup := O.representation.range
  discrete := O.discrete
  free := O.free
  compactQuotient :=
    isCompact_orbitRel_quotient_of_compact_cover O.compactSet O.compact O.orbit_cover
  marking := (MonoidHom.ofInjective O.faithful).symm

/-- A uniform displacement lower bound also bounds the surface's systole. -/
theorem ExerciseLiftedChainOutput.le_systole {g : ℕ} {L : ℝ}
    (O : ExerciseLiftedChainOutput g L) (hg : 0 < g) : L ≤ O.surface.systole := by
  apply O.surface.le_systole_of_displacement_lower L
    (O.surface.translationLengths_nonempty_of_genus_pos hg)
  exact O.displacement_lower

/-- Glue a prepared chain; a singleton chain already supplies the required surface. -/
theorem exists_hyperbolic_surface_of_prepared_chain {C : ℝ} {g n : ℕ} (hn : 0 < n)
    (genera : Fin n → ℕ) (X : ∀ i, ClosedHyperbolicSurface (genera i))
    (hsum : (∑ i, genera i) = g) (P : ExerciseGluingPreparation C g n genera X) :
    ∃ Y : ClosedHyperbolicSurface g, targetSystole C g ≤ Y.systole := by
  by_cases hone : n = 1
  · subst n
    have hgenus : genera 0 = g := by simpa using hsum
    subst g
    exact ⟨X 0, P.component_systole 0⟩
  · have hn2 : 2 ≤ n := by omega
    have hg : 0 < g := by
      have hi := P.component_genus (⟨0, hn⟩ : Fin n)
      have hle : genera (⟨0, hn⟩ : Fin n) ≤ ∑ i, genera i :=
        Finset.single_le_sum (fun i _ ↦ Nat.zero_le (genera i)) (Finset.mem_univ _)
      omega
    let O := hyperbolicChainAction hn2 genera X hsum P
    exact ⟨O.surface, O.le_systole hg⟩

/-- Polygon preparation and chain gluing provide the geometric input to the
systolic-growth theorem, including its independent logarithmic upper bound. -/
theorem geometricInput : GeometricInput where
  connect_surfaces_along_chain := by
    intro N a ha K
    refine ⟨gluingConstant K, gluingConstant_pos K, ?_⟩
    filter_upwards [exercise_eventually_gluing_preparation ha K] with g hprep
    intro n hn _hnN genera X hsum hcompare hsys
    obtain ⟨P⟩ := hprep n genera X hcompare hsys
    exact exists_hyperbolic_surface_of_prepared_chain hn genera X hsum P
  systole_upper_bound := exercise_log_systole_upper_bound

#print axioms geometricInput
#print axioms exists_hyperbolic_surface_of_prepared_chain
#print axioms ExerciseLiftedChainOutput.le_systole
#print axioms hyperbolicChainAction

end SystolicGrowth

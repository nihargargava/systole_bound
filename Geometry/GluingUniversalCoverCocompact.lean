module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingUniversalCoverDeck
public import Geometry.CoveringCompactLift

@[expose] public section

/-!
# A compact orbit-covering set in the actual glued universal cover

Compactness of the original quotient gives finitely many compact lifted local
sheet pieces. Their union meets every projection fiber. Native deck transitivity
then makes its translates cover the entire original based-path universal cover.
No fundamental domain, metric identification, or replacement is assumed.
-/

open Set

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Math. An actual compact set upstairs projects onto the entire native glued carrier. -/
theorem exists_compact_gluedUniversalCover_surjecting
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    ∃ K : Set (P.basedTopologicalUniversalCover x), IsCompact K ∧
      P.gluedUniversalCoverProjection x '' K = Set.univ :=
  exists_compact_set_surjecting_under_covering (P.gluedUniversalCoverProjection x)
    (P.gluedUniversalCoverProjection_isCoveringMap x)
    (P.gluedUniversalCoverProjection_surjective x)

/-- Math. A compact native lifted set covers every orbit of the actual deck group. -/
theorem exists_compact_gluedUniversalCover_orbit_cover
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    ∃ K : Set (P.basedTopologicalUniversalCover x), IsCompact K ∧
      ∀ e : P.basedTopologicalUniversalCover x,
        ∃ τ : P.gluedUniversalCoverDeckGroup x, e ∈ τ.val '' K := by
  obtain ⟨K, hK, hproj⟩ := P.exists_compact_gluedUniversalCover_surjecting x
  refine ⟨K, hK, ?_⟩
  intro e
  have he : P.gluedUniversalCoverProjection x e ∈
      P.gluedUniversalCoverProjection x '' K := by
    rw [hproj]
    exact mem_univ _
  obtain ⟨k, hk, hke⟩ := he
  obtain ⟨τ, hτ⟩ := P.exists_gluedUniversalCoverDeck_of_projection_eq x k e hke
  exact ⟨τ, k, hk, hτ⟩

#print axioms exists_compact_gluedUniversalCover_surjecting
#print axioms exists_compact_gluedUniversalCover_orbit_cover

/-- Math. A fixed actual compact orbit-covering set, for the later geometric transport. -/
noncomputable def gluedUniversalCoverCompactSet
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    Set (P.basedTopologicalUniversalCover x) :=
  Classical.choose (P.exists_compact_gluedUniversalCover_orbit_cover x)

/-- Math. Compactness is proved for this chosen native set, not supplied separately. -/
theorem gluedUniversalCoverCompactSet_isCompact
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    IsCompact (P.gluedUniversalCoverCompactSet x) :=
  (Classical.choose_spec (P.exists_compact_gluedUniversalCover_orbit_cover x)).1

/-- Math. This very compact set covers every native deck orbit. -/
theorem gluedUniversalCoverCompactSet_orbit_cover
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) :
    ∃ τ : P.gluedUniversalCoverDeckGroup x,
      e ∈ τ.val '' P.gluedUniversalCoverCompactSet x :=
  (Classical.choose_spec (P.exists_compact_gluedUniversalCover_orbit_cover x)).2 e

/-- Math. Every point has an actual deck translate in this same compact set,
with the quantifier order required by the final orbit-cover field. -/
theorem gluedUniversalCoverCompactSet_meets_orbit
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) :
    ∃ τ : P.gluedUniversalCoverDeckGroup x,
      τ.val e ∈ P.gluedUniversalCoverCompactSet x := by
  obtain ⟨τ, k, hk, hke⟩ := P.gluedUniversalCoverCompactSet_orbit_cover x e
  refine ⟨τ⁻¹, ?_⟩
  change τ.val.symm e ∈ P.gluedUniversalCoverCompactSet x
  rw [← hke, τ.val.symm_apply_apply]
  exact hk

#print axioms gluedUniversalCoverCompactSet
#print axioms gluedUniversalCoverCompactSet_isCompact
#print axioms gluedUniversalCoverCompactSet_orbit_cover
#print axioms gluedUniversalCoverCompactSet_meets_orbit

end SystolicGrowth.ExerciseGluingPreparation

module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingLocalContractibility
public import Geometry.GluingEssentialLoopSystole
public import Geometry.SurfaceUniversalCover
public import Vendored.TauCeti.AlgebraicTopology.UniversalCover.Covering
public import Vendored.TauCeti.Topology.IsLocalHomeomorph

@[expose] public section

/-!
# The topological universal cover of the actual glued carrier

Native small-ball contractions supply all local hypotheses for the already
attributed Tau Ceti based-path cover. The original quotient topology is
unchanged; unique lifting uses Mathlib directly. No metric identification,
Cartan--Hadamard conclusion, or projective holonomy is asserted here.
Closure of actual lifts detects nullhomotopy at every cover point; paths
between distinct points of one fiber pay the proved target downstairs.
-/

open Set
open scoped unitInterval ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The based-path topological universal cover of the actual glued surface. -/
abbrev basedTopologicalUniversalCover
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :=
  TauCeti.UniversalCover x

/-- The actual based-path endpoint projection to the original glued carrier. -/
def gluedUniversalCoverProjection
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    P.basedTopologicalUniversalCover x → P.GluedCarrier :=
  TauCeti.UniversalCover.proj

/-- The endpoint projection is a covering map, using the proved native
contractible neighborhood basis rather than an added surface hypothesis. -/
theorem gluedUniversalCoverProjection_isCoveringMap
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    IsCoveringMap (P.gluedUniversalCoverProjection x) :=
  TauCeti.UniversalCover.isCoveringMap x

/-- The constructed topological cover is simply connected. -/
instance basedTopologicalUniversalCoverSimplyConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    SimplyConnectedSpace (P.basedTopologicalUniversalCover x) :=
  TauCeti.UniversalCover.simplyConnectedSpace x

/-- Local path connectedness lifts along the actual endpoint covering. -/
instance basedTopologicalUniversalCoverLocallyPathConnectedSpace
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    LocallyPathConnectedSpace (P.basedTopologicalUniversalCover x) :=
  IsLocalHomeomorph.locallyPathConnectedSpace
    (P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph

/-- The chosen point makes the actual preconnected carrier nonempty; its
endpoint projection therefore covers the whole carrier, not just a component. -/
theorem gluedUniversalCoverProjection_surjective
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    Function.Surjective (P.gluedUniversalCoverProjection x) := by
  letI : ConnectedSpace P.GluedCarrier :=
    { toPreconnectedSpace := P.gluedCarrierPreconnectedSpace
      toNonempty := ⟨x⟩ }
  letI : PathConnectedSpace P.GluedCarrier :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  intro y
  have hy : y ∈ pathComponent x := PathConnectedSpace.joined x y
  rw [← TauCeti.UniversalCover.range_proj x] at hy
  exact hy

/-- Mathlib's based unique lifting theorem applies to the actual glued
universal cover from every simply connected locally path-connected source. -/
theorem gluedUniversalCoverProjection_existsUnique_continuousMap_lifts
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    {A : Type*} [TopologicalSpace A] [SimplyConnectedSpace A]
    [LocallyPathConnectedSpace A]
    (f : C(A, P.GluedCarrier)) (a₀ : A)
    (e₀ : P.basedTopologicalUniversalCover x)
    (he : P.gluedUniversalCoverProjection x e₀ = f a₀) :
    ∃! F : C(A, P.basedTopologicalUniversalCover x),
      F a₀ = e₀ ∧ P.gluedUniversalCoverProjection x ∘ F = f :=
  (P.gluedUniversalCoverProjection_isCoveringMap x).existsUnique_continuousMap_lifts
    f a₀ e₀ he

/-- The actual lift of a native path, starting at any specified cover point.
The construction is Mathlib's path lift, not a second copied implementation. -/
noncomputable def gluedUniversalCoverPathLift
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) {y : P.GluedCarrier}
    (β : Path (P.gluedUniversalCoverProjection x e) y) :
    C(I, P.basedTopologicalUniversalCover x) :=
  (P.gluedUniversalCoverProjection_isCoveringMap x).liftPath β e β.source

@[simp] theorem gluedUniversalCoverPathLift_zero
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) {y : P.GluedCarrier}
    (β : Path (P.gluedUniversalCoverProjection x e) y) :
    P.gluedUniversalCoverPathLift x e β 0 = e :=
  (P.gluedUniversalCoverProjection_isCoveringMap x).liftPath_zero β e β.source

@[simp] theorem gluedUniversalCoverProjection_pathLift
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) {y : P.GluedCarrier}
    (β : Path (P.gluedUniversalCoverProjection x e) y) (t : I) :
    P.gluedUniversalCoverProjection x (P.gluedUniversalCoverPathLift x e β t) = β t :=
  congrFun
    ((P.gluedUniversalCoverProjection_isCoveringMap x).liftPath_lifts β e β.source) t

/-- Uniqueness holds among all continuous lifts with the specified start. -/
theorem eq_gluedUniversalCoverPathLift_iff
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) {y : P.GluedCarrier}
    (β : Path (P.gluedUniversalCoverProjection x e) y)
    (Γ : C(I, P.basedTopologicalUniversalCover x)) :
    Γ = P.gluedUniversalCoverPathLift x e β ↔
      P.gluedUniversalCoverProjection x ∘ Γ = β ∧ Γ 0 = e :=
  (P.gluedUniversalCoverProjection_isCoveringMap x).eq_liftPath_iff' β.source

/-- Closure of the native lifted loop detects nullhomotopy at every cover
point, not only the distinguished constant-path point. -/
theorem gluedUniversalCoverLoopLift_one_eq_iff
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x)
    (β : Path (P.gluedUniversalCoverProjection x e)
      (P.gluedUniversalCoverProjection x e)) :
    P.gluedUniversalCoverPathLift x e β 1 = e ↔
      β.Homotopic (Path.refl (P.gluedUniversalCoverProjection x e)) :=
  simplyConnectedCover_liftPath_one_eq_iff
    (P.gluedUniversalCoverProjection_isCoveringMap x) e β

/-- A path between distinct points of one native cover fiber projects to an
essential loop. This is the topological input for displacement comparisons. -/
theorem gluedUniversalCover_projectedPath_nullhomotopic_iff
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    {e₀ e₁ : P.basedTopologicalUniversalCover x}
    (h : P.gluedUniversalCoverProjection x e₁ = P.gluedUniversalCoverProjection x e₀)
    (Γ : Path e₀ e₁) :
    ((Γ.map (P.gluedUniversalCoverProjection_isCoveringMap x).continuous).cast
      rfl h.symm).Homotopic (Path.refl (P.gluedUniversalCoverProjection x e₀)) ↔
      e₁ = e₀ := by
  let β : Path (P.gluedUniversalCoverProjection x e₀)
      (P.gluedUniversalCoverProjection x e₀) :=
    (Γ.map (P.gluedUniversalCoverProjection_isCoveringMap x).continuous).cast rfl h.symm
  have hΓ : (Γ : C(I, P.basedTopologicalUniversalCover x)) =
      P.gluedUniversalCoverPathLift x e₀ β :=
    (P.eq_gluedUniversalCoverPathLift_iff x e₀ β Γ).mpr ⟨rfl, Γ.source⟩
  change β.Homotopic (Path.refl (P.gluedUniversalCoverProjection x e₀)) ↔ e₁ = e₀
  rw [← P.gluedUniversalCoverLoopLift_one_eq_iff, ← hΓ]
  change Γ 1 = e₀ ↔ e₁ = e₀
  rw [Γ.target]

/-- Every path between distinct points in one native cover fiber pays the
target downstairs. No unconstructed metric or isometry upstairs is assumed. -/
theorem targetSystole_le_variation_of_universalCover_path
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    {e₀ e₁ : P.basedTopologicalUniversalCover x}
    (h : P.gluedUniversalCoverProjection x e₁ = P.gluedUniversalCoverProjection x e₀)
    (hne : e₁ ≠ e₀) (Γ : Path e₀ e₁) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ENNReal.ofReal (targetSystole C g) ≤
      eVariationOn (P.gluedUniversalCoverProjection x ∘ Γ) univ := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  apply P.targetSystole_le_variation_of_essential_path
    ((Γ.map (P.gluedUniversalCoverProjection_isCoveringMap x).continuous).cast rfl h.symm)
  exact fun hnull => hne
    ((P.gluedUniversalCover_projectedPath_nullhomotopic_iff x h Γ).mp hnull)

/-- Actual endpoint-fixed path homotopy classes are open in the native
compact-open topology, by the imported semilocal theorem. -/
theorem gluedCarrier_isOpen_setOf_path_homotopic
    (P : ExerciseGluingPreparation C g n genera X) {x y : P.GluedCarrier}
    (p : Path x y) :
    IsOpen {q : Path x y | q.Homotopic p} :=
  p.isOpen_setOf_homotopic

/-- The actual native path-homotopy quotient is discrete. -/
theorem gluedCarrier_pathHomotopyQuotient_discreteTopology
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier) :
    DiscreteTopology (Path.Homotopic.Quotient x y) := inferInstance

end SystolicGrowth.ExerciseGluingPreparation

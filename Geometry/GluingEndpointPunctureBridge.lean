module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingPuncturedComponentHomotopy
public import Geometry.DirichletPuncturedSpine
public import Geometry.DirichletPuncturePolarLoop
public import Geometry.SurfaceTwoCenterBoundarySpine

@[expose] public section

/-!
# Endpoint components are the actual one-center-punctured surfaces

The first and last components of a gluing chain have only one active puncture.
Their center-punctured carriers are homeomorphic, by the identity on original
quotient points, to the existing one-center-punctured carriers. The induced
based fundamental-group equivalences are the literal maps of these
homeomorphisms, so they can be composed with the one-puncture spine marking.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane Topology

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

def Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex (hn : 2 ≤ n) : Fin n := ⟨0, by omega⟩

def Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex (hn : 2 ≤ n) : Fin n := ⟨n - 1, by omega⟩

theorem firstEndpointCenterPunctured_mem_iff
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (q : (X (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)).Carrier) :
    q ∈ P.componentCenterPuncturedSet (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn) ↔
      q ≠ (Quotient.mk'' (P.centers (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)).2 :
        (X (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)).Carrier) := by
  have hnext : 0 + 1 < n := by omega
  rw [P.componentCenterPuncturedSet_eq]
  simp only [Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex, hnext]
  change q ∉ (∅ ∪ {(Quotient.mk'' (P.centers (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)).2 :
    (X (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)).Carrier)}) ↔ _
  constructor
  · intro h heq
    apply h
    exact Set.mem_union_right ∅ (Set.mem_singleton_iff.mpr heq)
  · intro h hmem
    rcases Set.mem_or_mem_of_mem_union hmem with hempty | hsingle
    · exact hempty.elim
    · exact h (Set.mem_singleton_iff.mp hsingle)

theorem lastEndpointCenterPunctured_mem_iff
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (q : (X (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)).Carrier) :
    q ∈ P.componentCenterPuncturedSet (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn) ↔
      q ≠ (Quotient.mk'' (P.centers (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)).1 :
        (X (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)).Carrier) := by
  have hlast : 0 < n - 1 := by omega
  have hnotnext : ¬ (n - 1 + 1 < n) := by omega
  rw [P.componentCenterPuncturedSet_eq]
  simp only [Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex, hlast, hnotnext]
  change q ∉ ({(Quotient.mk'' (P.centers (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)).1 :
    (X (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)).Carrier)} ∪ ∅) ↔ _
  constructor
  · intro h heq
    apply h
    exact Set.mem_union_left ∅ (Set.mem_singleton_iff.mpr heq)
  · intro h hmem
    rcases Set.mem_or_mem_of_mem_union hmem with hsingle | hempty
    · exact h (Set.mem_singleton_iff.mp hsingle)
    · exact hempty.elim

/-- Identity-on-quotient homeomorphism from the first actual chain component
with its active center removed to the original one-center-punctured carrier. -/
def firstEndpointCenterPuncturedHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n) :
    P.CenterPuncturedChainComponent (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn) ≃ₜ
      (X (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)).CenterPuncturedCarrier
        (P.centers (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)).2 where
  toFun q := ⟨q.1,
    (P.firstEndpointCenterPunctured_mem_iff hn q.1).mp q.2⟩
  invFun q := ⟨q.1,
    (P.firstEndpointCenterPunctured_mem_iff hn q.1).mpr q.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem firstEndpointCenterPuncturedHomeomorph_val
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (q : P.CenterPuncturedChainComponent (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)) :
    (P.firstEndpointCenterPuncturedHomeomorph hn q).1 = q.1 := rfl

/-- Identity-on-quotient homeomorphism from the last actual chain component
with its active center removed to the original one-center-punctured carrier. -/
def lastEndpointCenterPuncturedHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n) :
    P.CenterPuncturedChainComponent (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn) ≃ₜ
      (X (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)).CenterPuncturedCarrier
        (P.centers (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)).1 where
  toFun q := ⟨q.1,
    (P.lastEndpointCenterPunctured_mem_iff hn q.1).mp q.2⟩
  invFun q := ⟨q.1,
    (P.lastEndpointCenterPunctured_mem_iff hn q.1).mpr q.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem lastEndpointCenterPuncturedHomeomorph_val
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (q : P.CenterPuncturedChainComponent (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)) :
    (P.lastEndpointCenterPuncturedHomeomorph hn q).1 = q.1 := rfl

noncomputable def Internal.GluingEndpointPunctureBridgeHelpers.fundamentalGroupEquivOfHomeomorph
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : Y ≃ₜ Z) (q : Y) : FundamentalGroup Y q ≃* FundamentalGroup Z (e q) := by
  let h := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e.toHomotopyEquiv
  have hbij : Function.Bijective (FundamentalGroup.map ⟨e, e.continuous⟩ q) :=
    h.fullyFaithfulFunctor.map_bijective
      (FundamentalGroupoid.mk q) (FundamentalGroupoid.mk q)
  exact MulEquiv.ofBijective (FundamentalGroup.map ⟨e, e.continuous⟩ q) hbij

/-- The first endpoint identification induces the based group equivalence by
the literal identity-on-quotient homeomorphism. -/
def firstEndpointPuncturedFundamentalGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (q : P.CenterPuncturedChainComponent (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)) :
    FundamentalGroup (P.CenterPuncturedChainComponent (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)) q ≃*
      FundamentalGroup ((X (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)).CenterPuncturedCarrier
        (P.centers (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)).2)
        (P.firstEndpointCenterPuncturedHomeomorph hn q) :=
  Internal.GluingEndpointPunctureBridgeHelpers.fundamentalGroupEquivOfHomeomorph (P.firstEndpointCenterPuncturedHomeomorph hn) q

@[simp]
theorem firstEndpointPuncturedFundamentalGroupEquiv_loop
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (q : P.CenterPuncturedChainComponent (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)) (p : Path q q) :
    P.firstEndpointPuncturedFundamentalGroupEquiv hn q ⟦p⟧ =
      ⟦p.map (P.firstEndpointCenterPuncturedHomeomorph hn).continuous⟧ := rfl

/-- The last endpoint identification induces the based group equivalence by
the literal identity-on-quotient homeomorphism. -/
def lastEndpointPuncturedFundamentalGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (q : P.CenterPuncturedChainComponent (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)) :
    FundamentalGroup (P.CenterPuncturedChainComponent (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)) q ≃*
      FundamentalGroup ((X (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)).CenterPuncturedCarrier
        (P.centers (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)).1)
        (P.lastEndpointCenterPuncturedHomeomorph hn q) :=
  Internal.GluingEndpointPunctureBridgeHelpers.fundamentalGroupEquivOfHomeomorph (P.lastEndpointCenterPuncturedHomeomorph hn) q

@[simp]
theorem lastEndpointPuncturedFundamentalGroupEquiv_loop
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (q : P.CenterPuncturedChainComponent (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)) (p : Path q q) :
    P.lastEndpointPuncturedFundamentalGroupEquiv hn q ⟦p⟧ =
      ⟦p.map (P.lastEndpointCenterPuncturedHomeomorph hn).continuous⟧ := rfl

/-- The chosen gluing radius is strictly below half the systole of each
component, as required by the one-center Dirichlet polar-circle API. -/
theorem radius_twice_lt_componentSystole
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    2 * gluingRadius C g < (X i).systole := by
  calc
    2 * gluingRadius C g < 2 * gluingEmbeddedRadius C g := by
      nlinarith [P.radius_lt_embeddedRadius]
    _ < (X i).systole := P.twice_outer_lt_systole i

/-- ContinuousMap form of the first endpoint identity homeomorphism. -/
def firstEndpointCenterPuncturedMap
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n) :
    C(P.CenterPuncturedChainComponent (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn),
      (X (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)).CenterPuncturedCarrier
        (P.centers (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)).2) where
  toFun := P.firstEndpointCenterPuncturedHomeomorph hn
  continuous_toFun := (P.firstEndpointCenterPuncturedHomeomorph hn).continuous

/-- ContinuousMap form of the last endpoint identity homeomorphism. -/
def lastEndpointCenterPuncturedMap
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n) :
    C(P.CenterPuncturedChainComponent (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn),
      (X (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)).CenterPuncturedCarrier
        (P.centers (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)).1) where
  toFun := P.lastEndpointCenterPuncturedHomeomorph hn
  continuous_toFun := (P.lastEndpointCenterPuncturedHomeomorph hn).continuous

/-- The first endpoint's actual outgoing boundary circle becomes the original
one-center polar circle, by the identity on the ambient quotient carrier. -/
theorem firstEndpointHomeomorph_comp_rightPolarBoundaryMap
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n) :
    (P.firstEndpointCenterPuncturedMap hn).comp
        (P.componentRightPolarBoundaryMap (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)) =
      (X (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)).dirichletPuncturePolarCircle
        (P.centers (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)).2 (gluingRadius C g) P.radius_pos
        (P.radius_twice_lt_componentSystole (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)) := by
  apply ContinuousMap.ext
  intro θ
  apply Subtype.ext
  rfl

/-- The last endpoint's actual incoming boundary circle becomes the original
one-center polar circle, by the identity on the ambient quotient carrier. -/
theorem lastEndpointHomeomorph_comp_leftPolarBoundaryMap
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n) :
    (P.lastEndpointCenterPuncturedMap hn).comp
        (P.componentLeftPolarBoundaryMap (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)) =
      (X (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)).dirichletPuncturePolarCircle
        (P.centers (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)).1 (gluingRadius C g) P.radius_pos
        (P.radius_twice_lt_componentSystole (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)) := by
  apply ContinuousMap.ext
  intro θ
  apply Subtype.ext
  rfl

/-- The endpoint map transports the exact original outgoing one-turn loop to
the actual one-center positive polar loop without changing its basepoint. -/
theorem firstEndpointHomeomorph_map_rightPolarBoundaryLoop
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n) :
    (P.componentRightPolarBoundaryLoop (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)).map
        (P.firstEndpointCenterPuncturedHomeomorph hn).continuous =
      (X (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)).dirichletPuncturePolarOneTurn
        (P.centers (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)).2 (gluingRadius C g) P.radius_pos
        (P.radius_twice_lt_componentSystole (Internal.GluingEndpointPunctureBridgeHelpers.firstEndpointIndex hn)) 1 := by
  rw [ExerciseGluingPreparation.componentRightPolarBoundaryLoop,
    ClosedHyperbolicSurface.dirichletPuncturePolarOneTurn, Path.map_map]
  congr 1

/-- The endpoint map transports the exact original incoming one-turn loop to
the actual one-center positive polar loop without changing its basepoint. -/
theorem lastEndpointHomeomorph_map_leftPolarBoundaryLoop
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n) :
    (P.componentLeftPolarBoundaryLoop (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)).map
        (P.lastEndpointCenterPuncturedHomeomorph hn).continuous =
      (X (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)).dirichletPuncturePolarOneTurn
        (P.centers (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)).1 (gluingRadius C g) P.radius_pos
        (P.radius_twice_lt_componentSystole (Internal.GluingEndpointPunctureBridgeHelpers.lastEndpointIndex hn)) 1 := by
  rw [ExerciseGluingPreparation.componentLeftPolarBoundaryLoop,
    ClosedHyperbolicSurface.dirichletPuncturePolarOneTurn, Path.map_map]
  congr 1

#print axioms firstEndpointCenterPuncturedHomeomorph
#print axioms lastEndpointCenterPuncturedHomeomorph
#print axioms ExerciseGluingPreparation.componentCenterPuncturedSet_eq
#print axioms firstEndpointPuncturedFundamentalGroupEquiv
#print axioms lastEndpointPuncturedFundamentalGroupEquiv
#print axioms firstEndpointHomeomorph_comp_rightPolarBoundaryMap
#print axioms lastEndpointHomeomorph_comp_leftPolarBoundaryMap
#print axioms firstEndpointHomeomorph_map_rightPolarBoundaryLoop
#print axioms lastEndpointHomeomorph_map_leftPolarBoundaryLoop

end
end SystolicGrowth.ExerciseGluingPreparation

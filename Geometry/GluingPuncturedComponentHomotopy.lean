module

public import Geometry.SurfacePunctureRetraction
public import Geometry.GluingChainQuotient
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

@[expose] public section

/-!
# The actual retained component is a strong deformation retract

Remove precisely the actual disk centers prescribed by the component index.
Radial pushes inside the original embedded hyperbolic charts retract this
center-punctured quotient onto the original retained component. Each push
fixes the complement of its inner open disk; the supplied outer-plus-inner
separation preserves the other puncture. Disjoint outer balls are not assumed.
-/

open Set Metric
open scoped UpperHalfPlane Topology unitInterval ContinuousMap

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

def Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureActive (i : Fin n) (b : Bool) : Prop :=
  if b then 0 < i.1 else i.1 + 1 < n

def Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureCenter
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool) : ℍ :=
  if b then (P.centers i).1 else (P.centers i).2

/-- The original quotient with exactly its actually deleted disk centers removed.
The endpoint components remove one center; internal components remove two. -/
def componentCenterPuncturedSet
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) : Set (X i).Carrier :=
  {q | ∀ b : Bool, Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureActive i b →
    q ≠ (Quotient.mk'' (Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureCenter P i b) : (X i).Carrier)}

/-- The native center-punctured carrier; it retains the original quotient topology. -/
abbrev CenterPuncturedChainComponent
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :=
  ↥(P.componentCenterPuncturedSet i)

/-- The domain literally deletes the prescribed singleton centers, not disks
or an unrelated punctured replacement. -/
theorem componentCenterPuncturedSet_eq
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.componentCenterPuncturedSet i =
      ((if 0 < i.1 then {(Quotient.mk'' (P.centers i).1 : (X i).Carrier)} else ∅) ∪
       (if i.1 + 1 < n then {(Quotient.mk'' (P.centers i).2 : (X i).Carrier)} else ∅))ᶜ := by
  ext q
  by_cases hl : 0 < i.1 <;> by_cases hr : i.1 + 1 < n <;>
    simp [componentCenterPuncturedSet, Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureActive,
      Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureCenter, Bool.forall_bool, hl, hr, and_comm]

private theorem componentRetained_iff
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (q : (X i).Carrier) :
    q ∈ (X i).puncturedComponentSet (P.centers i).1 (P.centers i).2
      (gluingRadius C g) i ↔
      ∀ b : Bool, Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureActive i b →
        q ∉ (X i).orbitBall (Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureCenter P i b) (gluingRadius C g) := by
  by_cases hl : 0 < i.1 <;> by_cases hr : i.1 + 1 < n <;>
    simp [ClosedHyperbolicSurface.puncturedComponentSet,
      ClosedHyperbolicSurface.punctureDeletedSet, Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureActive,
      Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureCenter, Bool.forall_bool, hl, hr, and_comm]

private theorem componentCenter_mem_inner
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool) :
    (Quotient.mk'' (Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureCenter P i b) : (X i).Carrier) ∈
      (X i).orbitBall (Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureCenter P i b) (gluingRadius C g) :=
  ⟨_, mem_ball_self P.radius_pos, rfl⟩

/-- The complete original retained component lies in the actual center-punctured domain. -/
theorem componentRetained_subset_centerPunctured
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (X i).puncturedComponentSet (P.centers i).1 (P.centers i).2
      (gluingRadius C g) i ⊆ P.componentCenterPuncturedSet i := by
  intro q hq b hb heq
  exact (componentRetained_iff P i q).mp hq b hb
    (heq ▸ componentCenter_mem_inner P i b)

private theorem componentOuter_disjoint_other_inner
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool) :
    Disjoint ((X i).orbitBall (Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureCenter P i b) (gluingEmbeddedRadius C g))
      ((X i).orbitBall (Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureCenter P i (!b)) (gluingRadius C g)) := by
  cases b
  · exact (X i).disjoint_orbitBalls_of_orbit_separated _ _ _ _
      ((X i).orbit_separation_symm _ _ _ (P.separated_outer_add_inner i))
  · exact (X i).disjoint_orbitBalls_of_orbit_separated _ _ _ _
      (P.separated_outer_add_inner i)

def Internal.GluingPuncturedComponentHomotopyHelpers.componentActivePushFn
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool)
    (hb : Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureActive i b) (p : I × P.CenterPuncturedChainComponent i) :
    (X i).Carrier :=
  (X i).puncturePushFn (Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureCenter P i b) (gluingRadius C g)
    (gluingEmbeddedRadius C g) P.radius_lt_embeddedRadius (P.twice_outer_lt_systole i)
      (p.1, ⟨p.2.1, p.2.2 b hb⟩)

theorem Internal.GluingPuncturedComponentHomotopyHelpers.componentActivePushFn_mem
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool)
    (hb : Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureActive i b) (p : I × P.CenterPuncturedChainComponent i) :
    Internal.GluingPuncturedComponentHomotopyHelpers.componentActivePushFn P i b hb p ∈ P.componentCenterPuncturedSet i := by
  intro c hc
  by_cases hcb : c = b
  · subst c
    exact (X i).puncturePushFn_ne_center _ _ _ P.radius_lt_embeddedRadius
      (P.twice_outer_lt_systole i) _
  · have hc' : c = !b := by cases b <;> cases c <;> simp_all
    subst c
    have hs : Disjoint
        ((X i).orbitBall (Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureCenter P i b) (gluingEmbeddedRadius C g))
        {(Quotient.mk'' (Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureCenter P i (!b)) : (X i).Carrier)} :=
      (componentOuter_disjoint_other_inner P i b).mono Set.Subset.rfl
        (singleton_subset_iff.mpr (componentCenter_mem_inner P i (!b)))
    exact (X i).puncturePushFn_preserves_not_mem _ _ _ P.radius_lt_embeddedRadius
      (P.twice_outer_lt_systole i) _ _ hs (by simpa using p.2.2 (!b) hc)

def Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool) :
    C(I × P.CenterPuncturedChainComponent i, P.CenterPuncturedChainComponent i) := by
  classical
  exact if hb : Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureActive i b then
    { toFun := fun p => ⟨Internal.GluingPuncturedComponentHomotopyHelpers.componentActivePushFn P i b hb p,
        Internal.GluingPuncturedComponentHomotopyHelpers.componentActivePushFn_mem P i b hb p⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact ((X i).puncturePushFn_continuous _ _ _ P.radius_lt_embeddedRadius
          (P.twice_outer_lt_systole i)).comp
            (continuous_fst.prodMk
              ((continuous_subtype_val.comp continuous_snd).subtype_mk _)) }
    else ContinuousMap.snd

private theorem componentSidePushMap_zero
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool)
    (q : P.CenterPuncturedChainComponent i) : Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap P i b (0, q) = q := by
  classical
  apply Subtype.ext
  by_cases hb : Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureActive i b
  · simpa only [Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap, dif_pos hb, ContinuousMap.coe_mk, Internal.GluingPuncturedComponentHomotopyHelpers.componentActivePushFn]
      using (X i).puncturePushFn_zero _ _ _ P.radius_lt_embeddedRadius
        (P.twice_outer_lt_systole i) ⟨q.1, q.2 b hb⟩
  · simp [Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap, hb]

private theorem componentSidePushMap_fixed
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool)
    (p : I × P.CenterPuncturedChainComponent i)
    (hp : p.2.1 ∈ (X i).puncturedComponentSet (P.centers i).1 (P.centers i).2
      (gluingRadius C g) i) : Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap P i b p = p.2 := by
  classical
  apply Subtype.ext
  by_cases hb : Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureActive i b
  · simp only [Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap, dif_pos hb, ContinuousMap.coe_mk]
    exact (X i).puncturePushFn_fixed (Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureCenter P i b) _ _
      P.radius_lt_embeddedRadius (P.twice_outer_lt_systole i)
      (p.1, ⟨p.2.1, p.2.2 b hb⟩) ((componentRetained_iff P i _).mp hp b hb)
  · simp [Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap, hb]

private theorem componentSidePushMap_preserves_other
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool)
    (p : I × P.CenterPuncturedChainComponent i)
    (hp : p.2.1 ∉ (X i).orbitBall (Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureCenter P i (!b)) (gluingRadius C g)) :
    (Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap P i b p).1 ∉
      (X i).orbitBall (Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureCenter P i (!b)) (gluingRadius C g) := by
  classical
  by_cases hb : Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureActive i b
  · simp only [Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap, dif_pos hb, ContinuousMap.coe_mk]
    exact (X i).puncturePushFn_preserves_not_mem _ _ _ P.radius_lt_embeddedRadius
      (P.twice_outer_lt_systole i) (p.1, ⟨p.2.1, p.2.2 b hb⟩) _
      (componentOuter_disjoint_other_inner P i b) hp
  · simpa [Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap, hb] using hp

private theorem componentSidePushMap_one_not_mem
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool)
    (hb : Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureActive i b) (q : P.CenterPuncturedChainComponent i) :
    (Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap P i b (1, q)).1 ∉
      (X i).orbitBall (Internal.GluingPuncturedComponentHomotopyHelpers.componentPunctureCenter P i b) (gluingRadius C g) := by
  classical
  simpa only [Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap, dif_pos hb, ContinuousMap.coe_mk, Internal.GluingPuncturedComponentHomotopyHelpers.componentActivePushFn]
    using (X i).puncturePushFn_one_not_mem_inner _ _ _ P.radius_lt_embeddedRadius
      (P.twice_outer_lt_systole i) ⟨q.1, q.2 b hb⟩

/-- Both actual punctures are pushed with the same time parameter. Every
intermediate point remains in the original center-punctured quotient. -/
def componentPunctureHomotopyMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    C(I × P.CenterPuncturedChainComponent i, P.CenterPuncturedChainComponent i) :=
  (Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap P i false).comp
    (ContinuousMap.fst.prodMk (Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap P i true))

@[simp]
theorem componentPunctureHomotopyMap_zero
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.CenterPuncturedChainComponent i) : P.componentPunctureHomotopyMap i (0, q) = q := by
  change Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap P i false (0, Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap P i true (0, q)) = q
  rw [componentSidePushMap_zero, componentSidePushMap_zero]

/-- The complete retained carrier, in particular each original polar boundary
loop, stays pointwise fixed throughout the homotopy. -/
theorem componentPunctureHomotopyMap_fixed
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (p : I × P.CenterPuncturedChainComponent i)
    (hp : p.2.1 ∈ (X i).puncturedComponentSet (P.centers i).1 (P.centers i).2
      (gluingRadius C g) i) : P.componentPunctureHomotopyMap i p = p.2 := by
  change Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap P i false (p.1, Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap P i true p) = p.2
  rw [componentSidePushMap_fixed P i true p hp]
  exact componentSidePushMap_fixed P i false p hp

theorem componentPunctureHomotopyMap_one_mem
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.CenterPuncturedChainComponent i) :
    (P.componentPunctureHomotopyMap i (1, q)).1 ∈
      (X i).puncturedComponentSet (P.centers i).1 (P.centers i).2 (gluingRadius C g) i := by
  apply (componentRetained_iff P i _).mpr
  intro b hb
  cases b
  · exact componentSidePushMap_one_not_mem P i false hb (Internal.GluingPuncturedComponentHomotopyHelpers.componentSidePushMap P i true (1, q))
  · exact componentSidePushMap_preserves_other P i false _
      (componentSidePushMap_one_not_mem P i true hb q)

/-- Literal inclusion of the original retained component into its center-punctured quotient. -/
def componentPunctureInclusion
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    C(P.ChainComponent i, P.CenterPuncturedChainComponent i) where
  toFun q := ⟨q.1, P.componentRetained_subset_centerPunctured i q.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The endpoint radial retraction has the actual retained component as codomain. -/
def componentPunctureRetraction
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    C(P.CenterPuncturedChainComponent i, P.ChainComponent i) where
  toFun q := ⟨(P.componentPunctureHomotopyMap i (1, q)).1,
    P.componentPunctureHomotopyMap_one_mem i q⟩
  continuous_toFun :=
    ((P.componentPunctureHomotopyMap i).continuous.comp
      (continuous_const.prodMk continuous_id)).subtype_val.subtype_mk _

@[simp]
theorem componentPunctureRetraction_inclusion
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (q : P.ChainComponent i) :
    P.componentPunctureRetraction i (P.componentPunctureInclusion i q) = q := by
  apply Subtype.ext
  change (P.componentPunctureHomotopyMap i (1, P.componentPunctureInclusion i q)).1 = q.1
  exact congrArg (fun z : P.CenterPuncturedChainComponent i => z.1)
    (P.componentPunctureHomotopyMap_fixed i (1, P.componentPunctureInclusion i q) q.2)

/-- Genuine strong deformation retraction of the original center-punctured
quotient onto the entire actual retained component. -/
def componentPunctureDeformationRetraction
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (ContinuousMap.id (P.CenterPuncturedChainComponent i)).HomotopyRel
      ((P.componentPunctureInclusion i).comp (P.componentPunctureRetraction i))
      {q | q.1 ∈ (X i).puncturedComponentSet (P.centers i).1 (P.centers i).2
        (gluingRadius C g) i} where
  toHomotopy :=
    { toContinuousMap := P.componentPunctureHomotopyMap i
      map_zero_left := P.componentPunctureHomotopyMap_zero i
      map_one_left := fun _ => rfl }
  prop' := fun t q hq => P.componentPunctureHomotopyMap_fixed i (t, q) hq

/-- Every original retained point is fixed for all times; this includes the
literal incoming and outgoing polar circle maps used by the gluing. -/
@[simp]
theorem componentPunctureDeformationRetraction_inclusion
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (t : I) (q : P.ChainComponent i) :
    P.componentPunctureDeformationRetraction i (t, P.componentPunctureInclusion i q) =
      P.componentPunctureInclusion i q :=
  P.componentPunctureHomotopyMap_fixed i (t, P.componentPunctureInclusion i q) q.2

theorem componentPunctureRetraction_inclusion_loop
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.ChainComponent i) (p : Path q q) :
    ((p.map (P.componentPunctureInclusion i).continuous).map
      (P.componentPunctureRetraction i).continuous).cast
        (P.componentPunctureRetraction_inclusion i q).symm
        (P.componentPunctureRetraction_inclusion i q).symm = p := by
  apply Path.ext
  funext t
  exact P.componentPunctureRetraction_inclusion i (p t)

/-- The reversed strong deformation retraction restricts to a genuine based
loop homotopy. The original retained basepoint remains fixed for all times. -/
def componentPunctureInclusionRetractionLoopHomotopy
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.ChainComponent i)
    (p : Path (P.componentPunctureInclusion i q) (P.componentPunctureInclusion i q)) :
    Path.Homotopy
      (((p.map (P.componentPunctureRetraction i).continuous).cast
        (P.componentPunctureRetraction_inclusion i q).symm
        (P.componentPunctureRetraction_inclusion i q).symm).map
          (P.componentPunctureInclusion i).continuous) p where
  toFun a := (P.componentPunctureDeformationRetraction i).symm (a.1, p a.2)
  continuous_toFun := (P.componentPunctureDeformationRetraction i).symm.continuous.comp
    (continuous_fst.prodMk (p.continuous.comp continuous_snd))
  map_zero_left := fun t => (P.componentPunctureDeformationRetraction i).symm.apply_zero (p t)
  map_one_left := fun t => (P.componentPunctureDeformationRetraction i).symm.apply_one (p t)
  prop' := by
    intro t u hu
    have hfix : (P.componentPunctureDeformationRetraction i).symm
        (t, P.componentPunctureInclusion i q) = P.componentPunctureInclusion i q :=
      (P.componentPunctureDeformationRetraction i).symm.eq_snd t q.2
    rcases hu with hu | hu
    · subst u
      change (P.componentPunctureDeformationRetraction i).symm (t, p 0) =
        P.componentPunctureInclusion i (P.componentPunctureRetraction i (p 0))
      rw [p.source, P.componentPunctureRetraction_inclusion]
      exact hfix
    · have hu : u = 1 := by simpa using hu
      subst u
      change (P.componentPunctureDeformationRetraction i).symm (t, p 1) =
        P.componentPunctureInclusion i (P.componentPunctureRetraction i (p 1))
      rw [p.target, P.componentPunctureRetraction_inclusion]
      exact hfix

/-- Exact based π₁ equivalence at every actual retained point. The forward map
is the radial retraction and the inverse is the original literal inclusion. -/
def componentPunctureFundamentalGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.ChainComponent i) :
    FundamentalGroup (P.CenterPuncturedChainComponent i) (P.componentPunctureInclusion i q) ≃*
      FundamentalGroup (P.ChainComponent i) q where
  toFun := FundamentalGroup.mapOfEq (P.componentPunctureRetraction i)
    (P.componentPunctureRetraction_inclusion i q)
  invFun := FundamentalGroup.map (P.componentPunctureInclusion i) q
  left_inv := by
    intro γ
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
      ← Path.Homotopic.Quotient.mk_map, Path.Homotopic.Quotient.eq]
    exact ⟨P.componentPunctureInclusionRetractionLoopHomotopy i q p⟩
  right_inv := by
    intro γ
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast, P.componentPunctureRetraction_inclusion_loop]
  map_mul' := (FundamentalGroup.mapOfEq (P.componentPunctureRetraction i)
    (P.componentPunctureRetraction_inclusion i q)).map_mul

theorem componentPunctureFundamentalGroupEquiv_toMonoidHom
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.ChainComponent i) :
    (P.componentPunctureFundamentalGroupEquiv i q).toMonoidHom =
      FundamentalGroup.mapOfEq (P.componentPunctureRetraction i)
        (P.componentPunctureRetraction_inclusion i q) := rfl

theorem componentPunctureFundamentalGroupEquiv_symm_toMonoidHom
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.ChainComponent i) :
    (P.componentPunctureFundamentalGroupEquiv i q).symm.toMonoidHom =
      FundamentalGroup.map (P.componentPunctureInclusion i) q := rfl

/-- Retained loops, hence the original peripheral polar loops, are preserved
by the based equivalence with no change of their representative paths. -/
@[simp]
theorem componentPunctureFundamentalGroupEquiv_map_loop
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.ChainComponent i) (p : Path q q) :
    P.componentPunctureFundamentalGroupEquiv i q
      ⟦p.map (P.componentPunctureInclusion i).continuous⟧ = ⟦p⟧ :=
  (P.componentPunctureFundamentalGroupEquiv i q).apply_symm_apply ⟦p⟧

end

end SystolicGrowth.ExerciseGluingPreparation

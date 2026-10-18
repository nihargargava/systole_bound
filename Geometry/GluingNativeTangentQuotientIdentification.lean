module

public import Geometry.GluingNativeTangentDescent
public import Geometry.GluingNativeComponentTangentEquivariance
public import Geometry.GluingSpinChainCovering
public import Geometry.GluingSeamOverlap
public import Geometry.GluingNativeTangentCollarOverlap

@[expose] public section

/-!
# The actual native unit tangent bundle of the clutched surface

The genuine component-interior and retained-collar maps are patched on the
original physical frame orbits. Literal Fermi boundary clutching then descends
this map to the already constructed compact frame quotient.
-/

open Set Metric UpperHalfPlane Topology Filter Bundle
open scoped UpperHalfPlane MatrixGroups ContinuousMap

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- An overlap of two retained collars lies in the genuine component interior,
by actual separation of the two deleted disks. -/
theorem mem_componentInteriorSet_of_mem_both_collars
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.ChainComponent i) (hl : q ∈ P.incomingCollar i)
    (hr : q ∈ P.outgoingCollar i) : q.val ∈ P.componentInteriorSet i := by
  have hlb := (X i).punctureCollar_subset_orbitBall _ _ _ hl
  have hrb := (X i).punctureCollar_subset_orbitBall _ _ _ hr
  rw [← (X i).carrier_ball_eq_orbitBall] at hlb hrb
  have hlr : dist q.val (Quotient.mk'' (P.centers i).1) < gluingEmbeddedRadius C g := hlb
  have hrr : dist q.val (Quotient.mk'' (P.centers i).2) < gluingEmbeddedRadius C g := hrb
  have htri := dist_triangle (Quotient.mk'' (P.centers i).1 : (X i).Carrier) q.val
    (Quotient.mk'' (P.centers i).2)
  rw [dist_comm (Quotient.mk'' (P.centers i).1) q.val] at htri
  have hsep := P.carrier_centers_outer_add_inner_le_dist i
  exact P.mem_componentInteriorSet_of_radius_lt_dist i q.val (by linarith) (by linarith)

/-- Genuine local domains covering one retained component, indexed by its
actual incident path edges rather than an invented frame atlas. -/
inductive ComponentTangentPatch (n : ℕ) (i : Fin n) where
  | interior
  | incoming (k : Fin (n - 1)) (index_eq : gluingChainEdgeRight k = i)
  | outgoing (k : Fin (n - 1)) (index_eq : gluingChainEdgeLeft k = i)

def componentTangentPatchSet (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (s : ComponentTangentPatch n i) : Set (P.TangentChainComponent i) := by
  cases s with
  | interior => exact {q | (X i).tangentFrameBase q.val ∈ P.componentInteriorSet i}
  | incoming k hi =>
    subst i
    exact {q | P.tangentChainComponentBase _ q ∈ P.incomingCollar _}
  | outgoing k hi =>
    subst i
    exact {q | P.tangentChainComponentBase _ q ∈ P.outgoingCollar _}

/-- Literal physical native transport on each already verified local domain. -/
def componentTangentPatchMap (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (s : ComponentTangentPatch n i) : P.componentTangentPatchSet i s → P.NativeUnitTangentCarrier := by
  cases s with
  | interior =>
    exact fun q => (P.nativeComponentInteriorUnitTangentHomeomorph i ⟨q.val.val, q.property⟩).val
  | incoming k hi =>
    subst i
    exact P.incomingTangentCollarNativeUnit k
  | outgoing k hi =>
    subst i
    exact P.outgoingTangentCollarNativeUnit k

theorem componentTangentPatchSet_isOpen
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (s : ComponentTangentPatch n i) : IsOpen (P.componentTangentPatchSet i s) := by
  cases s with
  | interior =>
    exact isOpen_interior.preimage ((X i).continuous_tangentFrameBase.comp continuous_subtype_val)
  | incoming k hi =>
    subst i
    exact (P.incomingCollar_isOpen _ (by simp [gluingChainEdgeRight])).preimage
      (((X _).continuous_tangentFrameBase.comp continuous_subtype_val).subtype_mk _)
  | outgoing k hi =>
    subst i
    exact (P.outgoingCollar_isOpen _ (by have := k.2; simp only [gluingChainEdgeLeft]; omega)).preimage
      (((X _).continuous_tangentFrameBase.comp continuous_subtype_val).subtype_mk _)

theorem continuous_componentTangentPatchMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (s : ComponentTangentPatch n i) : Continuous (P.componentTangentPatchMap i s) := by
  cases s with
  | interior =>
    exact continuous_subtype_val.comp ((P.nativeComponentInteriorUnitTangentHomeomorph i).continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))
  | incoming k hi =>
    subst i
    exact P.continuous_incomingTangentCollarNativeUnit k
  | outgoing k hi =>
    subst i
    exact P.continuous_outgoingTangentCollarNativeUnit k

theorem componentTangentPatchSet_incoming_iff
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (k : Fin (n - 1))
    (hi : gluingChainEdgeRight k = i) (q : P.TangentChainComponent i) :
    q ∈ P.componentTangentPatchSet i (.incoming k hi) ↔
      P.tangentChainComponentBase i q ∈ P.incomingCollar i := by
  subst i
  rfl

theorem componentTangentPatchSet_outgoing_iff
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (k : Fin (n - 1))
    (hi : gluingChainEdgeLeft k = i) (q : P.TangentChainComponent i) :
    q ∈ P.componentTangentPatchSet i (.outgoing k hi) ↔
      P.tangentChainComponentBase i q ∈ P.outgoingCollar i := by
  subst i
  rfl

theorem exists_componentTangentPatch
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.TangentChainComponent i) : ∃ s : ComponentTangentPatch n i,
      q ∈ P.componentTangentPatchSet i s := by
  by_cases hl : ∃ h : 0 < i.val, P.tangentChainComponentBase i q ∈ P.incomingCollar i
  · obtain ⟨hi, hq⟩ := hl
    let k : Fin (n - 1) := ⟨i.val - 1, by have := i.2; omega⟩
    have hki : gluingChainEdgeRight k = i := Fin.ext (by dsimp [gluingChainEdgeRight, k]; omega)
    refine ⟨.incoming k hki, ?_⟩
    exact (P.componentTangentPatchSet_incoming_iff i k hki q).mpr hq
  by_cases hr : ∃ h : i.val + 1 < n, P.tangentChainComponentBase i q ∈ P.outgoingCollar i
  · obtain ⟨hi, hq⟩ := hr
    let k : Fin (n - 1) := ⟨i.val, by omega⟩
    have hki : gluingChainEdgeLeft k = i := Fin.ext rfl
    refine ⟨.outgoing k hki, ?_⟩
    exact (P.componentTangentPatchSet_outgoing_iff i k hki q).mpr hq
  exact ⟨.interior, P.mem_componentInteriorSet_of_not_mem_collars i
    (P.tangentChainComponentBase i q) (fun hi hq => hl ⟨hi, hq⟩) (fun hi hq => hr ⟨hi, hq⟩)⟩

/-- Every local map keeps the actual base point of its retained component. -/
theorem componentTangentPatchMap_proj
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (s : ComponentTangentPatch n i) (q : P.componentTangentPatchSet i s) :
    (P.componentTangentPatchMap i s q).val.proj =
      P.gluedMk ⟨i, P.tangentChainComponentBase i q.val⟩ := by
  cases s with
  | interior => exact P.nativeComponentInteriorUnitTangentHomeomorph_proj i _
  | incoming k hi =>
    subst i
    exact P.incomingTangentCollarNativeUnit_proj k q
  | outgoing k hi =>
    subst i
    exact P.outgoingTangentCollarNativeUnit_proj k q

theorem componentTangentPatchMap_injective
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (s : ComponentTangentPatch n i) : Function.Injective (P.componentTangentPatchMap i s) := by
  cases s with
  | interior =>
    intro q q' h
    have heq := (P.nativeComponentInteriorUnitTangentHomeomorph i).injective (Subtype.ext h)
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun r : P.ComponentInteriorTangentCarrier i => r.val) heq
  | incoming k hi =>
    subst i
    exact P.incomingTangentCollarNativeUnit_injective k
  | outgoing k hi =>
    subst i
    exact P.outgoingTangentCollarNativeUnit_injective k

/-- Each actual local map covers the entire native unit fiber over every
base point in its own retained component domain. -/
theorem componentTangentPatchMap_surjective_fiber
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (s : ComponentTangentPatch n i) (q : P.componentTangentPatchSet i s)
    (v : P.NativeUnitTangentCarrier)
    (hv : v.val.proj = (P.componentTangentPatchMap i s q).val.proj) :
    ∃! q', P.componentTangentPatchMap i s q' = v := by
  cases s with
  | interior =>
    have hv' : v.val.proj ∈ Set.range (fun b : P.componentInteriorSet i =>
        P.gluedMk (P.componentInteriorPoint i b)) := by
      rw [hv, P.componentTangentPatchMap_proj]
      exact ⟨⟨(X i).tangentFrameBase q.val.val, q.property⟩, rfl⟩
    let r := (P.nativeComponentInteriorUnitTangentHomeomorph i).symm ⟨v, hv'⟩
    let q' : P.componentTangentPatchSet i .interior :=
      ⟨⟨r.val, interior_subset r.property⟩, r.property⟩
    have heq : P.componentTangentPatchMap i .interior q' = v :=
      congrArg Subtype.val ((P.nativeComponentInteriorUnitTangentHomeomorph i).apply_symm_apply ⟨v, hv'⟩)
    refine ⟨q', heq, ?_⟩
    intro q'' hq''
    exact P.componentTangentPatchMap_injective i .interior (hq''.trans heq.symm)
  | incoming k hi =>
    subst i
    exact P.incomingTangentCollarNativeUnit_surjective_fiber k q v hv
  | outgoing k hi =>
    subst i
    exact P.outgoingTangentCollarNativeUnit_surjective_fiber k q v hv

theorem componentTangentPatchSet_mem_iff_of_base_eq
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (s : ComponentTangentPatch n i) (q q' : P.TangentChainComponent i)
    (h : P.tangentChainComponentBase i q = P.tangentChainComponentBase i q') :
    q ∈ P.componentTangentPatchSet i s ↔ q' ∈ P.componentTangentPatchSet i s := by
  cases s with
  | interior =>
    have hv := congrArg Subtype.val h
    change (X i).tangentFrameBase q.val = (X i).tangentFrameBase q'.val at hv
    change (X i).tangentFrameBase q.val ∈ P.componentInteriorSet i ↔
      (X i).tangentFrameBase q'.val ∈ P.componentInteriorSet i
    rw [hv]
  | incoming k hi =>
    subst i
    change P.tangentChainComponentBase _ q ∈ P.incomingCollar _ ↔
      P.tangentChainComponentBase _ q' ∈ P.incomingCollar _
    rw [h]
  | outgoing k hi =>
    subst i
    change P.tangentChainComponentBase _ q ∈ P.outgoingCollar _ ↔
      P.tangentChainComponentBase _ q' ∈ P.outgoingCollar _
    rw [h]

/-- Every retained base point has an actual physical component frame; this
uses the original quotient representatives, not a supplied bundle section. -/
theorem tangentChainComponentBase_surjective
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Function.Surjective (P.tangentChainComponentBase i) := by
  intro b
  obtain ⟨z, hz⟩ := Quotient.mk_surjective b.val
  let f : (X i).TangentFrameCarrier := Quotient.mk _ (⟨z, 1⟩ : HalfPlaneTangentFrame)
  have hf : (X i).tangentFrameBase f = b.val := hz
  exact ⟨⟨f, hf ▸ b.property⟩, Subtype.ext hf⟩

/-- All actual sphere representatives are in the literal polar boundary used
by the already constructed frame seam homeomorphism. -/
theorem punctureCircle_subset_polarBoundary
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) :
    (X i).punctureCircle o (gluingRadius C g) ⊆
      (X i).polarBoundary o (gluingRadius C g) := by
  rintro b ⟨z, hz, hzb⟩
  have hrad : dist o z = gluingRadius C g := by
    simpa only [mem_sphere, dist_comm] using hz
  let H := gluingPolarCollarHomeomorph o (gluingRadius C g / 2)
    (gluingRadius C g + 1) (by linarith [P.radius_pos])
  let q : GluingPolarAnnulus o (gluingRadius C g / 2) (gluingRadius C g + 1) :=
    ⟨z, by rw [hrad]; constructor <;> linarith [P.radius_pos]⟩
  have heq := congrArg Subtype.val (H.symm_apply_apply q)
  change gluingPolarPoint o (H q).1 (H q).2.val = z at heq
  have hr : (H q).2.val = gluingRadius C g := hrad
  rw [hr] at heq
  exact ⟨(H q).1, (congrArg (fun w : ℍ => (Quotient.mk'' w : (X i).Carrier)) heq).trans hzb⟩

theorem componentTangentPatchMap_incoming_eq_interior
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (k : Fin (n - 1))
    (hi : gluingChainEdgeRight k = i) (q : P.TangentChainComponent i)
    (hc : q ∈ P.componentTangentPatchSet i (.incoming k hi))
    (hq : q ∈ P.componentTangentPatchSet i .interior) :
    P.componentTangentPatchMap i (.incoming k hi) ⟨q, hc⟩ =
      P.componentTangentPatchMap i .interior ⟨q, hq⟩ := by
  subst i
  exact P.incomingTangentCollarNativeUnit_eq_componentInterior k ⟨q, hc⟩ hq

theorem componentTangentPatchMap_outgoing_eq_interior
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (k : Fin (n - 1))
    (hi : gluingChainEdgeLeft k = i) (q : P.TangentChainComponent i)
    (hc : q ∈ P.componentTangentPatchSet i (.outgoing k hi))
    (hq : q ∈ P.componentTangentPatchSet i .interior) :
    P.componentTangentPatchMap i (.outgoing k hi) ⟨q, hc⟩ =
      P.componentTangentPatchMap i .interior ⟨q, hq⟩ := by
  subst i
  exact P.outgoingTangentCollarNativeUnit_eq_componentInterior k ⟨q, hc⟩ hq

/-- The real physical maps agree on every actual retained-component overlap,
including intersections of distinct collar domains. -/
theorem componentTangentPatchMap_overlap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (s t : ComponentTangentPatch n i) (q : P.TangentChainComponent i)
    (hs : q ∈ P.componentTangentPatchSet i s)
    (ht : q ∈ P.componentTangentPatchSet i t) :
    P.componentTangentPatchMap i s ⟨q, hs⟩ = P.componentTangentPatchMap i t ⟨q, ht⟩ := by
  cases s with
  | interior =>
    cases t with
    | interior => rfl
    | incoming k hi => exact (P.componentTangentPatchMap_incoming_eq_interior i k hi q ht hs).symm
    | outgoing k hi => exact (P.componentTangentPatchMap_outgoing_eq_interior i k hi q ht hs).symm
  | incoming k hi =>
    cases t with
    | interior => exact P.componentTangentPatchMap_incoming_eq_interior i k hi q hs ht
    | incoming k' hi' =>
      have hkk : k' = k := Fin.ext (by
        have h := congrArg Fin.val (hi'.trans hi.symm)
        change k'.val + 1 = k.val + 1 at h
        omega)
      subst k'
      rfl
    | outgoing k' hi' =>
      have hq : q ∈ P.componentTangentPatchSet i .interior :=
        P.mem_componentInteriorSet_of_mem_both_collars i (P.tangentChainComponentBase i q)
          ((P.componentTangentPatchSet_incoming_iff i k hi q).mp hs)
          ((P.componentTangentPatchSet_outgoing_iff i k' hi' q).mp ht)
      exact (P.componentTangentPatchMap_incoming_eq_interior i k hi q hs hq).trans
        (P.componentTangentPatchMap_outgoing_eq_interior i k' hi' q ht hq).symm
  | outgoing k hi =>
    cases t with
    | interior => exact P.componentTangentPatchMap_outgoing_eq_interior i k hi q hs ht
    | incoming k' hi' =>
      have hq : q ∈ P.componentTangentPatchSet i .interior :=
        P.mem_componentInteriorSet_of_mem_both_collars i (P.tangentChainComponentBase i q)
          ((P.componentTangentPatchSet_incoming_iff i k' hi' q).mp ht)
          ((P.componentTangentPatchSet_outgoing_iff i k hi q).mp hs)
      exact (P.componentTangentPatchMap_outgoing_eq_interior i k hi q hs hq).trans
        (P.componentTangentPatchMap_incoming_eq_interior i k' hi' q ht hq).symm
    | outgoing k' hi' =>
      have hkk : k' = k := Fin.ext (by
        have h := congrArg (fun j : Fin n => j.val) (hi'.trans hi.symm)
        exact h)
      subst k'
      rfl

def componentTangentPatchContinuousMap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (s : ComponentTangentPatch n i) : C(P.componentTangentPatchSet i s, P.NativeUnitTangentCarrier) :=
  ⟨P.componentTangentPatchMap i s, P.continuous_componentTangentPatchMap i s⟩

theorem componentTangentPatch_cover_nhds
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.TangentChainComponent i) : ∃ s : ComponentTangentPatch n i,
      P.componentTangentPatchSet i s ∈ 𝓝 q := by
  obtain ⟨s, hs⟩ := P.exists_componentTangentPatch i q
  exact ⟨s, (P.componentTangentPatchSet_isOpen i s).mem_nhds hs⟩

/-- The genuine physical frame map on the entire retained component,
constructed by continuous gluing of the verified actual local maps. -/
def nativeTangentChainComponent
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    C(P.TangentChainComponent i, P.NativeUnitTangentCarrier) :=
  ContinuousMap.liftCover (P.componentTangentPatchSet i)
    (P.componentTangentPatchContinuousMap i) (P.componentTangentPatchMap_overlap i)
    (P.componentTangentPatch_cover_nhds i)

theorem nativeTangentChainComponent_patch_apply
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (s : ComponentTangentPatch n i) (q : P.TangentChainComponent i)
    (hq : q ∈ P.componentTangentPatchSet i s) :
    P.nativeTangentChainComponent i q = P.componentTangentPatchMap i s ⟨q, hq⟩ :=
  ContinuousMap.liftCover_coe (⟨q, hq⟩ : P.componentTangentPatchSet i s)

theorem nativeTangentChainComponent_proj
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.TangentChainComponent i) :
    (P.nativeTangentChainComponent i q).val.proj =
      P.gluedMk ⟨i, P.tangentChainComponentBase i q⟩ := by
  obtain ⟨s, hs⟩ := P.exists_componentTangentPatch i q
  rw [P.nativeTangentChainComponent_patch_apply i s q hs]
  exact P.componentTangentPatchMap_proj i s ⟨q, hs⟩

theorem nativeTangentChainComponent_injective
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Function.Injective (P.nativeTangentChainComponent i) := by
  intro q q' h
  have hb := congrArg (fun v : P.NativeUnitTangentCarrier => v.val.proj) h
  rw [P.nativeTangentChainComponent_proj, P.nativeTangentChainComponent_proj] at hb
  have hbase := P.gluedMk_injective_component i hb
  obtain ⟨s, hs⟩ := P.exists_componentTangentPatch i q
  have hs' := (P.componentTangentPatchSet_mem_iff_of_base_eq i s q q' hbase).mp hs
  rw [P.nativeTangentChainComponent_patch_apply i s q hs,
    P.nativeTangentChainComponent_patch_apply i s q' hs'] at h
  exact congrArg Subtype.val (P.componentTangentPatchMap_injective i s h)

/-- The patched retained-component map is still a bijection on each literal
native unit tangent fiber; no independent bundle-surjectivity input is used. -/
theorem nativeTangentChainComponent_surjective_fiber
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.TangentChainComponent i) (v : P.NativeUnitTangentCarrier)
    (hv : v.val.proj = (P.nativeTangentChainComponent i q).val.proj) :
    ∃! q', P.nativeTangentChainComponent i q' = v := by
  obtain ⟨s, hs⟩ := P.exists_componentTangentPatch i q
  rw [P.nativeTangentChainComponent_patch_apply i s q hs] at hv
  obtain ⟨r, hr, _⟩ := P.componentTangentPatchMap_surjective_fiber i s ⟨q, hs⟩ v hv
  have heq : P.nativeTangentChainComponent i r.val = v :=
    (P.nativeTangentChainComponent_patch_apply i s r.val r.property).trans hr
  exact ⟨r.val, heq, fun q' hq' => P.nativeTangentChainComponent_injective i (hq'.trans heq.symm)⟩

theorem nativeTangentChainComponent_boundary_clutching
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (q : (X (gluingChainEdgeLeft k)).TangentBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    P.nativeTangentChainComponent (gluingChainEdgeRight k)
      (P.tangentLeftBoundaryInclusion _ (P.seamTangentHomeomorph k q)) =
    P.nativeTangentChainComponent (gluingChainEdgeLeft k)
      (P.tangentRightBoundaryInclusion _ q) := by
  change P.nativeTangentChainComponent (gluingChainEdgeRight k)
      (P.tangentIncomingBoundaryCollarInclusion _ (P.seamTangentHomeomorph k q)).val =
    P.nativeTangentChainComponent (gluingChainEdgeLeft k)
      (P.tangentOutgoingBoundaryCollarInclusion _ q).val
  rw [P.nativeTangentChainComponent_patch_apply _ (.incoming k rfl) _
      (P.tangentIncomingBoundaryCollarInclusion _ (P.seamTangentHomeomorph k q)).property,
    P.nativeTangentChainComponent_patch_apply _ (.outgoing k rfl) _
      (P.tangentOutgoingBoundaryCollarInclusion _ q).property]
  exact P.tangentCollarNativeUnit_boundary_clutching k q

/-- The actual retained-component maps descend through exactly the existing
physical frame seam relation. -/
def gluedTangentNativeUnit (P : ExerciseGluingPreparation C g n genera X) :
    P.GluedTangentCarrier → P.NativeUnitTangentCarrier :=
  Quotient.lift (fun a => P.nativeTangentChainComponent a.fst a.snd) fun a b h => by
    change Relation.EqvGen P.tangentChainRelation a b at h
    induction h with
    | rel a b h =>
      obtain ⟨k, q, rfl, rfl⟩ := h
      exact (P.nativeTangentChainComponent_boundary_clutching k q).symm
    | refl a => rfl
    | symm a b h ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

theorem continuous_gluedTangentNativeUnit
    (P : ExerciseGluingPreparation C g n genera X) : Continuous P.gluedTangentNativeUnit :=
  (continuous_sigma fun i => (P.nativeTangentChainComponent i).continuous).quotient_lift _

theorem gluedTangentNativeUnit_proj
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedTangentCarrier) :
    (P.gluedTangentNativeUnit q).val.proj = P.gluedTangentBase q := by
  induction q using Quotient.inductionOn with
  | h a => exact P.nativeTangentChainComponent_proj a.fst a.snd

theorem gluedTangentNativeUnit_surjective
    (P : ExerciseGluingPreparation C g n genera X) : Function.Surjective P.gluedTangentNativeUnit := by
  intro v
  obtain ⟨⟨i, b⟩, hb⟩ := Quotient.mk_surjective v.val.proj
  obtain ⟨q, hq⟩ := P.tangentChainComponentBase_surjective i b
  have hv : v.val.proj = (P.nativeTangentChainComponent i q).val.proj := by
    rw [P.nativeTangentChainComponent_proj, hq]
    exact hb.symm
  obtain ⟨q', hq', _⟩ := P.nativeTangentChainComponent_surjective_fiber i q v hv
  exact ⟨Quotient.mk _ ⟨i, q'⟩, hq'⟩

/-- Every genuine base seam matching lifts to the original physical tangent
matching, using the literal retained boundary and its Fermi homeomorphism. -/
theorem tangentChainRelation_lift_base
    (P : ExerciseGluingPreparation C g n genera X) (a : P.TangentChainPieces)
    (b : P.ChainPieces) (h : P.chainRelation (P.tangentChainPieceBase a) b) :
    ∃ a', P.tangentChainRelation a a' ∧ P.tangentChainPieceBase a' = b := by
  obtain ⟨i, a⟩ := a
  obtain ⟨k, z, ha, hb⟩ := h
  have hi : i = gluingChainEdgeLeft k := congrArg Sigma.fst ha
  subst i
  have hbase : P.tangentChainComponentBase _ a = P.rightCirclePoint _ z :=
    eq_of_heq (Sigma.mk.inj_iff.mp ha).2
  let q : (X (gluingChainEdgeLeft k)).TangentBoundaryCarrier
      (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) :=
    ⟨a.val, P.punctureCircle_subset_polarBoundary _ _
      ⟨z.val, z.property, (congrArg Subtype.val hbase).symm⟩⟩
  have hsource : P.tangentSeamSource k q = (⟨gluingChainEdgeLeft k, a⟩ : P.TangentChainPieces) := by
    apply congrArg (Sigma.mk (gluingChainEdgeLeft k))
    exact Subtype.ext rfl
  have htan : P.tangentChainRelation (⟨gluingChainEdgeLeft k, a⟩ : P.TangentChainPieces)
      (P.tangentSeamTarget k q) := ⟨k, q, hsource.symm, rfl⟩
  refine ⟨P.tangentSeamTarget k q, htan, ?_⟩
  exact P.chainRelation_right_unique (P.tangentChainRelation_base htan)
    ⟨k, z, ha, hb⟩

/-- The reverse genuine seam can equally be lifted from its incoming frame;
the actual seam homeomorphism, not a new inverse transition, supplies it. -/
theorem tangentChainRelation_lift_base_reverse
    (P : ExerciseGluingPreparation C g n genera X) (a : P.TangentChainPieces)
    (b : P.ChainPieces) (h : P.chainRelation b (P.tangentChainPieceBase a)) :
    ∃ a', P.tangentChainRelation a' a ∧ P.tangentChainPieceBase a' = b := by
  obtain ⟨i, a⟩ := a
  obtain ⟨k, z, hb, ha⟩ := h
  have hi : i = gluingChainEdgeRight k := congrArg Sigma.fst ha
  subst i
  let z' := gluingBoundaryCircleIsometry (P.centers (gluingChainEdgeLeft k)).2
    (P.centers (gluingChainEdgeRight k)).1 (gluingRadius C g) z
  have hbase : P.tangentChainComponentBase _ a =
      P.leftCirclePoint _ z' :=
    eq_of_heq (Sigma.mk.inj_iff.mp ha).2
  let q : (X (gluingChainEdgeRight k)).TangentBoundaryCarrier
      (P.centers (gluingChainEdgeRight k)).1 (gluingRadius C g) :=
    ⟨a.val, P.punctureCircle_subset_polarBoundary _ _
      ⟨z'.val, z'.property,
        (congrArg Subtype.val hbase).symm⟩⟩
  let r := (P.seamTangentHomeomorph k).symm q
  have htarget : P.tangentSeamTarget k r = (⟨gluingChainEdgeRight k, a⟩ : P.TangentChainPieces) := by
    change (⟨gluingChainEdgeRight k,
      P.tangentLeftBoundaryInclusion _ (P.seamTangentHomeomorph k r)⟩ : P.TangentChainPieces) = _
    rw [(P.seamTangentHomeomorph k).apply_symm_apply]
    apply congrArg (Sigma.mk (gluingChainEdgeRight k))
    exact Subtype.ext rfl
  have htan : P.tangentChainRelation (P.tangentSeamSource k r)
      (⟨gluingChainEdgeRight k, a⟩ : P.TangentChainPieces) := ⟨k, r, rfl, htarget.symm⟩
  refine ⟨P.tangentSeamSource k r, htan, ?_⟩
  exact P.chainRelation_left_unique (P.tangentChainRelation_base htan)
    ⟨k, z, hb, ha⟩

theorem tangentChainPiece_eq_of_base_eq_of_native_eq
    (P : ExerciseGluingPreparation C g n genera X) (a b : P.TangentChainPieces)
    (hb : P.tangentChainPieceBase a = P.tangentChainPieceBase b)
    (hn : P.nativeTangentChainComponent a.fst a.snd =
      P.nativeTangentChainComponent b.fst b.snd) : a = b := by
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  have hij : i = j := congrArg Sigma.fst hb
  subst j
  exact congrArg (Sigma.mk i) (P.nativeTangentChainComponent_injective i hn)

/-- No new frame equivalence is introduced: equality of native unit vectors
is exactly equality in the original clutched physical frame quotient. -/
theorem gluedTangentNativeUnit_injective
    (P : ExerciseGluingPreparation C g n genera X) : Function.Injective P.gluedTangentNativeUnit := by
  intro q q'
  induction q using Quotient.inductionOn with
  | h a =>
    induction q' using Quotient.inductionOn with
    | h b =>
      intro hn
      have hb := congrArg (fun v : P.NativeUnitTangentCarrier => v.val.proj) hn
      rw [P.gluedTangentNativeUnit_proj, P.gluedTangentNativeUnit_proj] at hb
      change P.gluedMk (P.tangentChainPieceBase a) =
        P.gluedMk (P.tangentChainPieceBase b) at hb
      rcases (P.gluedMk_eq_iff _ _).mp hb with hab | hab | hba
      · exact congrArg (Quotient.mk P.tangentChainSetoid)
          (P.tangentChainPiece_eq_of_base_eq_of_native_eq a b hab hn)
      · obtain ⟨a', hrel, hbase⟩ := P.tangentChainRelation_lift_base a (P.tangentChainPieceBase b) hab
        have hquot : (Quotient.mk P.tangentChainSetoid a : P.GluedTangentCarrier) =
            Quotient.mk P.tangentChainSetoid a' := Quotient.sound (Relation.EqvGen.rel _ _ hrel)
        have hn' : P.nativeTangentChainComponent a'.fst a'.snd =
            P.nativeTangentChainComponent b.fst b.snd :=
          (congrArg P.gluedTangentNativeUnit hquot).symm.trans hn
        have heq := P.tangentChainPiece_eq_of_base_eq_of_native_eq a' b hbase hn'
        exact hquot.trans (congrArg (Quotient.mk P.tangentChainSetoid) heq)
      · obtain ⟨a', hrel, hbase⟩ :=
          P.tangentChainRelation_lift_base_reverse a (P.tangentChainPieceBase b) hba
        have hquot : (Quotient.mk P.tangentChainSetoid a' : P.GluedTangentCarrier) =
            Quotient.mk P.tangentChainSetoid a := Quotient.sound (Relation.EqvGen.rel _ _ hrel)
        have hn' : P.nativeTangentChainComponent a'.fst a'.snd =
            P.nativeTangentChainComponent b.fst b.snd :=
          (congrArg P.gluedTangentNativeUnit hquot).trans hn
        have heq := P.tangentChainPiece_eq_of_base_eq_of_native_eq a' b hbase hn'
        exact hquot.symm.trans (congrArg (Quotient.mk P.tangentChainSetoid) heq)

/-- The actual tangent total-space topology is Hausdorff: projection separates
different basepoints, and a genuine local trivialization separates one fiber. -/
instance gluedTangentTotalSpaceT2Space
    (P : ExerciseGluingPreparation C g n genera X) :
    T2Space (TotalSpace ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)) := by
  apply t2_iff_nhds.mpr
  intro x y h
  letI : NeBot (𝓝 x ⊓ 𝓝 y) := h
  let E := (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)
  have hp := FiberBundle.continuous_proj ℂ E
  have hb : x.proj = y.proj := tendsto_nhds_unique
    (hp.continuousAt.mono_left inf_le_left) (hp.continuousAt.mono_left inf_le_right)
  let t := trivializationAt ℂ E x.proj
  have hx : x ∈ t.source := FiberBundle.mem_trivializationAt_proj_source
  have hy : y ∈ t.source := by
    apply t.mem_source.mpr
    rw [← hb]
    exact mem_baseSet_trivializationAt ℂ E x.proj
  have ht : t x = t y := tendsto_nhds_unique
    ((t.toOpenPartialHomeomorph.continuousAt hx).mono_left inf_le_left)
    ((t.toOpenPartialHomeomorph.continuousAt hy).mono_left inf_le_right)
  exact t.toOpenPartialHomeomorph.injOn hx hy ht

instance nativeUnitTangentCarrierT2Space
    (P : ExerciseGluingPreparation C g n genera X) : T2Space P.NativeUnitTangentCarrier :=
  inferInstance

/-- The genuine globally clutched physical frame carrier is the actual
native unit tangent bundle of the glued manifold, homeomorphically. -/
def gluedTangentNativeUnitHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) :
    P.GluedTangentCarrier ≃ₜ P.NativeUnitTangentCarrier :=
  IsHomeomorph.homeomorph P.gluedTangentNativeUnit
    (isHomeomorph_iff_continuous_bijective.mpr
      ⟨P.continuous_gluedTangentNativeUnit,
        P.gluedTangentNativeUnit_injective, P.gluedTangentNativeUnit_surjective⟩)

@[simp] theorem gluedTangentNativeUnitHomeomorph_apply
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedTangentCarrier) :
    P.gluedTangentNativeUnitHomeomorph q = P.gluedTangentNativeUnit q := rfl

theorem gluedTangentNativeUnitHomeomorph_proj
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedTangentCarrier) :
    (P.gluedTangentNativeUnitHomeomorph q).val.proj = P.gluedTangentBase q :=
  P.gluedTangentNativeUnit_proj q

#print axioms mem_componentInteriorSet_of_mem_both_collars
#print axioms exists_componentTangentPatch
#print axioms componentTangentPatchMap_surjective_fiber
#print axioms nativeTangentChainComponent
#print axioms nativeTangentChainComponent_boundary_clutching
#print axioms gluedTangentNativeUnit
#print axioms gluedTangentNativeUnit_surjective
#print axioms gluedTangentNativeUnit_injective
#print axioms gluedTangentNativeUnitHomeomorph
#print axioms gluedTangentNativeUnitHomeomorph_proj

end

end SystolicGrowth.ExerciseGluingPreparation

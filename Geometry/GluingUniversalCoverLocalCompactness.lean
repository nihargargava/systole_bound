module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingUniversalCover
public import Mathlib.Topology.Separation.Regular

@[expose] public section

/-!
# Local compactness of the native universal cover

The endpoint projection is an actual local homeomorphism over the compact
Hausdorff glued carrier. Shrinking an open chart neighborhood in that carrier
gives compact neighborhoods in the original based-path cover topology.
-/

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual based-path universal cover is locally compact in its original
topology, by shrinking neighborhoods inside a covering chart over the compact
Hausdorff glued carrier. -/
instance basedTopologicalUniversalCoverLocallyCompactSpace
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    LocallyCompactSpace (P.basedTopologicalUniversalCover x) := by
  letI : CompactSpace P.GluedCarrier := P.gluedCarrierCompactSpace
  letI : T2Space P.GluedCarrier := P.gluedCarrierT2Space
  let p := P.gluedUniversalCoverProjection x
  let hp := P.gluedUniversalCoverProjection_isCoveringMap x
  let hl := hp.isLocalHomeomorph
  refine ⟨fun e N hN => ?_⟩
  let φ := hl.localInverseAt e
  obtain ⟨O, hON, hOopen, heO⟩ := mem_nhds_iff.mp hN
  have heTarget : e ∈ φ.target := hl.self_mem_localInverseAt_target
  have hφsymm : φ.symm = p := by
    dsimp [φ, hl, hp, p]
    exact P.gluedUniversalCoverProjection_isCoveringMap x |>.isLocalHomeomorph.localInverseAt_symm e
  let S : Set (P.basedTopologicalUniversalCover x) := O ∩ φ.target
  have hSopen : IsOpen S := hOopen.inter φ.open_target
  have hbaseS : e ∈ S := ⟨heO, heTarget⟩
  let W : Set P.GluedCarrier := φ.symm '' S
  have hWopen : IsOpen W := by
    exact φ.symm.isOpen_image_of_subset_source hSopen (by simp [S])
  have hbaseW : p e ∈ W := by
    refine ⟨e, hbaseS, ?_⟩
    rw [hφsymm]
  have hWsource : W ⊆ φ.source := by
    rintro y ⟨z, hz, rfl⟩
    exact φ.map_target hz.2
  obtain ⟨V, hVopen, hbaseV, hVclosureW⟩ :=
    isCompact_singleton.exists_isOpen_closure_subset
      (hWopen.mem_nhdsSet.mpr (Set.singleton_subset_iff.mpr hbaseW))
  have hVsource : closure V ⊆ φ.source := hVclosureW.trans hWsource
  have hclosureCompact : IsCompact (closure V) :=
    isCompact_univ.of_isClosed_subset isClosed_closure (fun _ _ => by trivial)
  let K : Set (P.basedTopologicalUniversalCover x) := φ '' closure V
  have hKcompact : IsCompact K :=
    hclosureCompact.image_of_continuousOn (φ.continuousOn_toFun.mono hVsource)
  have hVsource' : V ⊆ φ.source := subset_trans subset_closure hVsource
  have himageOpen : IsOpen (φ '' V) := φ.isOpen_image_of_subset_source hVopen hVsource'
  have hφbase : φ (p e) = e := by
    dsimp [φ, hl]
    exact P.gluedUniversalCoverProjection_isCoveringMap x |>.isLocalHomeomorph.localInverseAt_apply_self
  have heImage : e ∈ φ '' V := ⟨p e, Set.singleton_subset_iff.mp hbaseV, hφbase⟩
  have himageK : φ '' V ⊆ K := Set.image_mono subset_closure
  have hKN : K ⊆ N := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨w, hwS, rfl⟩ := hVclosureW hz
    rw [φ.right_inv hwS.2]
    exact hON hwS.1
  exact ⟨K, Filter.mem_of_superset (himageOpen.mem_nhds heImage) himageK, hKN, hKcompact⟩

#print axioms basedTopologicalUniversalCoverLocallyCompactSpace

end SystolicGrowth.ExerciseGluingPreparation

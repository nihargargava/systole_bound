module

public import BuserSarnak.BuserSarnakProjectiveLevelMarking
public import BuserSarnak.BuserSarnakProjectiveConeElimination
public import BuserSarnak.BuserSarnakFinalMarking

@[expose] public section

/-!
# Final assembly through the projective finite quotient

The projective octagon quotient removes the central scalar before applying
Reidemeister--Schreier.  Its cleaned presentation therefore has a smaller
Tietze certificate than the lifted route, while its kernel is canonically
equivalent to the same principal-level group.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations
open PrefixClosedFiniteQuotientSchreierData

noncomputable local instance buserSarnakProjectiveTargetRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

noncomputable local instance buserSarnakProjectiveTargetDegenerateDecidable
    {p : ℕ} [NeZero p]
    {S : BuserSarnakProjectiveQuotientSectionData p} :
    DecidablePred
      S.schreierData.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol :=
  Classical.decPred _

/-- Exact Tietze data from the projective cleaned presentation to the fixed
standard surface presentation.  Unlike the lifted certificate, this one has
only six base generators and five base relators. -/
structure BuserSarnakProjectiveLevelTargetPresentationData
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (S : BuserSarnakProjectiveQuotientSectionData p) where
  toTargetGenerator :
    S.schreierData.nondegenerateSchreierSymbol →
      FreeGroup (SurfaceGenerator (data.halfImageIndex + 1))
  fromTargetGenerator :
    SurfaceGenerator (data.halfImageIndex + 1) →
      FreeGroup S.schreierData.nondegenerateSchreierSymbol
  mapsCleanedRelators :
    ∀ q : BuserSarnakProjectiveReductionRange p,
      ∀ r : ProjectiveOctagonRelator,
        RelatorEquivalent
          ({surfaceRelator (data.halfImageIndex + 1)} :
            Set (FreeGroup
              (SurfaceGenerator (data.halfImageIndex + 1))))
          (FreeGroup.lift toTargetGenerator
            (S.schreierData.cleanedTau q
              (projectiveOctagonRelator r))) 1
  mapsSurfaceRelator :
    RelatorEquivalent
      (S.schreierData.cleanedSchreierRelators projectiveOctagonRelators)
      (FreeGroup.lift fromTargetGenerator
        (surfaceRelator (data.halfImageIndex + 1))) 1
  from_toTargetGenerator :
    ∀ z : S.schreierData.nondegenerateSchreierSymbol,
      RelatorEquivalent
        (S.schreierData.cleanedSchreierRelators projectiveOctagonRelators)
        (FreeGroup.lift fromTargetGenerator (toTargetGenerator z))
        (FreeGroup.of z)
  to_fromTargetGenerator :
    ∀ y : SurfaceGenerator (data.halfImageIndex + 1),
      RelatorEquivalent
        ({surfaceRelator (data.halfImageIndex + 1)} :
          Set (FreeGroup
            (SurfaceGenerator (data.halfImageIndex + 1))))
        (FreeGroup.lift toTargetGenerator (fromTargetGenerator y))
        (FreeGroup.of y)

namespace BuserSarnakProjectiveLevelTargetPresentationData

/-- Forget the fixed-surface presentation and retain the generic cleaned
Reidemeister--Schreier target certificate. -/
def toCleanedTargetPresentationData
    {p : ℕ} [NeZero p] {data : BuserSarnakCorrectionData p}
    {S : BuserSarnakProjectiveQuotientSectionData p}
    (C : BuserSarnakProjectiveLevelTargetPresentationData data S) :
    S.schreierData.CleanedReidemeisterSchreierTargetPresentationData
      projectiveOctagonRelators
      (SurfaceGenerator (data.halfImageIndex + 1)) where
  targetRelators :=
    {surfaceRelator (data.halfImageIndex + 1)}
  toTargetGenerator := C.toTargetGenerator
  fromTargetGenerator := C.fromTargetGenerator
  mapsCleanedRelators := by
    intro q r hr
    rcases hr with ⟨i, rfl⟩
    exact C.mapsCleanedRelators q i
  mapsTargetRelators := by
    intro s hs
    rw [Set.mem_singleton_iff.mp hs]
    exact C.mapsSurfaceRelator
  from_toTargetGenerator := C.from_toTargetGenerator
  to_fromTargetGenerator := C.to_fromTargetGenerator

/-- A complete semantic Tietze equivalence from the canonical projective
cleaned presentation packages directly as the fixed surface target data. -/
noncomputable def ofCanonicalProjectiveConeTietzeEquiv
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (E : TietzeEquiv (CanonicalProjectiveConeRelators p)
      ({surfaceRelator (data.halfImageIndex + 1)} :
        Set (FreeGroup (SurfaceGenerator (data.halfImageIndex + 1))))) :
    BuserSarnakProjectiveLevelTargetPresentationData data
      (canonicalBuserSarnakProjectiveQuotientSectionData p) := by
  let C := CleanedReidemeisterSchreierTargetPresentationData.ofTietzeEquiv E
  refine
    { toTargetGenerator := C.toTargetGenerator
      fromTargetGenerator := C.fromTargetGenerator
      mapsCleanedRelators := ?_
      mapsSurfaceRelator := ?_
      from_toTargetGenerator := C.from_toTargetGenerator
      to_fromTargetGenerator := C.to_fromTargetGenerator }
  · intro q r
    exact C.mapsCleanedRelators q (projectiveOctagonRelator r) ⟨r, rfl⟩
  · apply C.mapsTargetRelators
    change surfaceRelator (data.halfImageIndex + 1) ∈
      ({surfaceRelator (data.halfImageIndex + 1)} :
        Set (FreeGroup (SurfaceGenerator (data.halfImageIndex + 1))))
    exact Set.mem_singleton _

/-- The projective octagon relators lie in the free reduction kernel. -/
lemma projectiveOctagonRelators_le_schreierKernel
    {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    Subgroup.normalClosure projectiveOctagonRelators ≤
      S.schreierData.kernel := by
  change Subgroup.normalClosure projectiveOctagonRelators ≤
    (buserSarnakProjectiveReductionMap p).ker
  exact PresentedGroup.closure_rels_subset_ker
    (buserSarnakProjectiveReductionImage_relations p)

/-- A completed projective target certificate identifies the standard surface
group with the projective finite-reduction kernel. -/
noncomputable def surfaceEquivProjectivePresentedKernel
    {p : ℕ} [NeZero p] {data : BuserSarnakCorrectionData p}
    {S : BuserSarnakProjectiveQuotientSectionData p}
    (C : BuserSarnakProjectiveLevelTargetPresentationData data S) :
    SurfaceGroup (data.halfImageIndex + 1) ≃*
      (buserSarnakProjectiveReductionPresentedHom p).ker :=
  (C.toCleanedTargetPresentationData.targetPresentedGroupEquivKernel
      (projectiveOctagonRelators_le_schreierKernel S)).trans
    (presentedFreeKernelRelatorQuotientEquivPresentedKernel
      (buserSarnakProjectiveReductionImage_relations p))

/-- The projective finite-reduction kernel is the concrete principal-level
group once the lifted octagon presentation is faithful. -/
noncomputable def projectivePresentedKernelEquivLevelGroup23
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (hfaith : Function.Injective liftedOctagonToQuaternion) :
    (buserSarnakProjectiveReductionPresentedHom p).ker ≃*
      buserSarnakLevelGroup23 p :=
  (buserSarnakLiftedKernelEquivProjectiveKernel p hp hp2).symm.trans
    (buserSarnakOctagonPresentedKernelEquivLevelGroup23 p hfaith)

/-- A projective cleaned-presentation certificate gives the desired
principal-level marking. -/
noncomputable def levelGroupMarking
    {p : ℕ} [NeZero p] {data : BuserSarnakCorrectionData p}
    {S : BuserSarnakProjectiveQuotientSectionData p}
    (C : BuserSarnakProjectiveLevelTargetPresentationData data S)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hfaith : Function.Injective liftedOctagonToQuaternion) :
    buserSarnakLevelGroup23 p ≃*
      SurfaceGroup (data.halfImageIndex + 1) :=
  (projectivePresentedKernelEquivLevelGroup23 p hp hp2 hfaith).symm.trans
    C.surfaceEquivProjectivePresentedKernel.symm

end BuserSarnakProjectiveLevelTargetPresentationData

/-- A uniform family of projective finite Tietze certificates.  The canonical
section has `halfImageIndex` states, so this is the smaller certificate route. -/
structure BuserSarnakUniformProjectiveLevelTargetPresentationData where
  certificate : ∀ (p : ℕ) [NeZero p]
      (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3),
    BuserSarnakProjectiveLevelTargetPresentationData
      (buserSarnakCorrectionData p hp hp2 hp3)
      (canonicalBuserSarnakProjectiveQuotientSectionData p)

namespace BuserSarnakUniformProjectiveLevelTargetPresentationData

/-- The projective certificates and a faithful lifted presentation produce
the base family of marked Buser--Sarnak surfaces. -/
noncomputable def toBaseSurfaceMarking
    (C : BuserSarnakUniformProjectiveLevelTargetPresentationData)
    (hfaith : Function.Injective liftedOctagonToQuaternion) :
    BuserSarnakBaseSurfaceMarking :=
  BuserSarnakBaseSurfaceMarking.mk (by
    intro p _ hp hp2 hp3
    exact (C.certificate p hp hp2 hp3).levelGroupMarking hp hp2 hfaith)

/-- The established corridor proof removes the infinite-group assumption:
only the finite projective Tietze certificates remain. -/
noncomputable def toBaseSurfaceMarkingUnconditional
    (C : BuserSarnakUniformProjectiveLevelTargetPresentationData) :
    BuserSarnakBaseSurfaceMarking :=
  C.toBaseSurfaceMarking liftedOctagonToQuaternion_injective

/-- Uniform projective certificates now suffice for the arithmetic input
required by the main systolic-growth reduction. -/
noncomputable def toBuserSarnakInputUnconditional
    (C : BuserSarnakUniformProjectiveLevelTargetPresentationData) :
    BuserSarnakInput :=
  C.toBaseSurfaceMarkingUnconditional.toBuserSarnakInput

end BuserSarnakUniformProjectiveLevelTargetPresentationData

end

end SystolicGrowth

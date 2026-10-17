module

public import Vendored.ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.TargetPresentation
public import BuserSarnak.BuserSarnakCorrection
public import SurfaceGroup.Tietze
public import SurfaceGroup.Presentation
public import SurfaceGroup.Standard

@[expose] public section

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete

abbrev SurfaceCyclicQuotient (d : ℕ) := Multiplicative (ZMod d)

def surfaceCyclicBaseGenerator {g : ℕ} (hg : 0 < g) : SurfaceGenerator g :=
  (⟨0, hg⟩, false)

def surfaceCyclicGeneratorImage {g d : ℕ} (hg : 0 < g) :
    SurfaceGenerator g → SurfaceCyclicQuotient d :=
  fun x => if x = surfaceCyclicBaseGenerator hg then Multiplicative.ofAdd 1 else 1

def surfaceCyclicQuotientMap {g d : ℕ} (hg : 0 < g) :
    FreeGroup (SurfaceGenerator g) →* SurfaceCyclicQuotient d :=
  FreeGroup.lift (surfaceCyclicGeneratorImage hg)

def surfaceCyclicQuotientSectionWord {g d : ℕ} [NeZero d] (hg : 0 < g)
    (q : SurfaceCyclicQuotient d) : List (SurfaceGenerator g × Bool) :=
  List.replicate q.toAdd.val (surfaceCyclicBaseGenerator hg, true)

lemma surfaceCyclicQuotientMap_mk_sectionWord {g d : ℕ} [NeZero d]
    (hg : 0 < g) (q : SurfaceCyclicQuotient d) :
    surfaceCyclicQuotientMap (d := d) hg
      (FreeGroup.mk (surfaceCyclicQuotientSectionWord hg q)) = q := by
  change (FreeGroup.lift (surfaceCyclicGeneratorImage (d := d) hg))
    (FreeGroup.mk (surfaceCyclicQuotientSectionWord hg q)) = q
  rw [FreeGroup.lift_mk]
  simp [surfaceCyclicQuotientSectionWord, surfaceCyclicGeneratorImage,
    surfaceCyclicBaseGenerator]
  apply Multiplicative.toAdd.injective
  simpa using ZMod.natCast_zmod_val q.toAdd

def surfaceCyclicPositiveCertificate {g d : ℕ} [NeZero d] (hg : 0 < g) :
    PositivePrefixClosedQuotientSectionWordCertificate
      (SurfaceGenerator g) (SurfaceCyclicQuotient d) where
  quotientMap := surfaceCyclicQuotientMap hg
  quotientSectionWord := surfaceCyclicQuotientSectionWord hg
  quotientMap_mk_quotientSectionWord :=
    surfaceCyclicQuotientMap_mk_sectionWord hg
  quotientSectionWord_positive := by
    intro q xb hxb
    have hxb' := List.eq_of_mem_replicate hxb
    exact congrArg Prod.snd hxb'
  prefixState := by
    intro q acc rest hcat
    have hlen := congrArg List.length hcat
    simp only [List.length_append, surfaceCyclicQuotientSectionWord,
      List.length_replicate] at hlen
    have hle : acc.length ≤ q.toAdd.val := by omega
    have hacc : acc = List.replicate acc.length
        (surfaceCyclicBaseGenerator hg, true) := by
      calc
        acc = (acc ++ rest).take acc.length := by simp
        _ = (List.replicate q.toAdd.val
            (surfaceCyclicBaseGenerator hg, true)).take acc.length := by
          simpa [surfaceCyclicQuotientSectionWord] using
            congrArg (List.take acc.length) hcat
        _ = List.replicate acc.length
            (surfaceCyclicBaseGenerator hg, true) := by
          rw [List.take_replicate, min_eq_left hle]
    have hmap : surfaceCyclicQuotientMap (d := d) hg (FreeGroup.mk acc) =
        Multiplicative.ofAdd (acc.length : ZMod d) := by
      change (FreeGroup.lift (surfaceCyclicGeneratorImage (d := d) hg))
        (FreeGroup.mk acc) = Multiplicative.ofAdd (acc.length : ZMod d)
      rw [hacc, FreeGroup.lift_mk]
      simp [surfaceCyclicGeneratorImage, surfaceCyclicBaseGenerator]
      apply Multiplicative.toAdd.injective
      simp
    rw [hmap]
    change List.replicate ((acc.length : ZMod d).val)
      (surfaceCyclicBaseGenerator hg, true) = acc
    have hlt : acc.length < d :=
      lt_of_le_of_lt hle (ZMod.val_lt q.toAdd)
    rw [ZMod.val_cast_of_lt hlt]
    exact hacc.symm

def surfaceCyclicSchreierData {g d : ℕ} [NeZero d] (hg : 0 < g) :
    PrefixClosedFiniteQuotientSchreierData
      (SurfaceGenerator g) (SurfaceCyclicQuotient d) :=
  (surfaceCyclicPositiveCertificate (d := d) hg).toPrefixClosedFiniteQuotientSchreierData

lemma surfaceCyclicQuotientMap_surfaceRelator_eq_one {g d : ℕ} (hg : 0 < g) :
    surfaceCyclicQuotientMap (d := d) hg (surfaceRelator g) = 1 := by
  change (FreeGroup.lift (surfaceCyclicGeneratorImage (d := d) hg))
    (surfaceRelator g) = 1
  rw [surfaceRelator, map_list_prod]
  apply List.prod_eq_one
  intro z hz
  rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
  rw [List.mem_ofFn] at hw
  rcases hw with ⟨i, rfl⟩
  change (FreeGroup.lift (surfaceCyclicGeneratorImage (d := d) hg))
    (FreeGroup.of (i, false) * FreeGroup.of (i, true) *
      (FreeGroup.of (i, false))⁻¹ * (FreeGroup.of (i, true))⁻¹) = 1
  simp only [map_mul, map_inv]
  rw [mul_comm
    ((FreeGroup.lift (surfaceCyclicGeneratorImage (d := d) hg))
      (FreeGroup.of (i, false)))
    ((FreeGroup.lift (surfaceCyclicGeneratorImage (d := d) hg))
      (FreeGroup.of (i, true)))]
  group

lemma surfaceCyclicRelators_le_kernel {g d : ℕ} [NeZero d] (hg : 0 < g) :
    Subgroup.normalClosure ({surfaceRelator g} : Set (FreeGroup (SurfaceGenerator g))) ≤
      (surfaceCyclicSchreierData (d := d) hg).toFiniteQuotientSchreierData.kernel := by
  change Subgroup.normalClosure
      ({surfaceRelator g} : Set (FreeGroup (SurfaceGenerator g))) ≤
    (surfaceCyclicQuotientMap (d := d) hg).ker
  apply Subgroup.normalClosure_le_normal
  intro r hr
  simp only [Set.mem_singleton_iff] at hr
  rw [hr]
  change surfaceCyclicQuotientMap (d := d) hg (surfaceRelator g) = 1
  exact surfaceCyclicQuotientMap_surfaceRelator_eq_one hg

lemma surfaceCyclicRelatorRelations {g d : ℕ} (hg : 0 < g) :
    ∀ r ∈ ({surfaceRelator g} : Set (FreeGroup (SurfaceGenerator g))),
      FreeGroup.lift (surfaceCyclicGeneratorImage (d := d) hg) r = 1 := by
  intro r hr
  simp only [Set.mem_singleton_iff] at hr
  rw [hr]
  exact surfaceCyclicQuotientMap_surfaceRelator_eq_one hg

def surfaceCyclicPresentedHom {g d : ℕ} (hg : 0 < g) :
    SurfaceGroup g →* SurfaceCyclicQuotient d :=
  PresentedGroup.toGroup (surfaceCyclicRelatorRelations (d := d) hg)

@[simp] lemma surfaceCyclicPresentedHom_of_baseGenerator {g d : ℕ} (hg : 0 < g) :
    surfaceCyclicPresentedHom (d := d) hg
        (PresentedGroup.of (surfaceCyclicBaseGenerator hg)) =
      Multiplicative.ofAdd 1 := by
  rw [surfaceCyclicPresentedHom, PresentedGroup.toGroup.of]
  simp [surfaceCyclicGeneratorImage]

theorem surfaceCyclicPresentedHom_surjective {g d : ℕ} [NeZero d] (hg : 0 < g) :
    Function.Surjective (surfaceCyclicPresentedHom (d := d) hg) := by
  intro q
  refine ⟨PresentedGroup.of (surfaceCyclicBaseGenerator hg) ^ q.toAdd.val, ?_⟩
  rw [map_pow, surfaceCyclicPresentedHom_of_baseGenerator]
  apply Multiplicative.toAdd.injective
  simpa using ZMod.natCast_zmod_val q.toAdd

theorem surfaceCyclicPresentedHom_ker_index {g d : ℕ} [NeZero d] (hg : 0 < g) :
    (surfaceCyclicPresentedHom (d := d) hg).ker.index = d := by
  rw [Subgroup.index_ker]
  have hrange : (surfaceCyclicPresentedHom (d := d) hg).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (surfaceCyclicPresentedHom_surjective (d := d) hg)
  rw [hrange]
  simp [Nat.card_eq_fintype_card, ZMod.card]

instance surfaceCyclicPresentedHom_ker_finiteIndex {g d : ℕ} [NeZero d]
    (hg : 0 < g) : (surfaceCyclicPresentedHom (d := d) hg).ker.FiniteIndex := by
  rw [Subgroup.finiteIndex_iff, surfaceCyclicPresentedHom_ker_index hg]
  exact Nat.ne_of_gt (NeZero.pos d)

abbrev surfaceCyclicSchreierRelators {g d : ℕ} [NeZero d] (hg : 0 < g) :
    Set (FreeGroup
      (FiniteQuotientSchreierData.FiniteSchreierSymbol
        (SurfaceGenerator g) (SurfaceCyclicQuotient d))) :=
  (surfaceCyclicSchreierData (d := d) hg).toFiniteQuotientSchreierData.presentationRelators
    ({surfaceRelator g} : Set (FreeGroup (SurfaceGenerator g)))

noncomputable def surfaceCyclicRawPresentedEquivKernel
    {g d : ℕ} [NeZero d] (hg : 0 < g) :
    PresentedGroup (surfaceCyclicSchreierRelators (d := d) hg) ≃*
      (surfaceCyclicPresentedHom (d := d) hg).ker := by
  let D := surfaceCyclicSchreierData (d := d) hg
  exact
    (D.toFiniteQuotientSchreierData.presentationPresentedGroupEquivOfIsPrefixClosedQuotientSection
        (surfaceCyclicRelators_le_kernel (d := d) hg) D.isPrefixClosed).trans
      (ReidemeisterSchreier.Discrete.Presentations.presentedFreeKernelRelatorQuotientEquivPresentedKernel
          (surfaceCyclicRelatorRelations (d := d) hg))

end
end SystolicGrowth

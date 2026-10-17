module

public import BuserSarnak.BuserSarnakCorrection
public import BuserSarnak.BuserSarnakMarking
public import SurfaceGroup.Raw

@[expose] public section

namespace SystolicGrowth

noncomputable section

open scoped Pointwise

/-! ## Finite-index compact quotients

The Buser--Sarnak correction replaces a principal level group by a finite-index
cyclic kernel.  The following lemma records the compactness argument needed for
that replacement.  It deliberately uses an orbit-covering compact set, rather
than assuming that compactness descends abstractly through an unspecified map
between orbit quotients.
-/

theorem isCompact_orbitRel_quotient_of_finiteIndex_subgroup
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    (H D : Subgroup G) (hDH : D ≤ H)
    [(D.subgroupOf H).FiniteIndex] [ContinuousConstSMul H X]
    (K : Set X) (hK : IsCompact K)
    (hcover : ∀ z : X, ∃ gamma : H, gamma • z ∈ K) :
    IsCompact (Set.univ : Set (MulAction.orbitRel.Quotient D X)) := by
  obtain ⟨t, -, ht⟩ :=
    Subgroup.exists_leftTransversal_of_FiniteIndex
      (D := D.subgroupOf H) (H := ⊤) le_top
  let KD : Set X :=
    ⋃ r ∈ t, (fun z : X ↦ ((r : H)⁻¹ • z)) '' K
  have hKD : IsCompact KD := by
    exact t.isCompact_biUnion fun r _ ↦
      hK.image (continuous_const_smul (r : H)⁻¹)
  have hDcover : ∀ z : X, ∃ gamma : D, gamma • z ∈ KD := by
    intro z
    obtain ⟨g, hgK⟩ := hcover z
    have hgUnion : g ∈
        ⋃ r ∈ t, (r : H) • (D.subgroupOf H : Set H) := by
      rw [ht]
      exact Subgroup.mem_top g
    obtain ⟨r, hgUnion⟩ := Set.mem_iUnion.mp hgUnion
    obtain ⟨hr, hgCoset⟩ := Set.mem_iUnion.mp hgUnion
    let h : H := (r : H)⁻¹ * g
    have hh : h ∈ D.subgroupOf H :=
      (mem_leftCoset_iff (s := (D.subgroupOf H : Set H)) (r : H)).mp hgCoset
    have hmul : (r : H) * h = g := by
      simp [h]
    refine ⟨⟨h, hh⟩, ?_⟩
    simp only [KD, Set.mem_iUnion]
    refine ⟨r, ⟨hr, ?_⟩⟩
    refine ⟨g • z, hgK, ?_⟩
    rw [← hmul]
    change (r : H)⁻¹ • (((r : H) * h) • z) = h • z
    rw [mul_smul, inv_smul_smul]
  exact isCompact_orbitRel_quotient_of_compact_cover KD hKD hDcover

theorem finiteIndex_subgroupOf_trans
    {G : Type*} [Group G] {D L H : Subgroup G}
    (hDL : D ≤ L) (hLH : L ≤ H)
    [(D.subgroupOf L).FiniteIndex] [(L.subgroupOf H).FiniteIndex] :
    (D.subgroupOf H).FiniteIndex := by
  have hDrelL : D.IsFiniteRelIndex L :=
    Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
  have hLrelH : L.IsFiniteRelIndex H :=
    Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
  have hDrelH : D.IsFiniteRelIndex H := by
    rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero]
    rw [← Subgroup.relIndex_mul_relIndex D L H hDL hLH]
    exact mul_ne_zero
      (Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp hDrelL)
      (Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp hLrelH)
  exact Subgroup.isFiniteRelIndex_iff_finiteIndex.mp hDrelH

/-! ## The corrected cyclic kernel -/

/-- Pull the standard cyclic quotient of a surface group back through a
marking of the principal Buser--Sarnak level group. -/
noncomputable def buserSarnakCyclicHom
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (marking : buserSarnakLevelGroup23 p ≃*
      SurfaceGroup (data.halfImageIndex + 1)) :
    buserSarnakLevelGroup23 p →* SurfaceCyclicQuotient data.degree :=
  (surfaceCyclicPresentedHom
    (g := data.halfImageIndex + 1) (d := data.degree) (by omega)).comp
      marking.toMonoidHom

/-- The cyclic correction, embedded as an actual matrix subgroup. -/
noncomputable def buserSarnakCorrectedLevelGroup23
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (marking : buserSarnakLevelGroup23 p ≃*
      SurfaceGroup (data.halfImageIndex + 1)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
  (buserSarnakCyclicHom data marking).ker.map
    (buserSarnakLevelGroup23 p).subtype

/-- Pulling a homomorphism back along an equivalence identifies its kernel
with the original kernel. -/
noncomputable def buserSarnakCyclicKernelEquiv
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (marking : buserSarnakLevelGroup23 p ≃*
      SurfaceGroup (data.halfImageIndex + 1)) :
    (buserSarnakCyclicHom data marking).ker ≃*
      (surfaceCyclicPresentedHom
        (g := data.halfImageIndex + 1) (d := data.degree) (by omega)).ker where
  toFun x := ⟨marking x, by
    change (surfaceCyclicPresentedHom
      (g := data.halfImageIndex + 1) (d := data.degree) (by omega))
        (marking x) = 1
    exact x.property⟩
  invFun y := ⟨marking.symm y, by
    change (surfaceCyclicPresentedHom
      (g := data.halfImageIndex + 1) (d := data.degree) (by omega))
        (marking (marking.symm y)) = 1
    rw [marking.apply_symm_apply]
    exact y.property⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_mul' x y := by
    ext
    simp

/-- The corrected matrix group has exactly the genus supplied by the cyclic
surface-kernel calculation. -/
noncomputable def buserSarnakCorrectedLevelGroup23Marking
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (marking : buserSarnakLevelGroup23 p ≃*
      SurfaceGroup (data.halfImageIndex + 1)) :
    buserSarnakCorrectedLevelGroup23 data marking ≃*
      SurfaceGroup (1 + data.degree * data.halfImageIndex) := by
  letI : NeZero data.degree := ⟨Nat.ne_of_gt data.degree_pos⟩
  exact
    (Subgroup.equivMapOfInjective
      (buserSarnakCyclicHom data marking).ker
      (buserSarnakLevelGroup23 p).subtype Subtype.val_injective).symm |>.trans
    (buserSarnakCyclicKernelEquiv data marking) |>.trans
    (surfaceCyclicKernelEquivSurface data.halfImageIndex data.degree)

theorem buserSarnakCorrectedLevelGroup23_le_level
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (marking : buserSarnakLevelGroup23 p ≃*
      SurfaceGroup (data.halfImageIndex + 1)) :
    buserSarnakCorrectedLevelGroup23 data marking ≤
      buserSarnakLevelGroup23 p := by
  rintro gamma ⟨x, hx, rfl⟩
  exact x.property

theorem buserSarnakCorrectedLevelGroup23_subgroupOf_level_eq
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (marking : buserSarnakLevelGroup23 p ≃*
      SurfaceGroup (data.halfImageIndex + 1)) :
    (buserSarnakCorrectedLevelGroup23 data marking).subgroupOf
      (buserSarnakLevelGroup23 p) =
        (buserSarnakCyclicHom data marking).ker := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := Subtype.ext hxy
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem buserSarnakLevelGroup23_le_fullDeckGroup23 (p : ℕ) :
    buserSarnakLevelGroup23 p ≤
      BuserSarnakQuaternionUnit.fullDeckGroup23 := by
  rintro gamma ⟨q, hq, rfl⟩
  exact ⟨q, rfl⟩

theorem buserSarnakCorrectedLevelGroup23_finiteIndexInLevel
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (marking : buserSarnakLevelGroup23 p ≃*
      SurfaceGroup (data.halfImageIndex + 1)) :
    ((buserSarnakCorrectedLevelGroup23 data marking).subgroupOf
      (buserSarnakLevelGroup23 p)).FiniteIndex := by
  letI : NeZero data.degree := ⟨Nat.ne_of_gt data.degree_pos⟩
  rw [buserSarnakCorrectedLevelGroup23_subgroupOf_level_eq data marking]
  exact Subgroup.finiteIndex_ker (buserSarnakCyclicHom data marking)

theorem buserSarnakCorrectedLevelGroup23_finiteIndexInFull
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (marking : buserSarnakLevelGroup23 p ≃*
      SurfaceGroup (data.halfImageIndex + 1)) :
    ((buserSarnakCorrectedLevelGroup23 data marking).subgroupOf
      BuserSarnakQuaternionUnit.fullDeckGroup23).FiniteIndex := by
  letI : ((buserSarnakCorrectedLevelGroup23 data marking).subgroupOf
      (buserSarnakLevelGroup23 p)).FiniteIndex :=
    buserSarnakCorrectedLevelGroup23_finiteIndexInLevel data marking
  letI : (BuserSarnakQuaternionUnit.levelSubgroupOfFull23 p).FiniteIndex :=
    BuserSarnakQuaternionUnit.levelSubgroupOfFull23_finiteIndex p
  letI : ((buserSarnakLevelGroup23 p).subgroupOf
      BuserSarnakQuaternionUnit.fullDeckGroup23).FiniteIndex := by
    rw [← BuserSarnakQuaternionUnit.levelSubgroupOfFull23_eq_subgroupOf p]
    infer_instance
  exact finiteIndex_subgroupOf_trans
    (buserSarnakCorrectedLevelGroup23_le_level data marking)
    (buserSarnakLevelGroup23_le_fullDeckGroup23 p)

theorem buserSarnakCorrectedLevelGroup23_isDiscrete
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (marking : buserSarnakLevelGroup23 p ≃*
      SurfaceGroup (data.halfImageIndex + 1)) :
    IsDiscrete (buserSarnakCorrectedLevelGroup23 data marking :
      Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)) := by
  apply (BuserSarnakQuaternionUnit.levelDeckGroup_isDiscrete
    (a := 2) (b := 3) (by norm_num) (by norm_num) (p : ℤ)).mono
  exact buserSarnakCorrectedLevelGroup23_le_level data marking

theorem buserSarnakCorrectedLevelGroup23_free
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p)
    (marking : buserSarnakLevelGroup23 p ≃*
      SurfaceGroup (data.halfImageIndex + 1)) :
    ∀ gamma : buserSarnakCorrectedLevelGroup23 data marking,
      ∀ z : UpperHalfPlane, gamma • z = z → gamma = 1 := by
  intro gamma z hfix
  let gammaLevel : buserSarnakLevelGroup23 p :=
    ⟨gamma, buserSarnakCorrectedLevelGroup23_le_level data marking gamma.property⟩
  have hfixLevel : gammaLevel • z = z := hfix
  have hgamma := BuserSarnakQuaternionUnit.levelDeckGroup_free23
    hp hp2 gammaLevel z hfixLevel
  apply Subtype.ext
  change (gammaLevel : Matrix.SpecialLinearGroup (Fin 2) ℝ) = 1
  exact congrArg Subtype.val hgamma

theorem buserSarnakCorrectedLevelGroup23_compactQuotient
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (marking : buserSarnakLevelGroup23 p ≃*
      SurfaceGroup (data.halfImageIndex + 1)) :
    IsCompact (Set.univ : Set (MulAction.orbitRel.Quotient
      (buserSarnakCorrectedLevelGroup23 data marking) UpperHalfPlane)) := by
  letI : ((buserSarnakCorrectedLevelGroup23 data marking).subgroupOf
      BuserSarnakQuaternionUnit.fullDeckGroup23).FiniteIndex :=
    buserSarnakCorrectedLevelGroup23_finiteIndexInFull data marking
  exact isCompact_orbitRel_quotient_of_finiteIndex_subgroup
    BuserSarnakQuaternionUnit.fullDeckGroup23
    (buserSarnakCorrectedLevelGroup23 data marking)
    ((buserSarnakCorrectedLevelGroup23_le_level data marking).trans
      (buserSarnakLevelGroup23_le_fullDeckGroup23 p))
    BuserSarnakQuaternionUnit.fullFundamentalSet23
    BuserSarnakQuaternionUnit.fullFundamentalSet23_isCompact
    BuserSarnakQuaternionUnit.fullFundamentalSet23_orbit_cover

/-! ## Corrected surfaces and the Buser--Sarnak input -/

theorem buserSarnakCorrectedGenus_eq_arithmeticGenus
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    1 + data.degree * data.halfImageIndex = arithmeticGenus 12 p := by
  have hpoly : p * (p ^ 2 - 1) = p ^ 3 - p := by
    simp [Nat.mul_sub_left_distrib, pow_succ, Nat.mul_comm]
  calc
    1 + data.degree * data.halfImageIndex =
        data.degree * data.halfImageIndex + 1 := by omega
    _ = (p * (p ^ 2 - 1)) / 2 + 1 := data.corrected_genus_eq
    _ = (p ^ 3 - p) / 2 + 1 := by rw [hpoly]
    _ = arithmeticGenus 12 p :=
      (arithmeticGenus_twelve_of_odd (hp.odd_of_ne_two hp2)).symm

noncomputable def buserSarnakCorrectedLevelGroup23ArithmeticMarking
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (marking : buserSarnakLevelGroup23 p ≃*
      SurfaceGroup (data.halfImageIndex + 1)) :
    buserSarnakCorrectedLevelGroup23 data marking ≃*
      SurfaceGroup (arithmeticGenus 12 p) := by
  rw [← buserSarnakCorrectedGenus_eq_arithmeticGenus data hp hp2]
  exact buserSarnakCorrectedLevelGroup23Marking data marking

theorem BuserSarnakQuaternionUnit.systole_lower23_of_deckGroup_le
    {g p : ℕ} (hg : 0 < g) (hp : p.Prime) (hp2 : p ≠ 2)
    (X : ClosedHyperbolicSurface g)
    (hdeck : X.deckGroup ≤ buserSarnakLevelGroup23 p) :
    4 * Real.log (p : ℝ) ≤ X.systole := by
  apply ClosedHyperbolicSurface.le_systole_of_displacement_lower X _
    (ClosedHyperbolicSurface.translationLengths_nonempty_of_genus_pos X hg)
  intro gamma hgamma z
  change 4 * Real.log (p : ℝ) ≤ dist z
    ((gamma : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z)
  apply displacement_lower_of_abs_trace_lower_bound p hp z gamma
  apply BuserSarnakQuaternionUnit.nontrivial_levelDeckGroup_real_abs_trace_lower_bound23
    hp hp2 (hdeck gamma.property)
  intro hgammaCoe
  apply hgamma
  apply Subtype.ext
  exact hgammaCoe

noncomputable def buserSarnakCorrectedSurfaceOfMarking
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (marking : buserSarnakLevelGroup23 p ≃*
      SurfaceGroup (data.halfImageIndex + 1)) :
    ClosedHyperbolicSurface (arithmeticGenus 12 p) where
  deckGroup := buserSarnakCorrectedLevelGroup23 data marking
  discrete := buserSarnakCorrectedLevelGroup23_isDiscrete data marking
  free := buserSarnakCorrectedLevelGroup23_free hp hp2 data marking
  compactQuotient :=
    buserSarnakCorrectedLevelGroup23_compactQuotient data marking
  marking :=
    buserSarnakCorrectedLevelGroup23ArithmeticMarking data hp hp2 marking

theorem buserSarnakCorrectedSurfaceOfMarking_systole_lower
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (marking : buserSarnakLevelGroup23 p ≃*
      SurfaceGroup (data.halfImageIndex + 1)) :
    4 * Real.log (p : ℝ) ≤
      (buserSarnakCorrectedSurfaceOfMarking data hp hp2 marking).systole := by
  apply BuserSarnakQuaternionUnit.systole_lower23_of_deckGroup_le
    (by simp [arithmeticGenus]) hp hp2
  exact buserSarnakCorrectedLevelGroup23_le_level data marking

/-- The only remaining Buser--Sarnak marking datum after the correction is
the honest genus of the principal level group.  No corrected genus is assumed
here. -/
structure BuserSarnakBaseSurfaceMarking where
  marking : ∀ (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3),
    buserSarnakLevelGroup23 p ≃*
      SurfaceGroup
        ((buserSarnakCorrectionData p hp hp2 hp3).halfImageIndex + 1)

namespace BuserSarnakBaseSurfaceMarking

noncomputable def correctedSurface (base : BuserSarnakBaseSurfaceMarking)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ClosedHyperbolicSurface (arithmeticGenus 12 p) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact buserSarnakCorrectedSurfaceOfMarking
    (buserSarnakCorrectionData p hp hp2 hp3) hp hp2
    (base.marking p hp hp2 hp3)

theorem correctedSurface_systole_lower
    (base : BuserSarnakBaseSurfaceMarking)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    4 * Real.log (p : ℝ) ≤
      (base.correctedSurface p hp hp2 hp3).systole := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact buserSarnakCorrectedSurfaceOfMarking_systole_lower
    (buserSarnakCorrectionData p hp hp2 hp3) hp hp2
    (base.marking p hp hp2 hp3)

/-- A base-level surface marking now produces the full corrected arithmetic
family expected by the main reduction. The correction data is constructed
from the kernel-checked central-pair cardinality theorem. -/
noncomputable def toBuserSarnakInput
    (base : BuserSarnakBaseSurfaceMarking) : BuserSarnakInput where
  h := 12
  h_pos := by norm_num
  surface := base.correctedSurface
  systole_lower := base.correctedSurface_systole_lower

end BuserSarnakBaseSurfaceMarking

end

end SystolicGrowth

module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public import Mathlib.GroupTheory.CosetCover
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Topology.Order.LiminfLimsup

@[expose] public section

open Filter Set UpperHalfPlane
open scoped MatrixGroups Pointwise UpperHalfPlane commutatorElement

namespace SystolicGrowth

/-! ## Closed hyperbolic surfaces and their systoles

We use the uniformization description of an oriented closed hyperbolic surface:
it is a quotient of the Poincaré upper half-plane by a free, discrete,
cocompact subgroup of `SL(2, ℝ)`.  Mathlib supplies both the Poincaré metric on
`ℍ` and the isometric action of `SL(2, ℝ)` on it.
-/

/-- The two standard generators `aᵢ, bᵢ` associated to the `i`-th handle of
an orientable surface of genus `g`. -/
abbrev SurfaceGenerator (g : ℕ) := Fin g × Bool

/-- The relator `∏ᵢ [aᵢ,bᵢ]` in the usual presentation of the fundamental
group of a closed orientable surface of genus `g`.

We use a list, rather than a finset, because multiplication in a free group is
not commutative. -/
def surfaceRelator (g : ℕ) : FreeGroup (SurfaceGenerator g) :=
  (List.ofFn fun i : Fin g ↦
    ⁅FreeGroup.of (i, false), FreeGroup.of (i, true)⁆).prod

/-- The standard group
`⟨a₁,b₁,…,a_g,b_g ∣ ∏ᵢ [aᵢ,bᵢ] = 1⟩` of a closed orientable
surface of genus `g`. -/
abbrev SurfaceGroup (g : ℕ) := PresentedGroup ({surfaceRelator g} : Set _)

/-- A standard handle generator remains nontrivial in the surface-group
presentation of every positive genus. -/
theorem surfaceGroup_generator_ne_one {g : ℕ} (hg : 0 < g) :
    PresentedGroup.of ((⟨0, hg⟩, false) : SurfaceGenerator g) ≠ (1 : SurfaceGroup g) := by
  let a : SurfaceGenerator g := (⟨0, hg⟩, false)
  change PresentedGroup.of a ≠ 1
  let f : SurfaceGenerator g → Multiplicative ℤ :=
    fun x ↦ if x = a then Multiplicative.ofAdd 1 else 1
  have hrel : ∀ r ∈ ({surfaceRelator g} : Set (FreeGroup (SurfaceGenerator g))),
      FreeGroup.lift f r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff.mp hr, surfaceRelator, map_list_prod]
    apply List.prod_eq_one
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  let phi : SurfaceGroup g →* Multiplicative ℤ := PresentedGroup.toGroup hrel
  intro h
  have hphi := congrArg phi h
  have himage : phi (PresentedGroup.of a) = f a := PresentedGroup.toGroup.of hrel
  rw [himage] at hphi
  have hone : f a = 1 := hphi.trans (map_one phi)
  simp only [f, if_pos] at hone
  have hzero : (1 : ℤ) = 0 := congrArg Multiplicative.toAdd hone
  norm_num at hzero

/-- A compact set meeting every orbit gives a compact orbit-space quotient. -/
theorem isCompact_orbitRel_quotient_of_compact_cover
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    (K : Set X) (hK : IsCompact K) (hcover : ∀ x : X, ∃ g : G, g • x ∈ K) :
    IsCompact (Set.univ : Set (MulAction.orbitRel.Quotient G X)) := by
  letI := MulAction.orbitRel G X
  have himage : Quotient.mk' '' K =
      (Set.univ : Set (MulAction.orbitRel.Quotient G X)) := by
    apply Set.eq_univ_of_forall
    intro q
    induction q using Quotient.inductionOn'
    rename_i x
    obtain ⟨g, hg⟩ := hcover x
    refine ⟨g • x, hg, ?_⟩
    apply Quotient.sound
    exact ⟨g, rfl⟩
  rw [← himage]
  exact hK.image continuous_quotient_mk'

/-- Cocompactness passes from a continuously acting group to a finite-index
subgroup.  A finite set of left-coset representatives turns a compact
fundamental set for the large group into a finite union of compact translates
meeting every orbit of the subgroup. -/
theorem isCompact_orbitRel_quotient_of_finiteIndex
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] (H : Subgroup G) [H.FiniteIndex]
    (K : Set X) (hK : IsCompact K) (hcover : ∀ x : X, ∃ g : G, g • x ∈ K) :
    IsCompact (Set.univ : Set (MulAction.orbitRel.Quotient H X)) := by
  obtain ⟨t, -, ht⟩ :=
    Subgroup.exists_leftTransversal_of_FiniteIndex (D := H) (H := ⊤) le_top
  let KH : Set X :=
    ⋃ r ∈ t, (fun z : X ↦ ((r : G)⁻¹ • z)) '' K
  have hKH : IsCompact KH := by
    exact t.isCompact_biUnion fun r _ ↦
      hK.image (continuous_const_smul (r : G)⁻¹)
  have hHcover : ∀ x : X, ∃ h : H, h • x ∈ KH := by
    intro x
    obtain ⟨g, hgK⟩ := hcover x
    have hgUnion : g ∈ ⋃ r ∈ t, (r : G) • (H : Set G) := by
      rw [ht]
      exact Subgroup.mem_top g
    have hdecomp : ∃ r ∈ t, ∃ h ∈ H, (r : G) * h = g := by
      simpa using! hgUnion
    obtain ⟨r, hr, h, hh, hmul⟩ := hdecomp
    refine ⟨⟨h, hh⟩, ?_⟩
    simp only [KH, Set.mem_iUnion]
    refine ⟨r, ⟨hr, ?_⟩⟩
    refine ⟨g • x, hgK, ?_⟩
    rw [← hmul]
    change (r : G)⁻¹ • (((r : G) * h) • x) = h • x
    rw [mul_smul, inv_smul_smul]
  exact isCompact_orbitRel_quotient_of_compact_cover KH hKH hHcover

/-- The image of a finite-index subgroup under a surjective homomorphism has
finite index. -/
theorem Subgroup.FiniteIndex.map_of_surjective
    {G G' : Type*} [Group G] [Group G'] (H : Subgroup G) [H.FiniteIndex]
    (f : G →* G') (hf : Function.Surjective f) : (H.map f).FiniteIndex := by
  classical
  obtain ⟨t, -, ht⟩ :=
    Subgroup.exists_leftTransversal_of_FiniteIndex (D := H) (H := ⊤) le_top
  apply Subgroup.finiteIndex_of_leftCoset_cover_const
    (H := H.map f) (s := t) (g := fun r ↦ f r)
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨x, rfl⟩ := hf y
  have hxUnion : x ∈ ⋃ r ∈ t, (r : G) • (H : Set G) := by
    rw [ht]
    exact Subgroup.mem_top x
  have hdecomp : ∃ r ∈ t, ∃ h ∈ H, (r : G) * h = x := by
    simpa using! hxUnion
  obtain ⟨r, hr, h, hh, hmul⟩ := hdecomp
  refine Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr, ?_⟩⟩
  have hfh : f h ∈ H.map f := ⟨h, hh, rfl⟩
  have hmem := mem_leftCoset (s := (H.map f : Set G')) (f r) hfh
  simpa [← f.map_mul, hmul] using hmem

/-- For a properly discontinuous action on a proper metric space, every orbit
contains a point minimizing its distance to a prescribed basepoint. -/
theorem exists_smul_minimizing_distance
    {G X : Type*} [Group G] [MetricSpace X] [ProperSpace X] [MulAction G X]
    [ProperlyDiscontinuousSMul G X] (o x : X) :
    ∃ g : G, ∀ h : G, dist o (g • x) ≤ dist o (h • x) := by
  let S : Set G := {g | dist o (g • x) ≤ dist o x}
  have hSfinite : S.Finite := by
    apply (finite_disjoint_inter_image (Γ := G)
      (K := ({x} : Set X)) (L := Metric.closedBall o (dist o x))
      isCompact_singleton (isCompact_closedBall o (dist o x))).subset
    intro g hg
    change dist o (g • x) ≤ dist o x at hg
    refine ⟨g • x, ⟨?_, Metric.mem_closedBall.mpr (by simpa [dist_comm] using hg)⟩⟩
    exact ⟨x, Set.mem_singleton x, rfl⟩
  have hSne : S.Nonempty := by
    refine ⟨1, ?_⟩
    simp [S]
  obtain ⟨g, hgS, hgmin⟩ := Set.exists_min_image S
    (fun h : G ↦ dist o (h • x)) hSfinite hSne
  refine ⟨g, fun h ↦ ?_⟩
  by_cases hhS : h ∈ S
  · exact hgmin h hhS
  · exact hgS.trans (le_of_not_ge hhS)

/-- A marked closed oriented hyperbolic surface of genus `g`.

The subgroup `deckGroup ≤ SL(2, ℝ)` acts on the Poincaré upper half-plane.
Mathlib's properness theorem for this action implies that a discrete subgroup
acts properly discontinuously; freeness then makes the orbit space a
hyperbolic surface, while compactness makes it closed.  The marking identifies
the genus with the standard genus-`g` surface group and therefore records
the genus without an unconstrained numerical field. -/
structure ClosedHyperbolicSurface (g : ℕ) where
  /-- The group of orientation-preserving deck transformations. -/
  deckGroup : Subgroup SL(2, ℝ)
  /-- The deck group is discrete in `SL(2, ℝ)`. -/
  discrete : IsDiscrete (deckGroup : Set SL(2, ℝ))
  /-- No nonidentity deck transformation fixes a point of the hyperbolic plane. -/
  free : ∀ γ : deckGroup, ∀ z : ℍ, γ • z = z → γ = 1
  /-- The quotient by the deck group is compact. -/
  compactQuotient :
    IsCompact (Set.univ : Set (MulAction.orbitRel.Quotient deckGroup ℍ))
  /-- A marking by the standard fundamental group of a genus-`g` surface. -/
  marking : deckGroup ≃* SurfaceGroup g

namespace ClosedHyperbolicSurface

/-- The topology inherited by the deck group is discrete. -/
instance {g : ℕ} (X : ClosedHyperbolicSurface g) : DiscreteTopology X.deckGroup :=
  isDiscrete_iff_discreteTopology.mp X.discrete

/-- Deck transformations act by isometries of the Poincaré metric. -/
instance {g : ℕ} (X : ClosedHyperbolicSurface g) :
    IsIsometricSMul X.deckGroup ℍ :=
  ⟨fun γ ↦ isometry_smul ℍ (γ : SL(2, ℝ))⟩

/-- A closed hyperbolic surface's deck group acts properly discontinuously on
the Poincaré upper half-plane. -/
instance {g : ℕ} (X : ClosedHyperbolicSurface g) :
    ProperlyDiscontinuousSMul X.deckGroup ℍ := by
  infer_instance

/-- The underlying topological quotient of a closed hyperbolic surface. -/
abbrev Carrier {g : ℕ} (X : ClosedHyperbolicSurface g) :=
  MulAction.orbitRel.Quotient X.deckGroup ℍ

/-- The compactness field can be installed locally as the standard
`CompactSpace` instance expected by quotient-geometry libraries. -/
theorem carrierCompactSpace {g : ℕ}
    (X : ClosedHyperbolicSurface g) : CompactSpace X.Carrier :=
  ⟨X.compactQuotient⟩

/-- Freeness in the fixed-point formulation commonly used for Fuchsian
groups: an element fixing one point fixes every point (and is the identity). -/
theorem fixes_every_point_of_exists_fixed_point {g : ℕ}
    (X : ClosedHyperbolicSurface g) (gamma : X.deckGroup)
    (hfixed : ∃ z : ℍ, gamma • z = z) : ∀ z : ℍ, gamma • z = z := by
  obtain ⟨z, hz⟩ := hfixed
  have hgamma : gamma = 1 := X.free gamma z hz
  subst gamma
  simp

/-- Translation lengths of nonidentity deck transformations.

For a cocompact torsion-free Fuchsian group these are precisely the lengths
whose infimum is the length of the shortest noncontractible closed geodesic in
the quotient. -/
def translationLengths {g : ℕ} (X : ClosedHyperbolicSurface g) : Set ℝ :=
  { length | ∃ γ : X.deckGroup, γ ≠ 1 ∧ ∃ z : ℍ, length = dist z (γ • z) }

/-- Translation lengths are bounded below by zero. -/
theorem translationLengths_bddBelow {g : ℕ} (X : ClosedHyperbolicSurface g) :
    BddBelow X.translationLengths := by
  refine ⟨0, ?_⟩
  rintro length ⟨γ, hγ, z, rfl⟩
  exact dist_nonneg

/-- Positive genus forces the translation-length set to be nonempty, through
the marking by the standard nontrivial surface group. -/
theorem translationLengths_nonempty_of_genus_pos {g : ℕ}
    (X : ClosedHyperbolicSurface g) (hg : 0 < g) : X.translationLengths.Nonempty := by
  let x : SurfaceGroup g := PresentedGroup.of ((⟨0, hg⟩, false) : SurfaceGenerator g)
  have hx : x ≠ 1 := by
    simpa [x] using surfaceGroup_generator_ne_one hg
  let gamma : X.deckGroup := X.marking.symm x
  have hgamma : gamma ≠ 1 := by
    intro h
    apply hx
    have hmap := congrArg X.marking h
    simpa [gamma] using hmap
  exact ⟨dist (I : ℍ) (gamma • I), gamma, hgamma, I, rfl⟩

/-- The systole of a closed hyperbolic surface: the infimum of the translation
lengths of its nonidentity deck transformations. -/
noncomputable def systole {g : ℕ} (X : ClosedHyperbolicSurface g) : ℝ :=
  sInf X.translationLengths

/-- The systole is no larger than the displacement of any point by a
nonidentity deck transformation. -/
theorem systole_le_displacement {g : ℕ} (X : ClosedHyperbolicSurface g)
    (γ : X.deckGroup) (hγ : γ ≠ 1) (z : ℍ) :
    X.systole ≤ dist z (γ • z) := by
  rw [systole]
  exact csInf_le X.translationLengths_bddBelow ⟨γ, hγ, z, rfl⟩

/-- The systole is nonnegative in positive genus. -/
theorem systole_nonneg_of_genus_pos {g : ℕ} (X : ClosedHyperbolicSurface g)
    (hg : 0 < g) : 0 ≤ X.systole := by
  rw [systole]
  apply le_csInf (X.translationLengths_nonempty_of_genus_pos hg)
  rintro length ⟨γ, hγ, z, rfl⟩
  exact dist_nonneg

/-- A uniform lower bound for all nontrivial deck-transformation displacements
is a lower bound for the systole. -/
theorem le_systole_of_displacement_lower {g : ℕ} (X : ClosedHyperbolicSurface g)
    (L : ℝ) (hnonempty : X.translationLengths.Nonempty)
    (hlower : ∀ γ : X.deckGroup, γ ≠ 1 → ∀ z : ℍ, L ≤ dist z (γ • z)) :
    L ≤ X.systole := by
  rw [systole]
  apply le_csInf hnonempty
  rintro length ⟨γ, hgamma, z, hlength⟩
  rw [hlength]
  exact hlower γ hgamma z

end ClosedHyperbolicSurface

/-- The set of systoles realized by closed hyperbolic surfaces of genus `g`. -/
def systoleSpectrum (g : ℕ) : Set ℝ :=
  Set.range (fun X : ClosedHyperbolicSurface g ↦ X.systole)

/-- The supremal systole in genus `g`, denoted `Sys(g)` in the draft.

For `g ≥ 2`, the standard compactness/properness result on moduli space says
that this supremum is attained, so it agrees with the draft's maximum. -/
noncomputable def Sys (g : ℕ) : ℝ :=
  sSup (systoleSpectrum g)

end SystolicGrowth

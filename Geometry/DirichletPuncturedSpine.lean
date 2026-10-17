module

public import Geometry.DirichletCyclicBoundary
public import Geometry.DirichletPuncturedPolygon
public import Geometry.SurfacePunctureRetraction
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section

/-!
# The actual one-center-punctured Dirichlet quotient

The compact Dirichlet domain projects onto the original surface. Its center
fiber is a singleton, and distinct representatives in the same orbit lie on
its actual frontier. These facts provide quotient descent without changing
the original quotient topology.
-/

open Set Metric
open scoped UpperHalfPlane Topology unitInterval ContinuousMap

namespace SystolicGrowth
namespace ClosedHyperbolicSurface

noncomputable section

variable {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ)

theorem dirichletDomain_isCompact :
    IsCompact (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  obtain ⟨K, hK, hcover⟩ := X.exists_compact_covering
  exact X.isCompact_dirichletDomain_of_compact_covering o K hK hcover

/-- Orbit projection from the actual compact Dirichlet domain. -/
def dirichletOrbitProjection :
    C(Vendored.RiemannDynamics.dirichletDomain X.deckGroup o, X.Carrier) :=
  ⟨fun z => Quotient.mk'' z.1, continuous_quot_mk.comp continuous_subtype_val⟩

theorem dirichletOrbitProjection_surjective :
    Function.Surjective (X.dirichletOrbitProjection o) := by
  intro q
  obtain ⟨z, rfl⟩ := Quotient.mk_surjective q
  obtain ⟨γ, hγ⟩ := Vendored.RiemannDynamics.exists_smul_mem_dirichletDomain
    (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ) o z
  refine ⟨⟨γ • z, hγ⟩, ?_⟩
  exact Quotient.sound (MulAction.orbitRel_apply.mpr
    (MulAction.mem_orbit_iff.mpr ⟨γ, rfl⟩))

theorem dirichletOrbitProjection_isClosedMap :
    IsClosedMap (X.dirichletOrbitProjection o) := by
  letI : CompactSpace (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) :=
    isCompact_iff_compactSpace.mp (X.dirichletDomain_isCompact o)
  exact (X.dirichletOrbitProjection o).continuous.isClosedMap

theorem dirichletOrbitProjection_isQuotientMap :
    Topology.IsQuotientMap (X.dirichletOrbitProjection o) :=
  (X.dirichletOrbitProjection_isClosedMap o).isQuotientMap
    (X.dirichletOrbitProjection o).continuous
    (X.dirichletOrbitProjection_surjective o)

/-- The only representative of the center orbit in its Dirichlet domain is
the original center itself. -/
theorem dirichlet_center_fiber {z : ℍ}
    (hz : z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) :
    (Quotient.mk'' z : X.Carrier) = Quotient.mk'' o ↔ z = o := by
  constructor
  · intro h
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact h))
    have hd := hz γ
    rw [hγ, dist_self] at hd
    exact dist_eq_zero.mp (le_antisymm hd dist_nonneg)
  · rintro rfl
    rfl

theorem dirichletOrbitProjection_preimage_center :
    (X.dirichletOrbitProjection o) ⁻¹' {(Quotient.mk'' o : X.Carrier)} =
      {⟨o, Vendored.RiemannDynamics.basepoint_mem_dirichletDomain⟩} := by
  ext z
  simp only [mem_preimage, mem_singleton_iff]
  change (Quotient.mk'' z.1 : X.Carrier) = Quotient.mk'' o ↔ _
  rw [X.dirichlet_center_fiber o z.2]
  constructor
  · intro h
    apply Subtype.ext
    exact h
  · intro h
    exact congrArg Subtype.val h

/-- Distinct representatives of one orbit in the actual closed domain are
both boundary points. -/
theorem dirichlet_eq_orbit_frontier {z w : ℍ}
    (hz : z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)
    (hw : w ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)
    (hzw : (Quotient.mk'' z : X.Carrier) = Quotient.mk'' w) (hne : z ≠ w) :
    z ∈ frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) ∧
      w ∈ frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.exact hzw))
  have hγne : γ ≠ 1 := by
    intro he
    apply hne
    simpa only [he, one_smul] using hγ.symm
  have hd₁ : dist z (γ • o) = dist w o := by
    rw [← hγ]
    exact dist_smul γ w o
  have hd₂ : dist w (γ⁻¹ • o) = dist z o := by
    rw [← dist_smul γ w (γ⁻¹ • o), hγ, smul_inv_smul]
  have hzle := hz γ
  have hwle := hw γ⁻¹
  rw [hd₁] at hzle
  rw [hd₂] at hwle
  constructor
  · exact X.mem_frontier_dirichletDomain_of_mem_bisector o γ hγne hz
      (hd₁.trans (le_antisymm hwle hzle)).symm
  · exact X.mem_frontier_dirichletDomain_of_mem_bisector o γ⁻¹
      (inv_ne_one.mpr hγne) hw (hd₂.trans (le_antisymm hzle hwle)).symm

theorem dirichlet_frontier_ne_center {z : ℍ}
    (hz : z ∈ frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) :
    z ≠ o := by
  intro h
  subst z
  exact Set.disjoint_left.mp disjoint_interior_frontier
    (X.basepoint_mem_interior_dirichletDomain o) hz

theorem dirichlet_frontier_mem_domain {z : ℍ}
    (hz : z ∈ frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)) :
    z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := by
  simpa only [(Vendored.RiemannDynamics.isClosed_dirichletDomain X.deckGroup o).closure_eq]
    using frontier_subset_closure hz

/-- Restricted orbit map, with the original center and only that center removed. -/
def puncturedDirichletOrbitProjection :
    C({z : ℍ // z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∧ z ≠ o},
      X.CenterPuncturedCarrier o) :=
  ⟨fun z => ⟨Quotient.mk'' z.1, fun h => z.2.2
      ((X.dirichlet_center_fiber o z.2.1).mp h)⟩,
    Continuous.subtype_mk (continuous_quot_mk.comp continuous_subtype_val) _⟩

def puncturedDirichletPreimageHomeomorph :
    {z : ℍ // z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∧ z ≠ o} ≃ₜ
      {z : Vendored.RiemannDynamics.dirichletDomain X.deckGroup o //
        X.dirichletOrbitProjection o z ≠ (Quotient.mk'' o : X.Carrier)} where
  toFun z := ⟨⟨z.1, z.2.1⟩, (X.puncturedDirichletOrbitProjection o z).2⟩
  invFun z := ⟨z.1.1, z.1.2, fun h => z.2 (by
    change (Quotient.mk'' z.1.1 : X.Carrier) = Quotient.mk'' o
    rw [h])⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val _) _
  continuous_invFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) _

theorem puncturedDirichletOrbitProjection_isQuotientMap :
    Topology.IsQuotientMap (X.puncturedDirichletOrbitProjection o) := by
  have h := (X.dirichletOrbitProjection_isQuotientMap o).restrictPreimage_isOpen
    (isClosed_singleton.isOpen_compl : IsOpen ({(Quotient.mk'' o : X.Carrier)}ᶜ))
  exact h.comp (X.puncturedDirichletPreimageHomeomorph o).isQuotientMap

/-- The actual frontier projected into the original punctured surface. -/
def dirichletFrontierOrbitProjection :
    C(frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o),
      X.CenterPuncturedCarrier o) :=
  ⟨fun z => ⟨Quotient.mk'' z.1, fun h =>
      X.dirichlet_frontier_ne_center o z.2
        ((X.dirichlet_center_fiber o (X.dirichlet_frontier_mem_domain o z.2)).mp h)⟩,
    Continuous.subtype_mk (continuous_quot_mk.comp continuous_subtype_val) _⟩

/-- The boundary spine is exactly the orbit image of the actual frontier. -/
def dirichletBoundarySpine : Set (X.CenterPuncturedCarrier o) :=
  Set.range (X.dirichletFrontierOrbitProjection o)

/-- The natural frontier projection onto its actual orbit-image spine. -/
def dirichletFrontierSpineProjection :
    C(X.DirichletFrontier o, X.dirichletBoundarySpine o) :=
  ⟨fun z => ⟨X.dirichletFrontierOrbitProjection o z, z, rfl⟩,
    (X.dirichletFrontierOrbitProjection o).continuous.subtype_mk _⟩

theorem dirichletFrontierSpineProjection_surjective :
    Function.Surjective (X.dirichletFrontierSpineProjection o) := by
  rintro ⟨q, z, rfl⟩
  exact ⟨z, rfl⟩

theorem dirichletFrontierSpineProjection_isQuotientMap :
    Topology.IsQuotientMap (X.dirichletFrontierSpineProjection o) := by
  letI : CompactSpace (X.DirichletFrontier o) := isCompact_iff_compactSpace.mp
    ((X.dirichletDomain_isCompact o).of_isClosed_subset isClosed_frontier
      (fun _ hz => X.dirichlet_frontier_mem_domain o hz))
  exact (X.dirichletFrontierSpineProjection o).continuous.isClosedMap.isQuotientMap
    (X.dirichletFrontierSpineProjection o).continuous
    (X.dirichletFrontierSpineProjection_surjective o)

@[simp]
theorem puncturedDirichletOrbitProjection_frontierInclusion (z : X.DirichletFrontier o) :
    X.puncturedDirichletOrbitProjection o (X.dirichletFrontierInclusion o z) =
      X.dirichletFrontierOrbitProjection o z := rfl

/-- The actual polygon homotopy respects every fiber of the orbit map:
nontrivial identifications occur only where that homotopy is fixed. -/
theorem dirichletPunctureHomotopyMap_orbit_eq (t : I)
    (z w : X.PuncturedDirichletDomain o)
    (h : X.puncturedDirichletOrbitProjection o z =
      X.puncturedDirichletOrbitProjection o w) :
    X.puncturedDirichletOrbitProjection o (X.dirichletPunctureHomotopyMap o (t, z)) =
      X.puncturedDirichletOrbitProjection o (X.dirichletPunctureHomotopyMap o (t, w)) := by
  by_cases hzw : z = w
  · rw [hzw]
  have hval : z.1 ≠ w.1 := fun he => hzw (Subtype.ext he)
  have hfront := X.dirichlet_eq_orbit_frontier o z.2.1 w.2.1
    (congrArg Subtype.val h) hval
  rw [X.dirichletPunctureHomotopyMap_fixed o (t, z) hfront.1,
    X.dirichletPunctureHomotopyMap_fixed o (t, w) hfront.2]
  exact h

theorem dirichletPunctureRetraction_orbit_eq
    (z w : X.PuncturedDirichletDomain o)
    (h : X.puncturedDirichletOrbitProjection o z =
      X.puncturedDirichletOrbitProjection o w) :
    X.dirichletFrontierOrbitProjection o (X.dirichletPunctureRetraction o z) =
      X.dirichletFrontierOrbitProjection o (X.dirichletPunctureRetraction o w) := by
  have ht := X.dirichletPunctureHomotopyMap_orbit_eq o 1 z w h
  simpa only [X.dirichletPunctureHomotopyMap_one o,
    X.puncturedDirichletOrbitProjection_frontierInclusion o] using ht

def puncturedDirichletOrbitLift (q : X.CenterPuncturedCarrier o) :
    X.PuncturedDirichletDomain o :=
  (X.puncturedDirichletOrbitProjection_isQuotientMap o).surjective q |>.choose

private theorem puncturedDirichletOrbitLift_projection (q : X.CenterPuncturedCarrier o) :
    X.puncturedDirichletOrbitProjection o (X.puncturedDirichletOrbitLift o q) = q :=
  (X.puncturedDirichletOrbitProjection_isQuotientMap o).surjective q |>.choose_spec

def dirichletSpineRetractionFn (q : X.CenterPuncturedCarrier o) :
    X.dirichletBoundarySpine o :=
  ⟨X.dirichletFrontierOrbitProjection o
    (X.dirichletPunctureRetraction o (X.puncturedDirichletOrbitLift o q)), _, rfl⟩

theorem dirichletSpineRetractionFn_projection (z : X.PuncturedDirichletDomain o) :
    (X.dirichletSpineRetractionFn o (X.puncturedDirichletOrbitProjection o z)).1 =
      X.dirichletFrontierOrbitProjection o (X.dirichletPunctureRetraction o z) :=
  X.dirichletPunctureRetraction_orbit_eq o _ z
    (X.puncturedDirichletOrbitLift_projection o _)

/-- Retraction of the original punctured quotient onto its actual boundary spine. -/
def dirichletSpineRetraction :
    C(X.CenterPuncturedCarrier o, X.dirichletBoundarySpine o) where
  toFun := X.dirichletSpineRetractionFn o
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (X.puncturedDirichletOrbitProjection_isQuotientMap o).continuous_iff.mpr
    change Continuous ((fun q => (X.dirichletSpineRetractionFn o q).1) ∘
      X.puncturedDirichletOrbitProjection o)
    have h : (fun q => (X.dirichletSpineRetractionFn o q).1) ∘
        X.puncturedDirichletOrbitProjection o =
        (X.dirichletFrontierOrbitProjection o) ∘ X.dirichletPunctureRetraction o := by
      funext z
      exact X.dirichletSpineRetractionFn_projection o z
    rw [h]
    exact (X.dirichletFrontierOrbitProjection o).continuous.comp
      (X.dirichletPunctureRetraction o).continuous

/-- Exact quotient-descent equation for the radial retraction. -/
@[simp]
theorem dirichletSpineRetraction_projection (z : X.PuncturedDirichletDomain o) :
    X.dirichletSpineRetraction o (X.puncturedDirichletOrbitProjection o z) =
      X.dirichletFrontierSpineProjection o (X.dirichletPunctureRetraction o z) := by
  apply Subtype.ext
  exact X.dirichletSpineRetractionFn_projection o z

/-- Literal inclusion of the actual boundary spine into the original punctured carrier. -/
def dirichletSpineInclusion :
    C(X.dirichletBoundarySpine o, X.CenterPuncturedCarrier o) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def dirichletSpineHomotopyFn (p : I × X.CenterPuncturedCarrier o) :
    X.CenterPuncturedCarrier o :=
  X.puncturedDirichletOrbitProjection o (X.dirichletPunctureHomotopyMap o
    (p.1, X.puncturedDirichletOrbitLift o p.2))

theorem dirichletSpineHomotopyFn_projection (p : I × X.PuncturedDirichletDomain o) :
    X.dirichletSpineHomotopyFn o (p.1, X.puncturedDirichletOrbitProjection o p.2) =
      X.puncturedDirichletOrbitProjection o (X.dirichletPunctureHomotopyMap o p) :=
  X.dirichletPunctureHomotopyMap_orbit_eq o p.1 _ p.2
    (X.puncturedDirichletOrbitLift_projection o _)

/-- Jointly continuous descended polygon homotopy on the original quotient. -/
def dirichletSpineHomotopyMap :
    C(I × X.CenterPuncturedCarrier o, X.CenterPuncturedCarrier o) where
  toFun := X.dirichletSpineHomotopyFn o
  continuous_toFun := by
    apply (X.puncturedDirichletOrbitProjection_isQuotientMap o).continuous_lift_prod_right
    have h : (fun p : I × X.PuncturedDirichletDomain o =>
        X.dirichletSpineHomotopyFn o (p.1, X.puncturedDirichletOrbitProjection o p.2)) =
        (X.puncturedDirichletOrbitProjection o) ∘ X.dirichletPunctureHomotopyMap o := by
      funext p
      exact X.dirichletSpineHomotopyFn_projection o p
    rw [h]
    exact (X.puncturedDirichletOrbitProjection o).continuous.comp
      (X.dirichletPunctureHomotopyMap o).continuous

/-- Exact quotient-descent equation for every time and every actual representative. -/
@[simp]
theorem dirichletSpineHomotopyMap_projection (p : I × X.PuncturedDirichletDomain o) :
    X.dirichletSpineHomotopyMap o (p.1, X.puncturedDirichletOrbitProjection o p.2) =
      X.puncturedDirichletOrbitProjection o (X.dirichletPunctureHomotopyMap o p) :=
  X.dirichletSpineHomotopyFn_projection o p

@[simp]
theorem dirichletSpineHomotopyMap_zero (q : X.CenterPuncturedCarrier o) :
    X.dirichletSpineHomotopyMap o (0, q) = q := by
  change X.puncturedDirichletOrbitProjection o
    (X.dirichletPunctureHomotopyMap o (0, X.puncturedDirichletOrbitLift o q)) = q
  rw [X.dirichletPunctureHomotopyMap_zero o]
  exact X.puncturedDirichletOrbitLift_projection o q

@[simp]
theorem dirichletSpineHomotopyMap_one (q : X.CenterPuncturedCarrier o) :
    X.dirichletSpineHomotopyMap o (1, q) =
      X.dirichletSpineInclusion o (X.dirichletSpineRetraction o q) := by
  change X.puncturedDirichletOrbitProjection o
    (X.dirichletPunctureHomotopyMap o (1, X.puncturedDirichletOrbitLift o q)) = _
  rw [X.dirichletPunctureHomotopyMap_one o]
  rfl

theorem dirichletSpineHomotopyMap_fixed (p : I × X.CenterPuncturedCarrier o)
    (hp : p.2 ∈ X.dirichletBoundarySpine o) :
    X.dirichletSpineHomotopyMap o p = p.2 := by
  obtain ⟨z, hz⟩ := hp
  have h : X.puncturedDirichletOrbitProjection o (X.puncturedDirichletOrbitLift o p.2) =
      X.puncturedDirichletOrbitProjection o (X.dirichletFrontierInclusion o z) := by
    rw [X.puncturedDirichletOrbitLift_projection o,
      X.puncturedDirichletOrbitProjection_frontierInclusion o, hz]
  change X.puncturedDirichletOrbitProjection o
    (X.dirichletPunctureHomotopyMap o (p.1, X.puncturedDirichletOrbitLift o p.2)) = _
  rw [X.dirichletPunctureHomotopyMap_orbit_eq o p.1 _ _ h,
    X.dirichletPunctureHomotopyMap_fixed o
      (p.1, X.dirichletFrontierInclusion o z) z.2,
    X.puncturedDirichletOrbitProjection_frontierInclusion o, hz]

@[simp]
theorem dirichletSpineRetraction_inclusion (q : X.dirichletBoundarySpine o) :
    X.dirichletSpineRetraction o (X.dirichletSpineInclusion o q) = q := by
  apply Subtype.ext
  exact (X.dirichletSpineHomotopyMap_one o q.1).symm.trans
    (X.dirichletSpineHomotopyMap_fixed o (1, q.1) q.2)

/-- On every literal spine loop, inclusion followed by radial retraction is
the original representative, with only the canonical endpoint casts. -/
theorem dirichletSpineRetraction_inclusion_loop (q : X.dirichletBoundarySpine o)
    (p : Path q q) :
    ((p.map (X.dirichletSpineInclusion o).continuous).map
      (X.dirichletSpineRetraction o).continuous).cast
        (X.dirichletSpineRetraction_inclusion o q).symm
        (X.dirichletSpineRetraction_inclusion o q).symm = p := by
  apply Path.ext
  funext t
  exact X.dirichletSpineRetraction_inclusion o (p t)

/-- A genuine strong deformation retraction of the original center-punctured
surface fixing the whole actual boundary spine at every time. -/
def dirichletSpineDeformationRetraction :
    (ContinuousMap.id (X.CenterPuncturedCarrier o)).HomotopyRel
      ((X.dirichletSpineInclusion o).comp (X.dirichletSpineRetraction o))
      (X.dirichletBoundarySpine o) where
  toHomotopy :=
    { toContinuousMap := X.dirichletSpineHomotopyMap o
      map_zero_left := X.dirichletSpineHomotopyMap_zero o
      map_one_left := X.dirichletSpineHomotopyMap_one o }
  prop' := fun t q hq => X.dirichletSpineHomotopyMap_fixed o (t, q) hq

@[simp]
theorem dirichletSpineDeformationRetraction_inclusion (t : I)
    (q : X.dirichletBoundarySpine o) :
    X.dirichletSpineDeformationRetraction o (t, X.dirichletSpineInclusion o q) =
      X.dirichletSpineInclusion o q :=
  X.dirichletSpineHomotopyMap_fixed o (t, q.1) q.2

/-- Homotopy equivalence with the actual paired-boundary spine. -/
def dirichletSpineHomotopyEquiv :
    X.CenterPuncturedCarrier o ≃ₕ X.dirichletBoundarySpine o where
  toFun := X.dirichletSpineRetraction o
  invFun := X.dirichletSpineInclusion o
  left_inv := ⟨(X.dirichletSpineDeformationRetraction o).toHomotopy.symm⟩
  right_inv := by
    have h : (X.dirichletSpineRetraction o).comp (X.dirichletSpineInclusion o) =
        ContinuousMap.id (X.dirichletBoundarySpine o) := by
      apply ContinuousMap.ext
      intro q
      exact X.dirichletSpineRetraction_inclusion o q
    rw [h]

/-- Bijectivity of the literal retraction-induced map at every original
punctured-surface basepoint, including those moved by the radial homotopy. -/
theorem dirichletSpineRetraction_fundamentalGroupMap_bijective
    (q : X.CenterPuncturedCarrier o) :
    Function.Bijective (FundamentalGroup.map (X.dirichletSpineRetraction o) q) := by
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (X.dirichletSpineHomotopyEquiv o)
  exact e.fullyFaithfulFunctor.map_bijective (FundamentalGroupoid.mk q)
    (FundamentalGroupoid.mk q)

/-- Exact based π₁ equivalence, with the actual retracted basepoint and actual
retraction-induced forward map. No basepoint-preservation hypothesis is used. -/
def dirichletSpineFundamentalGroupEquiv (q : X.CenterPuncturedCarrier o) :
    FundamentalGroup (X.CenterPuncturedCarrier o) q ≃*
      FundamentalGroup (X.dirichletBoundarySpine o) (X.dirichletSpineRetraction o q) :=
  MulEquiv.ofBijective (FundamentalGroup.map (X.dirichletSpineRetraction o) q)
    (X.dirichletSpineRetraction_fundamentalGroupMap_bijective o q)

theorem dirichletSpineFundamentalGroupEquiv_toMonoidHom (q : X.CenterPuncturedCarrier o) :
    (X.dirichletSpineFundamentalGroupEquiv o q).toMonoidHom =
      FundamentalGroup.map (X.dirichletSpineRetraction o) q := rfl

/-- The equivalence takes an actual representative loop to its literal
radial-retraction image, with no change of the original source basepoint. -/
@[simp]
theorem dirichletSpineFundamentalGroupEquiv_loop (q : X.CenterPuncturedCarrier o)
    (p : Path q q) :
    X.dirichletSpineFundamentalGroupEquiv o q ⟦p⟧ =
      ⟦p.map (X.dirichletSpineRetraction o).continuous⟧ := rfl

end
end ClosedHyperbolicSurface
end SystolicGrowth

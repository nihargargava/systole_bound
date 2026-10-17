module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import BuserSarnak.OrientableWicksElementaryNormalization
public import Geometry.DirichletFanAngles
public import Geometry.EmbeddedTwoPunctureMarkedAmalgam
public import Geometry.GluingChainPrefixMarkedInduction
public import Geometry.SurfaceBoundaryGraphWicksAssembly
public import Geometry.SurfaceCharacterRank
public import Geometry.SurfacePeripheralOrientation
public import Geometry.SurfaceTwoCenterNativePeripheralTransport
public import Geometry.SurfaceTwoCenterPolarGeneratorComparison
public import Geometry.SurfaceTwoCenterRightPolarGeneratorComparison
public import Geometry.SystoleUpperFromArea
public import Vendored.RiemannDynamics.Teichmuller.PolygonRank

@[expose] public section

/-!
# Polygon area and preparation of surface chains

Paired polygon edges and vertex angles determine the area of each component.
Packing estimates then choose separated disks for gluing and prepare chains
of surfaces with comparable genera and systoles. The final record describes
a faithful, free, discrete surface-group action with a compact fundamental
set and a uniform displacement lower bound.

The conformal construction of that action is in
`GluingConformalSmoothSolution`; `SurfaceGluing` uses it to construct the
geometric input to the final theorem. Historical structure names are retained.
-/

open Filter MeasureTheory Set UpperHalfPlane
open scoped BigOperators ENNReal MatrixGroups Pointwise Topology UpperHalfPlane ContinuousMap

namespace SystolicGrowth

/-- The actual triangle set occurring in a finite fundamental-domain certificate. -/
def exerciseTriangleSet {g : ℕ} {X : ClosedHyperbolicSurface g}
    (T : FiniteTriangleFundamentalDomain X) (i : Fin T.triangleCount) : Set ℍ :=
  Vendored.RiemannDynamics.hyperbolicTriangle
    (T.vertices i).1 (T.vertices i).2.1 (T.vertices i).2.2

/-- The three corner angles, in the same order as `angleDeficit`. -/
noncomputable def exerciseCornerAngle {g : ℕ} {X : ClosedHyperbolicSurface g}
    (T : FiniteTriangleFundamentalDomain X)
    (c : Fin T.triangleCount × Fin 3) : ℝ :=
  if c.2 = 0 then
    Vendored.RiemannDynamics.sectorAngle
      (T.vertices c.1).1 (T.vertices c.1).2.1 (T.vertices c.1).2.2
  else if c.2 = 1 then
    Vendored.RiemannDynamics.sectorAngle
      (T.vertices c.1).2.1 (T.vertices c.1).1 (T.vertices c.1).2.2
  else
    Vendored.RiemannDynamics.sectorAngle
      (T.vertices c.1).2.2 (T.vertices c.1).1 (T.vertices c.1).2.1

/-- Elementary angle-convention check; no polygon construction is assumed. -/
theorem exercise_sum_cornerAngle {g : ℕ} {X : ClosedHyperbolicSurface g}
    (T : FiniteTriangleFundamentalDomain X) (i : Fin T.triangleCount) :
    (∑ k : Fin 3, exerciseCornerAngle T (i, k)) = Real.pi - T.angleDeficit i := by
  simp [Fin.sum_univ_succ, exerciseCornerAngle,
    FiniteTriangleFundamentalDomain.angleDeficit]
  ring

/-- Output certificate constructed by the proved G-POLYGON constructor.

Exact tiling and a.e. disjointness are needed: a triangle cover gives only an
upper area bound and cannot provide the lower area budget for gluing centers.
`edgeCount` counts paired polygon sides; `vertexCount` counts quotient vertex
classes. The fan has `2*edgeCount-2` triangles, potentially arbitrarily many.
There is no unjustified claim `triangleCount ≤ 4*g`.

The graph-character field must be constructed from the actual side-pairing
presentation, not assumed from the desired area or Euler formula. Every field
is supplied by the actual native polygon and its verified adapters. -/
structure ExercisePolygonCertificate {g : ℕ} (X : ClosedHyperbolicSurface g) where
  triangles : FiniteTriangleFundamentalDomain X
  triangle_measurable : ∀ i, NullMeasurableSet (exerciseTriangleSet triangles i) volume
  triangle_ae_disjoint : Pairwise (fun i j ↦
    AEDisjoint volume (exerciseTriangleSet triangles i) (exerciseTriangleSet triangles j))
  triangles_ae_exact : triangles.fundamentalDomain =ᵐ[volume]
    ⋃ i, exerciseTriangleSet triangles i
  edgeCount : ℕ
  vertexCount : ℕ
  fan_count : triangles.triangleCount + 2 = 2 * edgeCount
  connected_count : vertexCount ≤ edgeCount + 1
  cornerVertex : Fin triangles.triangleCount × Fin 3 → Fin vertexCount
  vertex_angles : ∀ v : Fin vertexCount,
    (∑ c : Fin triangles.triangleCount × Fin 3 with cornerVertex c = v,
      exerciseCornerAngle triangles c) = 2 * Real.pi
  graph_characters : AdditiveCharacterSpace X.deckGroup ≃ₗ[ℝ]
    (Fin (edgeCount + 1 - vertexCount) → ℝ)

/-- A fixed-point-free involution on a finite linearly ordered type partitions
the elements into pairs.  The smaller member of each pair is a canonical
representative, so the total cardinality is twice the number of representatives. -/
theorem fin_card_eq_two_mul_representatives (n : ℕ)
    (f : Fin n → Fin n) (hinvol : Function.Involutive f)
    (hfixed : ∀ i, f i ≠ i) :
    n = 2 * Fintype.card {i : Fin n // i < f i} := by
  classical
  let lower : Fin n → Prop := fun i => i < f i
  let upper : Fin n → Prop := fun i => f i < i
  have hpartition (i : Fin n) : lower i ∨ upper i := by
    rcases lt_or_gt_of_ne (hfixed i) with h | h
    · exact Or.inr h
    · exact Or.inl h
  let e : {i : Fin n // lower i} ≃ {i : Fin n // upper i} := {
    toFun := fun i => ⟨f i.1, by
      change f (f i.1) < f i.1
      simpa only [hinvol i.1] using i.2⟩
    invFun := fun i => ⟨f i.1, by
      change f i.1 < f (f i.1)
      simpa only [hinvol i.1] using i.2⟩
    left_inv := fun i => Subtype.ext (hinvol i.1)
    right_inv := fun i => Subtype.ext (hinvol i.1) }
  have hEq : Fintype.card {i : Fin n // lower i} =
      Fintype.card {i : Fin n // upper i} := Fintype.card_congr e
  let ecomp : {i : Fin n // upper i} ≃ {i : Fin n // ¬ lower i} := {
    toFun := fun i => ⟨i.1, fun hilow => (lt_asymm hilow i.2)⟩
    invFun := fun i => ⟨i.1, by
      have hle : f i.1 ≤ i.1 := not_lt.mp i.2
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · exact False.elim (hfixed i.1 heq)⟩
    left_inv := fun i => Subtype.ext rfl
    right_inv := fun i => Subtype.ext rfl }
  have hComplement : Fintype.card {i : Fin n // upper i} =
      Fintype.card (Fin n) - Fintype.card {i : Fin n // lower i} := by
    rw [Fintype.card_congr ecomp]
    exact Fintype.card_subtype_compl lower
  have hle : Fintype.card {i : Fin n // lower i} ≤ Fintype.card (Fin n) :=
    Fintype.card_subtype_le lower
  rw [Fintype.card_fin] at hComplement hle
  rw [← hEq] at hComplement
  have hsub : n - Fintype.card {i : Fin n // lower i} =
      Fintype.card {i : Fin n // lower i} := hComplement.symm
  have hsum := (Nat.sub_eq_iff_eq_add' hle).mp hsub
  simpa [two_mul] using hsum

/-- The actual boundary-vertex fan has exactly the polygon vertex count minus
two triangles.  This is the finite-index part of G-P3, before identifying the
number of polygon sides with twice the paired-side count. -/
theorem intrinsicVertexFan_triangleCount_add_two
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    B.intrinsicVertexFanTriangleFundamentalDomain.triangleCount + 2 =
      B.intrinsicBoundaryRadialCuts.card := by
  simp only [DirichletBoundarySegments.intrinsicVertexFanTriangleFundamentalDomain]
  exact Nat.sub_add_cancel (by
    have h := B.three_le_intrinsicBoundaryRadialCuts_card
    omega)

/-- Choose one actual side from each inverse-deck pair of the intrinsic
cyclic polygon boundary. -/
noncomputable def intrinsicPairedSideCount
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) : ℕ :=
  Fintype.card {i : Fin B.intrinsicBoundaryRadialCuts.card //
    i < B.intrinsicCyclicPairing i}

/-- The cyclic polygon enumerates both orientations of every paired side. -/
theorem intrinsicBoundarySideCount_eq_two_mul_paired
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryRadialCuts.card = 2 * intrinsicPairedSideCount B := by
  exact fin_card_eq_two_mul_representatives _ B.intrinsicCyclicPairing
    B.intrinsicCyclicPairing_involutive B.intrinsicCyclicPairing_ne_self

/-- G-P3 for the actual fan: its `n - 2` triangles plus two are exactly the
`2E` cyclically enumerated sides, where E counts inverse-deck side pairs. -/
theorem intrinsicVertexFan_fan_count
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    B.intrinsicVertexFanTriangleFundamentalDomain.triangleCount + 2 =
      2 * intrinsicPairedSideCount B := by
  rw [intrinsicVertexFan_triangleCount_add_two,
    intrinsicBoundarySideCount_eq_two_mul_paired]

/-- Actual quotient vertices of the cyclic polygon: two cyclic vertices are
identified precisely when they are related by a deck transformation. -/
def intrinsicVertexOrbitRel
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i j : Fin B.intrinsicBoundaryRadialCuts.card) : Prop :=
  ∃ γ : X.deckGroup, γ • B.intrinsicCyclicVertex i = B.intrinsicCyclicVertex j

/-- The vertex relation is the actual orbit equivalence relation for the
given deck action, rather than an independently selected polygon quotient. -/
def intrinsicVertexOrbitSetoid
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
  Setoid (Fin B.intrinsicBoundaryRadialCuts.card) where
  r := intrinsicVertexOrbitRel B
  iseqv := by
    constructor
    · intro i
      exact ⟨1, by simp⟩
    · intro i j hij
      rcases hij with ⟨γ, hγ⟩
      refine ⟨γ⁻¹, ?_⟩
      rw [← hγ]
      simp
    · intro i j k hij hjk
      rcases hij with ⟨γ, hγ⟩
      rcases hjk with ⟨δ, hδ⟩
      refine ⟨δ * γ, ?_⟩
      rw [mul_smul, hγ, hδ]

/-- Since the cyclic vertex set is finite, so is its actual deck-orbit
quotient. -/
noncomputable instance intrinsicVertexOrbitQuotientFintype
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    Fintype (Quotient (intrinsicVertexOrbitSetoid B)) :=
  Fintype.ofFinite _

open Vendored.RiemannDynamics in
/-- The existing native orbit quotient counts precisely the imported actual
polygon vertex classes, via an explicit quotient-to-orbit-class bijection. -/
theorem intrinsicVertexOrbitCount_eq_polygonVertexClassCount
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    polygonVertexClassCount X.deckGroup o =
      Fintype.card (Quotient (intrinsicVertexOrbitSetoid B)) := by
  classical
  have hvertices := B.range_intrinsicCyclicVertex_eq_polygonVertices
  let classOf : Fin B.intrinsicBoundaryRadialCuts.card →
      polygonVertexClasses X.deckGroup o := fun i =>
    ⟨MulAction.orbit X.deckGroup (B.intrinsicCyclicVertex i) ∩
      polygonVertices X.deckGroup o,
      ⟨B.intrinsicCyclicVertex i, hvertices ▸ Set.mem_range_self i, rfl⟩⟩
  have hclass : ∀ i j, intrinsicVertexOrbitRel B i j → classOf i = classOf j := by
    intro i j hij
    apply Subtype.ext
    rcases hij with ⟨γ, hγ⟩
    dsimp [classOf]
    rw [← hγ, MulAction.orbit_smul]
  let f : Quotient (intrinsicVertexOrbitSetoid B) →
      polygonVertexClasses X.deckGroup o := Quotient.lift classOf hclass
  have hinj : Function.Injective f := by
    intro a b hab
    induction a using Quotient.inductionOn with | h i =>
      induction b using Quotient.inductionOn with | h j =>
        apply Quotient.sound
        change intrinsicVertexOrbitRel B i j
        have heq : (classOf i).val = (classOf j).val := congrArg Subtype.val hab
        have hj : B.intrinsicCyclicVertex j ∈ (classOf j).val :=
          ⟨MulAction.mem_orbit_self _, hvertices ▸ Set.mem_range_self j⟩
        have hj' : B.intrinsicCyclicVertex j ∈ (classOf i).val := heq ▸ hj
        exact MulAction.mem_orbit_iff.mp hj'.1
  have hsurj : Function.Surjective f := by
    rintro ⟨C, v, hv, rfl⟩
    obtain ⟨i, rfl⟩ := hvertices.symm ▸ hv
    exact ⟨Quotient.mk _ i, rfl⟩
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  letI : Fintype (polygonVertexClasses X.deckGroup o) :=
    Fintype.ofEquiv (Quotient (intrinsicVertexOrbitSetoid B)) e
  exact (Set.ncard_eq_toFinset_card' _).trans
    ((Set.toFinset_card _).trans (Fintype.card_congr e).symm)

/-- Enumerate the actual deck-orbit vertex classes by `Fin V`. -/
noncomputable def intrinsicVertexClassIndex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Fin (Fintype.card (Quotient (intrinsicVertexOrbitSetoid B))) :=
  Fintype.equivFin (Quotient (intrinsicVertexOrbitSetoid B))
    (Quotient.mk (intrinsicVertexOrbitSetoid B) i)

/-- The reversed endpoint transport of every actual paired side identifies
the corresponding quotient vertex classes. -/
theorem intrinsicVertexClassIndex_pairing_start
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    intrinsicVertexClassIndex B i = intrinsicVertexClassIndex B
      (finRotate B.intrinsicBoundaryRadialCuts.card (B.intrinsicCyclicPairing i)) := by
  change Fintype.equivFin (Quotient (intrinsicVertexOrbitSetoid B))
      (Quotient.mk (intrinsicVertexOrbitSetoid B) i) =
    Fintype.equivFin (Quotient (intrinsicVertexOrbitSetoid B))
      (Quotient.mk (intrinsicVertexOrbitSetoid B)
        (finRotate B.intrinsicBoundaryRadialCuts.card (B.intrinsicCyclicPairing i)))
  apply congrArg (Fintype.equivFin (Quotient (intrinsicVertexOrbitSetoid B)))
  apply Quotient.sound
  exact ⟨(B.intrinsicCyclicEdge i).1.1.1⁻¹,
    (B.inverse_smul_intrinsicCyclicVertices_eq_reverse i).1⟩

/-- The other endpoint of every actual paired side has the same quotient
vertex class under the reversed cyclic endpoint transport. -/
theorem intrinsicVertexClassIndex_pairing_end
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    intrinsicVertexClassIndex B (finRotate B.intrinsicBoundaryRadialCuts.card i) =
    intrinsicVertexClassIndex B (B.intrinsicCyclicPairing i) := by
  change Fintype.equivFin (Quotient (intrinsicVertexOrbitSetoid B))
      (Quotient.mk (intrinsicVertexOrbitSetoid B)
        (finRotate B.intrinsicBoundaryRadialCuts.card i)) =
    Fintype.equivFin (Quotient (intrinsicVertexOrbitSetoid B))
      (Quotient.mk (intrinsicVertexOrbitSetoid B) (B.intrinsicCyclicPairing i))
  apply congrArg (Fintype.equivFin (Quotient (intrinsicVertexOrbitSetoid B)))
  apply Quotient.sound
  exact ⟨(B.intrinsicCyclicEdge i).1.1.1⁻¹,
    (B.inverse_smul_intrinsicCyclicVertices_eq_reverse i).2⟩

/-- The three corners of every actual fan triangle are indexed by their
original cyclic polygon vertices, including the non-wrapping terminal vertex. -/
noncomputable def intrinsicVertexFanCornerSideIndex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (c : Fin B.intrinsicVertexFanTriangleFundamentalDomain.triangleCount × Fin 3) :
    Fin B.intrinsicBoundaryRadialCuts.card :=
  if c.2 = 0 then ⟨0, by
    have h := B.three_le_intrinsicBoundaryRadialCuts_card
    omega⟩
  else if c.2 = 1 then B.intrinsicVertexFanSideIndex c.1
  else finRotate B.intrinsicBoundaryRadialCuts.card
    (B.intrinsicVertexFanSideIndex c.1)

/-- Assign every corner of the actual fan to its actual deck-orbit vertex
class, enumerated by a finite index type. -/
noncomputable def intrinsicVertexFanCornerClassIndex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (c : Fin B.intrinsicVertexFanTriangleFundamentalDomain.triangleCount × Fin 3) :
    Fin (Fintype.card (Quotient (intrinsicVertexOrbitSetoid B))) :=
  intrinsicVertexClassIndex B (intrinsicVertexFanCornerSideIndex B c)

/-- A natural number occurs as a representative position of a given actual
quotient vertex. -/
def intrinsicVertexIndexOccurs
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (q : Quotient (intrinsicVertexOrbitSetoid B)) (m : ℕ) : Prop :=
  ∃ i : Fin B.intrinsicBoundaryRadialCuts.card,
    i.val = m ∧ Quotient.mk (intrinsicVertexOrbitSetoid B) i = q

/-- Every quotient vertex has a boundary representative. -/
theorem intrinsicVertexIndexOccurs_exists
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (q : Quotient (intrinsicVertexOrbitSetoid B)) :
    ∃ m, intrinsicVertexIndexOccurs B q m := by
  obtain ⟨i, hi⟩ := Quotient.exists_rep q
  exact ⟨i.val, i, rfl, hi⟩

/-- The first boundary position representing a quotient vertex. -/
noncomputable def intrinsicVertexFirstPosition
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (q : Quotient (intrinsicVertexOrbitSetoid B)) : ℕ := by
  classical
  exact Nat.find (intrinsicVertexIndexOccurs_exists B q)

/-- At the first position, the quotient vertex really occurs. -/
theorem intrinsicVertexFirstPosition_spec
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (q : Quotient (intrinsicVertexOrbitSetoid B)) :
    intrinsicVertexIndexOccurs B q (intrinsicVertexFirstPosition B q) := by
  classical
  exact Nat.find_spec (intrinsicVertexIndexOccurs_exists B q)

/-- The first representing position is no later than any other position of
the same quotient vertex. -/
theorem intrinsicVertexFirstPosition_le
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (q : Quotient (intrinsicVertexOrbitSetoid B))
    {i : Fin B.intrinsicBoundaryRadialCuts.card}
    (hi : Quotient.mk (intrinsicVertexOrbitSetoid B) i = q) :
    intrinsicVertexFirstPosition B q ≤ i.val := by
  classical
  exact Nat.find_min' (intrinsicVertexIndexOccurs_exists B q) ⟨i, rfl, hi⟩

/-- A non-base vertex has positive first position. -/
theorem intrinsicVertexFirstPosition_pos
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (q : Quotient (intrinsicVertexOrbitSetoid B))
    (hq : q ≠ Quotient.mk (intrinsicVertexOrbitSetoid B)
      (⟨0, by have h := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩ :
        Fin B.intrinsicBoundaryRadialCuts.card)) :
    0 < intrinsicVertexFirstPosition B q := by
  have hspec := intrinsicVertexFirstPosition_spec B q
  rcases hspec with ⟨i, hi, hqrep⟩
  by_contra hn
  have hfirst : intrinsicVertexFirstPosition B q = 0 := by omega
  rw [hfirst] at hi
  have hi0 : i = ⟨0, by have h := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩ :=
    Fin.ext (by omega)
  apply hq
  calc
    q = Quotient.mk (intrinsicVertexOrbitSetoid B) i := hqrep.symm
    _ = Quotient.mk (intrinsicVertexOrbitSetoid B)
        (⟨0, by
          have _h := B.three_le_intrinsicBoundaryRadialCuts_card
          omega⟩ :
          Fin B.intrinsicBoundaryRadialCuts.card) := congrArg _ hi0

/-- The first occurrence, as an actual finite cyclic vertex index. -/
noncomputable def intrinsicVertexFirstIndex
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (q : Quotient (intrinsicVertexOrbitSetoid B)) :
    Fin B.intrinsicBoundaryRadialCuts.card :=
  ⟨intrinsicVertexFirstPosition B q, by
    rcases intrinsicVertexFirstPosition_spec B q with ⟨i, hi, _⟩
    rw [← hi]
    exact i.2⟩

/-- The first finite index represents its specified quotient vertex. -/
theorem intrinsicVertexFirstIndex_mk
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (q : Quotient (intrinsicVertexOrbitSetoid B)) :
    Quotient.mk (intrinsicVertexOrbitSetoid B) (intrinsicVertexFirstIndex B q) = q := by
  rcases intrinsicVertexFirstPosition_spec B q with ⟨i, hi, hq⟩
  have heq : intrinsicVertexFirstIndex B q = i := Fin.ext hi.symm
  rw [heq]
  exact hq

/-- Select the smaller side in an actual inverse-deck pair. -/
noncomputable def intrinsicPairedSideRepresentative
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    {j : Fin B.intrinsicBoundaryRadialCuts.card //
      j < B.intrinsicCyclicPairing j} := by
  classical
  by_cases h : i < B.intrinsicCyclicPairing i
  · exact ⟨i, h⟩
  · refine ⟨B.intrinsicCyclicPairing i, ?_⟩
    have hle : B.intrinsicCyclicPairing i ≤ i := not_lt.mp h
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [B.intrinsicCyclicPairing_involutive i]
      exact hlt
    · exact False.elim (B.intrinsicCyclicPairing_ne_self i heq)

/-- The selected representative is one of the two sides in the pairing orbit. -/
theorem intrinsicPairedSideRepresentative_spec
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    i = (intrinsicPairedSideRepresentative B i).1 ∨
      i = B.intrinsicCyclicPairing (intrinsicPairedSideRepresentative B i).1 := by
  classical
  unfold intrinsicPairedSideRepresentative
  split_ifs with h
  · exact Or.inl rfl
  · right
    change i = B.intrinsicCyclicPairing (B.intrinsicCyclicPairing i)
    exact (B.intrinsicCyclicPairing_involutive i).symm

/-- For a non-base quotient vertex, its first occurrence is reached by the
incoming boundary side immediately preceding that occurrence. -/
noncomputable def intrinsicVertexIncomingSide
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (q : Quotient (intrinsicVertexOrbitSetoid B))
    (hq : q ≠ Quotient.mk (intrinsicVertexOrbitSetoid B)
      (⟨0, by have h := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩ :
        Fin B.intrinsicBoundaryRadialCuts.card)) :
    {j : Fin B.intrinsicBoundaryRadialCuts.card //
      j < B.intrinsicCyclicPairing j} := by
  have hpos := intrinsicVertexFirstPosition_pos B q hq
  let k := intrinsicVertexFirstIndex B q
  let j : Fin B.intrinsicBoundaryRadialCuts.card :=
    ⟨k.val - 1, by omega⟩
  exact intrinsicPairedSideRepresentative B j

/-- A predecessor side followed by cyclic successor reaches the first
occurrence of any non-base vertex. -/
theorem intrinsicVertexFirstPosition_predecessor_rotate
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (q : Quotient (intrinsicVertexOrbitSetoid B))
    (hq : q ≠ Quotient.mk (intrinsicVertexOrbitSetoid B)
      (⟨0, by have h := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩ :
        Fin B.intrinsicBoundaryRadialCuts.card)) :
    let k := intrinsicVertexFirstIndex B q
    let j : Fin B.intrinsicBoundaryRadialCuts.card := ⟨k.val - 1, by
      have _h := intrinsicVertexFirstPosition_pos B q hq
      omega⟩
    finRotate B.intrinsicBoundaryRadialCuts.card j = k := by
  have hkpos := intrinsicVertexFirstPosition_pos B q hq
  let k := intrinsicVertexFirstIndex B q
  have hkposVal : 0 < k.val := by
    simpa [k, intrinsicVertexFirstIndex] using hkpos
  let j : Fin B.intrinsicBoundaryRadialCuts.card := ⟨k.val - 1, by omega⟩
  apply Fin.ext
  rw [finRotate_apply, Fin.val_add, Fin.val_one']
  have hn : 1 % B.intrinsicBoundaryRadialCuts.card = 1 :=
    Nat.mod_eq_of_lt (by have h := B.three_le_intrinsicBoundaryRadialCuts_card; omega)
  rw [hn, Nat.sub_add_cancel (by omega : 1 ≤ k.val), Nat.mod_eq_of_lt k.isLt]

/-- The predecessor side ends at the first representative of the quotient
vertex. -/
theorem intrinsicVertexFirstPosition_predecessor_class
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (q : Quotient (intrinsicVertexOrbitSetoid B))
    (hq : q ≠ Quotient.mk (intrinsicVertexOrbitSetoid B)
      (⟨0, by have h := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩ :
        Fin B.intrinsicBoundaryRadialCuts.card)) :
    let k := intrinsicVertexFirstIndex B q
    let j : Fin B.intrinsicBoundaryRadialCuts.card := ⟨k.val - 1, by
      have _h := intrinsicVertexFirstPosition_pos B q hq
      omega⟩
    Quotient.mk (intrinsicVertexOrbitSetoid B)
      (finRotate B.intrinsicBoundaryRadialCuts.card j) = q := by
  dsimp
  rw [intrinsicVertexFirstPosition_predecessor_rotate B q hq]
  exact intrinsicVertexFirstIndex_mk B q

/-- The first-entry representative is always the earlier of its paired sides;
the later side has its target endpoint represented already. -/
theorem intrinsicVertexIncomingSide_eq_predecessor
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (q : Quotient (intrinsicVertexOrbitSetoid B))
    (hq : q ≠ Quotient.mk (intrinsicVertexOrbitSetoid B)
      (⟨0, by have h := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩ :
        Fin B.intrinsicBoundaryRadialCuts.card)) :
    let k := intrinsicVertexFirstIndex B q
    let j : Fin B.intrinsicBoundaryRadialCuts.card := ⟨k.val - 1, by
      have _h := intrinsicVertexFirstPosition_pos B q hq
      omega⟩
    (intrinsicVertexIncomingSide B q hq).1 = j := by
  classical
  dsimp
  let k := intrinsicVertexFirstIndex B q
  let j : Fin B.intrinsicBoundaryRadialCuts.card := ⟨k.val - 1, by
    have h := intrinsicVertexFirstPosition_pos B q hq
    omega⟩
  have hjk : finRotate B.intrinsicBoundaryRadialCuts.card j = k :=
    intrinsicVertexFirstPosition_predecessor_rotate B q hq
  have hqj : Quotient.mk (intrinsicVertexOrbitSetoid B)
      (finRotate B.intrinsicBoundaryRadialCuts.card j) = q := by
    rw [hjk]
    exact intrinsicVertexFirstIndex_mk B q
  rcases intrinsicPairedSideRepresentative_spec B j with hjr | hjfr
  · exact hjr.symm
  · let r := (intrinsicPairedSideRepresentative B j).1
    have hrlt : r < B.intrinsicCyclicPairing r :=
      (intrinsicPairedSideRepresentative B j).2
    have hj : j = B.intrinsicCyclicPairing r := hjfr
    have hpairClass : Quotient.mk (intrinsicVertexOrbitSetoid B) r =
        Quotient.mk (intrinsicVertexOrbitSetoid B)
          (finRotate B.intrinsicBoundaryRadialCuts.card
            (B.intrinsicCyclicPairing r)) := by
      apply (Fintype.equivFin (Quotient (intrinsicVertexOrbitSetoid B))).injective
      exact intrinsicVertexClassIndex_pairing_start B r
    have hrot : finRotate B.intrinsicBoundaryRadialCuts.card j =
        finRotate B.intrinsicBoundaryRadialCuts.card (B.intrinsicCyclicPairing r) :=
      congrArg (finRotate B.intrinsicBoundaryRadialCuts.card) hj
    have hqr : Quotient.mk (intrinsicVertexOrbitSetoid B) r = q := by
      calc
        Quotient.mk (intrinsicVertexOrbitSetoid B) r =
            Quotient.mk (intrinsicVertexOrbitSetoid B)
              (finRotate B.intrinsicBoundaryRadialCuts.card
                (B.intrinsicCyclicPairing r)) := hpairClass
        _ = Quotient.mk (intrinsicVertexOrbitSetoid B)
              (finRotate B.intrinsicBoundaryRadialCuts.card j) := by rw [← hrot]
        _ = q := hqj
    have hfirst := intrinsicVertexFirstPosition_le B q hqr
    have hkr : k.val ≤ r.val := by
      simpa [k, intrinsicVertexFirstIndex] using hfirst
    have hrj : r.val < j.val := by
      have hv := congrArg Fin.val hj
      change j.val = (B.intrinsicCyclicPairing r).val at hv
      exact lt_of_lt_of_eq (Fin.lt_def.mp hrlt) hv.symm
    have hstep : j.val + 1 = k.val := by
      change (k.val - 1) + 1 = k.val
      have hkpos := intrinsicVertexFirstPosition_pos B q hq
      have hkposVal : 0 < k.val := by
        simpa [k, intrinsicVertexFirstIndex] using hkpos
      exact Nat.sub_add_cancel (by omega)
    have : r.val < k.val := by omega
    omega

/-- Map every non-base quotient vertex to its unique first-entry paired side. -/
noncomputable def intrinsicNonbaseVertexToPairedSide
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    {q : Quotient (intrinsicVertexOrbitSetoid B) //
      q ≠ Quotient.mk (intrinsicVertexOrbitSetoid B)
        (⟨0, by have _h := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩ :
          Fin B.intrinsicBoundaryRadialCuts.card)} →
    {j : Fin B.intrinsicBoundaryRadialCuts.card //
      j < B.intrinsicCyclicPairing j} :=
  fun q => intrinsicVertexIncomingSide B q.1 q.2

/-- The non-base subtype inherits finiteness from the quotient vertex set. -/
noncomputable instance intrinsicNonbaseVertexFintype
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    Fintype {q : Quotient (intrinsicVertexOrbitSetoid B) //
      q ≠ Quotient.mk (intrinsicVertexOrbitSetoid B)
        (⟨0, by have _h := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩ :
          Fin B.intrinsicBoundaryRadialCuts.card)} :=
  Fintype.ofFinite _

/-- Distinct actual quotient vertices cannot enter through the same paired
side: its later orientation has already-seen endpoint class. -/
theorem intrinsicNonbaseVertexToPairedSide_injective
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    Function.Injective (intrinsicNonbaseVertexToPairedSide B) := by
  classical
  intro a b hab
  have hval :
      ((intrinsicVertexIncomingSide B a.1 a.2).1).val =
        ((intrinsicVertexIncomingSide B b.1 b.2).1).val :=
    congrArg (fun s : {j : Fin B.intrinsicBoundaryRadialCuts.card //
      j < B.intrinsicCyclicPairing j} => s.1.val) hab
  have haPos := intrinsicVertexFirstPosition_pos B a.1 a.2
  have hbPos := intrinsicVertexFirstPosition_pos B b.1 b.2
  have hpa := congrArg Fin.val (intrinsicVertexIncomingSide_eq_predecessor B a.1 a.2)
  have hpb := congrArg Fin.val (intrinsicVertexIncomingSide_eq_predecessor B b.1 b.2)
  rw [hpa, hpb] at hval
  have hk : intrinsicVertexFirstIndex B a.1 = intrinsicVertexFirstIndex B b.1 := by
    apply Fin.ext
    have haPos' : 0 < (intrinsicVertexFirstIndex B a.1).val := by
      simpa [intrinsicVertexFirstIndex] using haPos
    have hbPos' : 0 < (intrinsicVertexFirstIndex B b.1).val := by
      simpa [intrinsicVertexFirstIndex] using hbPos
    dsimp only [Fin.val_mk] at hval
    omega
  apply Subtype.ext
  calc
    a.1 = Quotient.mk (intrinsicVertexOrbitSetoid B)
        (intrinsicVertexFirstIndex B a.1) :=
      (intrinsicVertexFirstIndex_mk B a.1).symm
    _ = Quotient.mk (intrinsicVertexOrbitSetoid B)
        (intrinsicVertexFirstIndex B b.1) := congrArg _ hk
    _ = b.1 := intrinsicVertexFirstIndex_mk B b.1

/-- The number of actual non-base quotient vertices is bounded by the number
of paired sides. -/
theorem intrinsicNonbaseVertexCount_le_pairedSideCount
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    Fintype.card {q : Quotient (intrinsicVertexOrbitSetoid B) //
      q ≠ Quotient.mk (intrinsicVertexOrbitSetoid B)
        (⟨0, Nat.zero_lt_of_lt
          (Nat.lt_of_lt_of_le (by decide : 1 < 3)
            B.three_le_intrinsicBoundaryRadialCuts_card)⟩ :
          Fin B.intrinsicBoundaryRadialCuts.card)} ≤ intrinsicPairedSideCount B := by
  exact Fintype.card_le_of_injective (intrinsicNonbaseVertexToPairedSide B)
    (intrinsicNonbaseVertexToPairedSide_injective B)

/-- G-P4 connected count: actual quotient vertex classes are at most one more
than the inverse-deck paired sides. -/
theorem intrinsicQuotientVertexCount_le_pairedSideCount_add_one
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o) :
    Fintype.card (Quotient (intrinsicVertexOrbitSetoid B)) ≤
      intrinsicPairedSideCount B + 1 := by
  classical
  let Q := Quotient (intrinsicVertexOrbitSetoid B)
  let base : Q := Quotient.mk (intrinsicVertexOrbitSetoid B)
    (⟨0, by have h := B.three_le_intrinsicBoundaryRadialCuts_card; omega⟩ :
      Fin B.intrinsicBoundaryRadialCuts.card)
  have hcard : Fintype.card {q : Q // q ≠ base} = Fintype.card Q - 1 := by
    rw [Fintype.card_subtype_compl (fun q : Q => q = base)]
    simp
  have hle := intrinsicNonbaseVertexCount_le_pairedSideCount B
  change Fintype.card {q : Q // q ≠ base} ≤ intrinsicPairedSideCount B at hle
  have hpos : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨base⟩
  rw [hcard] at hle
  exact Nat.sub_le_iff_le_add.mp hle
open Vendored.RiemannDynamics in
/-- The actual polygon interior angles in each native deck-orbit vertex class
sum to a full turn, by the proved translated vertex-star theorem. -/
theorem native_polygon_vertex_class_angle_sum
    {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (v : Fin (Fintype.card (Quotient (intrinsicVertexOrbitSetoid B)))) :
    (∑ j : Fin B.intrinsicBoundaryRadialCuts.card with intrinsicVertexClassIndex B j = v,
      sectorAngle (B.intrinsicCyclicVertex j)
        (B.intrinsicCyclicVertex ((finRotate B.intrinsicBoundaryRadialCuts.card).symm j))
        (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card j))) =
      2 * Real.pi := by
  classical
  let Q := Quotient (intrinsicVertexOrbitSetoid B)
  let e := Fintype.equivFin Q
  let i := intrinsicVertexFirstIndex B (e.symm v)
  have hi : intrinsicVertexClassIndex B i = v := by
    change e (Quotient.mk (intrinsicVertexOrbitSetoid B) i) = v
    rw [intrinsicVertexFirstIndex_mk]
    exact e.apply_symm_apply v
  let A : Fin B.intrinsicBoundaryRadialCuts.card → ℝ := fun j =>
    sectorAngle (B.intrinsicCyclicVertex j)
      (B.intrinsicCyclicVertex ((finRotate B.intrinsicBoundaryRadialCuts.card).symm j))
      (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card j))
  let α : ℍ → ℝ := fun z =>
    ∑ j : Fin B.intrinsicBoundaryRadialCuts.card with B.intrinsicCyclicVertex j = z, A j
  have hα (j : Fin B.intrinsicBoundaryRadialCuts.card) :
      α (B.intrinsicCyclicVertex j) = A j := by
    dsimp [α]
    apply Finset.sum_eq_single j
    · intro k hk hkj
      exact False.elim (hkj (B.intrinsicCyclicVertex_injective
        (Finset.mem_filter.mp hk).2))
    · simp
  let C := MulAction.orbit X.deckGroup (B.intrinsicCyclicVertex i) ∩
    polygonVertices X.deckGroup o
  have hclass (j : Fin B.intrinsicBoundaryRadialCuts.card) :
      intrinsicVertexClassIndex B j = v ↔
        B.intrinsicCyclicVertex j ∈ MulAction.orbit X.deckGroup (B.intrinsicCyclicVertex i) := by
    constructor
    · intro hj
      have heq : Quotient.mk (intrinsicVertexOrbitSetoid B) j =
          Quotient.mk (intrinsicVertexOrbitSetoid B) i :=
        e.injective (hj.trans hi.symm)
      obtain ⟨γ, hγ⟩ := Quotient.exact heq
      refine MulAction.mem_orbit_iff.mpr ⟨γ⁻¹, ?_⟩
      rw [← hγ, inv_smul_smul]
    · intro hj
      obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp hj
      rw [← hi]
      apply congrArg e
      apply Quotient.sound
      refine ⟨γ⁻¹, ?_⟩
      rw [← hγ, inv_smul_smul]
  obtain ⟨R, hdense⟩ := X.exists_dirichlet_orbit_density_bound o
  have hVfin := finite_polygonVertices
    (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
    X.deck_fixing_point_acts_trivially (X.basepoint_mem_interior_dirichletDomain o) hdense
  have hCfin : C.Finite := hVfin.subset (fun _ hz => hz.2)
  have hstar := sum_interiorAngle_vertexClass
    (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
    X.deck_fixing_point_acts_trivially (X.basepoint_mem_interior_dirichletDomain o) hdense
    (B.intrinsicCyclicVertex_mem_polygonVertices i) (α := α) (by
      intro z hz
      obtain ⟨j, rfl⟩ := B.exists_intrinsicCyclicVertex_eq_polygonVertex hz.2
      rw [hα]
      exact B.intrinsicCyclicVertex_prev_next_isInteriorAngleAt j)
  change (∑ᶠ z ∈ C, α z) = 2 * Real.pi at hstar
  rw [finsum_mem_eq_finite_toFinset_sum α hCfin] at hstar
  change (∑ j : Fin B.intrinsicBoundaryRadialCuts.card with intrinsicVertexClassIndex B j = v,
    A j) = 2 * Real.pi
  rw [← hstar]
  apply Finset.sum_bij (fun j _ => B.intrinsicCyclicVertex j)
  · intro j hj
    exact hCfin.mem_toFinset.mpr
      ⟨(hclass j).mp (Finset.mem_filter.mp hj).2,
        B.intrinsicCyclicVertex_mem_polygonVertices j⟩
  · intro j _ k _ hjk
    exact B.intrinsicCyclicVertex_injective hjk
  · intro z hz
    obtain ⟨j, rfl⟩ := B.exists_intrinsicCyclicVertex_eq_polygonVertex
      (hCfin.mem_toFinset.mp hz).2
    exact ⟨j, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (hclass j).mpr (hCfin.mem_toFinset.mp hz).1⟩, rfl⟩
  · intro j _
    exact (hα j).symm


/-- P-ANGLE: regroup the SAME original fan into actual vertex classes, using
the proved full corner fibers (including the boundary apex). -/
theorem exercisePolygonVertexAngles {g : ℕ} (_hg : 2 ≤ g)
    {X : ClosedHyperbolicSurface g} {o : ℍ} (B : DirichletBoundarySegments X o) :
    ∀ v : Fin (Fintype.card (Quotient (intrinsicVertexOrbitSetoid B))),
      (∑ c : Fin B.intrinsicVertexFanTriangleFundamentalDomain.triangleCount × Fin 3
        with intrinsicVertexFanCornerClassIndex B c = v,
        exerciseCornerAngle B.intrinsicVertexFanTriangleFundamentalDomain c) =
          2 * Real.pi := by
  classical
  intro v
  have hregroup :
      (∑ c : Fin B.intrinsicVertexFanTriangleFundamentalDomain.triangleCount × Fin 3
        with intrinsicVertexFanCornerClassIndex B c = v,
        exerciseCornerAngle B.intrinsicVertexFanTriangleFundamentalDomain c) =
      ∑ i : Fin B.intrinsicBoundaryRadialCuts.card with intrinsicVertexClassIndex B i = v,
        ∑ c : Fin B.intrinsicVertexFanTriangleFundamentalDomain.triangleCount × Fin 3
          with intrinsicVertexFanCornerSideIndex B c = i,
          exerciseCornerAngle B.intrinsicVertexFanTriangleFundamentalDomain c := by
    symm
    convert! (Finset.sum_fiberwise_eq_sum_filter
        (Finset.univ : Finset
          (Fin B.intrinsicVertexFanTriangleFundamentalDomain.triangleCount × Fin 3))
        (Finset.univ.filter (fun i => intrinsicVertexClassIndex B i = v))
        (intrinsicVertexFanCornerSideIndex B)
        (exerciseCornerAngle B.intrinsicVertexFanTriangleFundamentalDomain)) using 1
    all_goals simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        intrinsicVertexFanCornerClassIndex]
    congr 1
  rw [hregroup]
  calc
    _ = ∑ i : Fin B.intrinsicBoundaryRadialCuts.card with intrinsicVertexClassIndex B i = v,
        B.intrinsicCyclicInteriorAngle i := by
      apply Finset.sum_congr rfl
      intro i _
      change (∑ c : Fin (B.intrinsicBoundaryRadialCuts.card - 2) × Fin 3
        with B.intrinsicVertexFanCornerVertexIndex c = i,
          B.intrinsicVertexFanCornerAngle c) = B.intrinsicCyclicInteriorAngle i
      simpa only [Fin.ext_iff] using B.sum_intrinsicVertexFanCornerAngle_eq_interiorAngle i
    _ = 2 * Real.pi := native_polygon_vertex_class_angle_sum B v

open Vendored.RiemannDynamics in
/-- P-CHAR: the actual polygon character-rank theorem, transported through
the proved native side and vertex-class bijections. No area or Euler formula
is assumed to identify the rank. -/
noncomputable def exercisePolygonGraphCharacters {g : ℕ} (_hg : 2 ≤ g)
    {X : ClosedHyperbolicSurface g} {o : ℍ} (B : DirichletBoundarySegments X o) :
    AdditiveCharacterSpace X.deckGroup ≃ₗ[ℝ]
      (Fin (intrinsicPairedSideCount B + 1 -
        Fintype.card (Quotient (intrinsicVertexOrbitSetoid B))) → ℝ) := by
  classical
  let R := Classical.choose (X.exists_dirichlet_orbit_density_bound o)
  have hdense : ∀ z : ℍ, Metric.infDist z (MulAction.orbit X.deckGroup o) ≤ R :=
    Classical.choose_spec (X.exists_dirichlet_orbit_density_bound o)
  have hbase := X.basepoint_mem_interior_dirichletDomain o
  have hspace : AdditiveCharacterSpace X.deckGroup = homSubmodule X.deckGroup :=
    Submodule.ext (fun _ => Iff.rfl)
  have hfinite := finiteDimensional_homSubmodule
    (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
    X.deck_fixing_point_acts_trivially hbase hdense
  rw [← hspace] at hfinite
  letI := hfinite
  have hrank := finrank_homSubmodule_add_classCount
    (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
    X.deck_fixing_point_acts_trivially hbase hdense
  have hside : polygonSideCount X.deckGroup o = intrinsicPairedSideCount B := by
    have hforeign := B.polygonSideCount_eq_intrinsicBoundarySideCount_half
    have hnative := intrinsicBoundarySideCount_eq_two_mul_paired B
    omega
  rw [← hspace, hside, intrinsicVertexOrbitCount_eq_polygonVertexClassCount B] at hrank
  apply LinearEquiv.ofFinrankEq
  simp only [Module.finrank_pi, Fintype.card_fin]
  omega

/-- The actual non-tree physical edge alphabet has exactly `2g` letters.
This is a cardinality statement, not an assumed free fundamental-group
presentation: the graph basis and its peripheral word still need proof. -/
theorem intrinsicBoundaryNonTreeEdge_card {g : ℕ} (hg : 2 ≤ g)
    {X : ClosedHyperbolicSurface g} {o : ℍ} (B : DirichletBoundarySegments X o) :
    Fintype.card B.IntrinsicBoundaryNonTreeEdge = 2 * g := by
  classical
  let e : B.IntrinsicBoundaryGraphVertex ≃ Quotient (intrinsicVertexOrbitSetoid B) :=
    Quotient.congrRight (fun i j => B.intrinsicBoundaryGraphVertexSetoid_iff i j)
  have hvertices := Fintype.card_congr e
  have hgraph := B.intrinsicBoundaryNonTreeEdge_card_add_vertices
  rw [hvertices] at hgraph
  change Fintype.card B.IntrinsicBoundaryNonTreeEdge +
      Fintype.card (Quotient (intrinsicVertexOrbitSetoid B)) =
        intrinsicPairedSideCount B + 1 at hgraph
  have hrank : intrinsicPairedSideCount B + 1 -
      Fintype.card (Quotient (intrinsicVertexOrbitSetoid B)) = 2 * g := by
    have h := (exercisePolygonGraphCharacters hg B).finrank_eq
    rw [X.finrank_deckGroupCharacterSpace] at h
    simpa using h.symm
  omega

/-- **Math.** Once the actual tree-spliced polygon transition is proved
transitive, the literal peripheral word has an elementary Nielsen
normalization to the surface relator of this same genus. The genus is forced by the already-proved
`2g`-letter count; it is not chosen as an auxiliary assumption. -/
theorem exists_intrinsicBoundaryPeripheralNielsenProgram {g : ℕ} (hg : 2 ≤ g)
    {X : ClosedHyperbolicSurface g} {o : ℍ} (B : DirichletBoundarySegments X o)
    (horbit : ∀ i j : Fin B.intrinsicBoundaryRadialCuts.card,
      ∃ n : ℕ, B.intrinsicBoundaryTreeSplicedVertexPerm^[n] i = j) :
    ∃ (moves : List (FreeGroupNielsenMove B.IntrinsicBoundaryNonTreeEdge))
      (rename : B.IntrinsicBoundaryNonTreeEdge ≃ SurfaceGenerator g),
      FreeGroup.freeGroupCongr rename
        (FreeGroupNielsenProgram.toEquiv moves
          (FreeGroup.mk B.intrinsicBoundaryPeripheralLetters)) = surfaceRelator g := by
  classical
  let C := B.intrinsicBoundaryWicksCertificate_of_treeSplicedOneOrbit horbit
  obtain ⟨g', moves, rename, hnormalize⟩ :=
    OrientableWicksCertificate.exists_elementary_normalization C
  have hcard : Fintype.card B.IntrinsicBoundaryNonTreeEdge = g' * 2 := by
    calc
      Fintype.card B.IntrinsicBoundaryNonTreeEdge = Fintype.card (SurfaceGenerator g') :=
        Fintype.card_congr rename
      _ = g' * 2 := by
        simp only [SurfaceGenerator, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_bool]
  have hsource := intrinsicBoundaryNonTreeEdge_card hg B
  have hgenus : g' = g := by omega
  subst g'
  exact ⟨moves, rename, hnormalize⟩

/-- **Math.** The actual one-punctured quotient has a marked free presentation of this
same genus. Its unchanged positive polar loop is the standard surface
relator; transitivity and the peripheral normalization are constructed. -/
theorem exists_intrinsicBoundaryPunctureMarkedFreeEquiv {g : ℕ} (hg : 2 ≤ g)
    {X : ClosedHyperbolicSurface g} {o : ℍ} (B : DirichletBoundarySegments X o)
    (r : ℝ) (hr : 0 < r) (hsys : 2 * r < X.systole) :
    ∃ e : FundamentalGroup (X.CenterPuncturedCarrier o)
        (X.dirichletPuncturePolarCircle o r hr hsys
          (B.intrinsicBoundaryAngularVertices 0)) ≃* FreeGroup (SurfaceGenerator g),
      e ⟦X.dirichletPuncturePolarOneTurn o r hr hsys
        (B.intrinsicBoundaryAngularVertices 0)⟧ = surfaceRelator g := by
  classical
  obtain ⟨moves, rename, hnormalize⟩ :=
    exists_intrinsicBoundaryPeripheralNielsenProgram hg B
      B.intrinsicBoundaryTreeSplicedVertexPerm_oneOrbit
  refine ⟨(B.intrinsicBoundaryPunctureFundamentalGroupFreeEquiv r hr hsys).trans
    ((FreeGroupNielsenProgram.toEquiv moves).trans
      (FreeGroup.freeGroupCongr rename)), ?_⟩
  change FreeGroup.freeGroupCongr rename
    (FreeGroupNielsenProgram.toEquiv moves
      (B.intrinsicBoundaryPunctureFundamentalGroupFreeEquiv r hr hsys
        ⟦X.dirichletPuncturePolarOneTurn o r hr hsys
          (B.intrinsicBoundaryAngularVertices 0)⟧)) = _
  rw [B.intrinsicBoundaryPunctureFundamentalGroupFreeEquiv_polarOneTurn r hr hsys]
  exact hnormalize

#print axioms exists_intrinsicBoundaryPunctureMarkedFreeEquiv

/-- **Math.** The genuine puncture marking preserves positive winding at
every original polar basepoint, including the angle-one chain seam points. -/
theorem exists_intrinsicBoundaryPunctureMarkedFreeEquivAtAngle {g : ℕ} (hg : 2 ≤ g)
    {X : ClosedHyperbolicSurface g} {o : ℍ} (B : DirichletBoundarySegments X o)
    (r : ℝ) (hr : 0 < r) (hsys : 2 * r < X.systole) (θ : Circle) :
    ∃ e : FundamentalGroup (X.CenterPuncturedCarrier o)
        (X.dirichletPuncturePolarCircle o r hr hsys θ) ≃* FreeGroup (SurfaceGenerator g),
      e ⟦X.dirichletPuncturePolarOneTurn o r hr hsys θ⟧ = surfaceRelator g := by
  classical
  obtain ⟨moves, rename, hnormalize⟩ :=
    exists_intrinsicBoundaryPeripheralNielsenProgram hg B
      B.intrinsicBoundaryTreeSplicedVertexPerm_oneOrbit
  refine ⟨(B.intrinsicBoundaryPunctureFundamentalGroupFreeEquivAtAngle r hr hsys θ).trans
    ((FreeGroupNielsenProgram.toEquiv moves).trans
      (FreeGroup.freeGroupCongr rename)), ?_⟩
  change FreeGroup.freeGroupCongr rename
    (FreeGroupNielsenProgram.toEquiv moves
      (B.intrinsicBoundaryPunctureFundamentalGroupFreeEquivAtAngle r hr hsys θ
        ⟦X.dirichletPuncturePolarOneTurn o r hr hsys θ⟧)) = _
  rw [B.intrinsicBoundaryPunctureFundamentalGroupFreeEquivAtAngle_polarOneTurn r hr hsys θ]
  exact hnormalize

#print axioms exists_intrinsicBoundaryPunctureMarkedFreeEquivAtAngle

/-- **Math.** Reversing the handle order and exchanging each handle's pair
gives the inverse-relator convention while retaining the original polar loop. -/
theorem exists_intrinsicBoundaryPunctureMarkedFreeEquivAtAngleInverse
    {g : ℕ} (hg : 2 ≤ g) {X : ClosedHyperbolicSurface g} {o : ℍ}
    (B : DirichletBoundarySegments X o)
    (r : ℝ) (hr : 0 < r) (hsys : 2 * r < X.systole) (θ : Circle) :
    ∃ e : FundamentalGroup (X.CenterPuncturedCarrier o)
        (X.dirichletPuncturePolarCircle o r hr hsys θ) ≃* FreeGroup (SurfaceGenerator g),
      e ⟦X.dirichletPuncturePolarOneTurn o r hr hsys θ⟧ = (surfaceRelator g)⁻¹ := by
  obtain ⟨e, he⟩ := exists_intrinsicBoundaryPunctureMarkedFreeEquivAtAngle hg B r hr hsys θ
  refine ⟨e.trans (surfacePeripheralOrientationFreeEquiv g), ?_⟩
  change surfacePeripheralOrientationFreeEquiv g
    (e ⟦X.dirichletPuncturePolarOneTurn o r hr hsys θ⟧) = _
  rw [he, surfacePeripheralOrientationFreeEquiv_relator]

#print axioms exists_intrinsicBoundaryPunctureMarkedFreeEquivAtAngleInverse

/-- **Math.** The actual oriented ellipse exterior has a same-genus marking
whose unchanged positive coordinate boundary is the inverse surface relator.
The comparison is projected through the embedded chart and uses only the
proved one-center marking, not an assumed exterior boundary presentation. -/
theorem exists_embeddedFermiDiskExteriorMarkedFreeEquiv_inverse
    {g : ℕ} (hg : 2 ≤ g) {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U, f z = X.orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (r : ℝ) (hr : 0 < r) (hsysr : 2 * r < X.systole) (θ : Circle) :
    ∃ e : FundamentalGroup (embeddedCoordinatePunctureExterior f)
        (embeddedFermiDiskBoundaryExteriorCircle hball f hf γ m a b hformula θ) ≃*
          FreeGroup (SurfaceGenerator g),
      e ⟦(circleOneTurnLoop θ).map
        (embeddedFermiDiskBoundaryExteriorCircle hball f hf γ m a b hformula).continuous⟧ =
          (surfaceRelator g)⁻¹ := by
  obtain ⟨ρ, hρ, hρr, hq, _⟩ :=
    exists_embeddedFermiDiskBoundaryPolarHomotopy hball f hf γ m a b ha hb
      hformula r hr hsysr
  have hsys : 2 * ρ < X.systole := by linarith
  let o := γ • orientedFermiDiskPoint m a b 0
  let A := fermiSLPolarAngleMap γ (orientedFermiDiskPoint m a b 0)
  obtain ⟨e, he⟩ := exists_intrinsicBoundaryPunctureMarkedFreeEquivAtAngleInverse hg
    (X.dirichletBoundarySegments o) ρ hρ hsys (A θ)
  let H := embeddedFermiDiskBoundaryPolarHomotopy hball f hf γ m a b ha hb
    hformula ρ hρ hsys hq
  let E := embeddedFermiDiskExteriorBoundaryFundamentalGroupEquiv hball f hf γ m a b
    hformula θ
  refine ⟨E.trans ((FundamentalGroup.fundamentalGroupMulEquivOfPath (H.evalAt θ)).trans e), ?_⟩
  change e (FundamentalGroup.fundamentalGroupMulEquivOfPath (H.evalAt θ)
    (E ⟦(circleOneTurnLoop θ).map
      (embeddedFermiDiskBoundaryExteriorCircle hball f hf γ m a b hformula).continuous⟧)) = _
  rw [embeddedFermiDiskExteriorBoundaryFundamentalGroupEquiv_oneTurn,
    embeddedFermiDiskBoundaryPolarHomotopy_fundamentalGroup]
  exact he

#print axioms exists_embeddedFermiDiskExteriorMarkedFreeEquiv_inverse

/-- **Math.** The actual oriented two-puncture chart has a marked ambient
free presentation preserving its literal local-factor inclusion. The needed
exterior boundary equation is constructed from the one-center theorem on
this same chart; it is not an additional hypothesis. Either actual puncture
may be retained, without assuming an ordering of the original centers. -/
theorem exists_embeddedFermiTwoPunctureAmbientMarkedFreeEquiv
    {g : ℕ} (hg : 2 ≤ g) {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (γ : SL(2, ℝ)) (m c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hformula : ∀ z : U, f z = X.orbitProjection (γ • orientedFermiDiskPoint m c d z.1))
    (r₀ : ℝ) (hr₀ : 0 < r₀) (hsys : 2 * r₀ < X.systole)
    (p q : U) (a r : ℝ) (ha : max ‖p.1‖ ‖q.1‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpq : p ≠ q) (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (retainLower : Bool) :
    let θR := embeddedTwoPunctureMarkedAnnulusDirection p q a r ha ha1 hr1 hpq hpre hqre
    let zR := embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r
      ha ha1 hr1 haU hrU θR
    let exterior := embeddedTwoPunctureExteriorRelativeSide f p q a haU
    let localDisk := embeddedTwoPunctureLocalDiskRelativeSide f p q r
    let localMark := embeddedTwoPunctureRelativeLocalDiskFreeEquiv f hf p q r
      (zero_lt_one.trans hr1) hrU
      (((le_max_left _ _).trans_lt ha).trans (ha1.trans hr1))
      (((le_max_right _ _).trans_lt ha).trans (ha1.trans hr1))
      hpq hpre hqre (twoOpenCoverAmalgamOverlapRight exterior localDisk zR)
      (embeddedTwoPunctureRelativeBoundaryCircle_right_mem_localOverlap
        f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre)
    let cyclic := if retainLower then surfaceTwoBoundaryCyclicAmalgamEquiv (surfaceRelator g)
      else surfaceTwoBoundaryCyclicUpperAmalgamEquiv (surfaceRelator g)
    ∃ e : FundamentalGroup (embeddedTwoPunctureAmbientPoint f p q) zR.1 ≃*
        FreeGroup (SurfaceGenerator g ⊕ Unit),
      ∀ ξ : twoOpenCoverAmalgamSideGroup exterior localDisk zR false,
        e (twoOpenCoverSideToAmbient exterior localDisk zR false ξ) =
          cyclic (Monoid.PushoutI.of false (localMark ξ)) := by
  let θR := embeddedTwoPunctureMarkedAnnulusDirection p q a r ha ha1 hr1 hpq hpre hqre
  have ha0 : 0 ≤ a :=
    (norm_nonneg p.1).trans ((le_max_left _ _).trans_lt ha).le
  have hmark := exists_embeddedFermiDiskExteriorMarkedFreeEquiv_inverse
    hg hball f hf γ m c d hc hd hformula r₀ hr₀ hsys θR
  rw [embeddedFermiDiskBoundaryExteriorCircle_eq] at hmark
  obtain ⟨e₀, he₀⟩ := hmark
  let E := embeddedSurfaceClosedDiskExteriorBoundaryInclusionFundamentalGroupEquiv
    hball f hf a ha0 ha1 θR
  let eE := E.symm.trans e₀
  have heE : eE ⟦(circleOneTurnLoop θR).map
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1).continuous⟧ =
        (surfaceRelator g)⁻¹ := by
    change e₀ (E.symm _) = _
    rw [← embeddedSurfaceClosedDiskExteriorBoundaryInclusionFundamentalGroupEquiv_oneTurn
      hball f hf a ha0 ha1 θR]
    change e₀ (E.symm (E _)) = _
    exact (congrArg e₀ (E.symm_apply_apply _)).trans he₀
  cases retainLower
  · refine ⟨embeddedTwoPunctureAmbientMarkedUpperFreeEquiv
      hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE
      (surfaceRelator g) heE, ?_⟩
    intro ξ
    exact embeddedTwoPunctureAmbientMarkedUpperFreeEquiv_factor
      hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE
      (surfaceRelator g) heE false ξ
  · refine ⟨embeddedTwoPunctureAmbientMarkedFreeEquiv
      hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE
      (surfaceRelator g) heE, ?_⟩
    intro ξ
    exact embeddedTwoPunctureAmbientMarkedFreeEquiv_factor
      hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE
      (surfaceRelator g) heE false ξ

#print axioms exists_embeddedFermiTwoPunctureAmbientMarkedFreeEquiv

section NativeAnnulusPeripheralMarking

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}
  (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) {U : Set ℂ}
  (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
  (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
  (p q : U)
  (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
  (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
  (hpre : p.1.re = 0) (hqre : q.1.re = 0)
  (hp : ‖p.1‖ < 1) (hq : ‖q.1‖ < 1) (hpq : p ≠ q)
  (hi : 0 < i.1) (hnext : i.1 + 1 < n)
  (γ : SL(2, ℝ)) (m A B : ℝ) (hA : 0 < A) (hB : 0 < B)
  (hformula : ∀ z : U,
    f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m A B z.1))
  (hleft : γ • orientedFermiDiskPoint m A B p.1 = (P.centers i).1)
  (hright : γ • orientedFermiDiskPoint m A B q.1 =
    P.componentCenterClosestDeck i • (P.centers i).2)
  (a r : ℝ) (ha : max ‖p.1‖ ‖q.1‖ < a) (ha1 : a < 1) (hr1 : 1 < r)
  (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
  (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
  (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
  (hsmall : ∀ (b : Bool) (θ : Circle),
    (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈ embeddedCoordinatePunctureDisk f)
  (d : ExerciseGluingPreparation.TwoCenterPolarSideComparisonData p q m A B ρ hA hB)

local notation "annulusθ" => embeddedTwoPunctureMarkedAnnulusDirection
  p q a r ha ha1 hr1 hpq hpre hqre
local notation "annulusZ" => embeddedTwoPunctureRelativeBoundaryCircle
  f hf p q a r ha ha1 hr1 haU hrU annulusθ
local notation "annulusExterior" => embeddedTwoPunctureExteriorRelativeSide f p q a haU
local notation "annulusLocal" => embeddedTwoPunctureLocalDiskRelativeSide f p q r
local notation "annulusQ" => twoOpenCoverAmalgamOverlapRight
  annulusExterior annulusLocal annulusZ
local notation "annulusCoord" => embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
  f hf p q r (zero_lt_one.trans hr1) hrU hpre hqre
local notation "annulusLower" => twoPuncturedDiskLowerSide
  (embeddedTwoPunctureLowerParameter p q r) (embeddedTwoPunctureUpperParameter p q r)
local notation "annulusUpper" => twoPuncturedDiskUpperSide
  (embeddedTwoPunctureLowerParameter p q r) (embeddedTwoPunctureUpperParameter p q r)
local notation "annulusL" => P.twoCenterSmallPolarRelativeLocalDiskMap
  i f p q r hr1 hpMap hqMap true ρ hρ hρr hsmall
local notation "annulusR" => P.twoCenterSmallPolarRelativeLocalDiskMap
  i f p q r hr1 hpMap hqMap false ρ hρ hρr hsmall

include hball hp hq hi hnext hformula hleft hright d

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Mark both literal native small polar loops at the actual
annulus basepoint. All side-generator and exterior-boundary equations are
proved from the original chart; neither peripheral word is an input premise. -/
theorem ExerciseGluingPreparation.exists_componentTwoCenterAnnulusPolarMarkedFreeEquiv
    (leftPath : Path (annulusL 1) annulusQ)
    (rightPath : Path (annulusR 1) annulusQ)
    (hleftSide : ∀ t : unitInterval, (annulusCoord (leftPath t) : ℂ) ∈
      if p.1.im < q.1.im then annulusLower else annulusUpper)
    (hrightSide : ∀ t : unitInterval, (annulusCoord (rightPath t) : ℂ) ∈
      if p.1.im < q.1.im then annulusUpper else annulusLower) :
    ∃ e : FundamentalGroup (embeddedTwoPunctureAmbientPoint f p q) annulusZ.1 ≃*
        FreeGroup (SurfaceGenerator (genera i) ⊕ Unit),
      e (twoOpenCoverSideToAmbient annulusExterior annulusLocal annulusZ false
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (leftPath.symm.trans (((circleOneTurnLoop 1).map (annulusL).continuous).trans
            leftPath))))) = FreeGroup.of (Sum.inr ()) ∧
      e (twoOpenCoverSideToAmbient annulusExterior annulusLocal annulusZ false
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (rightPath.symm.trans (((circleOneTurnLoop 1).map (annulusR).continuous).trans
            rightPath))))) =
        (FreeGroup.of (Sum.inr ()) * FreeGroup.map Sum.inl (surfaceRelator (genera i)))⁻¹ := by
  have hsys : 2 * gluingRadius C g < (X i).systole := by
    linarith [P.twice_outer_lt_systole i, P.radius_lt_embeddedRadius]
  have hqOverlap : annulusCoord annulusQ ∈ twoPuncturedDiskRelativeOverlap
      (embeddedTwoPunctureLowerParameter p q r)
      (embeddedTwoPunctureUpperParameter p q r) :=
    embeddedTwoPunctureRelativeBoundaryCircle_right_mem_localOverlap
      f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre
  have himne : p.1.im ≠ q.1.im := by
    intro heq
    apply hpq
    apply Subtype.ext
    apply Complex.ext
    · exact hpre.trans hqre.symm
    · exact heq
  rcases lt_or_gt_of_ne himne with horder | horder
  · have hL := P.componentTwoCenterNativeLeftPolarLoop_localFreeGenerator
      i f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext γ m A B hA hB
      hformula hleft r hr1 hrU ρ hρ hρr hsmall d horder annulusQ hqOverlap
      leftPath (by simpa only [if_pos horder] using hleftSide)
    have hR := P.componentTwoCenterNativeRightPolarLoop_localFreeGenerator
      i f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext γ m A B hA hB
      hformula hright r hr1 hrU ρ hρ hρr hsmall d horder annulusQ hqOverlap
      rightPath (by simpa only [if_pos horder] using hrightSide)
    simp only [Path.symm_symm] at hL hR
    obtain ⟨e, he⟩ := exists_embeddedFermiTwoPunctureAmbientMarkedFreeEquiv
      (P.component_genus i) hball f hf γ m A B hA hB hformula
      (gluingRadius C g) P.radius_pos hsys p q a r ha ha1 hr1 haU hrU hpq hpre hqre true
    refine ⟨e, ?_, ?_⟩
    · exact (he _).trans <|
        (congrArg (fun w : FreeGroup Bool =>
          surfaceTwoBoundaryCyclicAmalgamEquiv (surfaceRelator (genera i))
            ((Monoid.PushoutI.of false) w)) hL).trans
          (surfaceTwoBoundaryCyclicAmalgamEquiv_lower (surfaceRelator (genera i)))
    · exact (he _).trans <|
        (congrArg (fun w : FreeGroup Bool =>
          surfaceTwoBoundaryCyclicAmalgamEquiv (surfaceRelator (genera i))
            ((Monoid.PushoutI.of false) w)) hR).trans
          (surfaceTwoBoundaryCyclicAmalgamEquiv_upper (surfaceRelator (genera i)))
  · have hnorder : ¬p.1.im < q.1.im := not_lt.mpr horder.le
    have hL := P.componentTwoCenterNativeLeftPolarLoop_localFreeGenerator_upper
      i f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext γ m A B hA hB
      hformula hleft r hr1 hrU ρ hρ hρr hsmall d horder annulusQ hqOverlap
      leftPath (by simpa only [if_neg hnorder] using hleftSide)
    have hR := P.componentTwoCenterNativeRightPolarLoop_localFreeGenerator_lower
      i f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext γ m A B hA hB
      hformula hright r hr1 hrU ρ hρ hρr hsmall d horder annulusQ hqOverlap
      rightPath (by simpa only [if_neg hnorder] using hrightSide)
    simp only [Path.symm_symm] at hL hR
    obtain ⟨e, he⟩ := exists_embeddedFermiTwoPunctureAmbientMarkedFreeEquiv
      (P.component_genus i) hball f hf γ m A B hA hB hformula
      (gluingRadius C g) P.radius_pos hsys p q a r ha ha1 hr1 haU hrU hpq hpre hqre false
    refine ⟨e, ?_, ?_⟩
    · exact (he _).trans <|
        (congrArg (fun w : FreeGroup Bool =>
          surfaceTwoBoundaryCyclicUpperAmalgamEquiv (surfaceRelator (genera i))
            ((Monoid.PushoutI.of false) w)) hL).trans
          (surfaceTwoBoundaryCyclicUpperAmalgamEquiv_upper (surfaceRelator (genera i)))
    · exact (he _).trans <|
        (congrArg (fun w : FreeGroup Bool =>
          surfaceTwoBoundaryCyclicUpperAmalgamEquiv (surfaceRelator (genera i))
            ((Monoid.PushoutI.of false) w)) hR).trans
          (surfaceTwoBoundaryCyclicUpperAmalgamEquiv_lower (surfaceRelator (genera i)))

end NativeAnnulusPeripheralMarking

#print axioms ExerciseGluingPreparation.exists_componentTwoCenterAnnulusPolarMarkedFreeEquiv

/-- **Math.** Construct the actual two-center disk, its original puncture
coordinates and the boundary-compatible same-genus marking of its exterior.
All chart and cutoff inputs are supplied by the original gluing preparation. -/
theorem ExerciseGluingPreparation.exists_componentTwoCenterDiskExteriorMarkedFreePresentation
    {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
    {X : ∀ i, ClosedHyperbolicSurface (genera i)}
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ (U : Set ℂ) (_hU : IsOpen U) (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
      (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier)),
      ∃ p q : U, ‖p.1‖ < 1 ∧ ‖q.1‖ < 1 ∧
        f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∧
        f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∧
        p.1.re = 0 ∧ q.1.re = 0 ∧ p ≠ q ∧
        ∀ θ : Circle, ∃ e : FundamentalGroup (embeddedCoordinatePunctureExterior f)
            (embeddedSurfaceDiskBoundaryCircle hball f hf θ) ≃*
              FreeGroup (SurfaceGenerator (genera i)),
          e ⟦(circleOneTurnLoop θ).map
            (embeddedSurfaceDiskBoundaryCircle hball f hf).continuous⟧ =
              (surfaceRelator (genera i))⁻¹ := by
  obtain ⟨U, hU, hball, F, hF, _hL, _hR, e, he, _hm, hcoeff, hpoints⟩ :=
    P.exists_componentTwoCenterEmbeddedDiskChart_axisPunctures i
  obtain ⟨a, b, ha, hb, hcoord⟩ := hcoeff
  obtain ⟨p, q, hp, hq, hpF, hqF, hpre, hqre, hpq⟩ := hpoints
  let f : C(U, (X i).Carrier) := ⟨F, hF.continuous⟩
  let γ := (P.componentTwoCenterGeodesicVerticalizer i)⁻¹
  let m := (Real.log (P.componentTwoCenterGeodesicVerticalizer i • (P.centers i).1).im +
    Real.log (P.componentTwoCenterGeodesicVerticalizer i •
      (P.componentCenterClosestDeck i • (P.centers i).2)).im) / 2
  have hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1) := by
    intro z
    change F z = _
    rw [he, hcoord, P.componentTwoCenterGeodesicCoordinateHomeomorph_apply]
    rfl
  have hsys : 2 * gluingRadius C g < (X i).systole := by
    linarith [P.twice_outer_lt_systole i, P.radius_lt_embeddedRadius]
  refine ⟨U, hU, hball, f, hF, p, q, hp, hq, hpF, hqF, hpre, hqre, hpq, ?_⟩
  intro θ
  have hmark := exists_embeddedFermiDiskExteriorMarkedFreeEquiv_inverse
    (P.component_genus i) hball f hF γ m a b ha hb hformula
      (gluingRadius C g) P.radius_pos hsys θ
  rw [embeddedFermiDiskBoundaryExteriorCircle_eq] at hmark
  exact hmark

#print axioms ExerciseGluingPreparation.exists_componentTwoCenterDiskExteriorMarkedFreePresentation

/-- **Math.** The original preparation constructs a disk chart whose every
smaller open exterior has the required boundary-compatible same-genus marking.
Thus the radius selected by the actual annular open cover needs no new
marking assumption and preserves the literal positive unit boundary. -/
theorem ExerciseGluingPreparation.exists_componentTwoCenterOpenDiskExteriorMarkedFreePresentation
    {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
    {X : ∀ i, ClosedHyperbolicSurface (genera i)}
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ (U : Set ℂ) (_hU : IsOpen U) (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
      (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier)),
      ∃ p q : U, ‖p.1‖ < 1 ∧ ‖q.1‖ < 1 ∧
        f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∧
        f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∧
        p.1.re = 0 ∧ q.1.re = 0 ∧ p ≠ q ∧
        ∀ (s : ℝ) (_hs : 0 ≤ s) (hs1 : s < 1) (θ : Circle),
          ∃ e : FundamentalGroup (embeddedCoordinateClosedDiskExterior f s)
              (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf s hs1 θ) ≃*
                FreeGroup (SurfaceGenerator (genera i)),
            e ⟦(circleOneTurnLoop θ).map
              (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf s hs1).continuous⟧ =
                (surfaceRelator (genera i))⁻¹ := by
  obtain ⟨U, hU, hball, f, hf, p, q, hp, hq, hpF, hqF, hpre, hqre, hpq, hmark⟩ :=
    P.exists_componentTwoCenterDiskExteriorMarkedFreePresentation i
  refine ⟨U, hU, hball, f, hf, p, q, hp, hq, hpF, hqF, hpre, hqre, hpq, ?_⟩
  intro s hs hs1 θ
  obtain ⟨e, he⟩ := hmark θ
  let E := embeddedSurfaceClosedDiskExteriorBoundaryInclusionFundamentalGroupEquiv
    hball f hf s hs hs1 θ
  refine ⟨E.symm.trans e, ?_⟩
  change e (E.symm _) = _
  rw [← embeddedSurfaceClosedDiskExteriorBoundaryInclusionFundamentalGroupEquiv_oneTurn
    hball f hf s hs hs1 θ]
  change e (E.symm (E _)) = _
  exact (congrArg e (E.symm_apply_apply _)).trans he

#print axioms ExerciseGluingPreparation.exists_componentTwoCenterOpenDiskExteriorMarkedFreePresentation

/-- **Math.** One actual chart simultaneously supplies both original
puncture coordinates, their exact chosen lifted-center equations, every
smaller-exterior boundary marking, and small polar circles with a disk-
contained connector homotopic to the prescribed cut connector. All
containment and marking witnesses are constructed from the original
preparation, on the same chart. -/
theorem ExerciseGluingPreparation.exists_componentTwoCenterMarkedDiskPolarConnector_axisSegment
    {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
    {X : ∀ i, ClosedHyperbolicSurface (genera i)}
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ (U : Set ℂ) (_hU : IsOpen U) (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
      (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier)),
      ∃ (γ : SL(2, ℝ)) (m a b : ℝ), 0 < a ∧ 0 < b ∧
        (∀ z : U, f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1)) ∧
      ∃ p q : U, ‖p.1‖ < 1 ∧ ‖q.1‖ < 1 ∧
        f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∧
        f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∧
        p.1.re = 0 ∧ q.1.re = 0 ∧ p ≠ q ∧
        γ • orientedFermiDiskPoint m a b p.1 = (P.centers i).1 ∧
        γ • orientedFermiDiskPoint m a b q.1 =
          P.componentCenterClosestDeck i • (P.centers i).2 ∧
        (∀ t : unitInterval,
          P.componentCenterGeodPoint i t ∈ embeddedCoordinatePunctureDisk f) ∧
        (∀ t : unitInterval, ∃ z : U,
          z.1 = (((1 - (t : ℝ)) * p.1.im + (t : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I ∧
          ‖z.1‖ < 1 ∧ f z = P.componentCenterGeodPoint i t) ∧
        (∀ (s : ℝ) (_hs : 0 ≤ s) (hs1 : s < 1) (θ : Circle),
          ∃ e : FundamentalGroup (embeddedCoordinateClosedDiskExterior f s)
              (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf s hs1 θ) ≃*
                FreeGroup (SurfaceGenerator (genera i)),
            e ⟦(circleOneTurnLoop θ).map
              (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf s hs1).continuous⟧ =
                (surfaceRelator (genera i))⁻¹) ∧
        ∃ (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g),
          (∀ (b : Bool) (θ : Circle),
            (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
              embeddedCoordinatePunctureDisk f) ∧
          (∀ t : unitInterval,
            (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr t).val ∈
            embeddedCoordinatePunctureDisk f) ∧
          (P.componentTwoCenterSmallPolarCutBasedPath i ρ hρ hρr).Homotopic
            (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr) := by
  obtain ⟨U, hU, hball, F, hF, hL, hR, hsegment, e, he, _hm, hcoeff, hpoints⟩ :=
    P.exists_componentTwoCenterEmbeddedDiskChart_axisPunctures_centerSegment_liftedCenters i
  obtain ⟨a, b, ha, hb, hcoord⟩ := hcoeff
  obtain ⟨p, q, hp, hq, hpF, hqF, hpre, hqre, hpq, heL, heR⟩ := hpoints
  let f : C(U, (X i).Carrier) := ⟨F, hF.continuous⟩
  let γ := (P.componentTwoCenterGeodesicVerticalizer i)⁻¹
  let m := (Real.log (P.componentTwoCenterGeodesicVerticalizer i • (P.centers i).1).im +
    Real.log (P.componentTwoCenterGeodesicVerticalizer i •
      (P.componentCenterClosestDeck i • (P.centers i).2)).im) / 2
  have heFermi : ∀ z : ℂ, e z = γ • orientedFermiDiskPoint m a b z := by
    intro z
    rw [hcoord z, P.componentTwoCenterGeodesicCoordinateHomeomorph_apply]
    rfl
  have hFermiL : γ • orientedFermiDiskPoint m a b p.1 = (P.centers i).1 :=
    (heFermi p.1).symm.trans heL
  have hFermiR : γ • orientedFermiDiskPoint m a b q.1 =
      P.componentCenterClosestDeck i • (P.centers i).2 :=
    (heFermi q.1).symm.trans heR
  have hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1) := by
    intro z
    change F z = _
    rw [he, hcoord, P.componentTwoCenterGeodesicCoordinateHomeomorph_apply]
    rfl
  have hsys : 2 * gluingRadius C g < (X i).systole := by
    linarith [P.twice_outer_lt_systole i, P.radius_lt_embeddedRadius]
  have haxis : ∀ t : unitInterval, ∃ z : U,
      z.1 = (((1 - (t : ℝ)) * p.1.im + (t : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I ∧
      ‖z.1‖ < 1 ∧ f z = P.componentCenterGeodPoint i t := by
    intro t
    exact P.componentTwoCenterAxisChart_affineSegment i hball f e he m a b ha hcoord
      p q hpre hqre hp hq heL heR t
  refine ⟨U, hU, hball, f, hF, γ, m, a, b, ha, hb, hformula,
    p, q, hp, hq, hpF, hqF, hpre, hqre, hpq, hFermiL, hFermiR,
    hsegment, haxis, ?_, ?_⟩
  · intro s hs hs1 θ
    have hmark := exists_embeddedFermiDiskExteriorMarkedFreeEquiv_inverse
      (P.component_genus i) hball f hF γ m a b ha hb hformula
        (gluingRadius C g) P.radius_pos hsys θ
    rw [embeddedFermiDiskBoundaryExteriorCircle_eq] at hmark
    obtain ⟨e, he⟩ := hmark
    let E := embeddedSurfaceClosedDiskExteriorBoundaryInclusionFundamentalGroupEquiv
      hball f hF s hs hs1 θ
    refine ⟨E.symm.trans e, ?_⟩
    change e (E.symm _) = _
    rw [← embeddedSurfaceClosedDiskExteriorBoundaryInclusionFundamentalGroupEquiv_oneTurn
      hball f hF s hs hs1 θ]
    change e (E.symm (E _)) = _
    exact (congrArg e (E.symm_apply_apply _)).trans he
  · exact P.exists_componentTwoCenterSmallChartPolarCirclesAndConnector
      i hU hball f hF hL hR hsegment

/-- **Math.** Compatibility with callers that only require the exact lifted centers.
The stronger producer additionally constructs the literal affine axis segment
needed by the native connector-half containment lemmas. -/
theorem ExerciseGluingPreparation.exists_componentTwoCenterMarkedDiskPolarConnector_liftedCenters
    {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
    {X : ∀ i, ClosedHyperbolicSurface (genera i)}
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ (U : Set ℂ) (_hU : IsOpen U) (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
      (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier)),
      ∃ (γ : SL(2, ℝ)) (m a b : ℝ), 0 < a ∧ 0 < b ∧
        (∀ z : U, f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1)) ∧
      ∃ p q : U, ‖p.1‖ < 1 ∧ ‖q.1‖ < 1 ∧
        f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∧
        f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∧
        p.1.re = 0 ∧ q.1.re = 0 ∧ p ≠ q ∧
        γ • orientedFermiDiskPoint m a b p.1 = (P.centers i).1 ∧
        γ • orientedFermiDiskPoint m a b q.1 =
          P.componentCenterClosestDeck i • (P.centers i).2 ∧
        (∀ t : unitInterval,
          P.componentCenterGeodPoint i t ∈ embeddedCoordinatePunctureDisk f) ∧
        (∀ (s : ℝ) (_hs : 0 ≤ s) (hs1 : s < 1) (θ : Circle),
          ∃ e : FundamentalGroup (embeddedCoordinateClosedDiskExterior f s)
              (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf s hs1 θ) ≃*
                FreeGroup (SurfaceGenerator (genera i)),
            e ⟦(circleOneTurnLoop θ).map
              (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf s hs1).continuous⟧ =
                (surfaceRelator (genera i))⁻¹) ∧
        ∃ (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g),
          (∀ (b : Bool) (θ : Circle),
            (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
              embeddedCoordinatePunctureDisk f) ∧
          (∀ t : unitInterval,
            (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr t).val ∈
            embeddedCoordinatePunctureDisk f) ∧
          (P.componentTwoCenterSmallPolarCutBasedPath i ρ hρ hρr).Homotopic
            (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr) := by
  obtain ⟨U, hU, hball, f, hf, γ, m, a, b, ha, hb, hformula,
    p, q, hp, hq, hpMap, hqMap, hpre, hqre, hpq, hleft, hright,
    hsegment, _haxis, hmark, hsmall⟩ :=
    P.exists_componentTwoCenterMarkedDiskPolarConnector_axisSegment i
  exact ⟨U, hU, hball, f, hf, γ, m, a, b, ha, hb, hformula,
    p, q, hp, hq, hpMap, hqMap, hpre, hqre, hpq, hleft, hright,
    hsegment, hmark, hsmall⟩

/-- **Math.** Compatibility contract for callers that do not need the exact
lifted-center equations returned by the stronger same-chart producer. -/
theorem ExerciseGluingPreparation.exists_componentTwoCenterMarkedDiskPolarConnector
    {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
    {X : ∀ i, ClosedHyperbolicSurface (genera i)}
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ (U : Set ℂ) (_hU : IsOpen U) (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
      (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier)),
      ∃ (γ : SL(2, ℝ)) (m a b : ℝ), 0 < a ∧ 0 < b ∧
        (∀ z : U, f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1)) ∧
      ∃ p q : U, ‖p.1‖ < 1 ∧ ‖q.1‖ < 1 ∧
        f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∧
        f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∧
        p.1.re = 0 ∧ q.1.re = 0 ∧ p ≠ q ∧
        (∀ t : unitInterval,
          P.componentCenterGeodPoint i t ∈ embeddedCoordinatePunctureDisk f) ∧
        (∀ (s : ℝ) (_hs : 0 ≤ s) (hs1 : s < 1) (θ : Circle),
          ∃ e : FundamentalGroup (embeddedCoordinateClosedDiskExterior f s)
              (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf s hs1 θ) ≃*
                FreeGroup (SurfaceGenerator (genera i)),
            e ⟦(circleOneTurnLoop θ).map
              (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf s hs1).continuous⟧ =
                (surfaceRelator (genera i))⁻¹) ∧
        ∃ (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g),
          (∀ (b : Bool) (θ : Circle),
            (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
              embeddedCoordinatePunctureDisk f) ∧
          (∀ t : unitInterval,
            (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr t).val ∈
            embeddedCoordinatePunctureDisk f) ∧
          (P.componentTwoCenterSmallPolarCutBasedPath i ρ hρ hρr).Homotopic
            (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr) := by
  obtain ⟨U, hU, hball, f, hf, γ, m, a, b, ha, hb, hformula,
      p, q, hp, hq, hpF, hqF, hpre, hqre, hpq, _hFermiL, _hFermiR,
      hsegment, hmarking, ρ, hρ, hρr, hcircles, hcandidates, hpath⟩ :=
    P.exists_componentTwoCenterMarkedDiskPolarConnector_liftedCenters i
  exact ⟨U, hU, hball, f, hf, γ, m, a, b, ha, hb, hformula,
    p, q, hp, hq, hpF, hqF, hpre, hqre, hpq, hsegment, hmarking,
    ρ, hρ, hρr, hcircles, hcandidates, hpath⟩

#print axioms ExerciseGluingPreparation.exists_componentTwoCenterMarkedDiskPolarConnector_liftedCenters
#print axioms ExerciseGluingPreparation.exists_componentTwoCenterMarkedDiskPolarConnector_axisSegment
#print axioms ExerciseGluingPreparation.exists_componentTwoCenterMarkedDiskPolarConnector

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Construct the actual internal-component free marking at the
original left angle-one point, preserving both physical peripheral loops.
The chart, radius, side paths and annulus marking are constructed internally. -/
theorem ExerciseGluingPreparation.exists_internalComponentPolarMarkedFreeEquiv
    {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
    {X : ∀ i, ClosedHyperbolicSurface (genera i)}
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n) :
    ∃ e : FundamentalGroup (P.CenterPuncturedChainComponent i)
        (P.componentLeftPolarBoundaryMap i 1) ≃*
          FreeGroup (SurfaceGenerator (genera i) ⊕ Unit),
      e ⟦P.componentLeftPolarBoundaryLoop i⟧ = FreeGroup.of (Sum.inr ()) ∧
      e ⟦P.componentRightPolarBoundaryLoopAlongCut i⟧ =
        (FreeGroup.of (Sum.inr ()) * FreeGroup.map Sum.inl (surfaceRelator (genera i)))⁻¹ := by
  obtain ⟨U, hU, hball, f, hf, γ, m, A, B, hA, hB, hformula,
      p, q, hp, hq, hpMap, hqMap, hpre, hqre, hpq, hleft, hright,
      hsegment, haxis, _hExterior, _hOldSmall⟩ :=
    P.exists_componentTwoCenterMarkedDiskPolarConnector_axisSegment i
  obtain ⟨a, r, haU, hrU, ha, ha1, hr1, _hCover⟩ :=
    exists_embeddedTwoPunctureDiskOpenCover hU hball f hf p q hpq hp hq
  have hpaths := P.exists_componentTwoCenterAnnulusBasedNativeSidePaths
    i hU f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext
    γ m A B hA hB hformula hleft hright hsegment a ha ha1 haU r hr1 hrU haxis
  obtain ⟨ρ, hρ, hρr, hsmall, _hCandidate, ⟨d⟩, mid, _hMid, _hOverlap,
    leftHalf, rightHalf, _hLeftNative, _hRightNative, hcases⟩ := hpaths
  let θ := embeddedTwoPunctureMarkedAnnulusDirection p q a r ha ha1 hr1 hpq hpre hqre
  let zR := embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r
    ha ha1 hr1 haU hrU θ
  let exterior := embeddedTwoPunctureExteriorRelativeSide f p q a haU
  let localDisk := embeddedTwoPunctureLocalDiskRelativeSide f p q r
  let qR := twoOpenCoverAmalgamOverlapRight exterior localDisk zR
  let coord := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
    f hf p q r (zero_lt_one.trans hr1) hrU hpre hqre
  rcases hcases with hcase | hcase
  all_goals
    rcases hcase with ⟨horder, _hLeftHalf, _hRightHalf,
      η, _hEtaLower, _hEtaUpper, hLeftSide, hRightSide, hL, hR, hjoined⟩
    let leftPath := leftHalf.trans η
    let rightPath := rightHalf.symm.trans η
    have hleftSide : ∀ t : unitInterval, (coord (leftPath t) : ℂ) ∈
        if p.1.im < q.1.im then
          twoPuncturedDiskLowerSide (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r)
        else twoPuncturedDiskUpperSide (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r) := by
      first
      | simpa only [if_pos horder] using hLeftSide
      | simpa only [if_neg (not_lt.mpr horder.le)] using hLeftSide
    have hrightSide : ∀ t : unitInterval, (coord (rightPath t) : ℂ) ∈
        if p.1.im < q.1.im then
          twoPuncturedDiskUpperSide (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r)
        else twoPuncturedDiskLowerSide (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r) := by
      first
      | simpa only [if_pos horder] using hRightSide
      | simpa only [if_neg (not_lt.mpr horder.le)] using hRightSide
    obtain ⟨eAmbient, heLeft, heRight⟩ :=
      P.exists_componentTwoCenterAnnulusPolarMarkedFreeEquiv
        i hball f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext
        γ m A B hA hB hformula hleft hright a r ha ha1 hr1 haU hrU
        ρ hρ hρr hsmall d leftPath rightPath hleftSide hrightSide
    have hcut := hjoined.trans
      (P.componentTwoCenterSmallPolarCutBasedPath_homotopic_candidate i ρ hρ hρr).symm
    obtain ⟨eSmall, heSmallLeft, heSmallRight⟩ :=
      P.exists_componentTwoCenterSmallPolarMarkedFreeEquiv_of_localMarkedLoops
        i f p q hi hnext hpMap hqMap r hr1 ρ hρ hρr hsmall
        qR leftPath rightPath hL hR hcut eAmbient
        (FreeGroup.of (Sum.inr ()))
        ((FreeGroup.of (Sum.inr ()) * FreeGroup.map Sum.inl (surfaceRelator (genera i)))⁻¹)
        heLeft heRight
    exact P.componentSmallPolarMarkedFreeEquiv_transport
      i ρ hρ hρr eSmall
      (FreeGroup.of (Sum.inr ()))
      ((FreeGroup.of (Sum.inr ()) * FreeGroup.map Sum.inl (surfaceRelator (genera i)))⁻¹)
      heSmallLeft heSmallRight

#print axioms ExerciseGluingPreparation.exists_internalComponentPolarMarkedFreeEquiv

/-- **Math.** The actual retained internal component has the same physical
incoming and outgoing peripheral values at its original incoming point. -/
theorem ExerciseGluingPreparation.exists_internalRetainedPolarMarkedFreeEquiv
    {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
    {X : ∀ i, ClosedHyperbolicSurface (genera i)}
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n) :
    ∃ e : FundamentalGroup (P.ChainComponent i)
        (P.componentRetainedLeftPolarBoundaryMap i 1) ≃*
          FreeGroup (SurfaceGenerator (genera i) ⊕ Unit),
      e ⟦P.componentRetainedLeftPolarBoundaryLoop i⟧ = FreeGroup.of (Sum.inr ()) ∧
      e ⟦P.componentRetainedRightPolarBoundaryLoopAlongCut i⟧ =
        (FreeGroup.of (Sum.inr ()) * FreeGroup.map Sum.inl (surfaceRelator (genera i)))⁻¹ := by
  obtain ⟨eOriginal, hL, hR⟩ := P.exists_internalComponentPolarMarkedFreeEquiv i hi hnext
  refine ⟨P.componentRetainedPolarMarkedFreeEquiv_of_punctureMarking i eOriginal, ?_⟩
  exact P.componentRetainedPolarMarkedFreeEquiv_of_punctureMarking_values
    i eOriginal _ _ hL hR

#print axioms ExerciseGluingPreparation.exists_internalRetainedPolarMarkedFreeEquiv


/-- **Math.** The actual retained first component has its same-genus marking
at the original outgoing polar basepoint. The positive outgoing generator
is the inverse relator, as required by the ordered endpoint relation. -/
theorem exists_firstEndpointRetainedMarkedFreeEquiv_inverse
    {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
    {X : ∀ i, ClosedHyperbolicSurface (genera i)}
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (B : DirichletBoundarySegments (X ⟨0, by omega⟩)
      (P.centers ⟨0, by omega⟩).2) :
    ∃ e : FundamentalGroup (P.ChainComponent ⟨0, by omega⟩)
        (P.componentRetainedRightPolarBoundaryMap ⟨0, by omega⟩ 1) ≃*
          FreeGroup (SurfaceGenerator (genera ⟨0, by omega⟩)),
      e ⟦P.componentRetainedRightPolarBoundaryLoop ⟨0, by omega⟩⟧ =
        (surfaceRelator (genera ⟨0, by omega⟩))⁻¹ := by
  classical
  let i : Fin n := ⟨0, by omega⟩
  obtain ⟨moves, rename, hnormalize⟩ :=
    exists_intrinsicBoundaryPeripheralNielsenProgram (P.component_genus i) B
      B.intrinsicBoundaryTreeSplicedVertexPerm_oneOrbit
  refine ⟨((P.firstEndpointRetainedFreeEquiv hn B).trans
    ((FreeGroupNielsenProgram.toEquiv moves).trans (FreeGroup.freeGroupCongr rename))).trans
      (surfacePeripheralOrientationFreeEquiv (genera i)), ?_⟩
  change surfacePeripheralOrientationFreeEquiv (genera i)
    (FreeGroup.freeGroupCongr rename (FreeGroupNielsenProgram.toEquiv moves
      (P.firstEndpointRetainedFreeEquiv hn B
        ⟦P.componentRetainedRightPolarBoundaryLoop i⟧))) = _
  erw [P.firstEndpointRetainedFreeEquiv_rightPolarBoundaryLoop hn B,
    hnormalize, surfacePeripheralOrientationFreeEquiv_relator]

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** The actual first retained prefix has its outgoing inverse-relator
marking, constructed from the original preparation and native boundary map. -/
theorem ExerciseGluingPreparation.exists_firstRetainedPrefixPolarMarkedFreeEquiv
    {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
    {X : ∀ i, ClosedHyperbolicSurface (genera i)}
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (hk : k.val = 0) :
    ∃ e : FundamentalGroup ↥(P.gluedChainPrefix k)
        (P.gluedChainPrefixRightPolarBoundaryMap k 1) ≃*
          FreeGroup (SurfaceGenerator (genera (gluingChainEdgeLeft k))),
      e ⟦P.gluedChainPrefixRightPolarBoundaryLoop k⟧ =
        (surfaceRelator (genera (gluingChainEdgeLeft k)))⁻¹ := by
  have hn : 2 ≤ n := by have := k.isLt; omega
  have hidx : gluingChainEdgeLeft k = (⟨0, by omega⟩ : Fin n) := Fin.ext hk
  have he : ∃ e : FundamentalGroup (P.ChainComponent (gluingChainEdgeLeft k))
      (P.componentRetainedRightPolarBoundaryMap (gluingChainEdgeLeft k) 1) ≃*
        FreeGroup (SurfaceGenerator (genera (gluingChainEdgeLeft k))),
      e ⟦P.componentRetainedRightPolarBoundaryLoop (gluingChainEdgeLeft k)⟧ =
        (surfaceRelator (genera (gluingChainEdgeLeft k)))⁻¹ := by
    rw [hidx]
    exact exists_firstEndpointRetainedMarkedFreeEquiv_inverse P hn
      ((X ⟨0, by omega⟩).dirichletBoundarySegments (P.centers ⟨0, by omega⟩).2)
  obtain ⟨e, he⟩ := he
  refine ⟨(P.gluedChainPrefixZeroPolarFundamentalGroupEquiv k hk).trans e, ?_⟩
  change e (P.gluedChainPrefixZeroPolarFundamentalGroupEquiv k hk
    ⟦P.gluedChainPrefixRightPolarBoundaryLoop k⟧) = _
  rw [P.gluedChainPrefixZeroPolarFundamentalGroupEquiv_boundary k hk]
  exact he

#print axioms ExerciseGluingPreparation.exists_firstRetainedPrefixPolarMarkedFreeEquiv

/-- **Math.** Sum of the original component genera in a retained prefix. -/
def gluingChainPrefixGenus {n : ℕ} (genera : Fin n → ℕ)
    (k : Fin (n - 1)) : ℕ :=
  ∑ i ∈ Finset.range (k.val + 1), if hi : i < n then genera ⟨i, hi⟩ else 0

theorem gluingChainPrefixGenus_zero {n : ℕ} (genera : Fin n → ℕ)
    (k : Fin (n - 1)) (hk : k.val = 0) :
    gluingChainPrefixGenus genera k = genera (gluingChainEdgeLeft k) := by
  have hn : 0 < n := by have := k.isLt; omega
  simp [gluingChainPrefixGenus, hk, hn, gluingChainEdgeLeft]

theorem gluingChainPrefixGenus_succ {n : ℕ} (genera : Fin n → ℕ)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    gluingChainPrefixGenus genera k =
      gluingChainPrefixGenus genera j + genera (gluingChainEdgeLeft k) := by
  have hkn : k.val < n := by have := k.isLt; omega
  change (∑ i ∈ Finset.range (k.val + 1),
      if hi : i < n then genera ⟨i, hi⟩ else 0) =
    (∑ i ∈ Finset.range (j.val + 1),
      if hi : i < n then genera ⟨i, hi⟩ else 0) + genera (gluingChainEdgeLeft k)
  rw [show k.val + 1 = (j.val + 1) + 1 by omega, Finset.sum_range_succ]
  simp only [hjk, dif_pos hkn]
  rfl

theorem gluingChainPrefixGenus_add_last {n : ℕ} (genera : Fin n → ℕ)
    (k : Fin (n - 1)) (hk : k.val + 2 = n) :
    gluingChainPrefixGenus genera k + genera (gluingChainEdgeRight k) =
      ∑ i, genera i := by
  have hlast : k.val + 1 < n := by omega
  rw [Finset.sum_fin_eq_sum_range]
  have hsum := Finset.sum_range_succ
    (fun i => if hi : i < n then genera ⟨i, hi⟩ else 0) (k.val + 1)
  have hsize : k.val + 1 + 1 = n := by omega
  rw [hsize] at hsum
  rw [hsum]
  simp only [dif_pos hlast]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Every actual retained prefix carries its cumulative-genus free
marking at the unchanged outgoing polar point, with inverse ordered relator.
The induction uses only the internally constructed endpoint and component
markings; no marking of an earlier prefix is assumed by the conclusion. -/
theorem ExerciseGluingPreparation.exists_retainedPrefixPolarMarkedFreeEquiv
    {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
    {X : ∀ i, ClosedHyperbolicSurface (genera i)}
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    ∃ e : FundamentalGroup ↥(P.gluedChainPrefix k)
        (P.gluedChainPrefixRightPolarBoundaryMap k 1) ≃*
          FreeGroup (SurfaceGenerator (gluingChainPrefixGenus genera k)),
      e ⟦P.gluedChainPrefixRightPolarBoundaryLoop k⟧ =
        (surfaceRelator (gluingChainPrefixGenus genera k))⁻¹ := by
  have haux : ∀ (m : ℕ) (hm : m < n - 1),
      ∃ e : FundamentalGroup ↥(P.gluedChainPrefix ⟨m, hm⟩)
          (P.gluedChainPrefixRightPolarBoundaryMap ⟨m, hm⟩ 1) ≃*
            FreeGroup (SurfaceGenerator (gluingChainPrefixGenus genera ⟨m, hm⟩)),
        e ⟦P.gluedChainPrefixRightPolarBoundaryLoop ⟨m, hm⟩⟧ =
          (surfaceRelator (gluingChainPrefixGenus genera ⟨m, hm⟩))⁻¹ := by
    intro m
    induction m with
    | zero =>
        intro hm
        rw [gluingChainPrefixGenus_zero genera ⟨0, hm⟩ rfl]
        exact P.exists_firstRetainedPrefixPolarMarkedFreeEquiv ⟨0, hm⟩ rfl
    | succ m ih =>
        intro hm
        let k' : Fin (n - 1) := ⟨m + 1, hm⟩
        let j : Fin (n - 1) := ⟨m, by omega⟩
        have hjk : j.val + 1 = k'.val := rfl
        obtain ⟨ePrev, hPrev⟩ := ih j.isLt
        obtain ⟨eComp, hIncoming, hOutgoing⟩ :=
          P.exists_internalRetainedPolarMarkedFreeEquiv (gluingChainEdgeLeft k')
            (by change 0 < m + 1; omega)
            (by change m + 1 + 1 < n; omega)
        change ∃ e : FundamentalGroup ↥(P.gluedChainPrefix k')
            (P.gluedChainPrefixRightPolarBoundaryMap k' 1) ≃*
              FreeGroup (SurfaceGenerator (gluingChainPrefixGenus genera k')),
          e ⟦P.gluedChainPrefixRightPolarBoundaryLoop k'⟧ =
            (surfaceRelator (gluingChainPrefixGenus genera k'))⁻¹
        rw [gluingChainPrefixGenus_succ genera k' j hjk]
        exact ⟨P.gluedChainPrefixSuccessorMarkedFreeEquiv k' j hjk
          (gluingChainPrefixGenus genera j) ePrev hPrev eComp hIncoming,
          P.gluedChainPrefixSuccessorMarkedFreeEquiv_boundary k' j hjk
            (gluingChainPrefixGenus genera j) ePrev hPrev eComp hIncoming hOutgoing⟩
  exact haux k.val k.isLt

/-- **Math.** The actual retained last component has its same-genus marking
at the original incoming polar basepoint. Its positive incoming generator
is the inverse relator: reflection identifies it with the inverse outgoing
seam generator in the ordered chain relation. -/
theorem exists_lastEndpointRetainedMarkedFreeEquiv_inverse
    {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
    {X : ∀ i, ClosedHyperbolicSurface (genera i)}
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (B : DirichletBoundarySegments (X ⟨n - 1, by omega⟩)
      (P.centers ⟨n - 1, by omega⟩).1) :
    ∃ e : FundamentalGroup (P.ChainComponent ⟨n - 1, by omega⟩)
        (P.componentRetainedLeftPolarBoundaryMap ⟨n - 1, by omega⟩ 1) ≃*
          FreeGroup (SurfaceGenerator (genera ⟨n - 1, by omega⟩)),
      e ⟦P.componentRetainedLeftPolarBoundaryLoop ⟨n - 1, by omega⟩⟧ =
        (surfaceRelator (genera ⟨n - 1, by omega⟩))⁻¹ := by
  classical
  let i : Fin n := ⟨n - 1, by omega⟩
  obtain ⟨moves, rename, hnormalize⟩ :=
    exists_intrinsicBoundaryPeripheralNielsenProgram (P.component_genus i) B
      B.intrinsicBoundaryTreeSplicedVertexPerm_oneOrbit
  refine ⟨((P.lastEndpointRetainedFreeEquiv hn B).trans
    ((FreeGroupNielsenProgram.toEquiv moves).trans (FreeGroup.freeGroupCongr rename))).trans
      (surfacePeripheralOrientationFreeEquiv (genera i)), ?_⟩
  change surfacePeripheralOrientationFreeEquiv (genera i)
    (FreeGroup.freeGroupCongr rename (FreeGroupNielsenProgram.toEquiv moves
      (P.lastEndpointRetainedFreeEquiv hn B
        ⟦P.componentRetainedLeftPolarBoundaryLoop i⟧))) = _
  erw [P.lastEndpointRetainedFreeEquiv_leftPolarBoundaryLoop hn B,
    hnormalize, surfacePeripheralOrientationFreeEquiv_relator]

#print axioms exists_firstEndpointRetainedMarkedFreeEquiv_inverse
#print axioms exists_lastEndpointRetainedMarkedFreeEquiv_inverse

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** The actual last retained suffix has its incoming inverse-relator
marking, constructed from the original preparation and native boundary map. -/
theorem ExerciseGluingPreparation.exists_lastRetainedSuffixPolarMarkedFreeEquiv
    {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
    {X : ∀ i, ClosedHyperbolicSurface (genera i)}
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (hk : k.val + 2 = n) :
    ∃ e : FundamentalGroup ↥(P.gluedChainSuffix k)
        (P.gluedChainSuffixLeftPolarBoundaryMap k 1) ≃*
          FreeGroup (SurfaceGenerator (genera (gluingChainEdgeRight k))),
      e ⟦P.gluedChainSuffixLeftPolarBoundaryLoop k⟧ =
        (surfaceRelator (genera (gluingChainEdgeRight k)))⁻¹ := by
  have hn : 2 ≤ n := by omega
  have hidx : gluingChainEdgeRight k = (⟨n - 1, by omega⟩ : Fin n) := by
    apply Fin.ext
    change k.val + 1 = n - 1
    omega
  have he : ∃ e : FundamentalGroup (P.ChainComponent (gluingChainEdgeRight k))
      (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeRight k) 1) ≃*
        FreeGroup (SurfaceGenerator (genera (gluingChainEdgeRight k))),
      e ⟦P.componentRetainedLeftPolarBoundaryLoop (gluingChainEdgeRight k)⟧ =
        (surfaceRelator (genera (gluingChainEdgeRight k)))⁻¹ := by
    rw [hidx]
    exact exists_lastEndpointRetainedMarkedFreeEquiv_inverse P hn
      ((X ⟨n - 1, by omega⟩).dirichletBoundarySegments (P.centers ⟨n - 1, by omega⟩).1)
  obtain ⟨e, he⟩ := he
  refine ⟨(P.gluedChainSuffixLastPolarFundamentalGroupEquiv k hk).trans e, ?_⟩
  change e (P.gluedChainSuffixLastPolarFundamentalGroupEquiv k hk
    ⟦P.gluedChainSuffixLeftPolarBoundaryLoop k⟧) = _
  rw [P.gluedChainSuffixLastPolarFundamentalGroupEquiv_boundary k hk]
  exact he

#print axioms ExerciseGluingPreparation.exists_lastRetainedSuffixPolarMarkedFreeEquiv

/-- The genuine polygon certificate on the original Dirichlet domain.

The cyclic boundary and inverse-deck pairing determine the actual `n−2`
boundary-apex fan. Its exact tiling and a.e. disjointness are proved in
`DirichletVertexFan`. The two polygon contracts above supply per-class angle
sums and character rank through audited imports and actual native bijections.
No area, Euler formula, alternative polygon or replacement fan is assumed. -/
noncomputable def exercisePolygonCertificate {g : ℕ} (hg : 2 ≤ g)
    (X : ClosedHyperbolicSurface g) : ExercisePolygonCertificate X := by
  classical
  let B := X.dirichletBoundarySegments I
  refine
    { triangles := B.intrinsicVertexFanTriangleFundamentalDomain
      triangle_measurable := ?_
      triangle_ae_disjoint := ?_
      triangles_ae_exact := ?_
      edgeCount := intrinsicPairedSideCount B
      vertexCount := Fintype.card (Quotient (intrinsicVertexOrbitSetoid B))
      fan_count := intrinsicVertexFan_fan_count B
      connected_count := intrinsicQuotientVertexCount_le_pairedSideCount_add_one B
      cornerVertex := intrinsicVertexFanCornerClassIndex B
      vertex_angles := exercisePolygonVertexAngles hg B
      graph_characters := exercisePolygonGraphCharacters hg B }
  · intro i
    exact (B.intrinsicVertexFan_triangle_measurable i).nullMeasurableSet
  · exact B.intrinsicVertexFan_triangle_ae_disjoint
  · change Vendored.RiemannDynamics.dirichletDomain X.deckGroup I =ᵐ[volume]
      ⋃ i, Vendored.RiemannDynamics.hyperbolicTriangle
        (B.intrinsicVertexFanVertices i).1 (B.intrinsicVertexFanVertices i).2.1
        (B.intrinsicVertexFanVertices i).2.2
    rw [B.iUnion_intrinsicVertexFan_triangle_eq_dirichletDomain]

namespace ExercisePolygonCertificate

/-- The graph-character rank and surface marking give the Euler relation. -/
theorem euler_count {g : ℕ} {X : ClosedHyperbolicSurface g}
    (P : ExercisePolygonCertificate X) :
    P.edgeCount + 1 = P.vertexCount + 2 * g := by
  have hrank : P.edgeCount + 1 - P.vertexCount = 2 * g := by
    have h := P.graph_characters.finrank_eq
    rw [X.finrank_deckGroupCharacterSpace] at h
    simpa using h.symm
  have hconn := P.connected_count
  omega

/-- G-P7 is filled: reindex the finite corner sum by quotient vertex classes. -/
theorem total_corner_angles {g : ℕ} {X : ClosedHyperbolicSurface g}
    (P : ExercisePolygonCertificate X) :
    (∑ c : Fin P.triangles.triangleCount × Fin 3,
      exerciseCornerAngle P.triangles c) = 2 * Real.pi * P.vertexCount := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ P.cornerVertex
    (exerciseCornerAngle P.triangles)]
  simp [P.vertex_angles, nsmul_eq_mul]
  ring

/-- G-P8 is filled: the Euler and angle equations give the exact total defect. -/
theorem sum_angleDeficit {g : ℕ} {X : ClosedHyperbolicSurface g}
    (P : ExercisePolygonCertificate X) :
    (∑ i : Fin P.triangles.triangleCount, P.triangles.angleDeficit i) =
      4 * Real.pi * ((g : ℝ) - 1) := by
  have htotal := P.total_corner_angles
  rw [Fintype.sum_prod_type] at htotal
  simp_rw [exercise_sum_cornerAngle] at htotal
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at htotal
  have hfan : (P.triangles.triangleCount : ℝ) + 2 = 2 * P.edgeCount := by
    exact_mod_cast P.fan_count
  have heuler : (P.edgeCount : ℝ) + 1 = P.vertexCount + 2 * g := by
    exact_mod_cast P.euler_count
  have hfan_pi := congrArg (fun x : ℝ ↦ x * Real.pi) hfan
  have heuler_pi := congrArg (fun x : ℝ ↦ x * Real.pi) heuler
  nlinarith

/-- G-P9 is filled: disjoint tiling upgrades the existing cover bound to equality. -/
theorem covolume_eq_sum_angleDeficit {g : ℕ} {X : ClosedHyperbolicSurface g}
    (P : ExercisePolygonCertificate X) :
    covolume X.deckGroup ℍ volume =
      ∑ i : Fin P.triangles.triangleCount,
        ENNReal.ofReal (P.triangles.angleDeficit i) := by
  rw [X.covolume_eq_dirichletDomain_volume (I : ℍ)]
  letI : Countable (SurfaceGroup g) := by
    change Countable (Quotient (QuotientGroup.leftRel
      (Subgroup.normalClosure ({surfaceRelator g} : Set (FreeGroup (SurfaceGenerator g))))))
    infer_instance
  letI : Countable X.deckGroup :=
    (Equiv.countable_iff X.marking.toEquiv).mpr inferInstance
  calc
    volume (Vendored.RiemannDynamics.dirichletDomain X.deckGroup (I : ℍ)) =
        volume P.triangles.fundamentalDomain :=
      (X.dirichletDomain_isFundamentalDomain I).measure_eq P.triangles.isFundamentalDomain
    _ = volume (⋃ i, exerciseTriangleSet P.triangles i) :=
      measure_congr P.triangles_ae_exact
    _ = ∑' i : Fin P.triangles.triangleCount, volume (exerciseTriangleSet P.triangles i) :=
      measure_iUnion₀ P.triangle_ae_disjoint P.triangle_measurable
    _ = ∑ i : Fin P.triangles.triangleCount,
        ENNReal.ofReal (P.triangles.angleDeficit i) := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro i _
      exact volume_geodesicTriangle_eq_angleDeficit _ _ _
        (P.triangles.nondegenerate i).1 (P.triangles.nondegenerate i).2.1
        (P.triangles.nondegenerate i).2.2

end ExercisePolygonCertificate

/-- Exact area formula from the proved G-POLYGON constructor.
The upper and lower area consumers deliberately use the same certificate. -/
theorem exercise_covolume_eq_genus_area {g : ℕ} (hg : 2 ≤ g)
    (X : ClosedHyperbolicSurface g) :
    covolume X.deckGroup ℍ volume = ENNReal.ofReal (4 * Real.pi * ((g : ℝ) - 1)) := by
  let P := exercisePolygonCertificate hg X
  rw [P.covolume_eq_sum_angleDeficit, ← ENNReal.ofReal_sum_of_nonneg
    (fun i _ ↦ P.triangles.angleDeficit_nonneg i), P.sum_angleDeficit]

/-- The logarithmic upper-bound field is assembled from G-POLYGON. -/
theorem exercise_log_systole_upper_bound :
    ∃ K : ℝ, ∀ {g : ℕ}, 2 ≤ g → (X : ClosedHyperbolicSurface g) →
      X.systole ≤ K * Real.log (g : ℝ) := by
  refine ⟨18, ?_⟩
  intro g hg X
  apply X.systole_le_eighteen_log_of_covolume_le_genus hg
  have hg_real : (2 : ℝ) ≤ g := by exact_mod_cast hg
  have harea_nonneg : 0 ≤ 4 * Real.pi * ((g : ℝ) - 1) :=
    mul_nonneg (by positivity) (by linarith)
  rw [exercise_covolume_eq_genus_area hg X, ENNReal.toReal_ofReal harea_nonneg]
  nlinarith [Real.pi_pos]

/-- G-S1 is filled: strengthen the already proved eventual nonnegative target. -/
theorem exercise_eventually_target_pos (C : ℝ) :
    ∀ᶠ g : ℕ in atTop, 0 < targetSystole C g := by
  have hlog : Tendsto (fun g : ℕ ↦ Real.log g) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : ∀ᶠ g : ℕ in atTop, 1 < targetSystole C g / Real.log g :=
    (tendsto_targetSystole_div_log C).eventually
      (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 4 / 3))
  filter_upwards [hratio, hlog.eventually_gt_atTop 0] with g hr hl
  have h := (lt_div_iff₀ hl).mp hr
  linarith

/-- G-S2 is filled: the exact area budget chooses centers uniformly. There is
no surface-dependent threshold and no substituted component-genus radius. -/
theorem exercise_eventually_gluing_preparation {a : ℝ} (ha : 0 < a) (K : ℝ) :
    ∀ᶠ g : ℕ in atTop, ∀ (n : ℕ) (genera : Fin n → ℕ)
      (X : ∀ i, ClosedHyperbolicSurface (genera i)),
      (∀ i, a * (g : ℝ) ≤ (genera i : ℝ)) →
      (∀ i, (4 / 3 : ℝ) * Real.log g - K ≤ (X i).systole) →
      Nonempty (ExerciseGluingPreparation (gluingConstant K) g n genera X) := by
  classical
  have hlarge : ∀ᶠ g : ℕ in atTop, (2 : ℝ) ≤ a * (g : ℝ) :=
    (Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [exercise_eventually_target_pos (gluingConstant K),
    eventually_twice_gluingEmbeddedRadius_gluingConstant_lt K,
    eventually_exists_gluing_orbit_centers_of_component_area_budget
      (gluingConstant_pos K).le (by positivity : 0 < 4 * Real.pi) ha,
    hlarge] with g hL houter hcenters hlargeg
  intro n genera X hcompare hsys
  have hgen : ∀ i, 2 ≤ genera i := by
    intro i
    have h := hlargeg.trans (hcompare i)
    exact_mod_cast h
  have hsep : ∀ i, ∃ z : ℍ, ∀ γ : (X i).deckGroup,
      gluingSeparationRadius (gluingConstant K) g ≤ dist (I : ℍ) (γ • z) := by
    intro i
    apply hcenters (genera i) (X i) I (hcompare i)
    rw [exercise_covolume_eq_genus_area (hgen i) (X i)]
  choose z hz using hsep
  have hr : 0 ≤ gluingRadius (gluingConstant K) g := by
    rw [gluingRadius, Real.arsinh_nonneg_iff]
    exact div_nonneg hL.le (by positivity)
  refine ⟨⟨hL, hgen, ?_, (fun i ↦ houter (X i).systole (hsys i)),
    (fun i ↦ (I, z i)), hz⟩⟩
  intro i
  have h := houter (X i).systole (hsys i)
  dsimp [gluingEmbeddedRadius, gluingDepth] at h
  linarith

/-- A faithful, free, discrete action of the genus-`g` surface group on the
hyperbolic plane, with a compact fundamental set and every nonidentity
displacement at least `L`. Its compact quotient is the required surface. -/
structure ExerciseLiftedChainOutput (g : ℕ) (L : ℝ) where
  representation : SurfaceGroup g →* SL(2, ℝ)
  faithful : Function.Injective representation
  discrete : IsDiscrete (representation.range : Set SL(2, ℝ))
  free : ∀ γ : representation.range, ∀ z : ℍ, γ • z = z → γ = 1
  compactSet : Set ℍ
  compact : IsCompact compactSet
  orbit_cover : ∀ z : ℍ, ∃ γ : representation.range, γ • z ∈ compactSet
  displacement_lower : ∀ γ : representation.range, γ ≠ 1 → ∀ z : ℍ,
    L ≤ dist z (γ • z)

/-- **Math.** A marked closed hyperbolic surface with systole at least `L` supplies all
fields of the lifted-chain output. The only geometric input needed here is
the surface itself and its systole bound; compact orbit data comes from the
actual quotient covering. -/
noncomputable def ExerciseLiftedChainOutput.ofClosedHyperbolicSurface
    {g : ℕ} {L : ℝ} (X : ClosedHyperbolicSurface g)
    (hL : L ≤ X.systole) : ExerciseLiftedChainOutput g L := by
  let ρ : SurfaceGroup g →* SL(2, ℝ) :=
    X.deckGroup.subtype.comp X.marking.symm.toMonoidHom
  have hrange : (ρ.range : Set SL(2, ℝ)) = X.deckGroup := by
    ext A
    constructor
    · rintro ⟨a, rfl⟩
      exact (X.marking.symm a).property
    · intro hA
      let δ : X.deckGroup := ⟨A, hA⟩
      refine ⟨X.marking δ, ?_⟩
      change ((X.marking.symm (X.marking δ) : X.deckGroup) : SL(2, ℝ)) = A
      rw [X.marking.symm_apply_apply]
  let K : Set ℍ := Classical.choose X.exists_compact_orbit_cover
  have hK : IsCompact K := (Classical.choose_spec X.exists_compact_orbit_cover).1
  have hKcover : ∀ z : ℍ, ∃ δ : X.deckGroup, δ • z ∈ K :=
    (Classical.choose_spec X.exists_compact_orbit_cover).2
  refine ⟨ρ, ?_, ?_, ?_, K, hK, ?_, ?_⟩
  · intro a b hab
    apply X.marking.symm.injective
    apply Subtype.ext
    exact hab
  · rw [hrange]
    exact X.discrete
  · intro γ z hfix
    have hγ_mem : (γ : SL(2, ℝ)) ∈ X.deckGroup := by
      change (γ : SL(2, ℝ)) ∈ (X.deckGroup : Set SL(2, ℝ))
      rw [← hrange]
      exact γ.property
    let δ : X.deckGroup := ⟨γ, hγ_mem⟩
    have hδ : δ • z = z := by
      change (γ : SL(2, ℝ)) • z = z
      exact hfix
    have hδ_one := X.free δ z hδ
    apply Subtype.ext
    simpa [δ] using congrArg Subtype.val hδ_one
  · intro z
    obtain ⟨δ, hδ⟩ := hKcover z
    let γ : ρ.range := ⟨δ, by
      change (δ : SL(2, ℝ)) ∈ (ρ.range : Set SL(2, ℝ))
      rw [hrange]
      exact δ.property⟩
    refine ⟨γ, ?_⟩
    change (δ : SL(2, ℝ)) • z ∈ K
    exact hδ
  · intro γ hγ z
    have hγ_mem : (γ : SL(2, ℝ)) ∈ X.deckGroup := by
      change (γ : SL(2, ℝ)) ∈ (X.deckGroup : Set SL(2, ℝ))
      rw [← hrange]
      exact γ.property
    let δ : X.deckGroup := ⟨(γ : SL(2, ℝ)), hγ_mem⟩
    have hδ : δ ≠ 1 := by
      intro h
      apply hγ
      apply Subtype.ext
      simpa [δ] using congrArg Subtype.val h
    have hdist := X.systole_le_displacement δ hδ z
    change L ≤ dist z ((γ : SL(2, ℝ)) • z)
    have hdist' : X.systole ≤ dist z ((γ : SL(2, ℝ)) • z) := by
      change X.systole ≤ dist z ((γ : SL(2, ℝ)) • z) at hdist
      exact hdist
    exact hL.trans hdist'

end SystolicGrowth

module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.HyperbolicPacking

@[expose] public section

open MeasureTheory Set UpperHalfPlane
open scoped ENNReal Pointwise UpperHalfPlane

namespace SystolicGrowth

/-! ## Finite triangular fundamental domains

This module records the exact interface between an explicit polygonal
construction and the canonical Dirichlet domain used by the packing argument.
The certificate below is evidence produced by a concrete construction, not an
additional hypothesis in the eventual main theorem.
-/

namespace ClosedHyperbolicSurface

/-- Once a closed Dirichlet domain is known to lie in the closed ball of radius
`R` about its centre, only deck transformations with displacement at most
`2R` can impose a nonredundant Dirichlet inequality there.  Thus the canonical
domain has a concrete finite half-space presentation inside that ball.

This is the finite-sided reduction needed before a polygonal construction.
It intentionally does not claim that the resulting half-spaces have already
been converted into edges, vertices, or a triangulation. -/
theorem dirichletDomain_eq_closedBall_inter_finite_constraints {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (R : ℝ)
    (hbound : Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ⊆
      Metric.closedBall o R) :
    Vendored.RiemannDynamics.dirichletDomain X.deckGroup o =
      Metric.closedBall o R ∩ {z : ℍ |
        ∀ γ ∈ deckElementsDistLE X o (2 * R),
          dist z o ≤ dist z (γ • o)} := by
  ext z
  constructor
  · intro hz
    refine ⟨hbound hz, ?_⟩
    intro γ _
    exact (Vendored.RiemannDynamics.mem_dirichletDomain.mp hz) γ
  · rintro ⟨hzball, hzconstraints⟩
    apply Vendored.RiemannDynamics.mem_dirichletDomain.mpr
    intro γ
    by_contra hnot
    have hlt : dist z (γ • o) < dist z o := lt_of_not_ge hnot
    have hzdist : dist z o ≤ R := Metric.mem_closedBall.mp hzball
    have hdisplacement : dist o (γ • o) ≤ 2 * R := by
      exact le_of_lt <| calc
        dist o (γ • o) ≤ dist o z + dist z (γ • o) := dist_triangle _ _ _
        _ < dist o z + dist z o := add_lt_add_right hlt _
        _ = dist z o + dist z o := by rw [dist_comm o z]
        _ ≤ R + R := add_le_add hzdist hzdist
        _ = 2 * R := by ring
    have hmem : γ ∈ deckElementsDistLE X o (2 * R) :=
      (mem_deckElementsDistLE X o (2 * R) γ).mpr hdisplacement
    exact (not_lt_of_ge (hzconstraints γ hmem)) hlt

/-- The finitely many Dirichlet inequalities coming from displacement at most
`2 (R + 1)` already force a point into the ball of radius `R + 1`.

The proof uses the sphere of that radius as a finite witness shell.  A point
outside the shell projects to it along a geodesic segment from `o`; any
strictly violated Dirichlet inequality on the shell remains violated farther
along the segment by geodesic convexity of the corresponding half-space. -/
theorem finite_dirichlet_constraints_subset_closedBall {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (R : ℝ)
    (hbound : Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ⊆
      Metric.closedBall o R) :
    {z : ℍ | ∀ γ ∈ deckElementsDistLE X o (2 * (R + 1)),
      dist z o ≤ dist z (γ • o)} ⊆ Metric.closedBall o (R + 1) := by
  intro z hz
  by_contra hznot
  have hbase : o ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o :=
    Vendored.RiemannDynamics.basepoint_mem_dirichletDomain
  have hRnonneg : 0 ≤ R := by
    have h := Metric.mem_closedBall.mp (hbound hbase)
    simpa using h
  have hSpos : 0 < R + 1 := by linarith
  have hznot' : ¬ dist z o ≤ R + 1 := by
    simpa only [Metric.mem_closedBall] using hznot
  have hzfar : R + 1 < dist o z := by
    rw [dist_comm]
    exact lt_of_not_ge hznot'
  have hzpos : 0 < dist o z := by linarith
  let t : ℝ := (R + 1) / dist o z
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg hSpos.le hzpos.le
    · exact (div_le_one₀ hzpos).mpr hzfar.le
  let x : ℍ := Vendored.RiemannDynamics.geodInterp o z t
  have hxseg : x ∈ Vendored.RiemannDynamics.geodSeg o z := by
    dsimp [x]
    exact Vendored.RiemannDynamics.geodInterp_mem_geodSeg o z ht
  have hxdist : dist x o = R + 1 := by
    rw [dist_comm]
    dsimp [x]
    rw [Vendored.RiemannDynamics.dist_geodInterp_left o z ht]
    dsimp [t]
    exact div_mul_cancel₀ _ hzpos.ne'
  have hxnot : x ∉ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := by
    intro hx
    have hxle : dist x o ≤ R := Metric.mem_closedBall.mp (hbound hx)
    linarith
  have hxnot' : ¬ ∀ γ : X.deckGroup, dist x o ≤ dist x (γ • o) := by
    simpa only [Vendored.RiemannDynamics.mem_dirichletDomain] using hxnot
  push Not at hxnot'
  obtain ⟨γ, hγlt⟩ := hxnot'
  have hdisplacement : dist o (γ • o) ≤ 2 * (R + 1) := by
    exact le_of_lt <| calc
      dist o (γ • o) ≤ dist o x + dist x (γ • o) := dist_triangle _ _ _
      _ < dist o x + dist x o := add_lt_add_right hγlt _
      _ = dist x o + dist x o := by rw [dist_comm o x]
      _ = (R + 1) + (R + 1) := by rw [hxdist]
      _ = 2 * (R + 1) := by ring
  have hmem : γ ∈ deckElementsDistLE X o (2 * (R + 1)) :=
    (mem_deckElementsDistLE X o (2 * (R + 1)) γ).mpr hdisplacement
  have hzconstraint : dist z o ≤ dist z (γ • o) := hz γ hmem
  have hoconstraint : dist o o ≤ dist o (γ • o) := by
    rw [dist_self]
    exact dist_nonneg
  have hxconstraint : dist x o ≤ dist x (γ • o) :=
    Vendored.RiemannDynamics.geodSeg_subset_setOf_dist_le
      hoconstraint hzconstraint hxseg
  exact (not_lt_of_ge hxconstraint) hγlt

/-- The auxiliary bounding ball can be removed: if the Dirichlet domain is
contained in radius `R`, then the finite deck set of displacement at most
`2 (R + 1)` defines it globally. -/
theorem dirichletDomain_eq_finite_constraints_of_subset_closedBall {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (R : ℝ)
    (hbound : Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ⊆
      Metric.closedBall o R) :
    Vendored.RiemannDynamics.dirichletDomain X.deckGroup o =
      {z : ℍ | ∀ γ ∈ deckElementsDistLE X o (2 * (R + 1)),
        dist z o ≤ dist z (γ • o)} := by
  have hbound' : Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ⊆
      Metric.closedBall o (R + 1) := by
    intro z hz
    rw [Metric.mem_closedBall]
    exact (Metric.mem_closedBall.mp (hbound hz)).trans (by linarith)
  ext z
  constructor
  · intro hz γ _
    exact (Vendored.RiemannDynamics.mem_dirichletDomain.mp hz) γ
  · intro hz
    rw [X.dirichletDomain_eq_closedBall_inter_finite_constraints o (R + 1) hbound']
    exact ⟨X.finite_dirichlet_constraints_subset_closedBall o R hbound hz, hz⟩

/-- Every closed hyperbolic surface has a genuine finite Dirichlet half-space
presentation, with no auxiliary ball in the defining equality. -/
theorem exists_positive_radius_dirichletDomain_eq_finite_constraints
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) :
    ∃ R : ℝ, 0 < R ∧
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o =
        {z : ℍ | ∀ γ ∈ deckElementsDistLE X o (2 * R),
          dist z o ≤ dist z (γ • o)} := by
  obtain ⟨K, hK, hcover⟩ := X.exists_compact_covering
  have hcompact :=
    X.isCompact_dirichletDomain_of_compact_covering o K hK hcover
  obtain ⟨R, hbound⟩ :=
    (Metric.isBounded_iff_subset_closedBall o).mp hcompact.isBounded
  have hbase : o ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o :=
    Vendored.RiemannDynamics.basepoint_mem_dirichletDomain
  have hRnonneg : 0 ≤ R := by
    have h := Metric.mem_closedBall.mp (hbound hbase)
    simpa using h
  refine ⟨R + 1, by linarith, ?_⟩
  exact X.dirichletDomain_eq_finite_constraints_of_subset_closedBall o R hbound

/-- Every closed hyperbolic surface has a finite Dirichlet half-space
presentation.  The radius and finite set are extracted from the compactness
of its canonical Dirichlet domain. -/
theorem exists_dirichletDomain_eq_closedBall_inter_finite_constraints
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) :
    ∃ R : ℝ,
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o =
        Metric.closedBall o R ∩ {z : ℍ |
          ∀ γ ∈ deckElementsDistLE X o (2 * R),
            dist z o ≤ dist z (γ • o)} := by
  obtain ⟨K, hK, hcover⟩ := X.exists_compact_covering
  have hcompact :=
    X.isCompact_dirichletDomain_of_compact_covering o K hK hcover
  obtain ⟨R, hbound⟩ :=
    (Metric.isBounded_iff_subset_closedBall o).mp hcompact.isBounded
  exact ⟨R, X.dirichletDomain_eq_closedBall_inter_finite_constraints o R hbound⟩

/-- The canonical Dirichlet domain is geodesically convex.  Each defining
distance half-space is geodesically convex, so their intersection is as well. -/
theorem geodConvex_dirichletDomain {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) :
    Vendored.RiemannDynamics.GeodConvex
      (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  intro a ha b hb z hz
  apply Vendored.RiemannDynamics.mem_dirichletDomain.mpr
  intro γ
  exact Vendored.RiemannDynamics.geodSeg_subset_setOf_dist_le
    ((Vendored.RiemannDynamics.mem_dirichletDomain.mp ha) γ)
    ((Vendored.RiemannDynamics.mem_dirichletDomain.mp hb) γ) hz

/-- A nontrivial deck transformation cuts the compact Dirichlet domain in a
single (possibly degenerate) geodesic segment whenever its bisector meets the
domain.  Together with the finite-constraint theorem, this supplies a finite
family of concrete segment candidates for the still-missing polygonal
boundary construction. -/
theorem exists_geodSeg_eq_dirichletDomain_inter_bisector {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (γ : X.deckGroup) (hγ : γ ≠ 1)
    (hne : (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
      {z : ℍ | dist z o = dist z (γ • o)}).Nonempty) :
    ∃ a b : ℍ,
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
        {z : ℍ | dist z o = dist z (γ • o)} =
          Vendored.RiemannDynamics.geodSeg a b := by
  obtain ⟨K, hK, hcover⟩ := X.exists_compact_covering
  have hcompact :=
    X.isCompact_dirichletDomain_of_compact_covering o K hK hcover
  have hdistinct : o ≠ γ • o := by
    intro hfix
    exact hγ (X.free γ o hfix.symm)
  exact Vendored.RiemannDynamics.exists_geodSeg_eq_inter_bisector
    hcompact (X.geodConvex_dirichletDomain o) hdistinct hne

/-- A point satisfying all nonidentity constraints of a finite Dirichlet
presentation strictly is an interior point.  The finite intersection of the
corresponding strict half-spaces is an open neighbourhood contained in the
Dirichlet domain. -/
theorem mem_interior_dirichletDomain_of_strict_finite_constraints {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (F : Finset X.deckGroup)
    (hdir : Vendored.RiemannDynamics.dirichletDomain X.deckGroup o =
      {z : ℍ | ∀ γ ∈ F, dist z o ≤ dist z (γ • o)})
    {z : ℍ}
    (hstrict : ∀ γ ∈ F.erase 1, dist z o < dist z (γ • o)) :
    z ∈ interior (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  classical
  let U : Set ℍ := ⋂ γ ∈ F.erase 1,
    {w : ℍ | dist w o < dist w (γ • o)}
  have hUopen : IsOpen U := by
    dsimp [U]
    apply isOpen_biInter_finset
    intro γ _
    exact isOpen_lt (continuous_id.dist continuous_const)
      (continuous_id.dist continuous_const)
  have hUD : U ⊆ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := by
    intro w hw
    simp only [U, Set.mem_iInter, Set.mem_setOf_eq] at hw
    rw [hdir]
    intro γ hγ
    by_cases hγone : γ = 1
    · subst γ
      simp
    · exact (hw γ (Finset.mem_erase.mpr ⟨hγone, hγ⟩)).le
  have hzU : z ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_setOf_eq]
    exact hstrict
  exact interior_maximal hUD hUopen hzU

/-- For any finite exact Dirichlet presentation, every boundary point belongs
to the bisector of a nonidentity member of that presentation. -/
theorem frontier_dirichletDomain_subset_finite_bisectors_of_eq {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (F : Finset X.deckGroup)
    (hdir : Vendored.RiemannDynamics.dirichletDomain X.deckGroup o =
      {z : ℍ | ∀ γ ∈ F, dist z o ≤ dist z (γ • o)}) :
    frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) ⊆
      ⋃ γ ∈ F.erase 1,
        Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
          {z : ℍ | dist z o = dist z (γ • o)} := by
  classical
  intro z hzfront
  have hzD : z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o :=
    (Vendored.RiemannDynamics.isClosed_dirichletDomain X.deckGroup o).frontier_subset hzfront
  by_contra hnot
  have hzconstraints : ∀ γ ∈ F, dist z o ≤ dist z (γ • o) := by
    have hzconstraints : z ∈ {w : ℍ | ∀ γ ∈ F, dist w o ≤ dist w (γ • o)} := by
      rw [← hdir]
      exact hzD
    exact hzconstraints
  have hstrict : ∀ γ ∈ F.erase 1, dist z o < dist z (γ • o) := by
    intro γ hγ
    have hle : dist z o ≤ dist z (γ • o) :=
      hzconstraints γ (Finset.mem_of_mem_erase hγ)
    have hne : dist z o ≠ dist z (γ • o) := by
      intro heq
      apply hnot
      refine Set.mem_iUnion.mpr ⟨γ, ?_⟩
      refine Set.mem_iUnion.mpr ⟨hγ, ?_⟩
      exact ⟨hzD, heq⟩
    exact lt_of_le_of_ne hle hne
  have hzinterior :=
    X.mem_interior_dirichletDomain_of_strict_finite_constraints o F hdir hstrict
  exact (mem_frontier_iff_notMem_interior hzD).mp hzfront hzinterior

/-- The global finite presentation yields a finite boundary cover by
nontrivial Dirichlet bisector sections. -/
theorem exists_positive_radius_frontier_dirichletDomain_subset_finite_bisectors
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) :
    ∃ R : ℝ, 0 < R ∧
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) ⊆
        ⋃ γ ∈ (deckElementsDistLE X o (2 * R)).erase 1,
          Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
            {z : ℍ | dist z o = dist z (γ • o)} := by
  obtain ⟨R, hRpos, hdir⟩ :=
    X.exists_positive_radius_dirichletDomain_eq_finite_constraints o
  exact ⟨R, hRpos,
    X.frontier_dirichletDomain_subset_finite_bisectors_of_eq o
      (deckElementsDistLE X o (2 * R)) hdir⟩

/-- Every nonempty member of the finite boundary cover is a geodesic segment.
This is the exact segment-level input for the remaining cyclic-polygon step. -/
theorem exists_geodSeg_eq_finite_boundary_bisector_section {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) (R : ℝ) (γ : X.deckGroup)
    (hγ : γ ∈ (deckElementsDistLE X o (2 * R)).erase 1)
    (hne : (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
      {z : ℍ | dist z o = dist z (γ • o)}).Nonempty) :
    ∃ a b : ℍ,
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
        {z : ℍ | dist z o = dist z (γ • o)} =
          Vendored.RiemannDynamics.geodSeg a b := by
  exact X.exists_geodSeg_eq_dirichletDomain_inter_bisector o γ
    (Finset.ne_of_mem_erase hγ) hne

/-- A point of a nonidentity Dirichlet bisector section cannot be interior to
the Dirichlet domain: after a hyperbolic isometry normalizes the bisector to
the imaginary axis, the domain lies in one closed coordinate half-plane. -/
theorem mem_frontier_dirichletDomain_of_mem_bisector
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (γ : X.deckGroup)
    (hγ : γ ≠ 1) {z : ℍ}
    (hzD : z ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o)
    (hzeq : dist z o = dist z (γ • o)) :
    z ∈ frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  apply (mem_frontier_iff_notMem_interior hzD).mpr
  intro hzint
  have hpq : o ≠ γ • o := by
    intro hfix
    exact hγ (X.free γ o hfix.symm)
  obtain ⟨A, him, hre, h0⟩ :=
    Vendored.RiemannDynamics.exists_mirror_normalizer hpq
  have hzero : (A • z).re = 0 :=
    (Vendored.RiemannDynamics.bisector_re_eq_zero him hre h0 z).mp hzeq
  have hmapint : A • z ∈ interior
      (A • Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
    rw [interior_smul]
    exact ⟨z, hzint, rfl⟩
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · have hset := Vendored.RiemannDynamics.setOf_dist_le_eq_of_im_eq
      (a := A • o) (b := A • (γ • o)) him.symm (by rw [hre]; linarith)
    have hmid : ((A • o).re + (A • (γ • o)).re) / 2 = 0 := by
      rw [hre]
      ring
    have hsubset : A • Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ⊆
        {w : ℍ | w.re ≤ 0} := by
      rintro w ⟨x, hx, rfl⟩
      have hxcomp : dist (A • x) (A • o) ≤ dist (A • x) (A • (γ • o)) := by
        simpa only [dist_smul] using
          (Vendored.RiemannDynamics.mem_dirichletDomain.mp hx) γ
      change A • x ∈ {τ : ℍ | dist τ (A • o) ≤ dist τ (A • (γ • o))} at hxcomp
      rw [hset, hmid] at hxcomp
      exact hxcomp
    have hint : A • z ∈ interior {w : ℍ | w.re ≤ 0} :=
      interior_mono hsubset hmapint
    have hinterior : interior {w : ℍ | w.re ≤ (0 : ℝ)} = {w : ℍ | w.re < 0} := by
      change interior (UpperHalfPlane.re ⁻¹' Set.Iic 0) =
        UpperHalfPlane.re ⁻¹' Set.Iio 0
      calc
        interior (UpperHalfPlane.re ⁻¹' Set.Iic 0) =
            UpperHalfPlane.re ⁻¹' interior (Set.Iic 0) :=
          (UpperHalfPlane.isOpenMap_re.preimage_interior_eq_interior_preimage
            UpperHalfPlane.continuous_re (Set.Iic 0)).symm
        _ = UpperHalfPlane.re ⁻¹' Set.Iio 0 := by rw [interior_Iic]
    rw [hinterior] at hint
    change (A • z).re < 0 at hint
    linarith
  · have hset := Vendored.RiemannDynamics.setOf_dist_le_eq_of_im_eq'
      (a := A • o) (b := A • (γ • o)) him.symm (by rw [hre]; linarith)
    have hmid : ((A • o).re + (A • (γ • o)).re) / 2 = 0 := by
      rw [hre]
      ring
    have hsubset : A • Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ⊆
        {w : ℍ | 0 ≤ w.re} := by
      rintro w ⟨x, hx, rfl⟩
      have hxcomp : dist (A • x) (A • o) ≤ dist (A • x) (A • (γ • o)) := by
        simpa only [dist_smul] using
          (Vendored.RiemannDynamics.mem_dirichletDomain.mp hx) γ
      change A • x ∈ {τ : ℍ | dist τ (A • o) ≤ dist τ (A • (γ • o))} at hxcomp
      rw [hset, hmid] at hxcomp
      exact hxcomp
    have hint : A • z ∈ interior {w : ℍ | 0 ≤ w.re} :=
      interior_mono hsubset hmapint
    have hinterior : interior {w : ℍ | (0 : ℝ) ≤ w.re} = {w : ℍ | 0 < w.re} := by
      change interior (UpperHalfPlane.re ⁻¹' Set.Ici 0) =
        UpperHalfPlane.re ⁻¹' Set.Ioi 0
      calc
        interior (UpperHalfPlane.re ⁻¹' Set.Ici 0) =
            UpperHalfPlane.re ⁻¹' interior (Set.Ici 0) :=
          (UpperHalfPlane.isOpenMap_re.preimage_interior_eq_interior_preimage
            UpperHalfPlane.continuous_re (Set.Ici 0)).symm
        _ = UpperHalfPlane.re ⁻¹' Set.Ioi 0 := by rw [interior_Ici]
    rw [hinterior] at hint
    change 0 < (A • z).re at hint
    linarith

/-- In a finite Dirichlet presentation, a nonidentity bisector section is
exactly part of the topological boundary, not merely a boundary-cover
candidate. -/
theorem frontier_dirichletDomain_eq_finite_bisectors_of_eq
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (F : Finset X.deckGroup)
    (hdir : Vendored.RiemannDynamics.dirichletDomain X.deckGroup o =
      {z : ℍ | ∀ γ ∈ F, dist z o ≤ dist z (γ • o)}) :
    frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) =
      ⋃ γ ∈ F.erase 1,
        Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
          {z : ℍ | dist z o = dist z (γ • o)} := by
  apply Set.Subset.antisymm
  · exact X.frontier_dirichletDomain_subset_finite_bisectors_of_eq o F hdir
  · intro z hz
    obtain ⟨γ, hγcover⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hγ, hzsection⟩ := Set.mem_iUnion.mp hγcover
    exact X.mem_frontier_dirichletDomain_of_mem_bisector o γ
      (Finset.ne_of_mem_erase hγ) hzsection.1 hzsection.2

/-- The global finite presentation yields an exact finite bisector-section
description of the Dirichlet boundary. -/
theorem exists_positive_radius_frontier_dirichletDomain_eq_finite_bisectors
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) :
    ∃ R : ℝ, 0 < R ∧
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) =
        ⋃ γ ∈ (deckElementsDistLE X o (2 * R)).erase 1,
          Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
            {z : ℍ | dist z o = dist z (γ • o)} := by
  obtain ⟨R, hRpos, hdir⟩ :=
    X.exists_positive_radius_dirichletDomain_eq_finite_constraints o
  exact ⟨R, hRpos,
    X.frontier_dirichletDomain_eq_finite_bisectors_of_eq o
      (deckElementsDistLE X o (2 * R)) hdir⟩

/-- The Dirichlet boundary is an exact union of finitely many (possibly
degenerate) bisector segments. The index subtype is finite because it lies
over the finite deck set of bounded displacement. -/
theorem exists_finite_geodSeg_boundary_cover_dirichletDomain
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) :
    ∃ R : ℝ, 0 < R ∧ ∃ p :
      {γ : X.deckGroup // γ ∈ (deckElementsDistLE X o (2 * R)).erase 1 ∧
        (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
          {z : ℍ | dist z o = dist z (γ • o)}).Nonempty} → ℍ × ℍ,
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) =
        ⋃ i, Vendored.RiemannDynamics.geodSeg (p i).1 (p i).2 := by
  classical
  obtain ⟨R, hRpos, hfrontier⟩ :=
    X.exists_positive_radius_frontier_dirichletDomain_eq_finite_bisectors o
  let I := {γ : X.deckGroup // γ ∈ (deckElementsDistLE X o (2 * R)).erase 1 ∧
    (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
      {z : ℍ | dist z o = dist z (γ • o)}).Nonempty}
  have hpair : ∀ i : I, ∃ q : ℍ × ℍ,
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
        {z : ℍ | dist z o = dist z (i.1 • o)} =
          Vendored.RiemannDynamics.geodSeg q.1 q.2 := by
    intro i
    obtain ⟨a, b, hab⟩ :=
      X.exists_geodSeg_eq_finite_boundary_bisector_section o R i.1 i.2.1 i.2.2
    exact ⟨(a, b), hab⟩
  let p : I → ℍ × ℍ := fun i => (hpair i).choose
  refine ⟨R, hRpos, p, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    rw [hfrontier] at hz
    obtain ⟨γ, hγcover⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hγ, hzsection⟩ := Set.mem_iUnion.mp hγcover
    let i : I := ⟨γ, ⟨hγ, ⟨z, hzsection⟩⟩⟩
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [← (hpair i).choose_spec]
    exact hzsection
  · intro z hz
    obtain ⟨i, hzseg⟩ := Set.mem_iUnion.mp hz
    rw [← (hpair i).choose_spec] at hzseg
    rw [hfrontier]
    refine Set.mem_iUnion.mpr ⟨i.1, ?_⟩
    refine Set.mem_iUnion.mpr ⟨i.2.1, hzseg⟩

/-- A finite boundary segment cover retaining each segment's bisector label.
The sections may still be degenerate or overlap; this does not yet construct
cyclic polygon sides or their pairings. -/
theorem exists_finite_geodSeg_boundary_cover_with_sections
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) :
    ∃ R : ℝ, 0 < R ∧ ∃ p :
      {γ : X.deckGroup // γ ∈ (deckElementsDistLE X o (2 * R)).erase 1 ∧
        (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
          {z : ℍ | dist z o = dist z (γ • o)}).Nonempty} → ℍ × ℍ,
      (∀ i, Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
          {z : ℍ | dist z o = dist z (i.1 • o)} =
            Vendored.RiemannDynamics.geodSeg (p i).1 (p i).2) ∧
      frontier (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) =
        ⋃ i, Vendored.RiemannDynamics.geodSeg (p i).1 (p i).2 := by
  classical
  obtain ⟨R, hRpos, hfrontier⟩ :=
    X.exists_positive_radius_frontier_dirichletDomain_eq_finite_bisectors o
  let I := {γ : X.deckGroup // γ ∈ (deckElementsDistLE X o (2 * R)).erase 1 ∧
    (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
      {z : ℍ | dist z o = dist z (γ • o)}).Nonempty}
  have hpair : ∀ i : I, ∃ q : ℍ × ℍ,
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
        {z : ℍ | dist z o = dist z (i.1 • o)} =
          Vendored.RiemannDynamics.geodSeg q.1 q.2 := by
    intro i
    obtain ⟨a, b, hab⟩ :=
      X.exists_geodSeg_eq_finite_boundary_bisector_section o R i.1 i.2.1 i.2.2
    exact ⟨(a, b), hab⟩
  let p : I → ℍ × ℍ := fun i => (hpair i).choose
  have hsection : ∀ i : I,
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
        {z : ℍ | dist z o = dist z (i.1 • o)} =
          Vendored.RiemannDynamics.geodSeg (p i).1 (p i).2 :=
    fun i => (hpair i).choose_spec
  refine ⟨R, hRpos, p, hsection, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    rw [hfrontier] at hz
    obtain ⟨γ, hγcover⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hγ, hzsection⟩ := Set.mem_iUnion.mp hγcover
    let i : I := ⟨γ, ⟨hγ, ⟨z, hzsection⟩⟩⟩
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [← hsection i]
    exact hzsection
  · intro z hz
    obtain ⟨i, hzseg⟩ := Set.mem_iUnion.mp hz
    rw [← hsection i] at hzseg
    rw [hfrontier]
    refine Set.mem_iUnion.mpr ⟨i.1, ?_⟩
    exact Set.mem_iUnion.mpr ⟨i.2.1, hzseg⟩

/-- A compact set can be reached from any of its non-base points by extending
the geodesic from the base point to a terminal boundary point. -/
theorem exists_mem_frontier_geodSeg_of_isCompact
    {K : Set ℍ} (hK : IsCompact K) {o z : ℍ}
    (hz : z ∈ K) (hzo : z ≠ o) :
    ∃ b ∈ frontier K, z ∈ Vendored.RiemannDynamics.geodSeg o b := by
  obtain ⟨R, hbound⟩ :=
    (Metric.isBounded_iff_subset_closedBall o).mp hK.isBounded
  have hdpos : 0 < dist o z := dist_pos.mpr (Ne.symm hzo)
  have hdist_le : dist o z ≤ R := by
    have h : dist z o ≤ R := Metric.mem_closedBall.mp (hbound hz)
    simpa [dist_comm] using h
  let t : ℝ := (R + 1) / dist o z
  have htgt : 1 < t := by
    dsimp [t]
    exact (one_lt_div₀ hdpos).mpr (by linarith)
  have htpos : 0 < t := by linarith
  let y : ℍ := Vendored.RiemannDynamics.geodInterp o z t
  have hdoy : dist o y = t * dist o z := by
    dsimp [y]
    rw [Vendored.RiemannDynamics.dist_geodInterp_left_abs,
      abs_of_pos htpos]
  have hynot : y ∉ K := by
    intro hyK
    have hybound : dist o y ≤ R := by
      have h : dist y o ≤ R := Metric.mem_closedBall.mp (hbound hyK)
      simpa [dist_comm] using h
    rw [hdoy] at hybound
    dsimp [t] at hybound
    rw [div_mul_cancel₀ _ hdpos.ne'] at hybound
    linarith
  have hzy : dist z y = (t - 1) * dist o z := by
    calc
      dist z y = dist (Vendored.RiemannDynamics.geodInterp o z 1)
          (Vendored.RiemannDynamics.geodInterp o z t) := by
            dsimp [y]
            rw [Vendored.RiemannDynamics.geodInterp_one]
      _ = |1 - t| * dist o z :=
        Vendored.RiemannDynamics.dist_geodInterp_pair o z 1 t
      _ = (t - 1) * dist o z := by
        rw [abs_of_nonpos (by linarith : 1 - t ≤ 0)]
        ring
  have hzseg : z ∈ Vendored.RiemannDynamics.geodSeg o y := by
    rw [Vendored.RiemannDynamics.mem_geodSeg, hdoy, hzy]
    ring
  let f : ℝ → ℍ := fun u => Vendored.RiemannDynamics.geodInterp o y u
  have hfcont : Continuous f := by
    dsimp [f]
    exact Vendored.RiemannDynamics.continuous_geodInterp.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  let S : Set ℝ := f ⁻¹' K ∩ Set.Icc (0 : ℝ) 1
  have hSclosed : IsClosed S := by
    dsimp [S]
    exact (hK.isClosed.preimage hfcont).inter isClosed_Icc
  have hScompact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hSclosed (by
      intro u hu
      exact hu.2)
  rw [Vendored.RiemannDynamics.geodSeg_eq_image_geodInterp] at hzseg
  obtain ⟨s, hsIcc, hs_eq⟩ := hzseg
  have hfs : f s = z := by simpa [f] using hs_eq
  have hsS : s ∈ S := by
    change f s ∈ K ∧ s ∈ Set.Icc (0 : ℝ) 1
    exact ⟨hfs ▸ hz, hsIcc⟩
  have hSne : S.Nonempty := ⟨s, hsS⟩
  let q : ℝ := sSup S
  have hqS : q ∈ S := by
    dsimp [q]
    exact hScompact.sSup_mem hSne
  have hqIcc : q ∈ Set.Icc (0 : ℝ) 1 := hqS.2
  have hsleq : s ≤ q := by
    dsimp [q]
    exact le_csSup hScompact.bddAbove hsS
  let b : ℍ := f q
  have hbK : b ∈ K := hqS.1
  have hqne : q ≠ 1 := by
    intro hq
    apply hynot
    have h : f 1 ∈ K := by
      rw [← hq]
      exact hqS.1
    simpa only [f, Vendored.RiemannDynamics.geodInterp_one] using h
  have hqlt : q < 1 := lt_of_le_of_ne hqIcc.2 hqne
  have hbfront : b ∈ frontier K := by
    apply (mem_frontier_iff_notMem_interior hbK).mpr
    intro hbint
    have hpreopen : IsOpen (f ⁻¹' interior K) :=
      isOpen_interior.preimage hfcont
    have hqpre : q ∈ f ⁻¹' interior K := hbint
    obtain ⟨ε, hεpos, hεball⟩ :=
      Metric.isOpen_iff.mp hpreopen q hqpre
    let δ : ℝ := min (ε / 2) ((1 - q) / 2)
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact (lt_min_iff).mpr ⟨by linarith, by linarith⟩
    let u : ℝ := q + δ
    have hult : q < u := by
      dsimp [u]
      linarith
    have hule : u ≤ 1 := by
      have hδle : δ ≤ (1 - q) / 2 := by
        dsimp [δ]
        exact min_le_right _ _
      dsimp [u]
      linarith
    have hulower : 0 ≤ u := hqIcc.1.trans (le_of_lt hult)
    have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hulower, hule⟩
    have huball : u ∈ Metric.ball q ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hδle : δ ≤ ε / 2 := by
        dsimp [δ]
        exact min_le_left _ _
      change |q + δ - q| < ε
      rw [show q + δ - q = δ by ring, abs_of_pos hδpos]
      linarith
    have huK : f u ∈ K := interior_subset (hεball huball)
    have huS : u ∈ S := ⟨huK, huIcc⟩
    exact (not_lt_of_ge (le_csSup hScompact.bddAbove huS)) hult
  refine ⟨b, hbfront, ?_⟩
  rw [Vendored.RiemannDynamics.mem_geodSeg]
  rw [← hfs]
  change dist o (f s) + dist (f s) (f q) = dist o (f q)
  dsimp [f]
  rw [Vendored.RiemannDynamics.dist_geodInterp_left o y hsIcc,
    Vendored.RiemannDynamics.dist_geodInterp_pair,
    Vendored.RiemannDynamics.dist_geodInterp_left o y hqIcc,
    abs_of_nonpos (sub_nonpos.mpr hsleq)]
  ring

/-- The centre of a Dirichlet domain is an interior point: every nonidentity
deck transformation moves it a positive distance. -/
theorem basepoint_mem_interior_dirichletDomain {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) :
    o ∈ interior (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  obtain ⟨R, hRpos, hdir⟩ :=
    X.exists_positive_radius_dirichletDomain_eq_finite_constraints o
  apply X.mem_interior_dirichletDomain_of_strict_finite_constraints o
    (deckElementsDistLE X o (2 * R)) hdir
  intro γ hγ
  rw [dist_self]
  apply dist_pos.mpr
  intro hfix
  exact (Finset.ne_of_mem_erase hγ) (X.free γ o hfix.symm)

/-- The compact Dirichlet domain is covered by finitely many geodesic cones
from its interior centre over its finite family of boundary bisector segments.
The cones may be degenerate; proving a nondegenerate cyclic triangulation
remains a separate polygonal step. -/
theorem exists_finite_hyperbolic_triangle_cover_dirichletDomain
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) :
    ∃ R : ℝ, 0 < R ∧ ∃ p :
      {γ : X.deckGroup // γ ∈ (deckElementsDistLE X o (2 * R)).erase 1} → ℍ × ℍ,
      Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ⊆
        Vendored.RiemannDynamics.hyperbolicTriangle o o o ∪
          ⋃ i, Vendored.RiemannDynamics.hyperbolicTriangle
            o (p i).1 (p i).2 := by
  classical
  obtain ⟨R, hRpos, hboundary⟩ :=
    X.exists_positive_radius_frontier_dirichletDomain_subset_finite_bisectors o
  let I := {γ : X.deckGroup // γ ∈ (deckElementsDistLE X o (2 * R)).erase 1}
  let bisectorSection : X.deckGroup → Set ℍ := fun γ =>
    Vendored.RiemannDynamics.dirichletDomain X.deckGroup o ∩
      {z : ℍ | dist z o = dist z (γ • o)}
  have hpair : ∀ i : I, (bisectorSection i.1).Nonempty → ∃ q : ℍ × ℍ,
      bisectorSection i.1 = Vendored.RiemannDynamics.geodSeg q.1 q.2 := by
    intro i hne
    obtain ⟨a, b, hab⟩ :=
      X.exists_geodSeg_eq_finite_boundary_bisector_section o R i.1 i.2 hne
    exact ⟨(a, b), hab⟩
  let p : I → ℍ × ℍ := fun i =>
    if hne : (bisectorSection i.1).Nonempty then
      (hpair i hne).choose
    else (o, o)
  refine ⟨R, hRpos, p, ?_⟩
  obtain ⟨K, hK, hcover⟩ := X.exists_compact_covering
  have hcompact := X.isCompact_dirichletDomain_of_compact_covering o K hK hcover
  intro z hz
  by_cases hzo : z = o
  · left
    subst z
    exact Vendored.RiemannDynamics.mem_geodCone.mpr ⟨o,
      Vendored.RiemannDynamics.left_mem_geodSeg o o,
      Vendored.RiemannDynamics.left_mem_geodSeg o o⟩
  · right
    obtain ⟨w, hwfront, hzw⟩ :=
      exists_mem_frontier_geodSeg_of_isCompact hcompact hz hzo
    obtain ⟨γ, hγcover⟩ := Set.mem_iUnion.mp (hboundary hwfront)
    obtain ⟨hγ, hwsection⟩ := Set.mem_iUnion.mp hγcover
    let i : I := ⟨γ, hγ⟩
    have hne : (bisectorSection γ).Nonempty := ⟨w, hwsection⟩
    have hpseg : bisectorSection γ = Vendored.RiemannDynamics.geodSeg (p i).1 (p i).2 := by
      dsimp only [p]
      rw [dif_pos hne]
      exact (hpair i hne).choose_spec
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    change z ∈ Vendored.RiemannDynamics.geodCone o
      (Vendored.RiemannDynamics.geodSeg (p i).1 (p i).2)
    apply Vendored.RiemannDynamics.mem_geodCone.mpr
    refine ⟨w, ?_, hzw⟩
    rw [← hpseg]
    exact hwsection

end ClosedHyperbolicSurface

/-- A measurable fundamental domain covered by finitely many nondegenerate
geodesic triangles.  A polygonal construction supplies this certificate by
triangulating its fundamental polygon and proving its side-pairing tiling. -/
structure FiniteTriangleFundamentalDomain {g : ℕ} (X : ClosedHyperbolicSurface g) where
  triangleCount : ℕ
  vertices : Fin triangleCount → ℍ × ℍ × ℍ
  fundamentalDomain : Set ℍ
  isFundamentalDomain : IsFundamentalDomain X.deckGroup fundamentalDomain volume
  coveredByTriangles : fundamentalDomain ⊆ ⋃ i,
    Vendored.RiemannDynamics.hyperbolicTriangle
      (vertices i).1 (vertices i).2.1 (vertices i).2.2
  nondegenerate : ∀ i,
    (vertices i).1 ≠ (vertices i).2.1 ∧
      (vertices i).1 ≠ (vertices i).2.2 ∧
        (vertices i).2.1 ≠ (vertices i).2.2

namespace FiniteTriangleFundamentalDomain

/-- The angular defect of the `i`-th triangle in a finite fundamental-domain
certificate. Its hyperbolic area is exactly this quantity. -/
noncomputable def angleDeficit {g : ℕ} {X : ClosedHyperbolicSurface g}
    (T : FiniteTriangleFundamentalDomain X) (i : Fin T.triangleCount) : ℝ :=
  Real.pi - Vendored.RiemannDynamics.sectorAngle
      (T.vertices i).1 (T.vertices i).2.1 (T.vertices i).2.2
    - Vendored.RiemannDynamics.sectorAngle
      (T.vertices i).2.1 (T.vertices i).1 (T.vertices i).2.2
    - Vendored.RiemannDynamics.sectorAngle
      (T.vertices i).2.2 (T.vertices i).1 (T.vertices i).2.1

/-- Each defect is nonnegative, including triangles whose three vertices
lie on one geodesic. -/
theorem angleDeficit_nonneg {g : ℕ} {X : ClosedHyperbolicSurface g}
    (T : FiniteTriangleFundamentalDomain X) (i : Fin T.triangleCount) :
    0 ≤ T.angleDeficit i := by
  exact geodesicTriangle_angleDeficit_nonneg _ _ _
    (T.nondegenerate i).1 (T.nondegenerate i).2.1
    (T.nondegenerate i).2.2

/-- Each triangle's angular defect is at most `π`: the sector angles are
nonnegative, so subtracting them from `π` cannot increase the result. -/
theorem angleDeficit_le_pi {g : ℕ} {X : ClosedHyperbolicSurface g}
    (T : FiniteTriangleFundamentalDomain X) (i : Fin T.triangleCount) :
    T.angleDeficit i ≤ Real.pi := by
  unfold angleDeficit
  have h₁ := Vendored.RiemannDynamics.sectorAngle_nonneg
    (T.vertices i).1 (T.vertices i).2.1 (T.vertices i).2.2
  have h₂ := Vendored.RiemannDynamics.sectorAngle_nonneg
    (T.vertices i).2.1 (T.vertices i).1 (T.vertices i).2.2
  have h₃ := Vendored.RiemannDynamics.sectorAngle_nonneg
    (T.vertices i).2.2 (T.vertices i).1 (T.vertices i).2.1
  linarith

/-- The certificate alone bounds total defect by `π` per listed triangle.
This estimate is independent of genus and does not replace the missing
vertex-incidence and Euler-characteristic data of a triangulation. -/
theorem sum_angleDeficit_le_triangleCount_mul_pi {g : ℕ}
    {X : ClosedHyperbolicSurface g} (T : FiniteTriangleFundamentalDomain X) :
    (∑ i : Fin T.triangleCount, T.angleDeficit i) ≤
      (T.triangleCount : ℝ) * Real.pi := by
  calc
    (∑ i : Fin T.triangleCount, T.angleDeficit i) ≤
        ∑ _i : Fin T.triangleCount, Real.pi :=
      Finset.sum_le_sum (fun i _ ↦ T.angleDeficit_le_pi i)
    _ = (T.triangleCount : ℝ) * Real.pi := by simp [Finset.sum_const, nsmul_eq_mul]

/-- The covolume is bounded by the exact sum of triangular angular defects.
This is the measure-theoretic handoff for a polygonal Gauss--Bonnet argument;
it does not assume or assert that a genus-linear certificate exists. -/
theorem covolume_le_sum_angleDeficit {g : ℕ}
    {X : ClosedHyperbolicSurface g} (T : FiniteTriangleFundamentalDomain X) :
    covolume X.deckGroup ℍ volume ≤
      ∑ i : Fin T.triangleCount, ENNReal.ofReal (T.angleDeficit i) := by
  rw [X.covolume_eq_dirichletDomain_volume (I : ℍ)]
  letI : Countable (SurfaceGroup g) := by
    change Countable (Quotient (QuotientGroup.leftRel
      (Subgroup.normalClosure ({surfaceRelator g} : Set (FreeGroup (SurfaceGenerator g))))))
    infer_instance
  letI : Countable X.deckGroup :=
    (Equiv.countable_iff X.marking.toEquiv).mpr inferInstance
  calc
    volume (Vendored.RiemannDynamics.dirichletDomain X.deckGroup (I : ℍ)) =
        volume T.fundamentalDomain :=
      (X.dirichletDomain_isFundamentalDomain I).measure_eq T.isFundamentalDomain
    _ ≤ volume (⋃ i, Vendored.RiemannDynamics.hyperbolicTriangle
          (T.vertices i).1 (T.vertices i).2.1 (T.vertices i).2.2) :=
      measure_mono T.coveredByTriangles
    _ ≤ ∑' i : Fin T.triangleCount,
          volume (Vendored.RiemannDynamics.hyperbolicTriangle
            (T.vertices i).1 (T.vertices i).2.1 (T.vertices i).2.2) :=
      measure_iUnion_le _
    _ = ∑ i : Fin T.triangleCount, ENNReal.ofReal (T.angleDeficit i) := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro i _
      exact volume_geodesicTriangle_eq_angleDeficit _ _ _
        (T.nondegenerate i).1 (T.nondegenerate i).2.1
        (T.nondegenerate i).2.2

/-- Real-valued angular-defect covolume bound, ready for an Euler-characteristic
calculation of the total defect. -/
theorem covolume_toReal_le_sum_angleDeficit {g : ℕ}
    {X : ClosedHyperbolicSurface g} (T : FiniteTriangleFundamentalDomain X) :
    (covolume X.deckGroup ℍ volume).toReal ≤
      ∑ i : Fin T.triangleCount, T.angleDeficit i := by
  have h := T.covolume_le_sum_angleDeficit
  have htop : (∑ i : Fin T.triangleCount,
      ENNReal.ofReal (T.angleDeficit i)) ≠ ∞ := by
    exact ENNReal.sum_ne_top.mpr (fun i _ ↦ ENNReal.ofReal_ne_top)
  have hreal := ENNReal.toReal_mono htop h
  simpa [ENNReal.toReal_sum, ENNReal.toReal_ofReal (T.angleDeficit_nonneg _)]
    using hreal

/-- The canonical Dirichlet fundamental domain has no more area than the
finite triangular fundamental domain certificate. -/
theorem volume_dirichletDomain_le_fin_mul_pi {g : ℕ}
    {X : ClosedHyperbolicSurface g} (T : FiniteTriangleFundamentalDomain X)
    (o : ℍ) :
    volume (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) ≤
      T.triangleCount * ENNReal.ofReal Real.pi := by
  letI : Countable (SurfaceGroup g) := by
    change Countable (Quotient (QuotientGroup.leftRel
      (Subgroup.normalClosure ({surfaceRelator g} : Set (FreeGroup (SurfaceGenerator g))))))
    infer_instance
  letI : Countable X.deckGroup :=
    (Equiv.countable_iff X.marking.toEquiv).mpr inferInstance
  calc
    volume (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) =
        volume T.fundamentalDomain :=
      (X.dirichletDomain_isFundamentalDomain o).measure_eq T.isFundamentalDomain
    _ ≤ T.triangleCount * ENNReal.ofReal Real.pi := by
      apply volume_le_fin_mul_pi_of_finite_cover T.fundamentalDomain
        (fun i ↦ Vendored.RiemannDynamics.hyperbolicTriangle
          (T.vertices i).1 (T.vertices i).2.1 (T.vertices i).2.2)
      · exact T.coveredByTriangles
      · intro i
        exact volume_hyperbolicTriangle_le_pi _ _ _
          (T.nondegenerate i).1 (T.nondegenerate i).2.1 (T.nondegenerate i).2.2

/-- Real-valued form of the finite-triangle Dirichlet-area bound. -/
theorem volume_real_dirichletDomain_le_fin_mul_pi {g : ℕ}
    {X : ClosedHyperbolicSurface g} (T : FiniteTriangleFundamentalDomain X)
    (o : ℍ) :
    volume.real (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) ≤
      (T.triangleCount : ℝ) * Real.pi := by
  have h := T.volume_dirichletDomain_le_fin_mul_pi o
  have htop : T.triangleCount * ENNReal.ofReal Real.pi ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono htop h
  simpa [Measure.real, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal Real.pi_pos.le] using hreal

/-- A finite geodesic triangulation of a fundamental polygon supplies the
scalar Dirichlet-area estimate consumed by the packing argument. -/
theorem systole_le_max_log_of_fin_mul_pi {g : ℕ}
    {X : ClosedHyperbolicSurface g} (T : FiniteTriangleFundamentalDomain X)
    (o : ℍ) :
    X.systole ≤ max (2 * Real.log 2)
      (2 * Real.log (16 * ((T.triangleCount : ℝ) * Real.pi))) :=
  systole_le_max_log_of_dirichlet_volume_le X o
    (T.volume_real_dirichletDomain_le_fin_mul_pi o)

end FiniteTriangleFundamentalDomain

end SystolicGrowth

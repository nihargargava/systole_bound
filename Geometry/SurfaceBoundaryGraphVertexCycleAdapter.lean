module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceBoundaryGraphWicksCertificate
public import Geometry.DirichletPolygonBridge

@[expose] public section

/-!
# Adapting a contact cycle to native cyclic sides

The imported Dirichlet contact cycle can be read in the native cyclic-side
alphabet: each consecutive contact pair determines one of the already
enumerated actual sides, and the common polygon vertex is an endpoint of that
side. This adapter deliberately records both endpoint orientations. Identifying
which orientation agrees with the native successor, and proving the resulting
list exhausts a quotient-vertex fiber, are separate obligations.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- A side joining two tiles in the contact set of a polygon vertex is an
actual native cyclic side. The vertex is one of that side's original cyclic
endpoints after translating the first tile back to the base tile. -/
theorem exists_intrinsicCyclicEdge_of_contact_side
    (B : DirichletBoundarySegments X o) {v : ℍ}
    (hv : v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o)
    {γ δ : X.deckGroup}
    (hγ : γ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v)
    (hδ : δ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v)
    (hside : Vendored.RiemannDynamics.IsSideElement X.deckGroup o (γ⁻¹ * δ)) :
    ∃ i : Fin B.intrinsicBoundaryRadialCuts.card,
      (B.intrinsicCyclicEdge i).1.1.1 = γ⁻¹ * δ ∧
        (γ⁻¹ • v = B.intrinsicCyclicVertex i ∨
          γ⁻¹ • v = B.intrinsicCyclicVertex
            (finRotate B.intrinsicBoundaryRadialCuts.card i)) := by
  classical
  let side := Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o (γ⁻¹ * δ)
  have hpolygonSide : side ∈ Vendored.RiemannDynamics.polygonSides X.deckGroup o :=
    ⟨γ⁻¹ * δ, hside, rfl⟩
  obtain ⟨i, hi⟩ := B.exists_intrinsicCyclicClosedEdge_eq_polygonSide hpolygonSide
  have hsets : side = Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o
      (B.intrinsicCyclicEdge i).1.1.1 := by
    calc
      side = B.closedEdgeImage B.intrinsicCornerCuts (B.intrinsicCyclicEdge i) := hi.symm
      _ = Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o
          (B.intrinsicCyclicEdge i).1.1.1 :=
        B.intrinsicCyclicClosedEdge_eq_dirichletSideSet i
  have hlabelCenters : (γ⁻¹ * δ) • o = (B.intrinsicCyclicEdge i).1.1.1 • o :=
    Vendored.RiemannDynamics.smul_basepoint_eq_of_sideSet_eq
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
      X.deck_fixing_point_acts_trivially hside
      (B.intrinsicCyclicEdge_isSideElement i) hsets
  have hlabel : (B.intrinsicCyclicEdge i).1.1.1 = γ⁻¹ * δ :=
    (X.deck_smul_injective o) hlabelCenters.symm
  have hpoint : γ⁻¹ • v ∈ side :=
    Vendored.RiemannDynamics.smul_mem_dirichletSideSet_of_contact_pair hγ hδ
  have hvertex : γ⁻¹ • v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o :=
    Vendored.RiemannDynamics.smul_mem_polygonVertices hv hγ
  obtain ⟨R, hdense⟩ := X.exists_dirichlet_orbit_density_bound o
  have hendpoint : Vendored.RiemannDynamics.IsSegEndpoint side (γ⁻¹ • v) :=
    Vendored.RiemannDynamics.isSegEndpoint_of_vertex
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
      X.deck_fixing_point_acts_trivially
      (X.basepoint_mem_interior_dirichletDomain o) hdense hvertex hpolygonSide hpoint
  have hgeodSeg :
      Vendored.RiemannDynamics.geodSeg (B.intrinsicCyclicVertex i)
        (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i)) = side := by
    rw [← B.intrinsicCyclicEdge_closedImage_eq_geodSeg i,
      B.intrinsicCyclicClosedEdge_eq_dirichletSideSet i, hlabel]
  rw [← hgeodSeg] at hendpoint
  rcases (Vendored.RiemannDynamics.isSegEndpoint_geodSeg_iff
      (B.intrinsicCyclicVertex_next_ne i)).mp hendpoint with hstart | hend
  · exact ⟨i, hlabel, Or.inl hstart⟩
  · exact ⟨i, hlabel, Or.inr hend⟩

/-- Among contact centers around `v`, a side-neighbor of the center `e a` is
one of the two cyclic neighbors. The proof uses the actual two-side theorem
at the vertex, not a combinatorial transitivity premise. -/
theorem contact_side_neighbor_of_cycle
    {v : ℍ}
    (hv : v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o)
    {n : ℕ} {e : ℕ → X.deckGroup}
    (hn : 3 ≤ n)
    (hperiodic : ∀ k, e (k + n) = e k)
    (hcontact : ∀ k, e k ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v)
    (huniq : ∀ γ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v,
      ∃! k, k < n ∧ γ • o = e k • o)
    (hadjacent : ∀ k, Vendored.RiemannDynamics.IsSideElement X.deckGroup o
      ((e k)⁻¹ * e (k + 1)))
    {a : ℕ} (ha : a < n) {δ : X.deckGroup}
    (hδ : δ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v)
    (hside : Vendored.RiemannDynamics.IsSideElement X.deckGroup o ((e a)⁻¹ * δ)) :
    δ = e (a + 1) ∨ δ = e (a + (n - 1)) := by
  classical
  let prev := a + (n - 1)
  have hprev_next : prev + 1 = a + n := by
    dsimp [prev]
    omega
  have hprev_center : e (prev + 1) = e a := by
    rw [hprev_next, hperiodic]
  have hback : Vendored.RiemannDynamics.IsSideElement X.deckGroup o
      ((e a)⁻¹ * e prev) := by
    have hh := (hadjacent prev).inv
    rw [mul_inv_rev, inv_inv, hprev_center] at hh
    exact hh
  let w := (e a)⁻¹ • v
  have hwvertex : w ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o :=
    Vendored.RiemannDynamics.smul_mem_polygonVertices hv (hcontact a)
  have hforwardPoint : w ∈
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o ((e a)⁻¹ * e (a + 1)) :=
    Vendored.RiemannDynamics.smul_mem_dirichletSideSet_of_contact_pair
      (hcontact a) (hcontact (a + 1))
  have hbackPoint : w ∈
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o ((e a)⁻¹ * e prev) :=
    Vendored.RiemannDynamics.smul_mem_dirichletSideSet_of_contact_pair
      (hcontact a) (hcontact prev)
  have hsidePoint : w ∈
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o ((e a)⁻¹ * δ) :=
    Vendored.RiemannDynamics.smul_mem_dirichletSideSet_of_contact_pair
      (hcontact a) hδ
  obtain ⟨R, hdense⟩ := X.exists_dirichlet_orbit_density_bound o
  have hbase := X.basepoint_mem_interior_dirichletDomain o
  have hforwardPoly :
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o ((e a)⁻¹ * e (a + 1)) ∈
        Vendored.RiemannDynamics.polygonSides X.deckGroup o :=
    ⟨(e a)⁻¹ * e (a + 1), hadjacent a, rfl⟩
  have hbackPoly :
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o ((e a)⁻¹ * e prev) ∈
        Vendored.RiemannDynamics.polygonSides X.deckGroup o :=
    ⟨(e a)⁻¹ * e prev, hback, rfl⟩
  have hsidePoly :
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o ((e a)⁻¹ * δ) ∈
        Vendored.RiemannDynamics.polygonSides X.deckGroup o :=
    ⟨(e a)⁻¹ * δ, hside, rfl⟩
  have hforwardEnd : Vendored.RiemannDynamics.IsSegEndpoint
      (Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o ((e a)⁻¹ * e (a + 1))) w :=
    Vendored.RiemannDynamics.isSegEndpoint_of_vertex
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
      X.deck_fixing_point_acts_trivially hbase hdense hwvertex hforwardPoly hforwardPoint
  have hbackEnd : Vendored.RiemannDynamics.IsSegEndpoint
      (Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o ((e a)⁻¹ * e prev)) w :=
    Vendored.RiemannDynamics.isSegEndpoint_of_vertex
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
      X.deck_fixing_point_acts_trivially hbase hdense hwvertex hbackPoly hbackPoint
  have hsideEnd : Vendored.RiemannDynamics.IsSegEndpoint
      (Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o ((e a)⁻¹ * δ)) w :=
    Vendored.RiemannDynamics.isSegEndpoint_of_vertex
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
      X.deck_fixing_point_acts_trivially hbase hdense hwvertex hsidePoly hsidePoint
  obtain ⟨S₁, hS₁, S₂, hS₂, hS₁S₂, hS₁end, hS₂end, honlyTwo⟩ :=
    Vendored.RiemannDynamics.exists_two_sides_at_vertex
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
      X.deck_fixing_point_acts_trivially hbase hdense hwvertex
  have hforwardAmong := honlyTwo _ hforwardPoly hforwardEnd
  have hbackAmong := honlyTwo _ hbackPoly hbackEnd
  have hsideAmong := honlyTwo _ hsidePoly hsideEnd
  have hforwardNeBack :
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o ((e a)⁻¹ * e (a + 1)) ≠
        Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o ((e a)⁻¹ * e prev) := by
    intro heq
    have hcenters := Vendored.RiemannDynamics.smul_basepoint_eq_of_sideSet_eq
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
      X.deck_fixing_point_acts_trivially (hadjacent a) hback heq
    have hcenters := congrArg (e a • ·) hcenters
    rw [← mul_smul, ← mul_smul, mul_inv_cancel_left, mul_inv_cancel_left] at hcenters
    have hemod : ∀ k, e k = e (k % n) := by
      intro k
      conv_lhs => rw [show k = k % n + n * (k / n) from (Nat.mod_add_div k n).symm]
      generalize k / n = q
      induction q with
      | zero => simp
      | succ q ih =>
          rw [Nat.mul_succ, ← Nat.add_assoc, hperiodic, ih]
    have hforwardIndex : (a + 1) % n < n := Nat.mod_lt _ (by omega)
    have hbackIndex : prev % n < n := Nat.mod_lt _ (by omega)
    obtain ⟨r, hr, hruniq⟩ := huniq (e (a + 1)) (hcontact (a + 1))
    have hrforward : (a + 1) % n = r := hruniq _
      ⟨hforwardIndex, congrArg (fun z : X.deckGroup => z • o) (hemod (a + 1))⟩
    have hrback : prev % n = r := hruniq _
      ⟨hbackIndex,
        hcenters.trans (congrArg (fun z : X.deckGroup => z • o) (hemod prev))⟩
    have hmods : (a + 1) % n ≠ prev % n := by
      dsimp [prev]
      by_cases ha0 : a = 0
      · subst a
        simp only [Nat.zero_add]
        rw [Nat.mod_eq_of_lt (by omega : 1 < n)]
        rw [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
        omega
      · have ha : 0 < a := Nat.pos_of_ne_zero ha0
        have hprevmod : (a + (n - 1)) % n = a - 1 := by
          have heq : a + (n - 1) = (a - 1) + n := by omega
          rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : a - 1 < n)]
        by_cases hlast : a + 1 = n
        · rw [hlast, Nat.mod_self, hprevmod]
          omega
        · rw [Nat.mod_eq_of_lt (by omega : a + 1 < n), hprevmod]
          omega
    exact hmods (hrforward.trans hrback.symm)
  have hsideIsOne :
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o ((e a)⁻¹ * δ) =
        Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o ((e a)⁻¹ * e (a + 1)) ∨
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o ((e a)⁻¹ * δ) =
        Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o ((e a)⁻¹ * e prev) := by
    rcases hforwardAmong with hF | hF <;>
      rcases hbackAmong with hB | hB
    · exact (hforwardNeBack (hF.trans hB.symm)).elim
    · rcases hsideAmong with hQ | hQ
      · exact Or.inl (hQ.trans hF.symm)
      · exact Or.inr (hQ.trans hB.symm)
    · rcases hsideAmong with hQ | hQ
      · exact Or.inr (hQ.trans hB.symm)
      · exact Or.inl (hQ.trans hF.symm)
    · exact (hforwardNeBack (hF.trans hB.symm)).elim
  rcases hsideIsOne with hq | hq
  · have hcenters := Vendored.RiemannDynamics.smul_basepoint_eq_of_sideSet_eq
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
      X.deck_fixing_point_acts_trivially hside (hadjacent a) hq
    have hlabels := X.deck_smul_injective o hcenters
    left
    calc
      δ = e a * ((e a)⁻¹ * δ) := by group
      _ = e a * ((e a)⁻¹ * e (a + 1)) := by rw [hlabels]
      _ = e (a + 1) := by group
  · have hcenters := Vendored.RiemannDynamics.smul_basepoint_eq_of_sideSet_eq
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
      X.deck_fixing_point_acts_trivially hside hback hq
    have hlabels := X.deck_smul_injective o hcenters
    right
    calc
      δ = e a * ((e a)⁻¹ * δ) := by group
      _ = e a * ((e a)⁻¹ * e prev) := by rw [hlabels]
      _ = e prev := by group

/-- The only native cyclic sides incident to a specified polygon vertex are
the outgoing side and the incoming side immediately before it. This follows
from the imported exact-two-sides theorem and the proved native side
enumeration, rather than from a side-incidence assumption. -/
theorem intrinsic_side_endpoint_index
    (B : DirichletBoundarySegments X o) (q j : Fin B.intrinsicBoundaryRadialCuts.card)
    {v : ℍ}
    (hv : v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o)
    (hq : v = B.intrinsicCyclicVertex q)
    (hj : Vendored.RiemannDynamics.IsSegEndpoint
      (Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o
        (B.intrinsicCyclicEdge j).1.1.1) v) :
    j = q ∨ j = (finRotate B.intrinsicBoundaryRadialCuts.card).symm q := by
  classical
  let prev := (finRotate B.intrinsicBoundaryRadialCuts.card).symm q
  let side (i : Fin B.intrinsicBoundaryRadialCuts.card) :=
    Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o
      (B.intrinsicCyclicEdge i).1.1.1
  have hprev : finRotate B.intrinsicBoundaryRadialCuts.card prev = q := by
    exact Equiv.apply_symm_apply
      (finRotate B.intrinsicBoundaryRadialCuts.card) q
  have houtPoly : side q ∈ Vendored.RiemannDynamics.polygonSides X.deckGroup o :=
    ⟨(B.intrinsicCyclicEdge q).1.1.1, B.intrinsicCyclicEdge_isSideElement q, rfl⟩
  have hinPoly : side prev ∈ Vendored.RiemannDynamics.polygonSides X.deckGroup o :=
    ⟨(B.intrinsicCyclicEdge prev).1.1.1, B.intrinsicCyclicEdge_isSideElement prev, rfl⟩
  have hqOut : v ∈ side q := by
    rw [hq]
    change B.intrinsicCyclicVertex q ∈
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o
        (B.intrinsicCyclicEdge q).1.1.1
    rw [← B.intrinsicCyclicClosedEdge_eq_dirichletSideSet q,
      B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
    exact Vendored.RiemannDynamics.left_mem_geodSeg _ _
  have hqIn : v ∈ side prev := by
    rw [hq]
    change B.intrinsicCyclicVertex q ∈
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o
        (B.intrinsicCyclicEdge prev).1.1.1
    rw [← B.intrinsicCyclicClosedEdge_eq_dirichletSideSet prev,
      B.intrinsicCyclicEdge_closedImage_eq_geodSeg, hprev]
    exact Vendored.RiemannDynamics.right_mem_geodSeg _ _
  obtain ⟨R, hdense⟩ := X.exists_dirichlet_orbit_density_bound o
  have hbase := X.basepoint_mem_interior_dirichletDomain o
  have houtEnd := Vendored.RiemannDynamics.isSegEndpoint_of_vertex
    (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
    X.deck_fixing_point_acts_trivially hbase hdense hv houtPoly hqOut
  have hinEnd := Vendored.RiemannDynamics.isSegEndpoint_of_vertex
    (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
    X.deck_fixing_point_acts_trivially hbase hdense hv hinPoly hqIn
  obtain ⟨S₁, hS₁, S₂, hS₂, hS₁S₂, hS₁end, hS₂end, honlyTwo⟩ :=
    Vendored.RiemannDynamics.exists_two_sides_at_vertex
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
      X.deck_fixing_point_acts_trivially hbase hdense hv
  have houtAmong := honlyTwo (side q) houtPoly houtEnd
  have hinAmong := honlyTwo (side prev) hinPoly hinEnd
  have hsideAmong := honlyTwo (side j)
    ⟨(B.intrinsicCyclicEdge j).1.1.1, B.intrinsicCyclicEdge_isSideElement j, rfl⟩ hj
  have houtNe : side q ≠ side prev := by
    intro heq
    have hcenters := Vendored.RiemannDynamics.smul_basepoint_eq_of_sideSet_eq
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
      X.deck_fixing_point_acts_trivially
      (B.intrinsicCyclicEdge_isSideElement q)
      (B.intrinsicCyclicEdge_isSideElement prev) heq
    have hlabels := X.deck_smul_injective o hcenters
    have hindices := B.intrinsicCyclicEdge_label_injective hlabels
    have hrot : finRotate B.intrinsicBoundaryRadialCuts.card q = q := by
      calc
        finRotate B.intrinsicBoundaryRadialCuts.card q =
            finRotate B.intrinsicBoundaryRadialCuts.card prev := by
          rw [hindices]
        _ = q := hprev
    exact B.intrinsicCyclicVertex_next_ne q
      (congrArg B.intrinsicCyclicVertex hrot.symm)
  have hsideEq : side j = side q ∨ side j = side prev := by
    rcases houtAmong with hout | hout <;> rcases hinAmong with hin | hin
    · exact (houtNe (hout.trans hin.symm)).elim
    · rcases hsideAmong with hside | hside
      · exact Or.inl (hside.trans hout.symm)
      · exact Or.inr (hside.trans hin.symm)
    · rcases hsideAmong with hside | hside
      · exact Or.inr (hside.trans hin.symm)
      · exact Or.inl (hside.trans hout.symm)
    · exact (houtNe (hout.trans hin.symm)).elim
  rcases hsideEq with heq | heq
  · left
    have hcenters := Vendored.RiemannDynamics.smul_basepoint_eq_of_sideSet_eq
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
      X.deck_fixing_point_acts_trivially
      (B.intrinsicCyclicEdge_isSideElement j)
      (B.intrinsicCyclicEdge_isSideElement q) heq
    exact B.intrinsicCyclicEdge_label_injective (X.deck_smul_injective o hcenters)
  · right
    have hcenters := Vendored.RiemannDynamics.smul_basepoint_eq_of_sideSet_eq
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
      X.deck_fixing_point_acts_trivially
      (B.intrinsicCyclicEdge_isSideElement j)
      (B.intrinsicCyclicEdge_isSideElement prev) heq
    exact B.intrinsicCyclicEdge_label_injective (X.deck_smul_injective o hcenters)

/-- At consecutive contact edges, the endpoint sign of the native side labels
cannot flip. The paired old side and the next side are the two distinct
native sides at the intervening polygon corner. -/
theorem contact_cycle_endpoint_orientation_step
    (B : DirichletBoundarySegments X o) {v : ℍ}
    (hv : v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o)
    {n : ℕ} {e : ℕ → X.deckGroup}
    (hn : 3 ≤ n)
    (hperiodic : ∀ k, e (k + n) = e k)
    (hcontact : ∀ k, e k ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v)
    (huniq : ∀ γ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v,
      ∃! k, k < n ∧ γ • o = e k • o)
    {s : ℕ → Fin B.intrinsicBoundaryRadialCuts.card}
    (hsideLabel : ∀ k, (B.intrinsicCyclicEdge (s k)).1.1.1 = (e k)⁻¹ * e (k + 1))
    (hendpoint : ∀ k,
      (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k) ∨
        (e k)⁻¹ • v = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (s k)))
    (k : ℕ) :
    ((e k)⁻¹ • v = B.intrinsicCyclicVertex (s k)) ↔
      ((e (k + 1))⁻¹ • v = B.intrinsicCyclicVertex (s (k + 1))) := by
  classical
  let p := (e k)⁻¹ • v
  let pn := (e (k + 1))⁻¹ • v
  let r := B.intrinsicCyclicPairing (s k)
  have htransport : pn = (B.intrinsicCyclicEdge (s k)).1.1.1⁻¹ • p := by
    dsimp [pn, p]
    rw [← mul_smul, hsideLabel k]
    have hgroup : ((e k)⁻¹ * e (k + 1))⁻¹ * (e k)⁻¹ = (e (k + 1))⁻¹ := by
      group
    rw [hgroup]
  have hpnVertex : pn ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o :=
    Vendored.RiemannDynamics.smul_mem_polygonVertices hv (hcontact (k + 1))
  have hnextPoint : pn ∈
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o
        (B.intrinsicCyclicEdge (s (k + 1))).1.1.1 := by
    rcases hendpoint (k + 1) with hstart | hend
    · rw [← B.intrinsicCyclicClosedEdge_eq_dirichletSideSet (s (k + 1)),
        B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
      simpa only [pn, hstart] using Vendored.RiemannDynamics.left_mem_geodSeg
        (B.intrinsicCyclicVertex (s (k + 1)))
        (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card
          (s (k + 1))))
    · rw [← B.intrinsicCyclicClosedEdge_eq_dirichletSideSet (s (k + 1)),
        B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
      simpa only [pn, hend] using Vendored.RiemannDynamics.right_mem_geodSeg
        (B.intrinsicCyclicVertex (s (k + 1)))
        (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card
          (s (k + 1))))
  have hnextPoly : Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o
      (B.intrinsicCyclicEdge (s (k + 1))).1.1.1 ∈
        Vendored.RiemannDynamics.polygonSides X.deckGroup o :=
    ⟨(B.intrinsicCyclicEdge (s (k + 1))).1.1.1,
      B.intrinsicCyclicEdge_isSideElement (s (k + 1)), rfl⟩
  obtain ⟨R, hdense⟩ := X.exists_dirichlet_orbit_density_bound o
  have hbase := X.basepoint_mem_interior_dirichletDomain o
  have hnextEnd := Vendored.RiemannDynamics.isSegEndpoint_of_vertex
    (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
    X.deck_fixing_point_acts_trivially hbase hdense hpnVertex hnextPoly hnextPoint
  have htwoapart : e k • o ≠ e (k + 2) • o := by
    intro heq
    have hemod : ∀ x, e (x % n) = e x := by
      intro x
      conv_rhs => rw [show x = x % n + n * (x / n) from (Nat.mod_add_div x n).symm]
      generalize x / n = q
      induction q with
      | zero => simp
      | succ q ih =>
          rw [Nat.mul_succ, ← Nat.add_assoc, hperiodic, ih]
    obtain ⟨a, ha, huniqCenter⟩ := huniq (e k) (hcontact k)
    have hfirst : k % n = a := huniqCenter _
      ⟨Nat.mod_lt _ (by omega), by
        exact congrArg (fun γ : X.deckGroup => γ • o) (hemod k).symm⟩
    have hsecond : (k + 2) % n = a := huniqCenter _
      ⟨Nat.mod_lt _ (by omega), by
        exact heq.trans (congrArg (fun γ : X.deckGroup => γ • o) (hemod (k + 2)).symm)⟩
    have hmod : k % n = (k + 2) % n := hfirst.trans hsecond.symm
    have hmods : k % n ≠ (k + 2) % n := by
      intro h
      have hdvd : n ∣ (k + 2) - k :=
        (Nat.modEq_iff_dvd' (by omega : k ≤ k + 2)).mp h
      have hle := Nat.le_of_dvd (by omega : 0 < (k + 2) - k) hdvd
      omega
    exact hmods hmod
  have hsideNe : r ≠ s (k + 1) := by
    intro heq
    have hlabels :
        ((e k)⁻¹ * e (k + 1))⁻¹ = (e (k + 1))⁻¹ * e (k + 2) := by
      calc
        ((e k)⁻¹ * e (k + 1))⁻¹ =
            (B.intrinsicCyclicEdge r).1.1.1 := by
              rw [B.intrinsicCyclicEdge_pairing, B.inverseIntrinsicOpenEdge_label,
                hsideLabel k]
        _ = (B.intrinsicCyclicEdge (s (k + 1))).1.1.1 :=
          congrArg (fun i => (B.intrinsicCyclicEdge i).1.1.1) heq
        _ = (e (k + 1))⁻¹ * e (k + 2) := hsideLabel (k + 1)
    have hcancel : (e (k + 1))⁻¹ * e k = (e (k + 1))⁻¹ * e (k + 2) := by
      simpa only [mul_inv_rev, inv_inv] using hlabels
    have hcenters : e k • o = e (k + 2) • o := by
      exact congrArg (fun γ : X.deckGroup => γ • o) (mul_left_cancel hcancel)
    exact htwoapart hcenters
  rcases hendpoint k with hstart | hend
  · let q := finRotate B.intrinsicBoundaryRadialCuts.card r
    have hq : pn = B.intrinsicCyclicVertex q := by
      calc
        pn = (B.intrinsicCyclicEdge (s k)).1.1.1⁻¹ • p := htransport
        _ = B.intrinsicCyclicVertex q := by
          have hstart' : p = B.intrinsicCyclicVertex (s k) := hstart
          rw [hstart']
          simpa only [q] using (B.inverse_smul_intrinsicCyclicVertices_eq_reverse (s k)).1
    have hr : r = (finRotate B.intrinsicBoundaryRadialCuts.card).symm q := by
      dsimp [q]
      exact (Equiv.symm_apply_apply
        (finRotate B.intrinsicBoundaryRadialCuts.card) r).symm
    have hindex := B.intrinsic_side_endpoint_index q (s (k + 1)) hpnVertex hq hnextEnd
    rcases hindex with hnextq | hnextprev
    · have hstartNext : pn = B.intrinsicCyclicVertex (s (k + 1)) := by
        rw [hnextq]
        exact hq
      exact ⟨fun _ => hstartNext, fun _ => hstart⟩
    · exact (hsideNe (hnextprev.trans hr.symm).symm).elim
  · let q := r
    have hq : pn = B.intrinsicCyclicVertex q := by
      calc
        pn = (B.intrinsicCyclicEdge (s k)).1.1.1⁻¹ • p := htransport
        _ = B.intrinsicCyclicVertex q := by
          have hend' : p = B.intrinsicCyclicVertex
              (finRotate B.intrinsicBoundaryRadialCuts.card (s k)) := hend
          rw [hend']
          simpa only [q] using (B.inverse_smul_intrinsicCyclicVertices_eq_reverse (s k)).2
    have hr : r = q := rfl
    have hindex := B.intrinsic_side_endpoint_index q (s (k + 1)) hpnVertex hq hnextEnd
    rcases hindex with hnextq | hnextprev
    · exact (hsideNe (hnextq.trans hr.symm).symm).elim
    · have hterminalNext : pn = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (s (k + 1))) := by
        have hrot : finRotate B.intrinsicBoundaryRadialCuts.card
            (s (k + 1)) = q := by
          rw [hnextprev]
          exact Equiv.apply_symm_apply
            (finRotate B.intrinsicBoundaryRadialCuts.card) q
        exact hq.trans (congrArg B.intrinsicCyclicVertex hrot.symm)
      have hnotStartK : ¬ p = B.intrinsicCyclicVertex (s k) := by
        intro hs
        exact B.intrinsicCyclicVertex_next_ne (s k) (hs.symm.trans hend)
      have hnotStartNext : ¬ pn = B.intrinsicCyclicVertex (s (k + 1)) := by
        intro hs
        exact B.intrinsicCyclicVertex_next_ne (s (k + 1))
          (hs.symm.trans hterminalNext)
      exact ⟨fun hs => (hnotStartK hs).elim, fun hs => (hnotStartNext hs).elim⟩

/-- The local endpoint bit is constant around the complete periodic contact
cycle. Thus all of its native side labels use the same endpoint convention. -/
theorem contact_cycle_endpoint_orientation_constant
    (B : DirichletBoundarySegments X o) {v : ℍ}
    (hv : v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o)
    {n : ℕ} {e : ℕ → X.deckGroup}
    (hn : 3 ≤ n)
    (hperiodic : ∀ k, e (k + n) = e k)
    (hcontact : ∀ k, e k ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v)
    (huniq : ∀ γ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v,
      ∃! k, k < n ∧ γ • o = e k • o)
    {s : ℕ → Fin B.intrinsicBoundaryRadialCuts.card}
    (hsideLabel : ∀ k, (B.intrinsicCyclicEdge (s k)).1.1.1 = (e k)⁻¹ * e (k + 1))
    (hendpoint : ∀ k,
      (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k) ∨
        (e k)⁻¹ • v = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (s k))) :
    ∀ k, ((e k)⁻¹ • v = B.intrinsicCyclicVertex (s k)) ↔
      ((e 0)⁻¹ • v = B.intrinsicCyclicVertex (s 0)) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (B.contact_cycle_endpoint_orientation_step hv hn hperiodic hcontact huniq
      hsideLabel hendpoint k).symm.trans ih

/-- The native vertex transition is explicitly reverse-perimeter successor
after side pairing. -/
theorem intrinsicBoundaryOriginalVertexPerm_apply
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryOriginalVertexPerm i =
      (finRotate B.intrinsicBoundaryRadialCuts.card).symm
        (B.intrinsicCyclicPairing i) := by
  classical
  have hpos : 0 < B.intrinsicBoundaryRadialCuts.card :=
    lt_of_lt_of_le (by decide : 0 < 3) B.three_le_intrinsicBoundaryRadialCuts_card
  letI : NeZero B.intrinsicBoundaryRadialCuts.card := ⟨hpos.ne'⟩
  have hbase :
      (List.ofFn (fun j : Fin B.intrinsicBoundaryRadialCuts.card => j)).formPerm =
        finRotate B.intrinsicBoundaryRadialCuts.card := by
    let l := List.ofFn (fun j : Fin B.intrinsicBoundaryRadialCuts.card => j)
    apply Equiv.ext
    intro j
    have hj : j.1 < l.length := by
      change j.1 < (List.ofFn (fun k : Fin B.intrinsicBoundaryRadialCuts.card => k)).length
      rw [List.length_ofFn]
      exact j.2
    have hstep := List.formPerm_apply_getElem l
      (List.nodup_ofFn.mpr Function.injective_id) j.1 hj
    have hleft : l[j.1] = j := by simp [l]
    have hmod : (j.1 + 1) % l.length < l.length :=
      Nat.mod_lt _ (by simpa [l] using hpos)
    have hright : l[(j.1 + 1) % l.length]'hmod =
        finRotate B.intrinsicBoundaryRadialCuts.card j := by
      simp only [l, List.getElem_ofFn]
      apply Fin.ext
      simp [finRotate_apply, Fin.add_def]
    rw [hleft, hright] at hstep
    exact hstep
  have horder : B.intrinsicBoundaryOriginalSideOrder.formPerm =
      (finRotate B.intrinsicBoundaryRadialCuts.card).symm := by
    rw [intrinsicBoundaryOriginalSideOrder, List.formPerm_reverse, hbase]
    exact Equiv.ext (fun j => rfl)
  change B.intrinsicBoundaryOriginalSideOrder.formPerm
    (B.intrinsicCyclicPairing i) = _
  rw [horder]

/-- A contact-cycle step is a genuine step of the native vertex transition if
the contact vertex is the terminal endpoint of each side. In the opposite
orientation, it is the forward perimeter successor after side pairing; that
case is handled by reversing the contact cycle. -/
theorem contact_cycle_native_side_successor
    (B : DirichletBoundarySegments X o) {v : ℍ}
    (hv : v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o)
    {n : ℕ} {e : ℕ → X.deckGroup}
    (hn : 3 ≤ n)
    (hperiodic : ∀ k, e (k + n) = e k)
    (hcontact : ∀ k, e k ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v)
    (huniq : ∀ γ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v,
      ∃! k, k < n ∧ γ • o = e k • o)
    {s : ℕ → Fin B.intrinsicBoundaryRadialCuts.card}
    (hsideLabel : ∀ k, (B.intrinsicCyclicEdge (s k)).1.1.1 = (e k)⁻¹ * e (k + 1))
    (hendpoint : ∀ k,
      (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k) ∨
        (e k)⁻¹ • v = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (s k)))
    (k : ℕ) :
    ((e k)⁻¹ • v = B.intrinsicCyclicVertex (s k) →
      s (k + 1) = finRotate B.intrinsicBoundaryRadialCuts.card
        (B.intrinsicCyclicPairing (s k))) ∧
    (¬ (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k) →
      B.intrinsicBoundaryOriginalVertexPerm (s k) = s (k + 1)) := by
  classical
  let p := (e k)⁻¹ • v
  let pn := (e (k + 1))⁻¹ • v
  let r := B.intrinsicCyclicPairing (s k)
  have htransport : pn = (B.intrinsicCyclicEdge (s k)).1.1.1⁻¹ • p := by
    dsimp [pn, p]
    rw [← mul_smul, hsideLabel k]
    have hgroup : ((e k)⁻¹ * e (k + 1))⁻¹ * (e k)⁻¹ = (e (k + 1))⁻¹ := by
      group
    rw [hgroup]
  have hpnVertex : pn ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o :=
    Vendored.RiemannDynamics.smul_mem_polygonVertices hv (hcontact (k + 1))
  have hnextPoint : pn ∈
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o
        (B.intrinsicCyclicEdge (s (k + 1))).1.1.1 := by
    rcases hendpoint (k + 1) with hstart | hend
    · rw [← B.intrinsicCyclicClosedEdge_eq_dirichletSideSet (s (k + 1)),
        B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
      simpa only [pn, hstart] using Vendored.RiemannDynamics.left_mem_geodSeg
        (B.intrinsicCyclicVertex (s (k + 1)))
        (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card
          (s (k + 1))))
    · rw [← B.intrinsicCyclicClosedEdge_eq_dirichletSideSet (s (k + 1)),
        B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
      simpa only [pn, hend] using Vendored.RiemannDynamics.right_mem_geodSeg
        (B.intrinsicCyclicVertex (s (k + 1)))
        (B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card
          (s (k + 1))))
  have hnextPoly : Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o
      (B.intrinsicCyclicEdge (s (k + 1))).1.1.1 ∈
        Vendored.RiemannDynamics.polygonSides X.deckGroup o :=
    ⟨(B.intrinsicCyclicEdge (s (k + 1))).1.1.1,
      B.intrinsicCyclicEdge_isSideElement (s (k + 1)), rfl⟩
  obtain ⟨R, hdense⟩ := X.exists_dirichlet_orbit_density_bound o
  have hbase := X.basepoint_mem_interior_dirichletDomain o
  have hnextEnd := Vendored.RiemannDynamics.isSegEndpoint_of_vertex
    (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
    X.deck_fixing_point_acts_trivially hbase hdense hpnVertex hnextPoly hnextPoint
  have htwoapart : e k • o ≠ e (k + 2) • o := by
    intro heq
    have hemod : ∀ x, e (x % n) = e x := by
      intro x
      conv_rhs => rw [show x = x % n + n * (x / n) from (Nat.mod_add_div x n).symm]
      generalize x / n = q
      induction q with
      | zero => simp
      | succ q ih =>
          rw [Nat.mul_succ, ← Nat.add_assoc, hperiodic, ih]
    obtain ⟨a, ha, huniqCenter⟩ := huniq (e k) (hcontact k)
    have hfirst : k % n = a := huniqCenter _
      ⟨Nat.mod_lt _ (by omega), by
        exact congrArg (fun γ : X.deckGroup => γ • o) (hemod k).symm⟩
    have hsecond : (k + 2) % n = a := huniqCenter _
      ⟨Nat.mod_lt _ (by omega), by
        exact heq.trans (congrArg (fun γ : X.deckGroup => γ • o)
          (hemod (k + 2)).symm)⟩
    have hmod : k % n = (k + 2) % n := hfirst.trans hsecond.symm
    have hmods : k % n ≠ (k + 2) % n := by
      intro h
      have hdvd : n ∣ (k + 2) - k :=
        (Nat.modEq_iff_dvd' (by omega : k ≤ k + 2)).mp h
      have hle := Nat.le_of_dvd (by omega : 0 < (k + 2) - k) hdvd
      omega
    exact hmods hmod
  have hsideNe : r ≠ s (k + 1) := by
    intro heq
    have hlabels :
        ((e k)⁻¹ * e (k + 1))⁻¹ = (e (k + 1))⁻¹ * e (k + 2) := by
      calc
        ((e k)⁻¹ * e (k + 1))⁻¹ =
            (B.intrinsicCyclicEdge r).1.1.1 := by
              rw [B.intrinsicCyclicEdge_pairing, B.inverseIntrinsicOpenEdge_label,
                hsideLabel k]
        _ = (B.intrinsicCyclicEdge (s (k + 1))).1.1.1 :=
          congrArg (fun i => (B.intrinsicCyclicEdge i).1.1.1) heq
        _ = (e (k + 1))⁻¹ * e (k + 2) := hsideLabel (k + 1)
    have hcancel : (e (k + 1))⁻¹ * e k = (e (k + 1))⁻¹ * e (k + 2) := by
      simpa only [mul_inv_rev, inv_inv] using hlabels
    have hcenters : e k • o = e (k + 2) • o :=
      congrArg (fun γ : X.deckGroup => γ • o) (mul_left_cancel hcancel)
    exact htwoapart hcenters
  have hindex (q : Fin B.intrinsicBoundaryRadialCuts.card)
      (hq : pn = B.intrinsicCyclicVertex q) :
      s (k + 1) = q ∨
        s (k + 1) = (finRotate B.intrinsicBoundaryRadialCuts.card).symm q :=
    B.intrinsic_side_endpoint_index q (s (k + 1)) hpnVertex hq hnextEnd
  constructor
  · intro hstart
    let q := finRotate B.intrinsicBoundaryRadialCuts.card r
    have hq : pn = B.intrinsicCyclicVertex q := by
      calc
        pn = (B.intrinsicCyclicEdge (s k)).1.1.1⁻¹ • p := htransport
        _ = B.intrinsicCyclicVertex q := by
          have hstart' : p = B.intrinsicCyclicVertex (s k) := hstart
          rw [hstart']
          simpa only [q] using (B.inverse_smul_intrinsicCyclicVertices_eq_reverse (s k)).1
    have hindex' := hindex q hq
    rcases hindex' with hnextq | hnextprev
    · exact hnextq
    · have hr : r = (finRotate B.intrinsicBoundaryRadialCuts.card).symm q := by
        change r = (finRotate B.intrinsicBoundaryRadialCuts.card).symm
          (finRotate B.intrinsicBoundaryRadialCuts.card r)
        exact (Equiv.symm_apply_apply (finRotate B.intrinsicBoundaryRadialCuts.card) r).symm
      exact (hsideNe (hr.trans hnextprev.symm)).elim
  · intro hnotstart
    have hend : p = B.intrinsicCyclicVertex
        (finRotate B.intrinsicBoundaryRadialCuts.card (s k)) := by
      rcases hendpoint k with hstart | hend
      · exact (hnotstart hstart).elim
      · exact hend
    let q := r
    have hq : pn = B.intrinsicCyclicVertex q := by
      calc
        pn = (B.intrinsicCyclicEdge (s k)).1.1.1⁻¹ • p := htransport
        _ = B.intrinsicCyclicVertex q := by
          have hend' : p = B.intrinsicCyclicVertex
              (finRotate B.intrinsicBoundaryRadialCuts.card (s k)) := hend
          rw [hend']
          simpa only [q] using (B.inverse_smul_intrinsicCyclicVertices_eq_reverse (s k)).2
    have hindex' := hindex q hq
    rcases hindex' with hnextq | hnextprev
    · have : r = s (k + 1) := hnextq.symm
      exact (hsideNe this).elim
    · have hs : s (k + 1) = (finRotate B.intrinsicBoundaryRadialCuts.card).symm r := hnextprev
      rw [B.intrinsicBoundaryOriginalVertexPerm_apply]
      exact hs.symm

/-- In the start-endpoint convention, the paired contact sides form the same
native vertex orbit in reverse cycle order. -/
theorem contact_cycle_paired_side_predecessor
    (B : DirichletBoundarySegments X o) {v : ℍ}
    (hv : v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o)
    {n : ℕ} {e : ℕ → X.deckGroup}
    (hn : 3 ≤ n)
    (hperiodic : ∀ k, e (k + n) = e k)
    (hcontact : ∀ k, e k ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v)
    (huniq : ∀ γ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v,
      ∃! k, k < n ∧ γ • o = e k • o)
    {s : ℕ → Fin B.intrinsicBoundaryRadialCuts.card}
    (hsideLabel : ∀ k, (B.intrinsicCyclicEdge (s k)).1.1.1 = (e k)⁻¹ * e (k + 1))
    (hendpoint : ∀ k,
      (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k) ∨
        (e k)⁻¹ • v = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (s k)))
    (hstart : ∀ k, (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k))
    (k : ℕ) :
    B.intrinsicBoundaryOriginalVertexPerm
        (B.intrinsicCyclicPairing (s (k + 1))) =
      B.intrinsicCyclicPairing (s k) := by
  have hstep := (B.contact_cycle_native_side_successor hv hn hperiodic
    hcontact huniq hsideLabel hendpoint k).1 (hstart k)
  rw [B.intrinsicBoundaryOriginalVertexPerm_apply,
    B.intrinsicCyclicPairing_involutive, hstep]
  exact Equiv.symm_apply_apply (finRotate B.intrinsicBoundaryRadialCuts.card)
    (B.intrinsicCyclicPairing (s k))

/-- Iterating the native vertex permutation follows the contact side sequence
when its endpoint orientation is terminal. -/
theorem contact_cycle_terminal_side_iterate
    (B : DirichletBoundarySegments X o) {v : ℍ}
    (hv : v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o)
    {n : ℕ} {e : ℕ → X.deckGroup}
    (hn : 3 ≤ n)
    (hperiodic : ∀ k, e (k + n) = e k)
    (hcontact : ∀ k, e k ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v)
    (huniq : ∀ γ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v,
      ∃! k, k < n ∧ γ • o = e k • o)
    {s : ℕ → Fin B.intrinsicBoundaryRadialCuts.card}
    (hsideLabel : ∀ k, (B.intrinsicCyclicEdge (s k)).1.1.1 = (e k)⁻¹ * e (k + 1))
    (hendpoint : ∀ k,
      (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k) ∨
        (e k)⁻¹ • v = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (s k)))
    (hterminal : ∀ k,
      ¬ (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k)) :
    ∀ m k, B.intrinsicBoundaryOriginalVertexPerm^[m] (s k) = s (k + m) := by
  intro m
  induction m with
  | zero => intro k; simp
  | succ m ih =>
    intro k
    rw [Function.iterate_succ_apply', ih]
    have hstep := (B.contact_cycle_native_side_successor hv hn hperiodic
      hcontact huniq hsideLabel hendpoint (k + m)).2 (hterminal (k + m))
    simpa [Nat.add_assoc] using hstep

/-- In start orientation, the native permutation iterates through the paired
contact sides in reverse contact-cycle order. -/
theorem contact_cycle_start_paired_side_iterate
    (B : DirichletBoundarySegments X o) {v : ℍ}
    (hv : v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o)
    {n : ℕ} {e : ℕ → X.deckGroup}
    (hn : 3 ≤ n)
    (hperiodic : ∀ k, e (k + n) = e k)
    (hcontact : ∀ k, e k ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v)
    (huniq : ∀ γ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v,
      ∃! k, k < n ∧ γ • o = e k • o)
    {s : ℕ → Fin B.intrinsicBoundaryRadialCuts.card}
    (hsideLabel : ∀ k, (B.intrinsicCyclicEdge (s k)).1.1.1 = (e k)⁻¹ * e (k + 1))
    (hendpoint : ∀ k,
      (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k) ∨
        (e k)⁻¹ • v = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (s k)))
    (hstart : ∀ k, (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k)) :
    ∀ m k, B.intrinsicBoundaryOriginalVertexPerm^[m]
      (B.intrinsicCyclicPairing (s (k + m))) =
        B.intrinsicCyclicPairing (s k) := by
  intro m
  induction m with
  | zero => intro k; simp
  | succ m ih =>
    intro k
    rw [Function.iterate_succ_apply]
    have hstep := B.contact_cycle_paired_side_predecessor hv hn hperiodic
      hcontact huniq hsideLabel hendpoint hstart (k + m)
    rw [show k + (m + 1) = (k + m) + 1 by omega, hstep]
    exact ih k

/-- The vendored complete contact cycle yields a periodic sequence of native
side indices. Each consecutive native side is incident to the deck-orbit
class of the chosen vertex. This does not yet identify the sequence with the
native original vertex permutation's orbit. -/
theorem exists_contact_cycle_native_sides
    (B : DirichletBoundarySegments X o) {v : ℍ}
    (hv : v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o) :
    ∃ (n : ℕ) (e : ℕ → X.deckGroup) (s : ℕ → Fin B.intrinsicBoundaryRadialCuts.card),
      3 ≤ n ∧ (∀ k, e (k + n) = e k) ∧
        (∀ k, e k ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v) ∧
        (∀ γ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v,
          ∃! k, k < n ∧ γ • o = e k • o) ∧
        (∀ k, Vendored.RiemannDynamics.IsSideElement X.deckGroup o
          ((e k)⁻¹ * e (k + 1))) ∧
        (∀ k, (B.intrinsicCyclicEdge (s k)).1.1.1 = (e k)⁻¹ * e (k + 1)) ∧
        (∀ k, (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k) ∨
          (e k)⁻¹ • v = B.intrinsicCyclicVertex
            (finRotate B.intrinsicBoundaryRadialCuts.card (s k))) := by
  classical
  obtain ⟨R, hdense⟩ := X.exists_dirichlet_orbit_density_bound o
  obtain ⟨n, e, hn, hperiodic, hcontact, hunique, hadjacent⟩ :=
    Vendored.RiemannDynamics.exists_vertex_cycle
      (inferInstance : ProperlyDiscontinuousSMul X.deckGroup ℍ)
      X.deck_fixing_point_acts_trivially
      (X.basepoint_mem_interior_dirichletDomain o) hdense hv
  choose s hs using fun k : ℕ =>
    B.exists_intrinsicCyclicEdge_of_contact_side hv (hcontact k) (hcontact (k + 1))
      (hadjacent k)
  refine ⟨n, e, s, hn, hperiodic, hcontact, hunique, hadjacent, ?_, ?_⟩
  · intro k
    exact (hs k).1
  · intro k
    exact (hs k).2

/-- Every native side whose terminal endpoint belongs to a given actual
vertex class occurs either in the contact cycle's side list or as the paired
orientation of one of those sides. The cycle is taken at the chosen native
representative of the class. -/
theorem terminal_side_occurs_in_contact_cycle
    (B : DirichletBoundarySegments X o)
    (i j : Fin B.intrinsicBoundaryRadialCuts.card) {v : ℍ}
    (hv : v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o)
    (hj : B.intrinsicCyclicVertex
      (finRotate B.intrinsicBoundaryRadialCuts.card j) = v)
    {n : ℕ} {e : ℕ → X.deckGroup}
    {s : ℕ → Fin B.intrinsicBoundaryRadialCuts.card}
    (hn : 3 ≤ n)
    (hperiodic : ∀ k, e (k + n) = e k)
    (hcontact : ∀ k, e k ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v)
    (huniq : ∀ γ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v,
      ∃! k, k < n ∧ γ • o = e k • o)
    (hadjacent : ∀ k, Vendored.RiemannDynamics.IsSideElement X.deckGroup o
      ((e k)⁻¹ * e (k + 1)))
    (hsideLabel : ∀ k, (B.intrinsicCyclicEdge (s k)).1.1.1 = (e k)⁻¹ * e (k + 1))
    (hfiber : B.intrinsicBoundaryGraphSideEnd i = B.intrinsicBoundaryGraphSideEnd j) :
    ∃ k, k < n ∧
      (i = s k ∨ i = B.intrinsicCyclicPairing (s k)) := by
  classical
  let xi := B.intrinsicCyclicVertex
    (finRotate B.intrinsicBoundaryRadialCuts.card i)
  have hquot : Quotient.mk B.intrinsicBoundaryGraphVertexSetoid
        (finRotate B.intrinsicBoundaryRadialCuts.card i) =
      Quotient.mk B.intrinsicBoundaryGraphVertexSetoid
        (finRotate B.intrinsicBoundaryRadialCuts.card j) := by
    simpa [intrinsicBoundaryGraphSideEnd, intrinsicBoundaryGraphSideStart] using hfiber
  obtain ⟨γ, hγxi⟩ :=
    (B.intrinsicBoundaryGraphVertexSetoid_iff _ _).mp (Quotient.exact hquot)
  have hγv : γ • xi = v := by
    calc
      γ • xi = γ • B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card i) := rfl
      _ = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card j) := hγxi
      _ = v := hj
  let sideLabel := (B.intrinsicCyclicEdge i).1.1.1
  have hxiSide : xi ∈
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o sideLabel := by
    dsimp [xi, sideLabel]
    rw [← B.intrinsicCyclicClosedEdge_eq_dirichletSideSet i,
      B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
    exact Vendored.RiemannDynamics.right_mem_geodSeg _ _
  have hxiDomain : xi ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := hxiSide.1
  have hLabelContact : sideLabel ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o xi :=
    Vendored.RiemannDynamics.mem_contactSet_of_mem_sideSet hxiSide
  have hγcontact : γ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v := by
    have h := (Vendored.RiemannDynamics.contact_shift γ 1 xi).mp
      (Vendored.RiemannDynamics.one_mem_contactSet hxiDomain)
    simpa only [mul_one, hγv] using h
  have hγLabelContact : γ * sideLabel ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v := by
    have h := (Vendored.RiemannDynamics.contact_shift γ sideLabel xi).mp hLabelContact
    simpa only [hγv] using h
  obtain ⟨a, ha, _⟩ := huniq γ hγcontact
  have hea : e a = γ := X.deck_smul_injective o ha.2.symm
  have hrelative : (e a)⁻¹ * (γ * sideLabel) = sideLabel := by
    rw [hea]
    group
  have hrelativeSide : Vendored.RiemannDynamics.IsSideElement X.deckGroup o
      ((e a)⁻¹ * (γ * sideLabel)) := by
    rw [hrelative]
    exact B.intrinsicCyclicEdge_isSideElement i
  have hneighbor := contact_side_neighbor_of_cycle hv hn hperiodic hcontact huniq
    hadjacent ha.1 hγLabelContact hrelativeSide
  have hperiodicSide : ∀ k, s (k + n) = s k := by
    intro k
    apply B.intrinsicCyclicEdge_label_injective
    calc
      (B.intrinsicCyclicEdge (s (k + n))).1.1.1 = (e (k + n))⁻¹ * e (k + n + 1) :=
        hsideLabel (k + n)
      _ = (e k)⁻¹ * e (k + 1) := by
        rw [hperiodic k, show k + n + 1 = (k + 1) + n by omega, hperiodic (k + 1)]
      _ = (B.intrinsicCyclicEdge (s k)).1.1.1 := (hsideLabel k).symm
  have hsmod : ∀ k, s k = s (k % n) := by
    intro k
    conv_lhs => rw [show k = k % n + n * (k / n) from (Nat.mod_add_div k n).symm]
    generalize k / n = q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [Nat.mul_succ, ← Nat.add_assoc, hperiodicSide, ih]
  rcases hneighbor with hforward | hback
  · have hLabelForward : sideLabel = (e a)⁻¹ * e (a + 1) := by
      calc
        sideLabel = γ⁻¹ * (γ * sideLabel) := by group
        _ = γ⁻¹ * e (a + 1) := by rw [hforward]
        _ = (e a)⁻¹ * e (a + 1) := by rw [hea]
    have hindex : s a = i := B.intrinsicCyclicEdge_label_injective <| by
      calc
        (B.intrinsicCyclicEdge (s a)).1.1.1 = (e a)⁻¹ * e (a + 1) := hsideLabel a
        _ = sideLabel := hLabelForward.symm
        _ = (B.intrinsicCyclicEdge i).1.1.1 := rfl
    exact ⟨a, ha.1, Or.inl hindex.symm⟩
  · let prev := a + (n - 1)
    have hprev_next : prev + 1 = a + n := by
      dsimp [prev]
      omega
    have hprev_center : e (prev + 1) = e a := by
      rw [hprev_next, hperiodic]
    have hLabelBack : sideLabel = (e a)⁻¹ * e prev := by
      calc
        sideLabel = γ⁻¹ * (γ * sideLabel) := by group
        _ = γ⁻¹ * e prev := by rw [hback]
        _ = (e a)⁻¹ * e prev := by rw [hea]
    have hpreviousLabel : (B.intrinsicCyclicEdge (s prev)).1.1.1 = sideLabel⁻¹ := by
      rw [hsideLabel prev, hprev_center, hLabelBack]
      group
    have hpairedLabel :
        (B.intrinsicCyclicEdge (B.intrinsicCyclicPairing (s prev))).1.1.1 = sideLabel := by
      rw [B.intrinsicCyclicEdge_pairing, B.inverseIntrinsicOpenEdge_label,
        hpreviousLabel]
      simp
    have hpaired : B.intrinsicCyclicPairing (s prev) = i :=
      B.intrinsicCyclicEdge_label_injective (by simpa [sideLabel] using hpairedLabel)
    refine ⟨prev % n, Nat.mod_lt _ (by omega), ?_⟩
    right
    calc
      i = B.intrinsicCyclicPairing (s prev) := hpaired.symm
      _ = B.intrinsicCyclicPairing (s (prev % n)) := by rw [← hsmod prev]

/-- Refine terminal-fiber coverage using the actual endpoint orientation. In
the terminal convention the fiber is covered by contact sides; in the start
convention it is covered by their paired orientations. No disjointness of
these lists is assumed, so loop-side self-identifications remain allowed. -/
theorem terminal_side_occurs_in_contact_cycle_oriented
    (B : DirichletBoundarySegments X o)
    (i j : Fin B.intrinsicBoundaryRadialCuts.card) {v : ℍ}
    (hv : v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o)
    (hj : B.intrinsicCyclicVertex
      (finRotate B.intrinsicBoundaryRadialCuts.card j) = v)
    {n : ℕ} {e : ℕ → X.deckGroup}
    {s : ℕ → Fin B.intrinsicBoundaryRadialCuts.card}
    (hn : 3 ≤ n)
    (hperiodic : ∀ k, e (k + n) = e k)
    (hcontact : ∀ k, e k ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v)
    (huniq : ∀ γ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v,
      ∃! k, k < n ∧ γ • o = e k • o)
    (hadjacent : ∀ k, Vendored.RiemannDynamics.IsSideElement X.deckGroup o
      ((e k)⁻¹ * e (k + 1)))
    (hsideLabel : ∀ k, (B.intrinsicCyclicEdge (s k)).1.1.1 = (e k)⁻¹ * e (k + 1))
    (hendpoint : ∀ k,
      (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k) ∨
        (e k)⁻¹ • v = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (s k)))
    (hfiber : B.intrinsicBoundaryGraphSideEnd i =
      B.intrinsicBoundaryGraphSideEnd j) :
    ( (∀ k, (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k)) →
        ∃ k, i = B.intrinsicCyclicPairing (s k)) ∧
    ( (∀ k, ¬ (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k)) →
        ∃ k, i = s k) := by
  classical
  let xi := B.intrinsicCyclicVertex
    (finRotate B.intrinsicBoundaryRadialCuts.card i)
  have hquot : Quotient.mk B.intrinsicBoundaryGraphVertexSetoid
        (finRotate B.intrinsicBoundaryRadialCuts.card i) =
      Quotient.mk B.intrinsicBoundaryGraphVertexSetoid
        (finRotate B.intrinsicBoundaryRadialCuts.card j) := by
    simpa [intrinsicBoundaryGraphSideEnd, intrinsicBoundaryGraphSideStart] using hfiber
  obtain ⟨γ, hγxi⟩ :=
    (B.intrinsicBoundaryGraphVertexSetoid_iff _ _).mp (Quotient.exact hquot)
  have hγv : γ • xi = v := by
    calc
      γ • xi = γ • B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card i) := rfl
      _ = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card j) := hγxi
      _ = v := hj
  let sideLabel := (B.intrinsicCyclicEdge i).1.1.1
  have hxiSide : xi ∈
      Vendored.RiemannDynamics.dirichletSideSet X.deckGroup o sideLabel := by
    dsimp [xi, sideLabel]
    rw [← B.intrinsicCyclicClosedEdge_eq_dirichletSideSet i,
      B.intrinsicCyclicEdge_closedImage_eq_geodSeg]
    exact Vendored.RiemannDynamics.right_mem_geodSeg _ _
  have hxiDomain : xi ∈ Vendored.RiemannDynamics.dirichletDomain X.deckGroup o := hxiSide.1
  have hLabelContact : sideLabel ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o xi :=
    Vendored.RiemannDynamics.mem_contactSet_of_mem_sideSet hxiSide
  have hγcontact : γ ∈ Vendored.RiemannDynamics.contactSet X.deckGroup o v := by
    have h := (Vendored.RiemannDynamics.contact_shift γ 1 xi).mp
      (Vendored.RiemannDynamics.one_mem_contactSet hxiDomain)
    simpa only [mul_one, hγv] using h
  have hγLabelContact : γ * sideLabel ∈
      Vendored.RiemannDynamics.contactSet X.deckGroup o v := by
    have h := (Vendored.RiemannDynamics.contact_shift γ sideLabel xi).mp hLabelContact
    simpa only [hγv] using h
  obtain ⟨a, ha, _⟩ := huniq γ hγcontact
  have hea : e a = γ := X.deck_smul_injective o ha.2.symm
  have hqa : (e a)⁻¹ • v = B.intrinsicCyclicVertex
      (finRotate B.intrinsicBoundaryRadialCuts.card i) := by
    calc
      (e a)⁻¹ • v = γ⁻¹ • v := by rw [hea]
      _ = γ⁻¹ • (γ • xi) := congrArg (γ⁻¹ • ·) hγv.symm
      _ = xi := by simp
      _ = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card i) := rfl
  have hrelativeSide : Vendored.RiemannDynamics.IsSideElement X.deckGroup o
      ((e a)⁻¹ * (γ * sideLabel)) := by
    rw [show (e a)⁻¹ * (γ * sideLabel) = sideLabel by rw [hea]; group]
    exact B.intrinsicCyclicEdge_isSideElement i
  have hneighbor := contact_side_neighbor_of_cycle hv hn hperiodic hcontact huniq
    hadjacent ha.1 hγLabelContact hrelativeSide
  constructor
  · intro hstartAll
    rcases hneighbor with hforward | hback
    · have hLabelForward : sideLabel = (e a)⁻¹ * e (a + 1) := by
        calc
          sideLabel = γ⁻¹ * (γ * sideLabel) := by group
          _ = γ⁻¹ * e (a + 1) := by rw [hforward]
          _ = (e a)⁻¹ * e (a + 1) := by rw [hea]
      have hindex : s a = i := B.intrinsicCyclicEdge_label_injective <| by
        calc
          (B.intrinsicCyclicEdge (s a)).1.1.1 = (e a)⁻¹ * e (a + 1) := hsideLabel a
          _ = sideLabel := hLabelForward.symm
          _ = (B.intrinsicCyclicEdge i).1.1.1 := rfl
      have hbad : B.intrinsicCyclicVertex i =
          B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i) := by
        calc
          B.intrinsicCyclicVertex i = B.intrinsicCyclicVertex (s a) :=
            congrArg B.intrinsicCyclicVertex hindex.symm
          _ = (e a)⁻¹ • v := (hstartAll a).symm
          _ = B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i) := hqa
      exact (B.intrinsicCyclicVertex_next_ne i hbad).elim
    · let prev := a + (n - 1)
      have hprev_next : prev + 1 = a + n := by
        dsimp [prev]
        omega
      have hprev_center : e (prev + 1) = e a := by
        rw [hprev_next, hperiodic]
      have hLabelBack : sideLabel = (e a)⁻¹ * e prev := by
        calc
          sideLabel = γ⁻¹ * (γ * sideLabel) := by group
          _ = γ⁻¹ * e prev := by rw [hback]
          _ = (e a)⁻¹ * e prev := by rw [hea]
      have hpreviousLabel : (B.intrinsicCyclicEdge (s prev)).1.1.1 = sideLabel⁻¹ := by
        rw [hsideLabel prev, hprev_center, hLabelBack]
        group
      have hpairedLabel :
          (B.intrinsicCyclicEdge (B.intrinsicCyclicPairing (s prev))).1.1.1 = sideLabel := by
        rw [B.intrinsicCyclicEdge_pairing, B.inverseIntrinsicOpenEdge_label,
          hpreviousLabel]
        simp
      have hpaired : B.intrinsicCyclicPairing (s prev) = i :=
        B.intrinsicCyclicEdge_label_injective (by simpa [sideLabel] using hpairedLabel)
      exact ⟨prev, hpaired.symm⟩
  · intro hterminalAll
    rcases hneighbor with hforward | hback
    · have hLabelForward : sideLabel = (e a)⁻¹ * e (a + 1) := by
        calc
          sideLabel = γ⁻¹ * (γ * sideLabel) := by group
          _ = γ⁻¹ * e (a + 1) := by rw [hforward]
          _ = (e a)⁻¹ * e (a + 1) := by rw [hea]
      have hindex : s a = i := B.intrinsicCyclicEdge_label_injective <| by
        calc
          (B.intrinsicCyclicEdge (s a)).1.1.1 = (e a)⁻¹ * e (a + 1) := hsideLabel a
          _ = sideLabel := hLabelForward.symm
          _ = (B.intrinsicCyclicEdge i).1.1.1 := rfl
      exact ⟨a, hindex.symm⟩
    · let prev := a + (n - 1)
      have hprev_next : prev + 1 = a + n := by
        dsimp [prev]
        omega
      have hprev_center : e (prev + 1) = e a := by
        rw [hprev_next, hperiodic]
      have hLabelBack : sideLabel = (e a)⁻¹ * e prev := by
        calc
          sideLabel = γ⁻¹ * (γ * sideLabel) := by group
          _ = γ⁻¹ * e prev := by rw [hback]
          _ = (e a)⁻¹ * e prev := by rw [hea]
      have hpreviousLabel : (B.intrinsicCyclicEdge (s prev)).1.1.1 = sideLabel⁻¹ := by
        rw [hsideLabel prev, hprev_center, hLabelBack]
        group
      have hpairedLabel :
          (B.intrinsicCyclicEdge (B.intrinsicCyclicPairing (s prev))).1.1.1 = sideLabel := by
        rw [B.intrinsicCyclicEdge_pairing, B.inverseIntrinsicOpenEdge_label,
          hpreviousLabel]
        simp
      have hpaired : B.intrinsicCyclicPairing (s prev) = i :=
        B.intrinsicCyclicEdge_label_injective (by simpa [sideLabel] using hpairedLabel)
      have htransport : (e (prev + 1))⁻¹ • v =
          (B.intrinsicCyclicEdge (s prev)).1.1.1⁻¹ • ((e prev)⁻¹ • v) := by
        rw [← mul_smul, hsideLabel prev]
        have hgroup : ((e prev)⁻¹ * e (prev + 1))⁻¹ * (e prev)⁻¹ =
            (e (prev + 1))⁻¹ := by group
        rw [hgroup]
      have htermPrev : (e prev)⁻¹ • v = B.intrinsicCyclicVertex
          (finRotate B.intrinsicBoundaryRadialCuts.card (s prev)) := by
        rcases hendpoint prev with hstart | hterm
        · exact (hterminalAll prev hstart).elim
        · exact hterm
      have hqpair : (e a)⁻¹ • v =
          B.intrinsicCyclicVertex (B.intrinsicCyclicPairing (s prev)) := by
        calc
          (e a)⁻¹ • v = (e (prev + 1))⁻¹ • v := by rw [hprev_center]
          _ = (B.intrinsicCyclicEdge (s prev)).1.1.1⁻¹ • ((e prev)⁻¹ • v) := htransport
          _ = B.intrinsicCyclicVertex (B.intrinsicCyclicPairing (s prev)) := by
            rw [htermPrev]
            exact (B.inverse_smul_intrinsicCyclicVertices_eq_reverse (s prev)).2
      have hbad : B.intrinsicCyclicVertex (B.intrinsicCyclicPairing (s prev)) =
          B.intrinsicCyclicVertex
            (finRotate B.intrinsicBoundaryRadialCuts.card
              (B.intrinsicCyclicPairing (s prev))) := by
        calc
          B.intrinsicCyclicVertex (B.intrinsicCyclicPairing (s prev)) =
              (e a)⁻¹ • v := hqpair.symm
          _ = B.intrinsicCyclicVertex (finRotate B.intrinsicBoundaryRadialCuts.card i) := hqa
          _ = B.intrinsicCyclicVertex
              (finRotate B.intrinsicBoundaryRadialCuts.card
                (B.intrinsicCyclicPairing (s prev))) := by rw [hpaired]
      exact (B.intrinsicCyclicVertex_next_ne _ hbad).elim

/-- The native vertex transition has exactly one orbit on every actual
terminal-side fiber. The proof uses a genuine Dirichlet contact cycle; its two
possible orientations give the same orbit, with paired indices traversed in
reverse order in the start-oriented case. -/
theorem intrinsicBoundaryOriginalVertexPerm_orbit_iff_same_sideEnd
    (B : DirichletBoundarySegments X o)
    (i j : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphSideEnd i = B.intrinsicBoundaryGraphSideEnd j ↔
      ∃ m : ℕ, B.intrinsicBoundaryOriginalVertexPerm^[m] i = j := by
  classical
  let v := B.intrinsicCyclicVertex
    (finRotate B.intrinsicBoundaryRadialCuts.card j)
  have hv : v ∈ Vendored.RiemannDynamics.polygonVertices X.deckGroup o :=
    B.intrinsicCyclicVertex_mem_polygonVertices _
  have hj : B.intrinsicCyclicVertex
      (finRotate B.intrinsicBoundaryRadialCuts.card j) = v := rfl
  obtain ⟨n, e, s, hn, hperiodic, hcontact, huniq, hadjacent, hsideLabel,
      hendpoint⟩ := B.exists_contact_cycle_native_sides hv
  have hperiodicSide : ∀ k, s (k + n) = s k := by
    intro k
    apply B.intrinsicCyclicEdge_label_injective
    calc
      (B.intrinsicCyclicEdge (s (k + n))).1.1.1 = (e (k + n))⁻¹ * e (k + n + 1) :=
        hsideLabel (k + n)
      _ = (e k)⁻¹ * e (k + 1) := by
        rw [hperiodic k, show k + n + 1 = (k + 1) + n by omega, hperiodic (k + 1)]
      _ = (B.intrinsicCyclicEdge (s k)).1.1.1 := (hsideLabel k).symm
  have hsmod : ∀ k, s k = s (k % n) := by
    intro k
    conv_lhs => rw [show k = k % n + n * (k / n) from (Nat.mod_add_div k n).symm]
    generalize k / n = q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [Nat.mul_succ, ← Nat.add_assoc, hperiodicSide, ih]
  have hconst := B.contact_cycle_endpoint_orientation_constant hv hn hperiodic
    hcontact huniq hsideLabel hendpoint
  have hpresIter : ∀ m,
      B.intrinsicBoundaryGraphSideEnd
          (B.intrinsicBoundaryOriginalVertexPerm^[m] i) =
        B.intrinsicBoundaryGraphSideEnd i := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        exact (B.intrinsicBoundaryOriginalVertexPerm_preserves_sideEnd
          (B.intrinsicBoundaryOriginalVertexPerm^[m] i)).trans ih
  constructor
  · intro hfiber
    have hcoverI := B.terminal_side_occurs_in_contact_cycle_oriented i j hv hj
      hn hperiodic hcontact huniq hadjacent hsideLabel hendpoint hfiber
    have hcoverJ := B.terminal_side_occurs_in_contact_cycle_oriented j j hv hj
      hn hperiodic hcontact huniq hadjacent hsideLabel hendpoint rfl
    by_cases hstart0 : (e 0)⁻¹ • v = B.intrinsicCyclicVertex (s 0)
    · have hstart : ∀ k, (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k) := by
        intro k
        exact (hconst k).mpr hstart0
      obtain ⟨ki, hik⟩ := hcoverI.1 hstart
      obtain ⟨kj, hjk⟩ := hcoverJ.1 hstart
      let ki0 := ki % n
      let kj0 := kj % n
      have hik0 : i = B.intrinsicCyclicPairing (s ki0) := by
        calc
          i = B.intrinsicCyclicPairing (s ki) := hik
          _ = B.intrinsicCyclicPairing (s ki0) := by rw [hsmod ki]
      have hjk0 : j = B.intrinsicCyclicPairing (s kj0) := by
        calc
          j = B.intrinsicCyclicPairing (s kj) := hjk
          _ = B.intrinsicCyclicPairing (s kj0) := by rw [hsmod kj]
      have hki0 : ki0 < n := Nat.mod_lt _ (by omega)
      have hkj0 : kj0 < n := Nat.mod_lt _ (by omega)
      by_cases hle : kj0 ≤ ki0
      · let m := ki0 - kj0
        have hsum : kj0 + m = ki0 := by dsimp [m]; omega
        have hseq : B.intrinsicCyclicPairing (s (kj0 + m)) =
            B.intrinsicCyclicPairing (s ki0) := by rw [hsum]
        refine ⟨m, ?_⟩
        calc
          B.intrinsicBoundaryOriginalVertexPerm^[m] i =
              B.intrinsicBoundaryOriginalVertexPerm^[m]
                (B.intrinsicCyclicPairing (s ki0)) :=
                  congrArg (B.intrinsicBoundaryOriginalVertexPerm^[m]) hik0
          _ = B.intrinsicBoundaryOriginalVertexPerm^[m]
                (B.intrinsicCyclicPairing (s (kj0 + m))) :=
                  congrArg (B.intrinsicBoundaryOriginalVertexPerm^[m]) hseq.symm
          _ = B.intrinsicCyclicPairing (s kj0) :=
            B.contact_cycle_start_paired_side_iterate hv hn hperiodic
              hcontact huniq hsideLabel hendpoint hstart m kj0
          _ = j := hjk0.symm
      · let m := n - kj0 + ki0
        have hsum : kj0 + m = ki0 + n := by dsimp [m]; omega
        have hseq : B.intrinsicCyclicPairing (s (kj0 + m)) =
            B.intrinsicCyclicPairing (s ki0) := by
          rw [hsum, hperiodicSide ki0]
        refine ⟨m, ?_⟩
        calc
          B.intrinsicBoundaryOriginalVertexPerm^[m] i =
              B.intrinsicBoundaryOriginalVertexPerm^[m]
                (B.intrinsicCyclicPairing (s ki0)) :=
                  congrArg (B.intrinsicBoundaryOriginalVertexPerm^[m]) hik0
          _ = B.intrinsicBoundaryOriginalVertexPerm^[m]
                (B.intrinsicCyclicPairing (s (kj0 + m))) :=
                  congrArg (B.intrinsicBoundaryOriginalVertexPerm^[m]) hseq.symm
          _ = B.intrinsicCyclicPairing (s kj0) :=
            B.contact_cycle_start_paired_side_iterate hv hn hperiodic
              hcontact huniq hsideLabel hendpoint hstart m kj0
          _ = j := hjk0.symm
    · have hterminal : ∀ k,
          ¬ (e k)⁻¹ • v = B.intrinsicCyclicVertex (s k) := by
        intro k hk
        exact hstart0 ((hconst k).mp hk)
      obtain ⟨ki, hik⟩ := hcoverI.2 hterminal
      obtain ⟨kj, hjk⟩ := hcoverJ.2 hterminal
      let ki0 := ki % n
      let kj0 := kj % n
      have hik0 : i = s ki0 := by
        calc
          i = s ki := hik
          _ = s ki0 := hsmod ki
      have hjk0 : j = s kj0 := by
        calc
          j = s kj := hjk
          _ = s kj0 := hsmod kj
      have hki0 : ki0 < n := Nat.mod_lt _ (by omega)
      have hkj0 : kj0 < n := Nat.mod_lt _ (by omega)
      by_cases hle : ki0 ≤ kj0
      · let m := kj0 - ki0
        have hsum : ki0 + m = kj0 := by dsimp [m]; omega
        refine ⟨m, ?_⟩
        calc
          B.intrinsicBoundaryOriginalVertexPerm^[m] i =
              B.intrinsicBoundaryOriginalVertexPerm^[m] (s ki0) :=
                congrArg (B.intrinsicBoundaryOriginalVertexPerm^[m]) hik0
          _ = s (ki0 + m) :=
            B.contact_cycle_terminal_side_iterate hv hn hperiodic hcontact huniq
              hsideLabel hendpoint hterminal m ki0
          _ = s kj0 := by rw [hsum]
          _ = j := hjk0.symm
      · let m := n - ki0 + kj0
        have hsum : ki0 + m = kj0 + n := by dsimp [m]; omega
        refine ⟨m, ?_⟩
        calc
          B.intrinsicBoundaryOriginalVertexPerm^[m] i =
              B.intrinsicBoundaryOriginalVertexPerm^[m] (s ki0) :=
                congrArg (B.intrinsicBoundaryOriginalVertexPerm^[m]) hik0
          _ = s (ki0 + m) :=
            B.contact_cycle_terminal_side_iterate hv hn hperiodic hcontact huniq
              hsideLabel hendpoint hterminal m ki0
          _ = s kj0 := by rw [hsum, hperiodicSide kj0]
          _ = j := hjk0.symm
  · rintro ⟨m, hiter⟩
    have hside := congrArg B.intrinsicBoundaryGraphSideEnd hiter
    exact (hpresIter m).symm.trans hside

#print axioms exists_intrinsicCyclicEdge_of_contact_side
#print axioms intrinsic_side_endpoint_index
#print axioms contact_cycle_endpoint_orientation_step
#print axioms intrinsicBoundaryOriginalVertexPerm_apply
#print axioms contact_cycle_native_side_successor
#print axioms contact_cycle_paired_side_predecessor
#print axioms contact_cycle_terminal_side_iterate
#print axioms contact_cycle_start_paired_side_iterate
#print axioms intrinsicBoundaryOriginalVertexPerm_orbit_iff_same_sideEnd
#print axioms exists_contact_cycle_native_sides
#print axioms terminal_side_occurs_in_contact_cycle
#print axioms terminal_side_occurs_in_contact_cycle_oriented

end

end SystolicGrowth.DirichletBoundarySegments

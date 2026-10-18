module

public import Geometry.SurfaceBoundaryGraphOpenCover
public import Geometry.SurfaceBoundaryGraphEdgeAlphabet
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

@[expose] public section

/-!
# Paths in the actual physical boundary-graph components

The open vertex stars and the canonically indexed physical midsections are
disjoint families. Connectedness of an actual path therefore confines it to
its initial component. The two overlap halves of a physical side remain
distinct even for a loop edge. The existing contractions then give uniqueness
of path-homotopy classes inside these components, in the original open unions.
-/

open Set UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

noncomputable section

private theorem path_mem_left_of_open_disjoint_union
    {A : Type*} [TopologicalSpace A] {U V : Set A}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    {x y : A} (p : Path x y) (hp : ∀ t, p t ∈ U ∪ V) (hx : x ∈ U) :
    ∀ t, p t ∈ U := by
  have hsub : range p ⊆ U :=
    (isPreconnected_range p.continuous).subset_left_of_subset_union hU hV hUV
      (by rintro z ⟨t, rfl⟩; exact hp t) ⟨x, ⟨0, p.source⟩, hx⟩
  exact fun t => hsub ⟨t, rfl⟩

private theorem path_mem_open_disjoint_component
    {A : Type*} [TopologicalSpace A] {ι : Type*} (U : ι → Set A)
    (hopen : ∀ i, IsOpen (U i))
    (hdisjoint : Pairwise (fun i j => Disjoint (U i) (U j)))
    {x y : A} (p : Path x y) (hp : ∀ t, p t ∈ ⋃ i, U i)
    {i : ι} (hx : x ∈ U i) : ∀ t, p t ∈ U i := by
  classical
  let V : Set A := ⋃ j : {j : ι // j ≠ i}, U j.val
  have hV : IsOpen V := isOpen_iUnion fun j => hopen j.val
  have hUV : Disjoint (U i) V := by
    apply Set.disjoint_left.mpr
    intro z hzU hzV
    obtain ⟨j, hzj⟩ := mem_iUnion.mp hzV
    exact Set.disjoint_left.mp (hdisjoint j.property.symm) hzU hzj
  apply path_mem_left_of_open_disjoint_union (hopen i) hV hUV p _ hx
  intro t
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hp t)
  by_cases hji : j = i
  · exact Or.inl (hji ▸ hj)
  · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)

private theorem subtypePaths_homotopic_of_contractible_subset
    {A : Type*} [TopologicalSpace A] {S T : Set A} [ContractibleSpace S]
    (hST : S ⊆ T) {x y : T} (p q : Path x y)
    (hp : ∀ t, (p t).val ∈ S) (hq : ∀ t, (q t).val ∈ S) : p.Homotopic q := by
  have hx : x.val ∈ S := by simpa only [p.source] using hp 0
  have hy : y.val ∈ S := by simpa only [p.target] using hp 1
  let pS : Path (⟨x.val, hx⟩ : S) ⟨y.val, hy⟩ :=
    { toFun := fun t => ⟨(p t).val, hp t⟩
      continuous_toFun := (continuous_subtype_val.comp p.continuous).subtype_mk _
      source' := Subtype.ext (congrArg (fun z : T => z.val) p.source)
      target' := Subtype.ext (congrArg (fun z : T => z.val) p.target) }
  let qS : Path (⟨x.val, hx⟩ : S) ⟨y.val, hy⟩ :=
    { toFun := fun t => ⟨(q t).val, hq t⟩
      continuous_toFun := (continuous_subtype_val.comp q.continuous).subtype_mk _
      source' := Subtype.ext (congrArg (fun z : T => z.val) q.source)
      target' := Subtype.ext (congrArg (fun z : T => z.val) q.target) }
  let j : C(S, T) :=
    ⟨fun z => ⟨z.val, hST z.property⟩, continuous_subtype_val.subtype_mk _⟩
  have h := (SimplyConnectedSpace.paths_homotopic pS qS).map j
  have hpmap : pS.map j.continuous = p := by ext t; rfl
  have hqmap : qS.map j.continuous = q := by ext t; rfl
  simpa only [hpmap, hqmap] using h

namespace DirichletBoundarySegments

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- Choosing the canonical physical orientation does not change a midsection. -/
theorem intrinsicBoundaryGraphEdgeMidsection_physicalEdge
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphEdgeMidsection (B.intrinsicBoundaryPhysicalEdge i).val =
      B.intrinsicBoundaryGraphEdgeMidsection i := by
  classical
  unfold intrinsicBoundaryPhysicalEdge
  split_ifs
  · rfl
  · exact B.intrinsicBoundaryGraphEdgeMidsection_pair i

/-- The actual midsection union has exactly one index per physical side pair. -/
theorem intrinsicBoundaryGraphMidsectionUnion_eq_physical
    (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryGraphMidsectionUnion =
      ⋃ e : B.IntrinsicBoundaryPhysicalEdge, B.intrinsicBoundaryGraphEdgeMidsection e.val := by
  ext q
  constructor
  · intro hq
    obtain ⟨i, hi⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨B.intrinsicBoundaryPhysicalEdge i,
      (B.intrinsicBoundaryGraphEdgeMidsection_physicalEdge i).symm ▸ hi⟩
  · intro hq
    obtain ⟨e, he⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨e.val, he⟩

/-- A point of a physical midsection determines its unique canonical side. -/
theorem intrinsicBoundaryGraphPhysicalMidsection_mem_unique
    (B : DirichletBoundarySegments X o) {e f : B.IntrinsicBoundaryPhysicalEdge}
    {q : B.IntrinsicBoundaryGraph}
    (he : q ∈ B.intrinsicBoundaryGraphEdgeMidsection e.val)
    (hf : q ∈ B.intrinsicBoundaryGraphEdgeMidsection f.val) : e = f := by
  rcases B.intrinsicBoundaryGraphEdgeMidsection_mem_unique he hf with h | h
  · exact Subtype.ext h.symm
  · have hlt := f.property
    rw [h, B.intrinsicCyclicPairing_involutive] at hlt
    exact (not_lt_of_ge e.property.le hlt).elim

/-- Distinct canonical physical sides have disjoint actual midsections. -/
theorem intrinsicBoundaryGraphPhysicalMidsection_disjoint
    (B : DirichletBoundarySegments X o) {e f : B.IntrinsicBoundaryPhysicalEdge}
    (hef : e ≠ f) :
    Disjoint (B.intrinsicBoundaryGraphEdgeMidsection e.val)
      (B.intrinsicBoundaryGraphEdgeMidsection f.val) := by
  apply Set.disjoint_left.mpr
  intro q he hf
  exact hef (B.intrinsicBoundaryGraphPhysicalMidsection_mem_unique he hf)

/-- Every actual path in the star union stays in its initial vertex star. -/
theorem intrinsicBoundaryGraphStarUnion_path_mem
    (B : DirichletBoundarySegments X o)
    {x y : ↥B.intrinsicBoundaryGraphStarUnion} (p : Path x y)
    {v : B.IntrinsicBoundaryGraphVertex}
    (hx : x.val ∈ B.intrinsicBoundaryGraphVertexStar v) :
    ∀ t, (p t).val ∈ B.intrinsicBoundaryGraphVertexStar v := by
  exact path_mem_open_disjoint_component B.intrinsicBoundaryGraphVertexStar
    B.intrinsicBoundaryGraphVertexStar_isOpen
    (fun _ _ h => B.intrinsicBoundaryGraphVertexStar_disjoint h)
    (p.map continuous_subtype_val) (fun t => (p t).property) hx

/-- Every actual path in the midsection union stays in its initial physical side. -/
theorem intrinsicBoundaryGraphMidsectionUnion_path_mem
    (B : DirichletBoundarySegments X o)
    {x y : ↥B.intrinsicBoundaryGraphMidsectionUnion} (p : Path x y)
    {e : B.IntrinsicBoundaryPhysicalEdge}
    (hx : x.val ∈ B.intrinsicBoundaryGraphEdgeMidsection e.val) :
    ∀ t, (p t).val ∈ B.intrinsicBoundaryGraphEdgeMidsection e.val := by
  apply path_mem_open_disjoint_component
    (fun e : B.IntrinsicBoundaryPhysicalEdge => B.intrinsicBoundaryGraphEdgeMidsection e.val)
    (fun e => B.intrinsicBoundaryGraphEdgeMidsection_isOpen e.val)
    (fun _ _ h => B.intrinsicBoundaryGraphPhysicalMidsection_disjoint h)
    (p.map continuous_subtype_val) _ hx
  intro t
  rw [← B.intrinsicBoundaryGraphMidsectionUnion_eq_physical]
  exact (p t).property

/-- The same confinement statement is valid in either original side orientation. -/
theorem intrinsicBoundaryGraphMidsectionUnion_path_mem_side
    (B : DirichletBoundarySegments X o)
    {x y : ↥B.intrinsicBoundaryGraphMidsectionUnion} (p : Path x y)
    {i : Fin B.intrinsicBoundaryRadialCuts.card}
    (hx : x.val ∈ B.intrinsicBoundaryGraphEdgeMidsection i) :
    ∀ t, (p t).val ∈ B.intrinsicBoundaryGraphEdgeMidsection i := by
  have h := B.intrinsicBoundaryGraphMidsectionUnion_path_mem p
    ((B.intrinsicBoundaryGraphEdgeMidsection_physicalEdge i).symm ▸ hx)
  simpa only [B.intrinsicBoundaryGraphEdgeMidsection_physicalEdge] using h

/-- Inside one actual physical midsection, the star union consists of its two
disjoint half-arms, even when both endpoint classes are the same vertex. -/
theorem intrinsicBoundaryGraphStarUnion_inter_midsection_eq_halves
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphStarUnion ∩ B.intrinsicBoundaryGraphEdgeMidsection i =
      B.intrinsicBoundaryGraphInitialOverlap i ∪ B.intrinsicBoundaryGraphTerminalOverlap i := by
  ext q
  constructor
  · rintro ⟨hstar, hmid⟩
    obtain ⟨v, hv⟩ := mem_iUnion.mp hstar
    have hq : q ∈ B.intrinsicBoundaryGraphVertexStar v ∩
        B.intrinsicBoundaryGraphEdgeMidsection i := ⟨hv, hmid⟩
    rw [B.intrinsicBoundaryGraphStarMidsection_eq_halves v i] at hq
    rcases hq with hq | hq
    · left
      split_ifs at hq
      · exact hq
      · exact False.elim hq
    · right
      split_ifs at hq
      · exact hq
      · exact False.elim hq
  · rintro (hq | hq)
    · exact ⟨mem_iUnion.mpr ⟨B.intrinsicBoundaryGraphSideStart i,
        B.intrinsicBoundaryGraphInitialOverlap_subset_star i hq⟩,
      B.intrinsicBoundaryGraphInitialOverlap_subset_midsection i hq⟩
    · exact ⟨mem_iUnion.mpr ⟨B.intrinsicBoundaryGraphSideEnd i,
        B.intrinsicBoundaryGraphTerminalOverlap_subset_star i hq⟩,
      B.intrinsicBoundaryGraphTerminalOverlap_subset_midsection i hq⟩

/-- An actual overlap path stays in the two half-arms of its initial physical edge. -/
private theorem intrinsicBoundaryGraphOverlap_path_mem_halves
    (B : DirichletBoundarySegments X o)
    {x y : ↥(B.intrinsicBoundaryGraphStarUnion ∩ B.intrinsicBoundaryGraphMidsectionUnion)}
    (p : Path x y) {i : Fin B.intrinsicBoundaryRadialCuts.card}
    (hx : x.val ∈ B.intrinsicBoundaryGraphEdgeMidsection i) :
    ∀ t, (p t).val ∈
      B.intrinsicBoundaryGraphInitialOverlap i ∪ B.intrinsicBoundaryGraphTerminalOverlap i := by
  let j : C(↥(B.intrinsicBoundaryGraphStarUnion ∩ B.intrinsicBoundaryGraphMidsectionUnion),
      ↥B.intrinsicBoundaryGraphMidsectionUnion) :=
    ⟨fun z => ⟨z.val, z.property.2⟩, continuous_subtype_val.subtype_mk _⟩
  have hmid := B.intrinsicBoundaryGraphMidsectionUnion_path_mem_side (p.map j.continuous) hx
  intro t
  rw [← B.intrinsicBoundaryGraphStarUnion_inter_midsection_eq_halves i]
  exact ⟨(p t).property.1, hmid t⟩

/-- An arbitrary path in the actual overlap starting in an initial half-arm
stays in that same half-arm. No connectedness of the whole overlap is assumed. -/
theorem intrinsicBoundaryGraphOverlap_path_mem_initial
    (B : DirichletBoundarySegments X o)
    {x y : ↥(B.intrinsicBoundaryGraphStarUnion ∩ B.intrinsicBoundaryGraphMidsectionUnion)}
    (p : Path x y) {i : Fin B.intrinsicBoundaryRadialCuts.card}
    (hx : x.val ∈ B.intrinsicBoundaryGraphInitialOverlap i) :
    ∀ t, (p t).val ∈ B.intrinsicBoundaryGraphInitialOverlap i := by
  exact path_mem_left_of_open_disjoint_union
    (B.intrinsicBoundaryGraphInitialOverlap_isOpen i)
    (B.intrinsicBoundaryGraphTerminalOverlap_isOpen i)
    (B.intrinsicBoundaryGraphOverlap_halves_disjoint i)
    (p.map continuous_subtype_val)
    (B.intrinsicBoundaryGraphOverlap_path_mem_halves p
      (B.intrinsicBoundaryGraphInitialOverlap_subset_midsection i hx)) hx

/-- An arbitrary path in the actual overlap starting in a terminal half-arm
stays in that same half-arm, including for loop edges. -/
theorem intrinsicBoundaryGraphOverlap_path_mem_terminal
    (B : DirichletBoundarySegments X o)
    {x y : ↥(B.intrinsicBoundaryGraphStarUnion ∩ B.intrinsicBoundaryGraphMidsectionUnion)}
    (p : Path x y) {i : Fin B.intrinsicBoundaryRadialCuts.card}
    (hx : x.val ∈ B.intrinsicBoundaryGraphTerminalOverlap i) :
    ∀ t, (p t).val ∈ B.intrinsicBoundaryGraphTerminalOverlap i := by
  apply path_mem_left_of_open_disjoint_union
    (B.intrinsicBoundaryGraphTerminalOverlap_isOpen i)
    (B.intrinsicBoundaryGraphInitialOverlap_isOpen i)
    (B.intrinsicBoundaryGraphOverlap_halves_disjoint i).symm
    (p.map continuous_subtype_val) _ hx
  intro t
  exact (B.intrinsicBoundaryGraphOverlap_path_mem_halves p
    (B.intrinsicBoundaryGraphTerminalOverlap_subset_midsection i hx) t).symm

/-- Any two actual star-union paths with the same endpoints are homotopic
inside the star union, using the contraction of their common vertex star. -/
theorem intrinsicBoundaryGraphStarUnion_paths_homotopic
    (B : DirichletBoundarySegments X o)
    {x y : ↥B.intrinsicBoundaryGraphStarUnion} (p q : Path x y) : p.Homotopic q := by
  obtain ⟨v, hv⟩ := mem_iUnion.mp x.property
  exact subtypePaths_homotopic_of_contractible_subset
    (fun _ hz => mem_iUnion.mpr ⟨v, hz⟩) p q
    (B.intrinsicBoundaryGraphStarUnion_path_mem p hv)
    (B.intrinsicBoundaryGraphStarUnion_path_mem q hv)

/-- Any two actual midsection-union paths with the same endpoints are homotopic
inside the midsection union, without identifying distinct physical sides. -/
theorem intrinsicBoundaryGraphMidsectionUnion_paths_homotopic
    (B : DirichletBoundarySegments X o)
    {x y : ↥B.intrinsicBoundaryGraphMidsectionUnion} (p q : Path x y) : p.Homotopic q := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
  exact subtypePaths_homotopic_of_contractible_subset
    (fun _ hz => mem_iUnion.mpr ⟨i, hz⟩) p q
    (B.intrinsicBoundaryGraphMidsectionUnion_path_mem_side p hi)
    (B.intrinsicBoundaryGraphMidsectionUnion_path_mem_side q hi)

/-- Any two actual overlap paths with the same endpoints are homotopic within
the overlap: their initial point selects a genuine contractible half-arm. -/
theorem intrinsicBoundaryGraphOverlap_paths_homotopic
    (B : DirichletBoundarySegments X o)
    {x y : ↥(B.intrinsicBoundaryGraphStarUnion ∩ B.intrinsicBoundaryGraphMidsectionUnion)}
    (p q : Path x y) : p.Homotopic q := by
  have hx := (Set.ext_iff.mp
    B.intrinsicBoundaryGraphStarUnion_inter_midsectionUnion x.val).mp x.property
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  rcases hi with hi | hi
  · apply subtypePaths_homotopic_of_contractible_subset
      (S := B.intrinsicBoundaryGraphInitialOverlap i) _ p q
      (B.intrinsicBoundaryGraphOverlap_path_mem_initial p hi)
      (B.intrinsicBoundaryGraphOverlap_path_mem_initial q hi)
    intro z hz
    exact ⟨mem_iUnion.mpr ⟨B.intrinsicBoundaryGraphSideStart i,
        B.intrinsicBoundaryGraphInitialOverlap_subset_star i hz⟩,
      mem_iUnion.mpr ⟨i, B.intrinsicBoundaryGraphInitialOverlap_subset_midsection i hz⟩⟩
  · apply subtypePaths_homotopic_of_contractible_subset
      (S := B.intrinsicBoundaryGraphTerminalOverlap i) _ p q
      (B.intrinsicBoundaryGraphOverlap_path_mem_terminal p hi)
      (B.intrinsicBoundaryGraphOverlap_path_mem_terminal q hi)
    intro z hz
    exact ⟨mem_iUnion.mpr ⟨B.intrinsicBoundaryGraphSideEnd i,
        B.intrinsicBoundaryGraphTerminalOverlap_subset_star i hz⟩,
      mem_iUnion.mpr ⟨i, B.intrinsicBoundaryGraphTerminalOverlap_subset_midsection i hz⟩⟩

/-- The disconnected star union has at most one path-homotopy class between
any prescribed endpoints; this does not assert that such a path exists. -/
instance intrinsicBoundaryGraphStarUnion_homotopicQuotient_subsingleton
    (B : DirichletBoundarySegments X o) (x y : ↥B.intrinsicBoundaryGraphStarUnion) :
    Subsingleton (Path.Homotopic.Quotient x y) where
  allEq p q := Path.Homotopic.Quotient.ind₂
    (fun p q => Path.Homotopic.Quotient.eq.mpr
      (B.intrinsicBoundaryGraphStarUnion_paths_homotopic p q)) p q

/-- Distinct physical midsections remain distinct components, with at most
one path-homotopy class between any prescribed endpoints in their union. -/
instance intrinsicBoundaryGraphMidsectionUnion_homotopicQuotient_subsingleton
    (B : DirichletBoundarySegments X o) (x y : ↥B.intrinsicBoundaryGraphMidsectionUnion) :
    Subsingleton (Path.Homotopic.Quotient x y) where
  allEq p q := Path.Homotopic.Quotient.ind₂
    (fun p q => Path.Homotopic.Quotient.eq.mpr
      (B.intrinsicBoundaryGraphMidsectionUnion_paths_homotopic p q)) p q

/-- The actual disconnected overlap likewise has at most one path-homotopy
class between prescribed endpoints, retaining both half-arms of loop edges. -/
instance intrinsicBoundaryGraphOverlap_homotopicQuotient_subsingleton
    (B : DirichletBoundarySegments X o)
    (x y : ↥(B.intrinsicBoundaryGraphStarUnion ∩ B.intrinsicBoundaryGraphMidsectionUnion)) :
    Subsingleton (Path.Homotopic.Quotient x y) where
  allEq p q := Path.Homotopic.Quotient.ind₂
    (fun p q => Path.Homotopic.Quotient.eq.mpr
      (B.intrinsicBoundaryGraphOverlap_paths_homotopic p q)) p q

end DirichletBoundarySegments

end

end SystolicGrowth

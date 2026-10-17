module

public import Geometry.SurfaceBoundaryGraphCombinatorics
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section

/-! Open vertex stars and paired-edge midsections in the original physical boundary graph.
All sets below use the literal side intervals and the original orbit-vertex relation. -/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane Classical

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- The actual arms incident to a fixed orbit vertex, before taking the physical quotient. -/
def intrinsicBoundaryGraphVertexStarPreimage (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) : Set B.intrinsicBoundaryIntervalCarrier :=
  {a | ((a.2 : ℝ) < 1 / 3 ∧ B.intrinsicBoundaryGraphSideStart a.1 = v) ∨
    (2 / 3 < (a.2 : ℝ) ∧ B.intrinsicBoundaryGraphSideEnd a.1 = v)}

/-- An open star in the original paired-side quotient, retaining every incident arm. -/
def intrinsicBoundaryGraphVertexStar (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) : Set (Quotient B.intrinsicBoundaryIntervalSetoid) :=
  Quotient.mk B.intrinsicBoundaryIntervalSetoid '' B.intrinsicBoundaryGraphVertexStarPreimage v

/-- Both representatives of the same physical edge, with their original reversed parameters. -/
def intrinsicBoundaryGraphEdgeMidsectionPreimage (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) : Set B.intrinsicBoundaryIntervalCarrier :=
  {a | (a.1 = i ∨ a.1 = B.intrinsicCyclicPairing i) ∧
    (1 / 4 : ℝ) < a.2 ∧ (a.2 : ℝ) < 3 / 4}

/-- The open middle of an actual paired edge, not of the auxiliary simple graph. -/
def intrinsicBoundaryGraphEdgeMidsection (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Set (Quotient B.intrinsicBoundaryIntervalSetoid) :=
  Quotient.mk B.intrinsicBoundaryIntervalSetoid '' B.intrinsicBoundaryGraphEdgeMidsectionPreimage i

@[simp]
theorem intrinsicBoundaryGraphVertexStarPreimage_zero (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (i, (0 : unitInterval)) ∈ B.intrinsicBoundaryGraphVertexStarPreimage v ↔
      B.intrinsicBoundaryGraphSideStart i = v := by
  norm_num [intrinsicBoundaryGraphVertexStarPreimage]

@[simp]
theorem intrinsicBoundaryGraphVertexStarPreimage_one (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (i, (1 : unitInterval)) ∈ B.intrinsicBoundaryGraphVertexStarPreimage v ↔
      B.intrinsicBoundaryGraphSideEnd i = v := by
  norm_num [intrinsicBoundaryGraphVertexStarPreimage]

private theorem starPreimage_endpoint_iff (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) (a : B.intrinsicBoundaryIntervalCarrier)
    (ha : B.IsIntrinsicBoundaryIntervalEndpoint a) :
    a ∈ B.intrinsicBoundaryGraphVertexStarPreimage v ↔
      Quotient.mk B.intrinsicBoundaryIntervalSetoid a =
        B.intrinsicBoundaryGraphVertexInclusion v := by
  rcases ha with h | h
  · have heq : a = (a.1, (0 : unitInterval)) := Prod.ext rfl h
    rw [heq, B.intrinsicBoundaryGraphVertexStarPreimage_zero,
      ← B.intrinsicBoundaryGraphVertexInclusion_start]
    exact B.intrinsicBoundaryGraphVertexInclusion_injective.eq_iff.symm
  · have heq : a = (a.1, (1 : unitInterval)) := Prod.ext rfl h
    rw [heq, B.intrinsicBoundaryGraphVertexStarPreimage_one,
      ← B.intrinsicBoundaryGraphVertexInclusion_end]
    exact B.intrinsicBoundaryGraphVertexInclusion_injective.eq_iff.symm

theorem intrinsicBoundaryGraphVertexStarPreimage_pair (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) (a : B.intrinsicBoundaryIntervalCarrier) :
    B.intrinsicBoundaryIntervalPair a ∈ B.intrinsicBoundaryGraphVertexStarPreimage v ↔
      a ∈ B.intrinsicBoundaryGraphVertexStarPreimage v := by
  obtain ⟨hstart, hend⟩ := B.intrinsicBoundaryGraphSide_pair_endpoints a.1
  simp only [intrinsicBoundaryGraphVertexStarPreimage, mem_setOf_eq,
    intrinsicBoundaryIntervalPair, unitInterval.coe_symm_eq, hstart, hend]
  constructor
  · rintro (⟨ht, hv⟩ | ⟨ht, hv⟩)
    · exact Or.inr ⟨by linarith, hv⟩
    · exact Or.inl ⟨by linarith, hv⟩
  · rintro (⟨ht, hv⟩ | ⟨ht, hv⟩)
    · exact Or.inr ⟨by linarith, hv⟩
    · exact Or.inl ⟨by linarith, hv⟩

/-- Explicit saturation includes all orbit-equivalent endpoint incidences. -/
theorem intrinsicBoundaryGraphVertexStarPreimage_saturated
    (B : DirichletBoundarySegments X o) (v : B.IntrinsicBoundaryGraphVertex)
    (a b : B.intrinsicBoundaryIntervalCarrier) (hab : B.intrinsicBoundaryIntervalSetoid a b) :
    a ∈ B.intrinsicBoundaryGraphVertexStarPreimage v ↔
      b ∈ B.intrinsicBoundaryGraphVertexStarPreimage v := by
  have hq := Quotient.sound hab
  rw [B.intrinsicBoundaryIntervalSetoid_iff] at hab
  rcases hab with rfl | rfl | ⟨ha, hb, _⟩
  · rfl
  · exact (B.intrinsicBoundaryGraphVertexStarPreimage_pair v a).symm
  · rw [starPreimage_endpoint_iff B v a ha, starPreimage_endpoint_iff B v b hb, hq]

theorem intrinsicBoundaryGraphEdgeMidsectionPreimage_pair
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (a : B.intrinsicBoundaryIntervalCarrier) :
    B.intrinsicBoundaryIntervalPair a ∈ B.intrinsicBoundaryGraphEdgeMidsectionPreimage i ↔
      a ∈ B.intrinsicBoundaryGraphEdgeMidsectionPreimage i := by
  have hpair : B.intrinsicCyclicPairing a.1 = i ↔ a.1 = B.intrinsicCyclicPairing i := by
    constructor
    · intro h
      simpa only [B.intrinsicCyclicPairing_involutive a.1] using
        congrArg B.intrinsicCyclicPairing h
    · intro h
      rw [h, B.intrinsicCyclicPairing_involutive i]
  have hinj : B.intrinsicCyclicPairing a.1 = B.intrinsicCyclicPairing i ↔ a.1 = i :=
    B.intrinsicCyclicPairing_involutive.injective.eq_iff
  simp only [intrinsicBoundaryGraphEdgeMidsectionPreimage, mem_setOf_eq,
    intrinsicBoundaryIntervalPair, unitInterval.coe_symm_eq, hpair, hinj]
  constructor
  · rintro ⟨hi, h0, h1⟩
    exact ⟨hi.symm, by linarith, by linarith⟩
  · rintro ⟨hi, h0, h1⟩
    exact ⟨hi.symm, by linarith, by linarith⟩

private theorem midsectionPreimage_not_endpoint (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (a : B.intrinsicBoundaryIntervalCarrier)
    (ha : a ∈ B.intrinsicBoundaryGraphEdgeMidsectionPreimage i) :
    ¬ B.IsIntrinsicBoundaryIntervalEndpoint a := by
  rintro (h | h)
  · have h0 := ha.2.1
    norm_num [h] at h0
  · have h1 := ha.2.2
    norm_num [h] at h1

/-- Midsections identify only the original reversed paired side, never distinct physical edges. -/
theorem intrinsicBoundaryGraphEdgeMidsectionPreimage_saturated
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (a b : B.intrinsicBoundaryIntervalCarrier) (hab : B.intrinsicBoundaryIntervalSetoid a b) :
    a ∈ B.intrinsicBoundaryGraphEdgeMidsectionPreimage i ↔
      b ∈ B.intrinsicBoundaryGraphEdgeMidsectionPreimage i := by
  rw [B.intrinsicBoundaryIntervalSetoid_iff] at hab
  rcases hab with rfl | rfl | ⟨ha, hb, _⟩
  · rfl
  · exact (B.intrinsicBoundaryGraphEdgeMidsectionPreimage_pair i a).symm
  · exact iff_of_false
      (fun h ↦ midsectionPreimage_not_endpoint B i a h ha)
      (fun h ↦ midsectionPreimage_not_endpoint B i b h hb)

private theorem preimage_quotient_image_eq {A : Type*} [TopologicalSpace A] (s : Setoid A)
    (U : Set A) (hU : ∀ a b, s a b → (a ∈ U ↔ b ∈ U)) :
    Quotient.mk s ⁻¹' (Quotient.mk s '' U) = U := by
  ext a
  constructor
  · rintro ⟨b, hb, hba⟩
    exact (hU b a (Quotient.exact hba)).1 hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- The native quotient preimage is exactly the specified incident interval arms. -/
theorem intrinsicBoundaryGraphVertexStar_preimage (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) :
    Quotient.mk B.intrinsicBoundaryIntervalSetoid ⁻¹' B.intrinsicBoundaryGraphVertexStar v =
      B.intrinsicBoundaryGraphVertexStarPreimage v :=
  preimage_quotient_image_eq _ _ (B.intrinsicBoundaryGraphVertexStarPreimage_saturated v)

/-- The native quotient preimage is exactly the two original paired middle intervals. -/
theorem intrinsicBoundaryGraphEdgeMidsection_preimage (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Quotient.mk B.intrinsicBoundaryIntervalSetoid ⁻¹' B.intrinsicBoundaryGraphEdgeMidsection i =
      B.intrinsicBoundaryGraphEdgeMidsectionPreimage i :=
  preimage_quotient_image_eq _ _ (B.intrinsicBoundaryGraphEdgeMidsectionPreimage_saturated i)

@[simp]
theorem intrinsicBoundaryGraphVertexStar_mem_mk (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) (a : B.intrinsicBoundaryIntervalCarrier) :
    Quotient.mk B.intrinsicBoundaryIntervalSetoid a ∈ B.intrinsicBoundaryGraphVertexStar v ↔
      a ∈ B.intrinsicBoundaryGraphVertexStarPreimage v := by
  change a ∈ Quotient.mk B.intrinsicBoundaryIntervalSetoid ⁻¹'
    B.intrinsicBoundaryGraphVertexStar v ↔ _
  rw [B.intrinsicBoundaryGraphVertexStar_preimage]

@[simp]
theorem intrinsicBoundaryGraphEdgeMidsection_mem_mk (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (a : B.intrinsicBoundaryIntervalCarrier) :
    Quotient.mk B.intrinsicBoundaryIntervalSetoid a ∈ B.intrinsicBoundaryGraphEdgeMidsection i ↔
      a ∈ B.intrinsicBoundaryGraphEdgeMidsectionPreimage i := by
  change a ∈ Quotient.mk B.intrinsicBoundaryIntervalSetoid ⁻¹'
    B.intrinsicBoundaryGraphEdgeMidsection i ↔ _
  rw [B.intrinsicBoundaryGraphEdgeMidsection_preimage]

theorem intrinsicBoundaryGraphVertexStarPreimage_isOpen (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) : IsOpen (B.intrinsicBoundaryGraphVertexStarPreimage v) := by
  have h0 : IsOpen {t : unitInterval | (t : ℝ) < 1 / 3} :=
    isOpen_lt continuous_subtype_val continuous_const
  have h1 : IsOpen {t : unitInterval | (2 / 3 : ℝ) < t} :=
    isOpen_lt continuous_const continuous_subtype_val
  convert ((isOpen_discrete {i | B.intrinsicBoundaryGraphSideStart i = v}).prod h0).union
    ((isOpen_discrete {i | B.intrinsicBoundaryGraphSideEnd i = v}).prod h1) using 1
  ext a
  simp only [intrinsicBoundaryGraphVertexStarPreimage, mem_union, mem_prod, mem_setOf_eq]
  exact or_congr and_comm and_comm

theorem intrinsicBoundaryGraphEdgeMidsectionPreimage_isOpen (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    IsOpen (B.intrinsicBoundaryGraphEdgeMidsectionPreimage i) := by
  have h0 : IsOpen {t : unitInterval | (1 / 4 : ℝ) < t} :=
    isOpen_lt continuous_const continuous_subtype_val
  have h1 : IsOpen {t : unitInterval | (t : ℝ) < 3 / 4} :=
    isOpen_lt continuous_subtype_val continuous_const
  exact (isOpen_discrete {j | j = i ∨ j = B.intrinsicCyclicPairing i}).prod (h0.inter h1)

/-- Openness follows from the explicit saturated preimage, not from openness of the quotient map. -/
theorem intrinsicBoundaryGraphVertexStar_isOpen (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) : IsOpen (B.intrinsicBoundaryGraphVertexStar v) := by
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
  change IsOpen (Quotient.mk B.intrinsicBoundaryIntervalSetoid ⁻¹'
    B.intrinsicBoundaryGraphVertexStar v)
  rw [B.intrinsicBoundaryGraphVertexStar_preimage]
  exact B.intrinsicBoundaryGraphVertexStarPreimage_isOpen v

theorem intrinsicBoundaryGraphEdgeMidsection_isOpen (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) : IsOpen (B.intrinsicBoundaryGraphEdgeMidsection i) := by
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
  change IsOpen (Quotient.mk B.intrinsicBoundaryIntervalSetoid ⁻¹'
    B.intrinsicBoundaryGraphEdgeMidsection i)
  rw [B.intrinsicBoundaryGraphEdgeMidsection_preimage]
  exact B.intrinsicBoundaryGraphEdgeMidsectionPreimage_isOpen i

/-- These actual vertex stars and physical edge middles cover the whole original graph. -/
theorem intrinsicBoundaryGraph_open_cover (B : DirichletBoundarySegments X o) :
    (⋃ v, B.intrinsicBoundaryGraphVertexStar v) ∪
      (⋃ i, B.intrinsicBoundaryGraphEdgeMidsection i) = univ := by
  apply eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ a =>
    by_cases h0 : (a.2 : ℝ) < 1 / 3
    · exact Or.inl (mem_iUnion.mpr ⟨B.intrinsicBoundaryGraphSideStart a.1,
        (B.intrinsicBoundaryGraphVertexStar_mem_mk _ a).2 (Or.inl ⟨h0, rfl⟩)⟩)
    by_cases h1 : (2 / 3 : ℝ) < a.2
    · exact Or.inl (mem_iUnion.mpr ⟨B.intrinsicBoundaryGraphSideEnd a.1,
        (B.intrinsicBoundaryGraphVertexStar_mem_mk _ a).2 (Or.inr ⟨h1, rfl⟩)⟩)
    exact Or.inr (mem_iUnion.mpr ⟨a.1,
      (B.intrinsicBoundaryGraphEdgeMidsection_mem_mk a.1 a).2
        ⟨Or.inl rfl, by linarith, by linarith⟩⟩)

theorem intrinsicBoundaryGraphVertexStar_mem_unique (B : DirichletBoundarySegments X o)
    {v w : B.IntrinsicBoundaryGraphVertex} {q : Quotient B.intrinsicBoundaryIntervalSetoid}
    (hv : q ∈ B.intrinsicBoundaryGraphVertexStar v)
    (hw : q ∈ B.intrinsicBoundaryGraphVertexStar w) : v = w := by
  induction q using Quotient.inductionOn with
  | _ a =>
    rw [B.intrinsicBoundaryGraphVertexStar_mem_mk] at hv hw
    rcases hv with ⟨h0, hv⟩ | ⟨h1, hv⟩ <;>
      rcases hw with ⟨h0', hw⟩ | ⟨h1', hw⟩
    · exact hv.symm.trans hw
    · linarith
    · linarith
    · exact hv.symm.trans hw

/-- Stars of different actual vertices are disjoint, including every loop incidence. -/
theorem intrinsicBoundaryGraphVertexStar_disjoint (B : DirichletBoundarySegments X o)
    {v w : B.IntrinsicBoundaryGraphVertex} (hvw : v ≠ w) :
    Disjoint (B.intrinsicBoundaryGraphVertexStar v) (B.intrinsicBoundaryGraphVertexStar w) := by
  apply Set.disjoint_left.mpr
  intro q hv hw
  exact hvw (B.intrinsicBoundaryGraphVertexStar_mem_unique hv hw)

/-- Duplicate cyclic indices name exactly the same physical midsection when they are paired. -/
theorem intrinsicBoundaryGraphEdgeMidsection_pair (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphEdgeMidsection (B.intrinsicCyclicPairing i) =
      B.intrinsicBoundaryGraphEdgeMidsection i := by
  ext q
  induction q using Quotient.inductionOn with
  | _ a =>
    simp only [B.intrinsicBoundaryGraphEdgeMidsection_mem_mk,
      intrinsicBoundaryGraphEdgeMidsectionPreimage, mem_setOf_eq,
      B.intrinsicCyclicPairing_involutive i, or_comm]

theorem intrinsicBoundaryGraphEdgeMidsection_mem_unique (B : DirichletBoundarySegments X o)
    {i j : Fin B.intrinsicBoundaryRadialCuts.card}
    {q : Quotient B.intrinsicBoundaryIntervalSetoid}
    (hi : q ∈ B.intrinsicBoundaryGraphEdgeMidsection i)
    (hj : q ∈ B.intrinsicBoundaryGraphEdgeMidsection j) :
    j = i ∨ j = B.intrinsicCyclicPairing i := by
  induction q using Quotient.inductionOn with
  | _ a =>
    rw [B.intrinsicBoundaryGraphEdgeMidsection_mem_mk] at hi hj
    rcases hi.1 with hi | hi <;> rcases hj.1 with hj | hj
    · exact Or.inl (hj.symm.trans hi)
    · right
      have h := congrArg B.intrinsicCyclicPairing (hj.symm.trans hi)
      simpa only [B.intrinsicCyclicPairing_involutive j] using h
    · exact Or.inr (hj.symm.trans hi)
    · exact Or.inl (B.intrinsicCyclicPairing_involutive.injective (hj.symm.trans hi))

/-- No two distinct physical midsections overlap; parallel edges are not conflated. -/
theorem intrinsicBoundaryGraphEdgeMidsection_disjoint (B : DirichletBoundarySegments X o)
    {i j : Fin B.intrinsicBoundaryRadialCuts.card} (hji : j ≠ i)
    (hjpair : j ≠ B.intrinsicCyclicPairing i) :
    Disjoint (B.intrinsicBoundaryGraphEdgeMidsection i)
      (B.intrinsicBoundaryGraphEdgeMidsection j) := by
  apply Set.disjoint_left.mpr
  intro q hi hj
  exact (B.intrinsicBoundaryGraphEdgeMidsection_mem_unique hi hj).elim hji hjpair

/-- Exact two-arm overlap formula on the literal intervals. A loop edge retains both arms. -/
theorem intrinsicBoundaryGraphStarMidsection_mem_mk (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (a : B.intrinsicBoundaryIntervalCarrier) :
    Quotient.mk B.intrinsicBoundaryIntervalSetoid a ∈
        B.intrinsicBoundaryGraphVertexStar v ∩ B.intrinsicBoundaryGraphEdgeMidsection i ↔
      (a.1 = i ∨ a.1 = B.intrinsicCyclicPairing i) ∧
        (((1 / 4 : ℝ) < a.2 ∧ (a.2 : ℝ) < 1 / 3 ∧
            B.intrinsicBoundaryGraphSideStart a.1 = v) ∨
          ((2 / 3 : ℝ) < a.2 ∧ (a.2 : ℝ) < 3 / 4 ∧
            B.intrinsicBoundaryGraphSideEnd a.1 = v)) := by
  rw [mem_inter_iff, B.intrinsicBoundaryGraphVertexStar_mem_mk,
    B.intrinsicBoundaryGraphEdgeMidsection_mem_mk]
  constructor
  · rintro ⟨⟨h0, hv⟩ | ⟨h1, hv⟩, hi, hlow, hupp⟩
    · exact ⟨hi, Or.inl ⟨hlow, h0, hv⟩⟩
    · exact ⟨hi, Or.inr ⟨h1, hupp, hv⟩⟩
  · rintro ⟨hi, ⟨hlow, h0, hv⟩ | ⟨h1, hupp, hv⟩⟩
    · exact ⟨Or.inl ⟨h0, hv⟩, hi, hlow, by linarith⟩
    · exact ⟨Or.inr ⟨h1, hv⟩, hi, by linarith, hupp⟩

/-- Every actual orbit vertex lies in its own star. -/
theorem intrinsicBoundaryGraphVertexInclusion_mem_star (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryGraphVertexInclusion v ∈ B.intrinsicBoundaryGraphVertexStar v := by
  induction v using Quotient.inductionOn with
  | _ i =>
    change B.intrinsicBoundaryGraphVertexInclusion (B.intrinsicBoundaryGraphSideStart i) ∈ _
    rw [B.intrinsicBoundaryGraphVertexInclusion_start,
      B.intrinsicBoundaryGraphVertexStar_mem_mk,
      B.intrinsicBoundaryGraphVertexStarPreimage_zero]
    rfl

/-- No actual vertex is in an edge midsection. -/
theorem intrinsicBoundaryGraphVertexInclusion_not_mem_midsection
    (B : DirichletBoundarySegments X o) (v : B.IntrinsicBoundaryGraphVertex)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphVertexInclusion v ∉ B.intrinsicBoundaryGraphEdgeMidsection i := by
  induction v using Quotient.inductionOn with
  | _ j =>
    change B.intrinsicBoundaryGraphVertexInclusion (B.intrinsicBoundaryGraphSideStart j) ∉ _
    rw [B.intrinsicBoundaryGraphVertexInclusion_start,
      B.intrinsicBoundaryGraphEdgeMidsection_mem_mk]
    intro h
    exact midsectionPreimage_not_endpoint B i (j, 0) h (Or.inl rfl)

/-- A continuous symmetric endpoint selector: it is zero on each initial star arm and one
on each terminal arm. Its middle part is retained solely to make a global continuous map. -/
def Internal.SurfaceBoundaryGraphOpenCoverHelpers.starEndpointParameter (s : unitInterval) : unitInterval :=
  projIcc 0 1 zero_le_one (3 * (s : ℝ) - 1)

private theorem continuous_starEndpointParameter : Continuous Internal.SurfaceBoundaryGraphOpenCoverHelpers.starEndpointParameter :=
  continuous_projIcc.comp (by fun_prop)

private theorem starEndpointParameter_symm (s : unitInterval) :
    Internal.SurfaceBoundaryGraphOpenCoverHelpers.starEndpointParameter (unitInterval.symm s) = unitInterval.symm (Internal.SurfaceBoundaryGraphOpenCoverHelpers.starEndpointParameter s) := by
  rw [Internal.SurfaceBoundaryGraphOpenCoverHelpers.starEndpointParameter, Internal.SurfaceBoundaryGraphOpenCoverHelpers.starEndpointParameter, unitInterval.symm_projIcc]
  congr 1
  rw [unitInterval.coe_symm_eq]
  ring

private theorem starEndpointParameter_eq_zero {s : unitInterval} (hs : (s : ℝ) < 1 / 3) :
    Internal.SurfaceBoundaryGraphOpenCoverHelpers.starEndpointParameter s = 0 := by
  exact projIcc_eq_zero.mpr (by linarith)

private theorem starEndpointParameter_eq_one {s : unitInterval} (hs : (2 / 3 : ℝ) < s) :
    Internal.SurfaceBoundaryGraphOpenCoverHelpers.starEndpointParameter s = 1 := by
  exact projIcc_eq_one.mpr (by linarith)

def Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushParameter (t s : unitInterval) : unitInterval :=
  Icc.convexComb s (Internal.SurfaceBoundaryGraphOpenCoverHelpers.starEndpointParameter s) t

private theorem starPushParameter_symm (t s : unitInterval) :
    Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushParameter t (unitInterval.symm s) = unitInterval.symm (Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushParameter t s) := by
  apply Subtype.ext
  simp only [Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushParameter, Icc.coe_convexComb, starEndpointParameter_symm,
    unitInterval.coe_symm_eq]
  ring

@[simp] private theorem starPushParameter_zero (s : unitInterval) : Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushParameter 0 s = s :=
  Icc.convexComb_zero _ _

@[simp] private theorem starPushParameter_at_zero (t : unitInterval) :
    Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushParameter t 0 = 0 := by
  rw [Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushParameter, starEndpointParameter_eq_zero (by norm_num)]
  exact Icc.convexComb_eq _ _

@[simp] private theorem starPushParameter_at_one (t : unitInterval) :
    Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushParameter t 1 = 1 := by
  rw [Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushParameter, starEndpointParameter_eq_one (by norm_num)]
  exact Icc.convexComb_eq _ _

def Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushInterval (B : DirichletBoundarySegments X o) (t : unitInterval)
    (a : B.intrinsicBoundaryIntervalCarrier) : B.intrinsicBoundaryIntervalCarrier :=
  (a.1, Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushParameter t a.2)

private theorem starPushInterval_pair (B : DirichletBoundarySegments X o)
    (t : unitInterval) (a : B.intrinsicBoundaryIntervalCarrier) :
    Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushInterval B t (B.intrinsicBoundaryIntervalPair a) =
      B.intrinsicBoundaryIntervalPair (Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushInterval B t a) :=
  Prod.ext rfl (starPushParameter_symm t a.2)

private theorem starPushInterval_endpoint (B : DirichletBoundarySegments X o)
    (t : unitInterval) (a : B.intrinsicBoundaryIntervalCarrier)
    (ha : B.IsIntrinsicBoundaryIntervalEndpoint a) : Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushInterval B t a = a := by
  change (a.1, Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushParameter t a.2) = a
  apply Prod.ext
  · rfl
  rcases ha with h | h <;> simp only [h,
    starPushParameter_at_zero, starPushParameter_at_one]

theorem Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushInterval_respects (B : DirichletBoundarySegments X o)
    (t : unitInterval) (a b : B.intrinsicBoundaryIntervalCarrier)
    (hab : B.intrinsicBoundaryIntervalSetoid a b) :
    Quotient.mk B.intrinsicBoundaryIntervalSetoid (Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushInterval B t a) =
      Quotient.mk B.intrinsicBoundaryIntervalSetoid (Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushInterval B t b) := by
  have hq := Quotient.sound hab
  rw [B.intrinsicBoundaryIntervalSetoid_iff] at hab
  rcases hab with rfl | rfl | ⟨ha, hb, _⟩
  · rfl
  · apply Quotient.sound
    change B.intrinsicBoundaryIntervalSetoid (Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushInterval B t a)
      (Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushInterval B t (B.intrinsicBoundaryIntervalPair a))
    rw [B.intrinsicBoundaryIntervalSetoid_iff, starPushInterval_pair]
    exact Or.inr (Or.inl rfl)
  · rw [starPushInterval_endpoint B t a ha, starPushInterval_endpoint B t b hb]
    exact hq

/-- The actual endpoint-directed graph homotopy. All original endpoint identifications are
fixed and all original side reversals remain exact throughout. -/
def intrinsicBoundaryGraphStarPush (B : DirichletBoundarySegments X o) (t : unitInterval) :
    Quotient B.intrinsicBoundaryIntervalSetoid → Quotient B.intrinsicBoundaryIntervalSetoid :=
  Quotient.lift (fun a ↦ Quotient.mk B.intrinsicBoundaryIntervalSetoid (Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushInterval B t a))
    (Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushInterval_respects B t)

@[simp]
theorem intrinsicBoundaryGraphStarPush_mk (B : DirichletBoundarySegments X o)
    (t : unitInterval) (a : B.intrinsicBoundaryIntervalCarrier) :
    B.intrinsicBoundaryGraphStarPush t (Quotient.mk B.intrinsicBoundaryIntervalSetoid a) =
      Quotient.mk B.intrinsicBoundaryIntervalSetoid
        (a.1, Icc.convexComb a.2 (projIcc 0 1 zero_le_one (3 * (a.2 : ℝ) - 1)) t) := rfl

theorem continuous_intrinsicBoundaryGraphStarPush (B : DirichletBoundarySegments X o) :
    Continuous (fun p : unitInterval × Quotient B.intrinsicBoundaryIntervalSetoid ↦
      B.intrinsicBoundaryGraphStarPush p.1 p.2) := by
  apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
  change Continuous (fun p : unitInterval × B.intrinsicBoundaryIntervalCarrier ↦
    Quotient.mk B.intrinsicBoundaryIntervalSetoid (Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushInterval B p.1 p.2))
  apply continuous_quotient_mk'.comp
  apply Continuous.prodMk (by fun_prop)
  exact Icc.continuous_convexComb_prod.comp
    ((by fun_prop : Continuous (fun p : unitInterval × B.intrinsicBoundaryIntervalCarrier ↦ p.2.2)).prodMk
      ((continuous_starEndpointParameter.comp (by fun_prop)).prodMk continuous_fst))

@[simp]
theorem intrinsicBoundaryGraphStarPush_zero (B : DirichletBoundarySegments X o)
    (q : Quotient B.intrinsicBoundaryIntervalSetoid) : B.intrinsicBoundaryGraphStarPush 0 q = q := by
  induction q using Quotient.inductionOn with
  | _ a => exact congrArg (Quotient.mk _) (Prod.ext rfl (starPushParameter_zero a.2))

@[simp]
theorem intrinsicBoundaryGraphStarPush_vertex (B : DirichletBoundarySegments X o)
    (t : unitInterval) (v : B.IntrinsicBoundaryGraphVertex) :
    B.intrinsicBoundaryGraphStarPush t (B.intrinsicBoundaryGraphVertexInclusion v) =
      B.intrinsicBoundaryGraphVertexInclusion v := by
  induction v using Quotient.inductionOn with
  | _ i =>
    change B.intrinsicBoundaryGraphStarPush t
      (B.intrinsicBoundaryGraphVertexInclusion (B.intrinsicBoundaryGraphSideStart i)) = _
    rw [B.intrinsicBoundaryGraphVertexInclusion_start]
    exact congrArg (Quotient.mk _) (starPushInterval_endpoint B t (i, 0) (Or.inl rfl))

private theorem starPushInterval_mem_star (B : DirichletBoundarySegments X o)
    (t : unitInterval) (v : B.IntrinsicBoundaryGraphVertex)
    (a : B.intrinsicBoundaryIntervalCarrier) (ha : a ∈ B.intrinsicBoundaryGraphVertexStarPreimage v) :
    Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushInterval B t a ∈ B.intrinsicBoundaryGraphVertexStarPreimage v := by
  rcases ha with ⟨h0, hv⟩ | ⟨h1, hv⟩
  · left
    refine ⟨?_, hv⟩
    change (Icc.convexComb a.2 (Internal.SurfaceBoundaryGraphOpenCoverHelpers.starEndpointParameter a.2) t : ℝ) < 1 / 3
    rw [starEndpointParameter_eq_zero h0, Icc.coe_convexComb]
    simp only [Set.Icc.coe_zero, mul_zero, add_zero]
    nlinarith [t.2.1, t.2.2, a.2.2.1]
  · right
    refine ⟨?_, hv⟩
    change (2 / 3 : ℝ) < (Icc.convexComb a.2 (Internal.SurfaceBoundaryGraphOpenCoverHelpers.starEndpointParameter a.2) t : ℝ)
    rw [starEndpointParameter_eq_one h1, Icc.coe_convexComb]
    simp only [Set.Icc.coe_one, mul_one]
    nlinarith [t.2.1, t.2.2, a.2.2.2]

theorem intrinsicBoundaryGraphStarPush_mem_star (B : DirichletBoundarySegments X o)
    (t : unitInterval) (v : B.IntrinsicBoundaryGraphVertex)
    (q : Quotient B.intrinsicBoundaryIntervalSetoid) (hq : q ∈ B.intrinsicBoundaryGraphVertexStar v) :
    B.intrinsicBoundaryGraphStarPush t q ∈ B.intrinsicBoundaryGraphVertexStar v := by
  induction q using Quotient.inductionOn with
  | _ a =>
    rw [B.intrinsicBoundaryGraphVertexStar_mem_mk] at hq
    exact (B.intrinsicBoundaryGraphVertexStar_mem_mk v (Internal.SurfaceBoundaryGraphOpenCoverHelpers.starPushInterval B t a)).2
      (starPushInterval_mem_star B t v a hq)

theorem intrinsicBoundaryGraphStarPush_one (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) (q : Quotient B.intrinsicBoundaryIntervalSetoid)
    (hq : q ∈ B.intrinsicBoundaryGraphVertexStar v) :
    B.intrinsicBoundaryGraphStarPush 1 q = B.intrinsicBoundaryGraphVertexInclusion v := by
  induction q using Quotient.inductionOn with
  | _ a =>
    rw [B.intrinsicBoundaryGraphVertexStar_mem_mk] at hq
    rcases hq with ⟨h0, hv⟩ | ⟨h1, hv⟩
    · change Quotient.mk _ (a.1, Icc.convexComb a.2 (Internal.SurfaceBoundaryGraphOpenCoverHelpers.starEndpointParameter a.2) 1) = _
      rw [Icc.convexComb_one, starEndpointParameter_eq_zero h0,
        ← B.intrinsicBoundaryGraphVertexInclusion_start, hv]
    · change Quotient.mk _ (a.1, Icc.convexComb a.2 (Internal.SurfaceBoundaryGraphOpenCoverHelpers.starEndpointParameter a.2) 1) = _
      rw [Icc.convexComb_one, starEndpointParameter_eq_one h1,
        ← B.intrinsicBoundaryGraphVertexInclusion_end, hv]

/-- The actual central vertex, regarded as a point of its open star. -/
def intrinsicBoundaryGraphStarCenter (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) : B.intrinsicBoundaryGraphVertexStar v :=
  ⟨B.intrinsicBoundaryGraphVertexInclusion v, B.intrinsicBoundaryGraphVertexInclusion_mem_star v⟩

/-- A genuine contraction of every open vertex star, fixing its original vertex throughout. -/
def intrinsicBoundaryGraphVertexStarContraction (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) :
    (ContinuousMap.id ↥(B.intrinsicBoundaryGraphVertexStar v)).Homotopy
      (ContinuousMap.const _ (B.intrinsicBoundaryGraphStarCenter v)) where
  toFun p := ⟨B.intrinsicBoundaryGraphStarPush p.1 p.2.1,
    B.intrinsicBoundaryGraphStarPush_mem_star p.1 v p.2.1 p.2.2⟩
  continuous_toFun := (B.continuous_intrinsicBoundaryGraphStarPush.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left q := Subtype.ext (B.intrinsicBoundaryGraphStarPush_zero q.1)
  map_one_left q := Subtype.ext (B.intrinsicBoundaryGraphStarPush_one v q.1 q.2)

@[simp]
theorem intrinsicBoundaryGraphVertexStarContraction_fixed (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) (t : unitInterval) :
    B.intrinsicBoundaryGraphVertexStarContraction v (t, B.intrinsicBoundaryGraphStarCenter v) =
      B.intrinsicBoundaryGraphStarCenter v :=
  Subtype.ext (B.intrinsicBoundaryGraphStarPush_vertex t v)

instance (B : DirichletBoundarySegments X o) (v : B.IntrinsicBoundaryGraphVertex) :
    ContractibleSpace ↥(B.intrinsicBoundaryGraphVertexStar v) :=
  (contractible_iff_id_nullhomotopic _).2
    ⟨B.intrinsicBoundaryGraphStarCenter v, ⟨B.intrinsicBoundaryGraphVertexStarContraction v⟩⟩

def Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionUnitParameter (s : Ioo (1 / 4 : ℝ) (3 / 4)) : unitInterval :=
  ⟨s.1, by constructor <;> linarith [s.2.1, s.2.2]⟩

theorem Internal.SurfaceBoundaryGraphOpenCoverHelpers.continuous_midsectionUnitParameter : Continuous Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionUnitParameter :=
  continuous_subtype_val.subtype_mk _

/-- The literal oriented side parametrizes its entire physical open midsection. -/
def intrinsicBoundaryGraphMidsectionParameterMap (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    C(↥(Ioo (1 / 4 : ℝ) (3 / 4)), ↥(B.intrinsicBoundaryGraphEdgeMidsection i)) where
  toFun s := ⟨Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionUnitParameter s),
    (B.intrinsicBoundaryGraphEdgeMidsection_mem_mk i _).2 ⟨Or.inl rfl, s.2⟩⟩
  continuous_toFun := (continuous_quotient_mk'.comp
    (continuous_const.prodMk Internal.SurfaceBoundaryGraphOpenCoverHelpers.continuous_midsectionUnitParameter)).subtype_mk _

theorem intrinsicBoundaryGraphMidsectionParameterMap_injective
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Function.Injective (B.intrinsicBoundaryGraphMidsectionParameterMap i) := by
  intro s t h
  have hrel : B.intrinsicBoundaryIntervalSetoid (i, Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionUnitParameter s)
      (i, Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionUnitParameter t) := Quotient.exact (congrArg Subtype.val h)
  rw [B.intrinsicBoundaryIntervalSetoid_iff] at hrel
  rcases hrel with h | h | ⟨hs, _, _⟩
  · exact Subtype.ext (congrArg (fun a ↦ (a.2 : ℝ)) h)
  · exact False.elim (B.intrinsicCyclicPairing_ne_self i (congrArg Prod.fst h).symm)
  · have hmem : (i, Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionUnitParameter s) ∈ B.intrinsicBoundaryGraphEdgeMidsectionPreimage i :=
      ⟨Or.inl rfl, s.2⟩
    exact False.elim (midsectionPreimage_not_endpoint B i _ hmem hs)

def Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (a : B.intrinsicBoundaryIntervalCarrier) : ℝ :=
  if a.1 = i then (a.2 : ℝ) else 1 - a.2

theorem Internal.SurfaceBoundaryGraphOpenCoverHelpers.continuous_midsectionCoordinate (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) : Continuous (Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate B i) := by
  apply continuous_prod_of_discrete_left.2
  intro j
  by_cases hji : j = i
  · simp only [Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate, hji, if_true]
    fun_prop
  · simp only [Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate, hji, if_false]
    fun_prop

theorem Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate_mem (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (a : B.intrinsicBoundaryIntervalCarrier)
    (ha : a ∈ B.intrinsicBoundaryGraphEdgeMidsectionPreimage i) :
    Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate B i a ∈ Ioo (1 / 4 : ℝ) (3 / 4) := by
  unfold Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate
  split_ifs
  · exact ha.2
  · exact ⟨by linarith [ha.2.2], by linarith [ha.2.1]⟩

theorem Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionParameterMap_coordinate (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (a : B.intrinsicBoundaryIntervalCarrier)
    (ha : a ∈ B.intrinsicBoundaryGraphEdgeMidsectionPreimage i) :
    (B.intrinsicBoundaryGraphMidsectionParameterMap i
      ⟨Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate B i a, Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate_mem B i a ha⟩).1 =
        Quotient.mk B.intrinsicBoundaryIntervalSetoid a := by
  rcases ha.1 with hi | hi
  · apply congrArg (Quotient.mk _)
    apply Prod.ext
    · exact hi.symm
    · apply Subtype.ext
      simp only [Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionUnitParameter, Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate, hi, if_true]
  · have hne : a.1 ≠ i := hi ▸ B.intrinsicCyclicPairing_ne_self i
    apply Quotient.sound
    change B.intrinsicBoundaryIntervalSetoid
      (i, Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionUnitParameter ⟨Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate B i a, _⟩) a
    rw [B.intrinsicBoundaryIntervalSetoid_iff]
    right
    left
    apply Prod.ext
    · exact hi
    · apply Subtype.ext
      simp only [intrinsicBoundaryIntervalPair, unitInterval.coe_symm_eq,
        Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionUnitParameter, Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate, hne, if_false]
      ring

theorem intrinsicBoundaryGraphMidsectionParameterMap_surjective
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Function.Surjective (B.intrinsicBoundaryGraphMidsectionParameterMap i) := by
  rintro ⟨q, hq⟩
  induction q using Quotient.inductionOn with
  | _ a =>
    have ha := (B.intrinsicBoundaryGraphEdgeMidsection_mem_mk i a).1 hq
    exact ⟨⟨Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate B i a, Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate_mem B i a ha⟩,
      Subtype.ext (Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionParameterMap_coordinate B i a ha)⟩

def Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionPreimageCoordinateMap (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    C(↥(Quotient.mk B.intrinsicBoundaryIntervalSetoid ⁻¹'
      B.intrinsicBoundaryGraphEdgeMidsection i), ↥(Ioo (1 / 4 : ℝ) (3 / 4))) where
  toFun a := ⟨Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate B i a.1, Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate_mem B i a.1
    ((B.intrinsicBoundaryGraphEdgeMidsection_mem_mk i a.1).1 a.2)⟩
  continuous_toFun := ((Internal.SurfaceBoundaryGraphOpenCoverHelpers.continuous_midsectionCoordinate B i).comp
    continuous_subtype_val).subtype_mk _

/-- A native interval homeomorphism for each physical midsection, with its original side
orientation. Its inverse reverses the original parameter on the paired side. -/
def intrinsicBoundaryGraphMidsectionHomeomorph (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    ↥(Ioo (1 / 4 : ℝ) (3 / 4)) ≃ₜ ↥(B.intrinsicBoundaryGraphEdgeMidsection i) := by
  let e := Equiv.ofBijective (B.intrinsicBoundaryGraphMidsectionParameterMap i)
    ⟨B.intrinsicBoundaryGraphMidsectionParameterMap_injective i,
      B.intrinsicBoundaryGraphMidsectionParameterMap_surjective i⟩
  refine { toEquiv := e, continuous_toFun :=
    (B.intrinsicBoundaryGraphMidsectionParameterMap i).continuous, continuous_invFun := ?_ }
  have hquot : Topology.IsQuotientMap
      ((B.intrinsicBoundaryGraphEdgeMidsection i).restrictPreimage
        (Quotient.mk B.intrinsicBoundaryIntervalSetoid)) :=
    isQuotientMap_quotient_mk'.restrictPreimage_isOpen
      (B.intrinsicBoundaryGraphEdgeMidsection_isOpen i)
  rw [hquot.continuous_iff]
  change Continuous (e.symm ∘ (B.intrinsicBoundaryGraphEdgeMidsection i).restrictPreimage
    (Quotient.mk B.intrinsicBoundaryIntervalSetoid))
  have heq : e.symm ∘ (B.intrinsicBoundaryGraphEdgeMidsection i).restrictPreimage
      (Quotient.mk B.intrinsicBoundaryIntervalSetoid) = Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionPreimageCoordinateMap B i := by
    funext a
    apply e.injective
    rw [Function.comp_apply, e.apply_symm_apply]
    exact (Subtype.ext (Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionParameterMap_coordinate B i a.1
      ((B.intrinsicBoundaryGraphEdgeMidsection_mem_mk i a.1).1 a.2))).symm
  rw [heq]
  exact (Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionPreimageCoordinateMap B i).continuous

@[simp]
theorem intrinsicBoundaryGraphMidsectionHomeomorph_apply (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (s : Ioo (1 / 4 : ℝ) (3 / 4)) :
    (B.intrinsicBoundaryGraphMidsectionHomeomorph i s).1 =
      Quotient.mk B.intrinsicBoundaryIntervalSetoid (i, Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionUnitParameter s) := by
  change (B.intrinsicBoundaryGraphMidsectionParameterMap i s).1 = _
  rfl

/-- The inverse reads the original parameter on the chosen side and its reversal on its mate. -/
theorem intrinsicBoundaryGraphMidsectionHomeomorph_symm_mk
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (a : B.intrinsicBoundaryIntervalCarrier)
    (ha : a ∈ B.intrinsicBoundaryGraphEdgeMidsectionPreimage i) :
    ((B.intrinsicBoundaryGraphMidsectionHomeomorph i).symm
      ⟨Quotient.mk B.intrinsicBoundaryIntervalSetoid a,
        (B.intrinsicBoundaryGraphEdgeMidsection_mem_mk i a).2 ha⟩).1 =
      if a.1 = i then (a.2 : ℝ) else 1 - a.2 := by
  have hpoint : B.intrinsicBoundaryGraphMidsectionHomeomorph i
      ⟨Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate B i a, Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionCoordinate_mem B i a ha⟩ =
        ⟨Quotient.mk B.intrinsicBoundaryIntervalSetoid a,
          (B.intrinsicBoundaryGraphEdgeMidsection_mem_mk i a).2 ha⟩ :=
    Subtype.ext (Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionParameterMap_coordinate B i a ha)
  have h := congrArg (B.intrinsicBoundaryGraphMidsectionHomeomorph i).symm hpoint
  rw [(B.intrinsicBoundaryGraphMidsectionHomeomorph i).symm_apply_apply] at h
  exact (congrArg Subtype.val h).symm

instance (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    ContractibleSpace ↥(B.intrinsicBoundaryGraphEdgeMidsection i) := by
  letI : ContractibleSpace ↥(Ioo (1 / 4 : ℝ) (3 / 4)) :=
    (convex_Ioo (1 / 4 : ℝ) (3 / 4)).contractibleSpace ⟨1 / 2, by constructor <;> norm_num⟩
  exact (B.intrinsicBoundaryGraphMidsectionHomeomorph i).symm.contractibleSpace

def Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionGraphParameter (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (s : Ioo (1 / 4 : ℝ) (3 / 4)) :
    Quotient B.intrinsicBoundaryIntervalSetoid :=
  (B.intrinsicBoundaryGraphMidsectionHomeomorph i s).1

theorem Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionGraphParameter_isOpenEmbedding (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Topology.IsOpenEmbedding (Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionGraphParameter B i) :=
  (B.intrinsicBoundaryGraphEdgeMidsection_isOpen i).isOpenEmbedding_subtypeVal.comp
    (B.intrinsicBoundaryGraphMidsectionHomeomorph i).isOpenEmbedding

/-- The initial half-arm of the actual side/star overlap. -/
def intrinsicBoundaryGraphInitialOverlap (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Set (Quotient B.intrinsicBoundaryIntervalSetoid) :=
  Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionGraphParameter B i '' {s | (s : ℝ) < 1 / 3}

/-- The terminal half-arm. It stays separate from the initial half even on a loop edge. -/
def intrinsicBoundaryGraphTerminalOverlap (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Set (Quotient B.intrinsicBoundaryIntervalSetoid) :=
  Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionGraphParameter B i '' {s | (2 / 3 : ℝ) < s}

theorem intrinsicBoundaryGraphInitialOverlap_isOpen (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) : IsOpen (B.intrinsicBoundaryGraphInitialOverlap i) :=
  (Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionGraphParameter_isOpenEmbedding B i).isOpenMap _
    (isOpen_lt continuous_subtype_val continuous_const)

theorem intrinsicBoundaryGraphTerminalOverlap_isOpen (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) : IsOpen (B.intrinsicBoundaryGraphTerminalOverlap i) :=
  (Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionGraphParameter_isOpenEmbedding B i).isOpenMap _
    (isOpen_lt continuous_const continuous_subtype_val)

theorem intrinsicBoundaryGraphInitialOverlap_subset_midsection
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphInitialOverlap i ⊆ B.intrinsicBoundaryGraphEdgeMidsection i := by
  rintro q ⟨s, _, rfl⟩
  exact (B.intrinsicBoundaryGraphMidsectionHomeomorph i s).2

theorem intrinsicBoundaryGraphTerminalOverlap_subset_midsection
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphTerminalOverlap i ⊆ B.intrinsicBoundaryGraphEdgeMidsection i := by
  rintro q ⟨s, _, rfl⟩
  exact (B.intrinsicBoundaryGraphMidsectionHomeomorph i s).2

theorem intrinsicBoundaryGraphInitialOverlap_subset_star
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphInitialOverlap i ⊆
      B.intrinsicBoundaryGraphVertexStar (B.intrinsicBoundaryGraphSideStart i) := by
  rintro q ⟨s, hs, rfl⟩
  change (B.intrinsicBoundaryGraphMidsectionHomeomorph i s).1 ∈ _
  rw [B.intrinsicBoundaryGraphMidsectionHomeomorph_apply,
    B.intrinsicBoundaryGraphVertexStar_mem_mk]
  exact Or.inl ⟨hs, rfl⟩

theorem intrinsicBoundaryGraphTerminalOverlap_subset_star
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphTerminalOverlap i ⊆
      B.intrinsicBoundaryGraphVertexStar (B.intrinsicBoundaryGraphSideEnd i) := by
  rintro q ⟨s, hs, rfl⟩
  change (B.intrinsicBoundaryGraphMidsectionHomeomorph i s).1 ∈ _
  rw [B.intrinsicBoundaryGraphMidsectionHomeomorph_apply,
    B.intrinsicBoundaryGraphVertexStar_mem_mk]
  exact Or.inr ⟨hs, rfl⟩

/-- The two actual half-arm components are disjoint, including when their vertices coincide. -/
theorem intrinsicBoundaryGraphOverlap_halves_disjoint (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Disjoint (B.intrinsicBoundaryGraphInitialOverlap i) (B.intrinsicBoundaryGraphTerminalOverlap i) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨s, hs, hsq⟩ ⟨t, ht, htq⟩
  have hst := (Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionGraphParameter_isOpenEmbedding B i).injective (hsq.trans htq.symm)
  subst t
  change (s : ℝ) < 1 / 3 at hs
  change (2 / 3 : ℝ) < s at ht
  linarith

/-- Exactly the incident half-arms form the star/edge overlap. Loop edges retain two
disjoint components; multiple physical edges retain their distinct midsections. -/
theorem intrinsicBoundaryGraphStarMidsection_eq_halves (B : DirichletBoundarySegments X o)
    (v : B.IntrinsicBoundaryGraphVertex) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphVertexStar v ∩ B.intrinsicBoundaryGraphEdgeMidsection i =
      (if B.intrinsicBoundaryGraphSideStart i = v then B.intrinsicBoundaryGraphInitialOverlap i else ∅) ∪
      (if B.intrinsicBoundaryGraphSideEnd i = v then B.intrinsicBoundaryGraphTerminalOverlap i else ∅) := by
  ext q
  constructor
  · rintro ⟨hstar, hmid⟩
    obtain ⟨s, hs⟩ := B.intrinsicBoundaryGraphMidsectionParameterMap_surjective i ⟨q, hmid⟩
    have hpoint : Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionGraphParameter B i s = q := congrArg Subtype.val hs
    have hraw : (i, Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionUnitParameter s) ∈ B.intrinsicBoundaryGraphVertexStarPreimage v := by
      apply (B.intrinsicBoundaryGraphVertexStar_mem_mk v _).1
      rw [← hpoint] at hstar
      change (B.intrinsicBoundaryGraphMidsectionHomeomorph i s).1 ∈ _ at hstar
      rw [B.intrinsicBoundaryGraphMidsectionHomeomorph_apply] at hstar
      exact hstar
    rcases hraw with ⟨h0, hv⟩ | ⟨h1, hv⟩
    · left
      rw [if_pos hv]
      exact ⟨s, h0, hpoint⟩
    · right
      rw [if_pos hv]
      exact ⟨s, h1, hpoint⟩
  · rintro (hq | hq)
    · by_cases hv : B.intrinsicBoundaryGraphSideStart i = v
      · rw [if_pos hv] at hq
        exact ⟨hv ▸ B.intrinsicBoundaryGraphInitialOverlap_subset_star i hq,
          B.intrinsicBoundaryGraphInitialOverlap_subset_midsection i hq⟩
      · simp only [if_neg hv, mem_empty_iff_false] at hq
    · by_cases hv : B.intrinsicBoundaryGraphSideEnd i = v
      · rw [if_pos hv] at hq
        exact ⟨hv ▸ B.intrinsicBoundaryGraphTerminalOverlap_subset_star i hq,
          B.intrinsicBoundaryGraphTerminalOverlap_subset_midsection i hq⟩
      · simp only [if_neg hv, mem_empty_iff_false] at hq

def Internal.SurfaceBoundaryGraphOpenCoverHelpers.initialOverlapParameterHomeomorph :
    ↥(Ioo (1 / 4 : ℝ) (1 / 3)) ≃ₜ {s : Ioo (1 / 4 : ℝ) (3 / 4) | (s : ℝ) < 1 / 3} where
  toFun s := ⟨⟨s.1, s.2.1, by linarith [s.2.2]⟩, s.2.2⟩
  invFun s := ⟨s.1.1, s.1.2.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def Internal.SurfaceBoundaryGraphOpenCoverHelpers.terminalOverlapParameterHomeomorph :
    ↥(Ioo (2 / 3 : ℝ) (3 / 4)) ≃ₜ {s : Ioo (1 / 4 : ℝ) (3 / 4) | (2 / 3 : ℝ) < s} where
  toFun s := ⟨⟨s.1, by linarith [s.2.1], s.2.2⟩, s.2.1⟩
  invFun s := ⟨s.1.1, s.2, s.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- A genuine interval homeomorphism onto the actual initial overlap component. -/
def intrinsicBoundaryGraphInitialOverlapHomeomorph (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    ↥(Ioo (1 / 4 : ℝ) (1 / 3)) ≃ₜ ↥(B.intrinsicBoundaryGraphInitialOverlap i) :=
  Internal.SurfaceBoundaryGraphOpenCoverHelpers.initialOverlapParameterHomeomorph.trans
    ((Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionGraphParameter_isOpenEmbedding B i).isEmbedding.homeomorphImage _)

/-- A genuine interval homeomorphism onto the actual terminal overlap component. -/
def intrinsicBoundaryGraphTerminalOverlapHomeomorph (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    ↥(Ioo (2 / 3 : ℝ) (3 / 4)) ≃ₜ ↥(B.intrinsicBoundaryGraphTerminalOverlap i) :=
  Internal.SurfaceBoundaryGraphOpenCoverHelpers.terminalOverlapParameterHomeomorph.trans
    ((Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionGraphParameter_isOpenEmbedding B i).isEmbedding.homeomorphImage _)

instance (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    ContractibleSpace ↥(B.intrinsicBoundaryGraphInitialOverlap i) := by
  letI : ContractibleSpace ↥(Ioo (1 / 4 : ℝ) (1 / 3)) :=
    (convex_Ioo (1 / 4 : ℝ) (1 / 3)).contractibleSpace ⟨7 / 24, by constructor <;> norm_num⟩
  exact (B.intrinsicBoundaryGraphInitialOverlapHomeomorph i).symm.contractibleSpace

instance (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    ContractibleSpace ↥(B.intrinsicBoundaryGraphTerminalOverlap i) := by
  letI : ContractibleSpace ↥(Ioo (2 / 3 : ℝ) (3 / 4)) :=
    (convex_Ioo (2 / 3 : ℝ) (3 / 4)).contractibleSpace ⟨17 / 24, by constructor <;> norm_num⟩
  exact (B.intrinsicBoundaryGraphTerminalOverlapHomeomorph i).symm.contractibleSpace

def Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionReverseParameter (s : Ioo (1 / 4 : ℝ) (3 / 4)) :
    Ioo (1 / 4 : ℝ) (3 / 4) :=
  ⟨1 - s, by constructor <;> linarith [s.2.1, s.2.2]⟩

private theorem midsectionReverseParameter_involutive : Function.Involutive Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionReverseParameter := by
  intro s
  apply Subtype.ext
  dsimp [Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionReverseParameter]
  ring

private theorem midsectionGraphParameter_pair (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) (s : Ioo (1 / 4 : ℝ) (3 / 4)) :
    Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionGraphParameter B (B.intrinsicCyclicPairing i) s =
      Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionGraphParameter B i (Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionReverseParameter s) := by
  unfold Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionGraphParameter
  rw [B.intrinsicBoundaryGraphMidsectionHomeomorph_apply,
    B.intrinsicBoundaryGraphMidsectionHomeomorph_apply]
  apply Eq.symm
  apply Quotient.sound
  change B.intrinsicBoundaryIntervalSetoid (i, Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionUnitParameter (Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionReverseParameter s))
    (B.intrinsicCyclicPairing i, Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionUnitParameter s)
  rw [B.intrinsicBoundaryIntervalSetoid_iff]
  right
  left
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp only [intrinsicBoundaryIntervalPair, unitInterval.coe_symm_eq,
      Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionUnitParameter, Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionReverseParameter]
    ring

/-- Reversing the original paired side exchanges its two literal overlap components. -/
theorem intrinsicBoundaryGraphInitialOverlap_pair (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphInitialOverlap (B.intrinsicCyclicPairing i) =
      B.intrinsicBoundaryGraphTerminalOverlap i := by
  ext q
  constructor
  · rintro ⟨s, hs, hsq⟩
    refine ⟨Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionReverseParameter s, ?_, (midsectionGraphParameter_pair B i s).symm.trans hsq⟩
    change (2 / 3 : ℝ) < 1 - (s : ℝ)
    change (s : ℝ) < 1 / 3 at hs
    linarith
  · rintro ⟨s, hs, hsq⟩
    refine ⟨Internal.SurfaceBoundaryGraphOpenCoverHelpers.midsectionReverseParameter s, ?_, ?_⟩
    · change 1 - (s : ℝ) < 1 / 3
      change (2 / 3 : ℝ) < s at hs
      linarith
    · rw [midsectionGraphParameter_pair B i, midsectionReverseParameter_involutive s]
      exact hsq

theorem intrinsicBoundaryGraphTerminalOverlap_pair (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphTerminalOverlap (B.intrinsicCyclicPairing i) =
      B.intrinsicBoundaryGraphInitialOverlap i := by
  have h := B.intrinsicBoundaryGraphInitialOverlap_pair (B.intrinsicCyclicPairing i)
  rw [B.intrinsicCyclicPairing_involutive i] at h
  exact h.symm

/-- The disconnected open vertex side of the actual groupoid van Kampen cover. -/
def intrinsicBoundaryGraphStarUnion (B : DirichletBoundarySegments X o) :
    Set (Quotient B.intrinsicBoundaryIntervalSetoid) := ⋃ v, B.intrinsicBoundaryGraphVertexStar v

/-- The disconnected open physical-edge side. Paired indices give the same component. -/
def intrinsicBoundaryGraphMidsectionUnion (B : DirichletBoundarySegments X o) :
    Set (Quotient B.intrinsicBoundaryIntervalSetoid) := ⋃ i, B.intrinsicBoundaryGraphEdgeMidsection i

theorem intrinsicBoundaryGraphStarUnion_isOpen (B : DirichletBoundarySegments X o) :
    IsOpen B.intrinsicBoundaryGraphStarUnion :=
  isOpen_iUnion B.intrinsicBoundaryGraphVertexStar_isOpen

theorem intrinsicBoundaryGraphMidsectionUnion_isOpen (B : DirichletBoundarySegments X o) :
    IsOpen B.intrinsicBoundaryGraphMidsectionUnion :=
  isOpen_iUnion B.intrinsicBoundaryGraphEdgeMidsection_isOpen

theorem intrinsicBoundaryGraphStarUnion_union_midsectionUnion (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryGraphStarUnion ∪ B.intrinsicBoundaryGraphMidsectionUnion = univ :=
  B.intrinsicBoundaryGraph_open_cover

/-- The actual overlap is precisely the union of the two disjoint half-arms of each
physical edge; it is not asserted path connected. -/
theorem intrinsicBoundaryGraphStarUnion_inter_midsectionUnion (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryGraphStarUnion ∩ B.intrinsicBoundaryGraphMidsectionUnion =
      ⋃ i, B.intrinsicBoundaryGraphInitialOverlap i ∪ B.intrinsicBoundaryGraphTerminalOverlap i := by
  ext q
  constructor
  · rintro ⟨hstar, hmid⟩
    obtain ⟨v, hv⟩ := mem_iUnion.mp hstar
    obtain ⟨i, hi⟩ := mem_iUnion.mp hmid
    have hq : q ∈ B.intrinsicBoundaryGraphVertexStar v ∩ B.intrinsicBoundaryGraphEdgeMidsection i :=
      ⟨hv, hi⟩
    rw [B.intrinsicBoundaryGraphStarMidsection_eq_halves v i] at hq
    refine mem_iUnion.mpr ⟨i, ?_⟩
    rcases hq with hq | hq
    · left
      split_ifs at hq with h
      · exact hq
      · exact False.elim hq
    · right
      split_ifs at hq with h
      · exact hq
      · exact False.elim hq
  · intro hq
    obtain ⟨i, hi⟩ := mem_iUnion.mp hq
    rcases hi with hi | hi
    · exact ⟨mem_iUnion.mpr ⟨B.intrinsicBoundaryGraphSideStart i,
        B.intrinsicBoundaryGraphInitialOverlap_subset_star i hi⟩,
      mem_iUnion.mpr ⟨i, B.intrinsicBoundaryGraphInitialOverlap_subset_midsection i hi⟩⟩
    · exact ⟨mem_iUnion.mpr ⟨B.intrinsicBoundaryGraphSideEnd i,
        B.intrinsicBoundaryGraphTerminalOverlap_subset_star i hi⟩,
      mem_iUnion.mpr ⟨i, B.intrinsicBoundaryGraphTerminalOverlap_subset_midsection i hi⟩⟩

end

end SystolicGrowth.DirichletBoundarySegments

module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarNeighborhoods
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# Actual open two-sided seam neighborhoods

At a consecutive pair of components, take the outgoing actual collar of
the first and incoming actual collar of the second. Their disjoint-union
image is open and contains the actual paired circles. Other-circle
avoidance and the proved one-step equivalence classes make this union
saturated for the original chain setoid. Its prescribed quotient image is
therefore open, giving the actual domain for a later signed seam chart.
The finite seam-contact set is closed, and every connected seam-only arc
lies in one actual seam circle, without a finite-contact assumption.
-/

open Metric Set UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual two-sided neighborhood before passage to the glued quotient. -/
def seamNeighborhood (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) : Set P.ChainPieces :=
  Sigma.mk (gluingChainEdgeLeft k) '' P.outgoingCollar (gluingChainEdgeLeft k) ∪
    Sigma.mk (gluingChainEdgeRight k) '' P.incomingCollar (gluingChainEdgeRight k)

/-- Both corresponding disks are genuinely deleted at any actual path edge,
so both collar images are open in the disjoint union. -/
theorem seamNeighborhood_isOpen (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) : IsOpen (P.seamNeighborhood k) := by
  apply IsOpen.union
  · exact isOpenMap_sigmaMk _ (P.outgoingCollar_isOpen _ (by
      change k.1 + 1 < n
      have := k.2
      omega))
  · exact isOpenMap_sigmaMk _ (P.incomingCollar_isOpen _ (by
      change 0 < k.1 + 1
      omega))

theorem seamSource_mem_seamNeighborhood (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1))
    (z : sphere (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    P.seamSource k z ∈ P.seamNeighborhood k :=
  Or.inl ⟨_, P.rightCirclePoint_mem_outgoingCollar _ z, rfl⟩

theorem seamTarget_mem_seamNeighborhood (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1))
    (z : sphere (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g)) :
    P.seamTarget k z ∈ P.seamNeighborhood k :=
  Or.inr ⟨_, P.leftCirclePoint_mem_incomingCollar _ _, rfl⟩

/-- Any generating partner of a point in this actual neighborhood stays in
it. An incoming collar cannot be the source of a different outgoing seam. -/
theorem seamNeighborhood_chainRelation (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) {a b : P.ChainPieces}
    (ha : a ∈ P.seamNeighborhood k) (hab : P.chainRelation a b) :
    b ∈ P.seamNeighborhood k := by
  rcases ha with ⟨x, hx, hxa⟩ | ⟨x, hx, hxa⟩
  · subst a
    obtain ⟨l, z, hsource, rfl⟩ := hab
    have hv := congrArg (fun a : P.ChainPieces => a.1.1) hsource
    change k.1 = l.1 at hv
    have hkl : k = l := Fin.ext hv
    subst l
    exact P.seamTarget_mem_seamNeighborhood k z
  · subst a
    have hcircle : x ∈ Set.range (P.rightCirclePoint (gluingChainEdgeRight k)) :=
      P.chainRelation_source_mem_rightCircle
        (a := ⟨gluingChainEdgeRight k, x⟩) (b := b) hab
    exact (Set.disjoint_left.mp
      (P.incomingCollar_disjoint_outgoingCircle (gluingChainEdgeRight k)) hx hcircle).elim

/-- Stability in the reverse direction uses the outgoing collar's avoidance
of its other, incoming boundary circle. -/
theorem seamNeighborhood_chainRelation_symm
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    {a b : P.ChainPieces} (ha : a ∈ P.seamNeighborhood k)
    (hba : P.chainRelation b a) : b ∈ P.seamNeighborhood k := by
  rcases ha with ⟨x, hx, hxa⟩ | ⟨x, hx, hxa⟩
  · subst a
    have hcircle : x ∈ Set.range (P.leftCirclePoint (gluingChainEdgeLeft k)) :=
      P.chainRelation_target_mem_leftCircle
        (a := b) (b := ⟨gluingChainEdgeLeft k, x⟩) hba
    exact (Set.disjoint_left.mp
      (P.outgoingCollar_disjoint_incomingCircle (gluingChainEdgeLeft k)) hx hcircle).elim
  · subst a
    obtain ⟨l, z, rfl, htarget⟩ := hba
    have hv := congrArg (fun a : P.ChainPieces => a.1.1) htarget
    change k.1 + 1 = l.1 + 1 at hv
    have hkl : k = l := Fin.ext (by omega)
    subst l
    exact P.seamSource_mem_seamNeighborhood k z

/-- This particular actual neighborhood is saturated for the original
generated equivalence relation, not for an auxiliary chart relation. -/
theorem seamNeighborhood_mem_iff_of_chainSetoid
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    {a b : P.ChainPieces} (hab : P.chainSetoid.r a b) :
    a ∈ P.seamNeighborhood k ↔ b ∈ P.seamNeighborhood k := by
  rcases (P.eqvGen_chainRelation_iff a b).mp hab with heq | hrel | hrev
  · rw [heq]
  · exact ⟨fun ha => P.seamNeighborhood_chainRelation k ha hrel,
      fun hb => P.seamNeighborhood_chainRelation_symm k hb hrel⟩
  · exact ⟨fun ha => P.seamNeighborhood_chainRelation_symm k ha hrev,
      fun hb => P.seamNeighborhood_chainRelation k hb hrev⟩

/-- Exact saturation of the actual prequotient neighborhood. -/
theorem preimage_gluedMk_image_seamNeighborhood
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedMk ⁻¹' (P.gluedMk '' P.seamNeighborhood k) = P.seamNeighborhood k := by
  ext a
  constructor
  · rintro ⟨b, hb, hba⟩
    exact (P.seamNeighborhood_mem_iff_of_chainSetoid k (Quotient.exact hba)).mp hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- The actual two-sided seam neighborhood is open in the prescribed glued
carrier with its original quotient topology. -/
theorem gluedSeamNeighborhood_isOpen
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsOpen (P.gluedMk '' P.seamNeighborhood k) := by
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen (P.gluedMk ⁻¹' (P.gluedMk '' P.seamNeighborhood k))
  rw [P.preimage_gluedMk_image_seamNeighborhood k]
  exact P.seamNeighborhood_isOpen k

/-- No generating source circle of another seam enters this neighborhood. -/
theorem seamSource_mem_seamNeighborhood_iff
    (P : ExerciseGluingPreparation C g n genera X) (k l : Fin (n - 1))
    (z : sphere (P.centers (gluingChainEdgeLeft l)).2 (gluingRadius C g)) :
    P.seamSource l z ∈ P.seamNeighborhood k ↔ l = k := by
  constructor
  · rintro (⟨x, _, hx⟩ | ⟨x, hx, hsource⟩)
    · have hv := congrArg (fun a : P.ChainPieces => a.1.1) hx
      exact Fin.ext hv.symm
    · have hrel : P.chainRelation (P.seamSource l z) (P.seamTarget l z) :=
        ⟨l, z, rfl, rfl⟩
      rw [← hsource] at hrel
      have hcircle : x ∈ Set.range (P.rightCirclePoint (gluingChainEdgeRight k)) :=
        P.chainRelation_source_mem_rightCircle
          (a := ⟨gluingChainEdgeRight k, x⟩) (b := P.seamTarget l z) hrel
      exact (Set.disjoint_left.mp
        (P.incomingCollar_disjoint_outgoingCircle (gluingChainEdgeRight k)) hx hcircle).elim
  · intro h
    subst l
    exact P.seamSource_mem_seamNeighborhood k z

/-- The same exact seam-index test holds for the transported target circles. -/
theorem seamTarget_mem_seamNeighborhood_iff
    (P : ExerciseGluingPreparation C g n genera X) (k l : Fin (n - 1))
    (z : sphere (P.centers (gluingChainEdgeLeft l)).2 (gluingRadius C g)) :
    P.seamTarget l z ∈ P.seamNeighborhood k ↔ l = k := by
  constructor
  · rintro (⟨x, hx, htarget⟩ | ⟨x, _, hx⟩)
    · have hrel : P.chainRelation (P.seamSource l z) (P.seamTarget l z) :=
        ⟨l, z, rfl, rfl⟩
      rw [← htarget] at hrel
      have hcircle : x ∈ Set.range (P.leftCirclePoint (gluingChainEdgeLeft k)) :=
        P.chainRelation_target_mem_leftCircle
          (a := P.seamSource l z) (b := ⟨gluingChainEdgeLeft k, x⟩) hrel
      exact (Set.disjoint_left.mp
        (P.outgoingCollar_disjoint_incomingCircle (gluingChainEdgeLeft k)) hx hcircle).elim
    · have hv := congrArg (fun a : P.ChainPieces => a.1.1) hx
      change k.1 + 1 = l.1 + 1 at hv
      exact Fin.ext (by omega)
  · intro h
    subst l
    exact P.seamTarget_mem_seamNeighborhood k z

#print axioms seamNeighborhood_isOpen
#print axioms seamNeighborhood_mem_iff_of_chainSetoid
#print axioms preimage_gluedMk_image_seamNeighborhood
#print axioms gluedSeamNeighborhood_isOpen
#print axioms seamSource_mem_seamNeighborhood_iff
#print axioms seamTarget_mem_seamNeighborhood_iff

/-- The actual identified radius-r circle at a path edge in the native quotient. -/
def gluedSeamCircle (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) : Set P.GluedCarrier :=
  Set.range (P.gluedMk ∘ P.seamSource k)

/-- The full actual seam-contact set; no crossing enumeration is imposed. -/
def gluedSeamSet (P : ExerciseGluingPreparation C g n genera X) : Set P.GluedCarrier :=
  ⋃ k : Fin (n - 1), P.gluedSeamCircle k

theorem gluedSeamCircle_isClosedEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Topology.IsClosedEmbedding (P.gluedMk ∘ P.seamSource k) := by
  letI : CompactSpace (sphere (P.centers (gluingChainEdgeLeft k)).2
      (gluingRadius C g)) := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  apply (P.gluedMk_continuous.comp (P.seamSource_continuous k)).isClosedEmbedding
  intro z w h
  have hcomp := P.gluedMk_injective_component (gluingChainEdgeLeft k) h
  exact (P.rightCirclePoint_isEmbedding (gluingChainEdgeLeft k)).injective hcomp

theorem gluedSeamCircle_isCompact
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsCompact (P.gluedSeamCircle k) := by
  letI : CompactSpace (sphere (P.centers (gluingChainEdgeLeft k)).2
      (gluingRadius C g)) := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  exact isCompact_range (P.gluedMk_continuous.comp (P.seamSource_continuous k))

theorem gluedSeamCircle_isClosed
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsClosed (P.gluedSeamCircle k) :=
  (P.gluedSeamCircle_isCompact k).isClosed

theorem gluedSeamSet_isClosed (P : ExerciseGluingPreparation C g n genera X) :
    IsClosed P.gluedSeamSet :=
  isClosed_iUnion_of_finite (P.gluedSeamCircle_isClosed)

/-- Different actual seam circles remain disjoint after all quotient identifications. -/
theorem gluedSeamCircle_disjoint (P : ExerciseGluingPreparation C g n genera X)
    {k l : Fin (n - 1)} (hkl : k ≠ l) :
    Disjoint (P.gluedSeamCircle k) (P.gluedSeamCircle l) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨z, rfl⟩ ⟨w, hw⟩
  change P.gluedMk (P.seamSource l w) = P.gluedMk (P.seamSource k z) at hw
  have hmem : P.gluedMk (P.seamSource l w) ∈
      P.gluedMk '' P.seamNeighborhood k := by
    rw [hw]
    exact ⟨P.seamSource k z, P.seamSource_mem_seamNeighborhood k z, rfl⟩
  have hpre : P.seamSource l w ∈
      P.gluedMk ⁻¹' (P.gluedMk '' P.seamNeighborhood k) := hmem
  rw [P.preimage_gluedMk_image_seamNeighborhood k] at hpre
  exact hkl ((P.seamSource_mem_seamNeighborhood_iff k l w).mp hpre).symm

/-- A connected subset of the actual seam set that meets one seam stays in it. -/
theorem subset_gluedSeamCircle_of_isPreconnected
    (P : ExerciseGluingPreparation C g n genera X) {s : Set P.GluedCarrier}
    (hs : IsPreconnected s) (hsub : s ⊆ P.gluedSeamSet) (k : Fin (n - 1))
    (hmeet : (s ∩ P.gluedSeamCircle k).Nonempty) : s ⊆ P.gluedSeamCircle k := by
  let U : Set P.GluedCarrier := ⋃ l : {l : Fin (n - 1) // l ≠ k}, P.gluedSeamCircle l.1
  have hU : IsClosed U := isClosed_iUnion_of_finite fun l => P.gluedSeamCircle_isClosed l.1
  have hdis : Disjoint (P.gluedSeamCircle k) U := by
    apply Set.disjoint_left.mpr
    intro x hx hUmem
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hUmem
    exact Set.disjoint_left.mp (P.gluedSeamCircle_disjoint (Ne.symm l.2)) hx hl
  have hcover : s ⊆ P.gluedSeamCircle k ∪ U := by
    intro x hx
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (hsub hx)
    by_cases hlk : l = k
    · subst l
      exact Or.inl hl
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨l, hlk⟩, hl⟩)
  have hpart := isPreconnected_iff_subset_of_disjoint_closed.mp hs
    (P.gluedSeamCircle k) U (P.gluedSeamCircle_isClosed k) hU hcover
    (by rw [Set.disjoint_iff_inter_eq_empty.mp hdis, Set.inter_empty])
  rcases hpart with hleft | hright
  · exact hleft
  · obtain ⟨x, hx, hxk⟩ := hmeet
    exact (Set.disjoint_left.mp hdis hxk (hright hx)).elim

/-- The image of any connected continuous arc in the full seam set lies in one
actual seam circle, even with arbitrary tangencies and infinitely many contacts. -/
theorem exists_gluedSeamCircle_of_continuous
    (P : ExerciseGluingPreparation C g n genera X) {α : Type*}
    [TopologicalSpace α] [ConnectedSpace α] (γ : α → P.GluedCarrier)
    (hγ : Continuous γ) (hseam : Set.range γ ⊆ P.gluedSeamSet) :
    ∃ k : Fin (n - 1), Set.range γ ⊆ P.gluedSeamCircle k := by
  obtain ⟨t⟩ := (inferInstance : Nonempty α)
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hseam (Set.mem_range_self t))
  exact ⟨k, P.subset_gluedSeamCircle_of_isPreconnected (isPreconnected_range hγ)
    hseam k ⟨γ t, Set.mem_range_self t, hk⟩⟩

/-- Interval formulation used by a connected complementary parameter arc. -/
theorem exists_gluedSeamCircle_of_continuousOn_Icc
    (P : ExerciseGluingPreparation C g n genera X) {a b : ℝ} (hab : a ≤ b)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Set.Icc a b))
    (hseam : Set.MapsTo γ (Set.Icc a b) P.gluedSeamSet) :
    ∃ k : Fin (n - 1), Set.MapsTo γ (Set.Icc a b) (P.gluedSeamCircle k) := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hseam (Set.left_mem_Icc.mpr hab))
  have hsub : γ '' Set.Icc a b ⊆ P.gluedSeamSet := Set.mapsTo_iff_image_subset.mp hseam
  have hcircle := P.subset_gluedSeamCircle_of_isPreconnected
    (isPreconnected_Icc.image γ hγ) hsub k
    ⟨γ a, ⟨a, Set.left_mem_Icc.mpr hab, rfl⟩, hk⟩
  exact ⟨k, Set.mapsTo_iff_image_subset.mpr hcircle⟩

/-- A continuous complementary arc connecting distinct actual seam circles cannot
stay in the seam-contact set. No finite-contact or transversality premise occurs. -/
theorem exists_not_mem_gluedSeamSet_of_endpoints
    (P : ExerciseGluingPreparation C g n genera X) {a b : ℝ} (hab : a ≤ b)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Set.Icc a b))
    {k l : Fin (n - 1)} (hkl : k ≠ l)
    (ha : γ a ∈ P.gluedSeamCircle k) (hb : γ b ∈ P.gluedSeamCircle l) :
    ∃ t ∈ Set.Icc a b, γ t ∉ P.gluedSeamSet := by
  by_contra h
  push Not at h
  have hsub : γ '' Set.Icc a b ⊆ P.gluedSeamSet :=
    Set.mapsTo_iff_image_subset.mp h
  have hcircle := P.subset_gluedSeamCircle_of_isPreconnected
    (isPreconnected_Icc.image γ hγ) hsub k
    ⟨γ a, ⟨a, Set.left_mem_Icc.mpr hab, rfl⟩, ha⟩
  exact Set.disjoint_left.mp (P.gluedSeamCircle_disjoint hkl)
    (hcircle ⟨b, Set.right_mem_Icc.mpr hab, rfl⟩) hb

/-- For a closed curve, a seam-only complementary parameter arc forces the
endpoints of the omitted excursion to lie on the same actual seam. This is
the topological exclusion of exactly one different-circle excursion. -/
theorem seam_indices_eq_of_closed_curve_complement_mem
    (P : ExerciseGluingPreparation C g n genera X) (γ : ℝ → P.GluedCarrier)
    (hγ : ContinuousOn γ (Set.Icc 0 1)) (hclose : γ 0 = γ 1)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
    (hleft : Set.MapsTo γ (Set.Icc 0 a) P.gluedSeamSet)
    (hright : Set.MapsTo γ (Set.Icc b 1) P.gluedSeamSet)
    {k l : Fin (n - 1)} (ha : γ a ∈ P.gluedSeamCircle k)
    (hb : γ b ∈ P.gluedSeamCircle l) : k = l := by
  have ha1 : a ≤ 1 := hab.trans hb1
  have hb0 : 0 ≤ b := ha0.trans hab
  have hleft_conn : IsPreconnected (γ '' Set.Icc 0 a) :=
    isPreconnected_Icc.image γ (hγ.mono (Set.Icc_subset_Icc le_rfl ha1))
  have hright_conn : IsPreconnected (γ '' Set.Icc b 1) :=
    isPreconnected_Icc.image γ (hγ.mono (Set.Icc_subset_Icc hb0 le_rfl))
  have h0left : γ 0 ∈ γ '' Set.Icc 0 a := ⟨0, ⟨le_rfl, ha0⟩, rfl⟩
  have h0right : γ 0 ∈ γ '' Set.Icc b 1 := ⟨1, ⟨hb1, le_rfl⟩, hclose.symm⟩
  have hconn := hleft_conn.union (γ 0) h0left h0right hright_conn
  have hsub : γ '' Set.Icc 0 a ∪ γ '' Set.Icc b 1 ⊆ P.gluedSeamSet :=
    Set.union_subset (Set.mapsTo_iff_image_subset.mp hleft)
      (Set.mapsTo_iff_image_subset.mp hright)
  have hcircle := P.subset_gluedSeamCircle_of_isPreconnected hconn hsub k
    ⟨γ a, Or.inl ⟨a, ⟨ha0, le_rfl⟩, rfl⟩, ha⟩
  by_contra hkl
  exact Set.disjoint_left.mp (P.gluedSeamCircle_disjoint hkl)
    (hcircle (Or.inr ⟨b, ⟨le_rfl, hb1⟩, rfl⟩)) hb

#print axioms SystolicGrowth.ExerciseGluingPreparation.gluedSeamCircle_isClosedEmbedding
#print axioms SystolicGrowth.ExerciseGluingPreparation.gluedSeamCircle_disjoint
#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_gluedSeamCircle_of_continuous
#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_not_mem_gluedSeamSet_of_endpoints
#print axioms SystolicGrowth.ExerciseGluingPreparation.seam_indices_eq_of_closed_curve_complement_mem

/-- The image of the original retained component in the prescribed chain quotient. -/
def gluedComponentImage (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Set P.GluedCarrier := Set.range (fun x : P.ChainComponent i => P.gluedMk ⟨i, x⟩)

theorem gluedComponentImage_isClosed
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    IsClosed (P.gluedComponentImage i) :=
  (P.gluedComponent_isClosedEmbedding i).isClosed_range

/-- Every point of the actual quotient still belongs to one original component image. -/
theorem exists_mem_gluedComponentImage
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    ∃ i : Fin n, x ∈ P.gluedComponentImage i := by
  obtain ⟨⟨i, a⟩, rfl⟩ := Quotient.exists_rep x
  exact ⟨i, a, rfl⟩

/-- Distinct original component images intersect only along the actual identified
seams; the equivalence closure introduces no extra intersections. -/
theorem gluedComponentImage_inter_subset_gluedSeamSet
    (P : ExerciseGluingPreparation C g n genera X) {i j : Fin n} (hij : i ≠ j) :
    P.gluedComponentImage i ∩ P.gluedComponentImage j ⊆ P.gluedSeamSet := by
  rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
  change P.gluedMk ⟨i, a⟩ ∈ P.gluedSeamSet
  rcases (P.gluedMk_eq_iff ⟨i, a⟩ ⟨j, b⟩).mp hb.symm with heq | hrel | hrev
  · exact (hij (congrArg Sigma.fst heq)).elim
  · obtain ⟨k, z, ha, _⟩ := hrel
    rw [ha]
    exact Set.mem_iUnion.mpr ⟨k, z, rfl⟩
  · obtain ⟨k, z, _, ha⟩ := hrev
    rw [ha, ← P.gluedMk_seamSource_eq_seamTarget k z]
    exact Set.mem_iUnion.mpr ⟨k, z, rfl⟩

/-- A connected seam-avoiding set stays in its original component, even with
arbitrary accumulation at the seam-contact set. -/
theorem subset_gluedComponentImage_of_isPreconnected
    (P : ExerciseGluingPreparation C g n genera X) {s : Set P.GluedCarrier}
    (hs : IsPreconnected s) (havoid : s ⊆ P.gluedSeamSetᶜ) (i : Fin n)
    (hmeet : (s ∩ P.gluedComponentImage i).Nonempty) : s ⊆ P.gluedComponentImage i := by
  let U : Set P.GluedCarrier := ⋃ j : {j : Fin n // j ≠ i}, P.gluedComponentImage j.1
  have hU : IsClosed U :=
    isClosed_iUnion_of_finite fun j => P.gluedComponentImage_isClosed j.1
  have hcover : s ⊆ P.gluedComponentImage i ∪ U := by
    intro x _
    obtain ⟨j, hj⟩ := P.exists_mem_gluedComponentImage x
    by_cases hji : j = i
    · subst j
      exact Or.inl hj
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  have hdis : s ∩ (P.gluedComponentImage i ∩ U) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hxi, hxU⟩
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxU
    exact havoid hx
      (P.gluedComponentImage_inter_subset_gluedSeamSet (Ne.symm j.2) ⟨hxi, hxj⟩)
  have hpart := isPreconnected_iff_subset_of_disjoint_closed.mp hs
    (P.gluedComponentImage i) U (P.gluedComponentImage_isClosed i) hU hcover hdis
  rcases hpart with hleft | hright
  · exact hleft
  · obtain ⟨x, hx, hxi⟩ := hmeet
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (hright hx)
    exact (havoid hx
      (P.gluedComponentImage_inter_subset_gluedSeamSet (Ne.symm j.2) ⟨hxi, hxj⟩)).elim

/-- The closure of a connected seam-avoiding arc stays in one closed original
component image, so all endpoint limits are retained there. -/
theorem exists_gluedComponentImage_closure_of_isConnected
    (P : ExerciseGluingPreparation C g n genera X) {s : Set P.GluedCarrier}
    (hs : IsConnected s) (havoid : s ⊆ P.gluedSeamSetᶜ) :
    ∃ i : Fin n, closure s ⊆ P.gluedComponentImage i := by
  obtain ⟨x, hx⟩ := hs.nonempty
  obtain ⟨i, hxi⟩ := P.exists_mem_gluedComponentImage x
  exact ⟨i, closure_minimal
    (P.subset_gluedComponentImage_of_isPreconnected hs.isPreconnected havoid i ⟨x, hx, hxi⟩)
    (P.gluedComponentImage_isClosed i)⟩

theorem exists_gluedComponentImage_of_continuous
    (P : ExerciseGluingPreparation C g n genera X) {α : Type*}
    [TopologicalSpace α] [ConnectedSpace α] (γ : α → P.GluedCarrier)
    (hγ : Continuous γ) (havoid : Set.range γ ⊆ P.gluedSeamSetᶜ) :
    ∃ i : Fin n, closure (Set.range γ) ⊆ P.gluedComponentImage i :=
  P.exists_gluedComponentImage_closure_of_isConnected (isConnected_range hγ) havoid

/-- Each arbitrary complementary excursion lies in one original component,
including its two seam endpoints by continuity and closedness. -/
theorem exists_gluedComponentImage_of_continuousOn_excursion
    (P : ExerciseGluingPreparation C g n genera X) {a b : ℝ} (hab : a < b)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Set.Icc a b))
    (havoid : Set.MapsTo γ (Set.Ioo a b) P.gluedSeamSetᶜ) :
    ∃ i : Fin n, Set.MapsTo γ (Set.Icc a b) (P.gluedComponentImage i) := by
  have hconn : IsConnected (γ '' Set.Ioo a b) :=
    (isConnected_Ioo hab).image γ (hγ.mono Set.Ioo_subset_Icc_self)
  obtain ⟨i, hi⟩ := P.exists_gluedComponentImage_closure_of_isConnected hconn
    (Set.mapsTo_iff_image_subset.mp havoid)
  have hγclosure : ContinuousOn γ (closure (Set.Ioo a b)) := by
    simpa only [closure_Ioo hab.ne] using hγ
  have hsub : γ '' Set.Icc a b ⊆ closure (γ '' Set.Ioo a b) := by
    simpa only [closure_Ioo hab.ne] using hγclosure.image_closure
  exact ⟨i, Set.mapsTo_iff_image_subset.mpr (hsub.trans hi)⟩

/-- The entire closed excursion has a continuous lift to the retained original
component through its actual closed embedding, with both endpoints included. -/
theorem exists_continuous_component_lift_of_excursion
    (P : ExerciseGluingPreparation C g n genera X) {a b : ℝ} (hab : a < b)
    (γ : ℝ → P.GluedCarrier) (hγ : ContinuousOn γ (Set.Icc a b))
    (havoid : Set.MapsTo γ (Set.Ioo a b) P.gluedSeamSetᶜ) :
    ∃ (i : Fin n) (δ : Set.Icc a b → P.ChainComponent i),
      Continuous δ ∧ ∀ t : Set.Icc a b, γ t = P.gluedMk ⟨i, δ t⟩ := by
  obtain ⟨i, hi⟩ := P.exists_gluedComponentImage_of_continuousOn_excursion hab γ hγ havoid
  let γ' : Set.Icc a b → P.gluedComponentImage i := fun t => ⟨γ t, hi t.2⟩
  have hγ' : Continuous γ' :=
    (continuousOn_iff_continuous_restrict.mp hγ).subtype_mk (fun t => hi t.2)
  let δ : Set.Icc a b → P.ChainComponent i :=
    (P.gluedComponentHomeomorph i).symm ∘ γ'
  refine ⟨i, δ, (P.gluedComponentHomeomorph i).symm.continuous.comp hγ', ?_⟩
  intro t
  exact (congrArg Subtype.val
    ((P.gluedComponentHomeomorph i).apply_symm_apply (γ' t))).symm

#print axioms SystolicGrowth.ExerciseGluingPreparation.gluedComponentImage_inter_subset_gluedSeamSet
#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_gluedComponentImage_of_continuous
#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_continuous_component_lift_of_excursion

end SystolicGrowth.ExerciseGluingPreparation

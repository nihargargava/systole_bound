module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSeamHomotopy
public import Geometry.GluingChainOpenCover
public import Mathlib.Topology.Piecewise

@[expose] public section

/-!
# Collar retractions for the actual chain cover

The original signed cylinder distinguishes the two retained halves of a cut.
Clamping the added half-collar to zero retracts each thickened chain side
onto its original closed side, without replacing any component or seam.
-/

open Set Filter
open scoped unitInterval Topology ContinuousMap

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- At nonpositive signed radius the genuine cylinder point is its outgoing
polar point in the original left component. -/
theorem seamCylinderHomeomorph_apply_of_nonpos
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : GluingSeamCylinder C g) (hp : p.2.1 ≤ 0) :
    (P.seamCylinderHomeomorph k p).1 =
      P.gluedMk (P.seamOutgoingPolarPoint k
        (p.1, ⟨gluingRadius C g - p.2.1, by
          constructor
          · linarith
          · change gluingRadius C g - p.2.1 < gluingRadius C g + gluingDepth C g
            linarith [p.2.2.1]⟩)) := by
  let a : Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g) :=
    (p.1, ⟨gluingRadius C g - p.2.1, by
      constructor
      · linarith
      · change gluingRadius C g - p.2.1 < gluingRadius C g + gluingDepth C g
        linarith [p.2.2.1]⟩)
  have h : P.seamCylinderHomeomorph k p = P.seamNeighborhoodProjection k
      ⟨P.seamOutgoingPolarPoint k a, P.seamOutgoingPolarPoint_mem k a⟩ := by
    apply (P.seamCylinderHomeomorph k).symm.injective
    rw [Homeomorph.symm_apply_apply, P.seamCylinderHomeomorph_symm_outgoing]
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp [a]
      ring
  exact congrArg Subtype.val h

/-- At nonnegative signed radius the same actual point is its reflected
incoming polar point in the original right component. -/
theorem seamCylinderHomeomorph_apply_of_nonneg
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : GluingSeamCylinder C g) (hp : 0 ≤ p.2.1) :
    (P.seamCylinderHomeomorph k p).1 =
      P.gluedMk (P.seamIncomingPolarPoint k
        (p.1⁻¹, ⟨gluingRadius C g + p.2.1, by
          constructor
          · linarith
          · change gluingRadius C g + p.2.1 < gluingRadius C g + gluingDepth C g
            linarith [p.2.2.2]⟩)) := by
  let a : Circle × Ico (gluingRadius C g) (gluingEmbeddedRadius C g) :=
    (p.1⁻¹, ⟨gluingRadius C g + p.2.1, by
      constructor
      · linarith
      · change gluingRadius C g + p.2.1 < gluingRadius C g + gluingDepth C g
        linarith [p.2.2.2]⟩)
  have h : P.seamCylinderHomeomorph k p = P.seamNeighborhoodProjection k
      ⟨P.seamIncomingPolarPoint k a, P.seamIncomingPolarPoint_mem k a⟩ := by
    apply (P.seamCylinderHomeomorph k).symm.injective
    rw [Homeomorph.symm_apply_apply, P.seamCylinderHomeomorph_symm_incoming]
    apply Prod.ext
    · exact (inv_inv p.1).symm
    · apply Subtype.ext
      dsimp [a]
      ring
  exact congrArg Subtype.val h

/-- The middle of the literal signed cylinder is exactly the original seam,
not just an abstract circle homotopy equivalent to the neighborhood. -/
theorem seamCylinderHomeomorph_mem_seamCircle_iff
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : GluingSeamCylinder C g) :
    (P.seamCylinderHomeomorph k p).1 ∈ P.gluedSeamCircle k ↔ p.2.1 = 0 := by
  constructor
  · intro hp
    rw [← P.range_gluedSeamCircleInclusion k] at hp
    obtain ⟨θ, hθ⟩ := hp
    have h : P.gluedSeamCircleInclusion k θ = P.seamCylinderHomeomorph k p :=
      Subtype.ext hθ
    have hc := (P.seamCylinderHomeomorph k).injective h
    exact (congrArg (fun q : GluingSeamCylinder C g => q.2.1) hc).symm
  · intro hp
    have h : p = (p.1, ⟨0, neg_lt_zero.mpr P.depth_pos, P.depth_pos⟩) := by
      apply Prod.ext
      · rfl
      · exact Subtype.ext hp
    rw [h]
    exact P.gluedSeamCircleInclusion_mem k p.1

/-! The literal signed coordinate identifies the two original closed sides. -/

theorem seamCylinderHomeomorph_mem_prefix_iff
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : GluingSeamCylinder C g) :
    (P.seamCylinderHomeomorph k p).1 ∈ P.gluedChainPrefix k ↔ p.2.1 ≤ 0 := by
  have hleft (h : p.2.1 ≤ 0) :
      (P.seamCylinderHomeomorph k p).1 ∈ P.gluedChainPrefix k := by
    rw [P.seamCylinderHomeomorph_apply_of_nonpos k p h]
    exact ⟨_, by change k.1 ≤ k.1; exact le_rfl, rfl⟩
  constructor
  · intro h
    by_contra hr
    have hright : (P.seamCylinderHomeomorph k p).1 ∈ P.gluedChainSuffix k := by
      rw [P.seamCylinderHomeomorph_apply_of_nonneg k p (le_of_not_ge hr)]
      exact ⟨_, by change k.1 < k.1 + 1; omega, rfl⟩
    have hseam : (P.seamCylinderHomeomorph k p).1 ∈ P.gluedSeamCircle k := by
      rw [← P.gluedChainPrefix_inter_suffix k]
      exact ⟨h, hright⟩
    exact hr (le_of_eq ((P.seamCylinderHomeomorph_mem_seamCircle_iff k p).mp hseam))
  · exact hleft

theorem seamCylinderHomeomorph_mem_suffix_iff
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : GluingSeamCylinder C g) :
    (P.seamCylinderHomeomorph k p).1 ∈ P.gluedChainSuffix k ↔ 0 ≤ p.2.1 := by
  have hright (h : 0 ≤ p.2.1) :
      (P.seamCylinderHomeomorph k p).1 ∈ P.gluedChainSuffix k := by
    rw [P.seamCylinderHomeomorph_apply_of_nonneg k p h]
    exact ⟨_, by change k.1 < k.1 + 1; omega, rfl⟩
  constructor
  · intro h
    by_contra hr
    have hleft : (P.seamCylinderHomeomorph k p).1 ∈ P.gluedChainPrefix k := by
      rw [P.seamCylinderHomeomorph_apply_of_nonpos k p (le_of_not_ge hr)]
      exact ⟨_, by change k.1 ≤ k.1; exact le_rfl, rfl⟩
    have hseam : (P.seamCylinderHomeomorph k p).1 ∈ P.gluedSeamCircle k := by
      rw [← P.gluedChainPrefix_inter_suffix k]
      exact ⟨hleft, h⟩
    exact hr (le_of_eq ((P.seamCylinderHomeomorph_mem_seamCircle_iff k p).mp hseam).symm)
  · exact hright

/-- Every point of the actual seam neighborhood at an earlier cut lies in
the original closed prefix at any later cut. This uses both actual collars:
their component indices are exactly `j` and `j + 1`. -/
theorem gluedMk_image_seamNeighborhood_subset_prefix_of_lt
    (P : ExerciseGluingPreparation C g n genera X) (j k : Fin (n - 1))
    (hjk : j.val < k.val) :
    P.gluedMk '' P.seamNeighborhood j ⊆ P.gluedChainPrefix k := by
  rintro q ⟨a, ha, rfl⟩
  rcases ha with ⟨x, hx, hxa⟩ | ⟨x, hx, hxa⟩
  · subst a
    refine ⟨_, ?_, rfl⟩
    change (gluingChainEdgeLeft j).val ≤ k.val
    dsimp [gluingChainEdgeLeft]
    omega
  · subst a
    refine ⟨_, ?_, rfl⟩
    change (gluingChainEdgeRight j).val ≤ k.val
    dsimp [gluingChainEdgeRight]
    omega

/-- Prefix images are monotone in their cut index. -/
theorem gluedChainPrefix_subset_of_le
    (P : ExerciseGluingPreparation C g n genera X) (j k : Fin (n - 1))
    (hjk : j.val ≤ k.val) : P.gluedChainPrefix j ⊆ P.gluedChainPrefix k := by
  rintro q ⟨a, ha, rfl⟩
  exact ⟨a, le_trans ha hjk, rfl⟩

/-- The entire original prefix neighborhood at an earlier cut is already
contained in every later closed prefix. In particular, the left collar need
not be truncated when restricting the chain open cover. -/
theorem gluedChainPrefixNeighborhood_subset_laterPrefix
    (P : ExerciseGluingPreparation C g n genera X) (j k : Fin (n - 1))
    (hjk : j.val < k.val) :
    P.gluedChainPrefixNeighborhood j ⊆ P.gluedChainPrefix k := by
  rintro q (hq | hq)
  · exact P.gluedChainPrefix_subset_of_le j k (le_of_lt hjk) hq
  · exact P.gluedMk_image_seamNeighborhood_subset_prefix_of_lt j k hjk hq

def Internal.GluingChainCollarRetractionHelpers.chainSide (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (b : Bool) : Set P.GluedCarrier :=
  if b then P.gluedChainPrefix k else P.gluedChainSuffix k

def Internal.GluingChainCollarRetractionHelpers.chainSideNeighborhood (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (b : Bool) : Set P.GluedCarrier :=
  Internal.GluingChainCollarRetractionHelpers.chainSide P k b ∪ P.gluedMk '' P.seamNeighborhood k

def Internal.GluingChainCollarRetractionHelpers.seamHalfClamp (b : Bool) (r : ℝ) : ℝ :=
  if b then min r 0 else max r 0

private theorem seamHalfClamp_mem
    (P : ExerciseGluingPreparation C g n genera X) (b : Bool)
    (r : Ioo (-gluingDepth C g) (gluingDepth C g)) :
    Internal.GluingChainCollarRetractionHelpers.seamHalfClamp b r ∈ Ioo (-gluingDepth C g) (gluingDepth C g) := by
  cases b
  · exact ⟨lt_of_lt_of_le r.2.1 (le_max_left _ _),
      max_lt r.2.2 P.depth_pos⟩
  · exact ⟨lt_min r.2.1 (neg_lt_zero.mpr P.depth_pos),
      lt_of_le_of_lt (min_le_left _ _) r.2.2⟩

theorem Internal.GluingChainCollarRetractionHelpers.seamHalfInterpolate_mem
    (P : ExerciseGluingPreparation C g n genera X) (b : Bool) (t : I)
    (r : Ioo (-gluingDepth C g) (gluingDepth C g)) :
    (1 - (t : ℝ)) * r + (t : ℝ) * Internal.GluingChainCollarRetractionHelpers.seamHalfClamp b r ∈
      Ioo (-gluingDepth C g) (gluingDepth C g) := by
  have h := (convex_Ioo (-gluingDepth C g) (gluingDepth C g)) r.2
    (seamHalfClamp_mem P b r) (sub_nonneg.mpr t.2.2) t.2.1 (by ring)
  simpa only [smul_eq_mul] using h

def Internal.GluingChainCollarRetractionHelpers.seamHalfRadialMap
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool) :
    C(I × ↥(P.gluedMk '' P.seamNeighborhood k), ↥(P.gluedMk '' P.seamNeighborhood k)) where
  toFun p := P.seamCylinderHomeomorph k
    (((P.seamCylinderHomeomorph k).symm p.2).1,
      ⟨(1 - (p.1 : ℝ)) * (((P.seamCylinderHomeomorph k).symm p.2).2 : ℝ) +
        (p.1 : ℝ) * Internal.GluingChainCollarRetractionHelpers.seamHalfClamp b (((P.seamCylinderHomeomorph k).symm p.2).2 : ℝ),
        Internal.GluingChainCollarRetractionHelpers.seamHalfInterpolate_mem P b p.1 ((P.seamCylinderHomeomorph k).symm p.2).2⟩)
  continuous_toFun := by
    apply (P.seamCylinderHomeomorph k).continuous.comp
    apply Continuous.prodMk
    · exact ((P.seamCylinderHomeomorph k).symm.continuous.comp continuous_snd).fst
    · apply Continuous.subtype_mk
      have ht : Continuous (fun p : I × ↥(P.gluedMk '' P.seamNeighborhood k) =>
          (p.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
      have hr : Continuous (fun p : I × ↥(P.gluedMk '' P.seamNeighborhood k) =>
          (((P.seamCylinderHomeomorph k).symm p.2).2 : ℝ)) :=
        continuous_subtype_val.comp
          ((P.seamCylinderHomeomorph k).symm.continuous.comp continuous_snd).snd
      have hc : Continuous (fun p : I × ↥(P.gluedMk '' P.seamNeighborhood k) =>
          Internal.GluingChainCollarRetractionHelpers.seamHalfClamp b (((P.seamCylinderHomeomorph k).symm p.2).2 : ℝ)) := by
        cases b
        · exact hr.max continuous_const
        · exact hr.min continuous_const
      exact ((continuous_const.sub ht).mul hr).add (ht.mul hc)

private theorem seamHalfRadialMap_zero
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool)
    (x : ↥(P.gluedMk '' P.seamNeighborhood k)) :
    Internal.GluingChainCollarRetractionHelpers.seamHalfRadialMap P k b (0, x) = x := by
  change P.seamCylinderHomeomorph k _ = x
  convert (P.seamCylinderHomeomorph k).apply_symm_apply x using 1
  apply congrArg (P.seamCylinderHomeomorph k)
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp

private theorem seamHalfRadialMap_one_mem
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool)
    (x : ↥(P.gluedMk '' P.seamNeighborhood k)) :
    (Internal.GluingChainCollarRetractionHelpers.seamHalfRadialMap P k b (1, x)).1 ∈ Internal.GluingChainCollarRetractionHelpers.chainSide P k b := by
  cases b
  · apply (P.seamCylinderHomeomorph_mem_suffix_iff k _).mpr
    change 0 ≤ (1 - (1 : ℝ)) * _ + (1 : ℝ) * max _ 0
    simpa only [sub_self, zero_mul, one_mul, zero_add] using le_max_right
      (((P.seamCylinderHomeomorph k).symm x).2 : ℝ) 0
  · apply (P.seamCylinderHomeomorph_mem_prefix_iff k _).mpr
    change (1 - (1 : ℝ)) * _ + (1 : ℝ) * min _ 0 ≤ 0
    simpa only [sub_self, zero_mul, one_mul, zero_add] using min_le_right
      (((P.seamCylinderHomeomorph k).symm x).2 : ℝ) 0

private theorem seamHalfRadialMap_fixed
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool)
    (t : I) (x : ↥(P.gluedMk '' P.seamNeighborhood k))
    (hx : x.1 ∈ Internal.GluingChainCollarRetractionHelpers.chainSide P k b) : Internal.GluingChainCollarRetractionHelpers.seamHalfRadialMap P k b (t, x) = x := by
  have hc : Internal.GluingChainCollarRetractionHelpers.seamHalfClamp b (((P.seamCylinderHomeomorph k).symm x).2 : ℝ) =
      (((P.seamCylinderHomeomorph k).symm x).2 : ℝ) := by
    cases b
    · apply max_eq_left
      apply (P.seamCylinderHomeomorph_mem_suffix_iff k _).mp
      simpa only [Homeomorph.apply_symm_apply, Internal.GluingChainCollarRetractionHelpers.chainSide, Bool.false_eq_true,
        ↓reduceIte] using hx
    · apply min_eq_left
      apply (P.seamCylinderHomeomorph_mem_prefix_iff k _).mp
      simpa only [Homeomorph.apply_symm_apply, Internal.GluingChainCollarRetractionHelpers.chainSide, ↓reduceIte] using hx
  change P.seamCylinderHomeomorph k _ = x
  convert (P.seamCylinderHomeomorph k).apply_symm_apply x using 1
  apply congrArg (P.seamCylinderHomeomorph k)
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    dsimp only
    rw [hc]
    ring

private theorem chainSide_isClosed
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool) :
    IsClosed (Internal.GluingChainCollarRetractionHelpers.chainSide P k b) := by
  cases b
  · exact P.gluedChainSuffix_isClosed k
  · exact P.gluedChainPrefix_isClosed k

private theorem chainSide_mem_of_not_other
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool)
    {q : P.GluedCarrier} (hq : q ∉ Internal.GluingChainCollarRetractionHelpers.chainSide P k (!b)) : q ∈ Internal.GluingChainCollarRetractionHelpers.chainSide P k b := by
  have h : q ∈ P.gluedChainPrefix k ∪ P.gluedChainSuffix k := by
    rw [P.gluedChainPrefix_union_suffix k]
    exact Set.mem_univ q
  cases b
  · exact h.resolve_left hq
  · exact h.resolve_right hq

private theorem chainSideNeighborhood_inter_other_subset
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool) :
    Internal.GluingChainCollarRetractionHelpers.chainSideNeighborhood P k b ∩ Internal.GluingChainCollarRetractionHelpers.chainSide P k (!b) ⊆
      P.gluedMk '' P.seamNeighborhood k := by
  cases b
  · exact P.gluedChainSuffixNeighborhood_inter_closedPrefix_subset k
  · exact P.gluedChainPrefixNeighborhood_inter_closedSuffix_subset k

def Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool)
    (p : I × ↥(Internal.GluingChainCollarRetractionHelpers.chainSideNeighborhood P k b)) : P.GluedCarrier := by
  classical
  exact if hx : p.2.1 ∈ P.gluedMk '' P.seamNeighborhood k then
    (Internal.GluingChainCollarRetractionHelpers.seamHalfRadialMap P k b (p.1, ⟨p.2.1, hx⟩)).1 else p.2.1

theorem Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn_fixed
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool)
    (p : I × ↥(Internal.GluingChainCollarRetractionHelpers.chainSideNeighborhood P k b)) (hp : p.2.1 ∈ Internal.GluingChainCollarRetractionHelpers.chainSide P k b) :
    Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn P k b p = p.2.1 := by
  classical
  unfold Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn
  split_ifs with hx
  · exact congrArg Subtype.val (seamHalfRadialMap_fixed P k b p.1 ⟨p.2.1, hx⟩ hp)
  · rfl

theorem Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn_continuous
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool) :
    Continuous (Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn P k b) := by
  classical
  let s : Set (I × ↥(Internal.GluingChainCollarRetractionHelpers.chainSideNeighborhood P k b)) :=
    {p | p.2.1 ∈ P.gluedMk '' P.seamNeighborhood k}
  have hs : IsOpen s := (P.gluedSeamNeighborhood_isOpen k).preimage
    (continuous_subtype_val.comp continuous_snd)
  have hc : ContinuousOn (Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn P k b) s := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hf : Continuous (fun p : s =>
        (p.1.1, (⟨p.1.2.1, p.2⟩ : ↥(P.gluedMk '' P.seamNeighborhood k)))) :=
      (continuous_fst.comp continuous_subtype_val).prodMk
        (((continuous_subtype_val.comp continuous_snd).comp
          continuous_subtype_val).subtype_mk _)
    have h := continuous_subtype_val.comp ((Internal.GluingChainCollarRetractionHelpers.seamHalfRadialMap P k b).continuous.comp hf)
    apply h.congr
    intro p
    dsimp only [Set.domRestrict, Function.comp_apply,
      Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn]
    have hp : p.1.2.1 ∈ P.gluedMk '' P.seamNeighborhood k := p.2
    rw [dite_eq_left hp]
  let v : Set (I × ↥(Internal.GluingChainCollarRetractionHelpers.chainSideNeighborhood P k b)) :=
    {p | p.2.1 ∉ Internal.GluingChainCollarRetractionHelpers.chainSide P k (!b)}
  have hv : IsOpen v := (chainSide_isClosed P k (!b)).isOpen_compl.preimage
    (continuous_subtype_val.comp continuous_snd)
  have hd : ContinuousOn (Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn P k b) v := by
    apply (continuous_subtype_val.comp continuous_snd).continuousOn.congr
    intro p hp
    exact Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn_fixed P k b p
      (chainSide_mem_of_not_other P k b hp)
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p ∈ s
  · exact hc.continuousAt (hs.mem_nhds hp)
  · have hpv : p ∈ v := by
      intro hother
      exact hp (chainSideNeighborhood_inter_other_subset P k b ⟨p.2.2, hother⟩)
    exact hd.continuousAt (hv.mem_nhds hpv)

theorem Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn_mem
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool)
    (p : I × ↥(Internal.GluingChainCollarRetractionHelpers.chainSideNeighborhood P k b)) :
    Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn P k b p ∈ Internal.GluingChainCollarRetractionHelpers.chainSideNeighborhood P k b := by
  classical
  unfold Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn
  split_ifs with hx
  · exact Or.inr (Internal.GluingChainCollarRetractionHelpers.seamHalfRadialMap P k b (p.1, ⟨p.2.1, hx⟩)).2
  · exact p.2.2

def Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyMap
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool) :
    C(I × ↥(Internal.GluingChainCollarRetractionHelpers.chainSideNeighborhood P k b), ↥(Internal.GluingChainCollarRetractionHelpers.chainSideNeighborhood P k b)) where
  toFun p := ⟨Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn P k b p, Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn_mem P k b p⟩
  continuous_toFun := (Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn_continuous P k b).subtype_mk _

theorem Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn_zero
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool)
    (x : ↥(Internal.GluingChainCollarRetractionHelpers.chainSideNeighborhood P k b)) : Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn P k b (0, x) = x.1 := by
  classical
  unfold Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn
  split_ifs with hx
  · exact congrArg Subtype.val (seamHalfRadialMap_zero P k b ⟨x.1, hx⟩)
  · rfl

theorem Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn_one_mem
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool)
    (x : ↥(Internal.GluingChainCollarRetractionHelpers.chainSideNeighborhood P k b)) :
    Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn P k b (1, x) ∈ Internal.GluingChainCollarRetractionHelpers.chainSide P k b := by
  classical
  unfold Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn
  split_ifs with hx
  · exact seamHalfRadialMap_one_mem P k b ⟨x.1, hx⟩
  · exact x.2.resolve_right hx

def Internal.GluingChainCollarRetractionHelpers.chainSideInclusion
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool) :
    C(↥(Internal.GluingChainCollarRetractionHelpers.chainSide P k b), ↥(Internal.GluingChainCollarRetractionHelpers.chainSideNeighborhood P k b)) where
  toFun x := ⟨x.1, Or.inl x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def Internal.GluingChainCollarRetractionHelpers.chainSideRetraction
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool) :
    C(↥(Internal.GluingChainCollarRetractionHelpers.chainSideNeighborhood P k b), ↥(Internal.GluingChainCollarRetractionHelpers.chainSide P k b)) where
  toFun x := ⟨Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn P k b (1, x), Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn_one_mem P k b x⟩
  continuous_toFun := ((Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn_continuous P k b).comp
    (continuous_const.prodMk continuous_id)).subtype_mk _

theorem Internal.GluingChainCollarRetractionHelpers.chainSideRetraction_inclusion
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool)
    (x : ↥(Internal.GluingChainCollarRetractionHelpers.chainSide P k b)) :
    Internal.GluingChainCollarRetractionHelpers.chainSideRetraction P k b (Internal.GluingChainCollarRetractionHelpers.chainSideInclusion P k b x) = x := by
  apply Subtype.ext
  exact Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn_fixed P k b (1, Internal.GluingChainCollarRetractionHelpers.chainSideInclusion P k b x) x.2

def Internal.GluingChainCollarRetractionHelpers.chainSideDeformationRetraction
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (b : Bool) :
    (ContinuousMap.id ↥(Internal.GluingChainCollarRetractionHelpers.chainSideNeighborhood P k b)).HomotopyRel
      ((Internal.GluingChainCollarRetractionHelpers.chainSideInclusion P k b).comp (Internal.GluingChainCollarRetractionHelpers.chainSideRetraction P k b))
      {x | x.1 ∈ Internal.GluingChainCollarRetractionHelpers.chainSide P k b} where
  toHomotopy :=
    { toContinuousMap := Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyMap P k b
      map_zero_left := fun x => Subtype.ext (Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn_zero P k b x)
      map_one_left := fun _ => rfl }
  prop' := by
    intro t x hx
    apply Subtype.ext
    exact Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn_fixed P k b (t, x) hx

/-- The literal inclusion of the original closed prefix into its actual
collar-thickened open side. -/
def gluedChainPrefixInclusion
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    C(↥(P.gluedChainPrefix k), ↥(P.gluedChainPrefixNeighborhood k)) :=
  Internal.GluingChainCollarRetractionHelpers.chainSideInclusion P k true

/-- Collapse only the added incoming half-collar; keep the original prefix. -/
def gluedChainPrefixRetraction
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    C(↥(P.gluedChainPrefixNeighborhood k), ↥(P.gluedChainPrefix k)) :=
  Internal.GluingChainCollarRetractionHelpers.chainSideRetraction P k true

@[simp] theorem gluedChainPrefixRetraction_inclusion
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainPrefix k)) :
    P.gluedChainPrefixRetraction k (P.gluedChainPrefixInclusion k x) = x :=
  Internal.GluingChainCollarRetractionHelpers.chainSideRetraction_inclusion P k true x

/-- The entire original closed prefix is fixed throughout this actual strong
deformation retraction of its open thickening. -/
def gluedChainPrefixDeformationRetraction
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    (ContinuousMap.id ↥(P.gluedChainPrefixNeighborhood k)).HomotopyRel
      ((P.gluedChainPrefixInclusion k).comp (P.gluedChainPrefixRetraction k))
      {x | x.1 ∈ P.gluedChainPrefix k} :=
  Internal.GluingChainCollarRetractionHelpers.chainSideDeformationRetraction P k true

/-- The literal inclusion of the original closed suffix into its open side. -/
def gluedChainSuffixInclusion
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    C(↥(P.gluedChainSuffix k), ↥(P.gluedChainSuffixNeighborhood k)) :=
  Internal.GluingChainCollarRetractionHelpers.chainSideInclusion P k false

/-- Collapse only the added outgoing half-collar; keep the original suffix. -/
def gluedChainSuffixRetraction
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    C(↥(P.gluedChainSuffixNeighborhood k), ↥(P.gluedChainSuffix k)) :=
  Internal.GluingChainCollarRetractionHelpers.chainSideRetraction P k false

@[simp] theorem gluedChainSuffixRetraction_inclusion
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (x : ↥(P.gluedChainSuffix k)) :
    P.gluedChainSuffixRetraction k (P.gluedChainSuffixInclusion k x) = x :=
  Internal.GluingChainCollarRetractionHelpers.chainSideRetraction_inclusion P k false x

/-- The same strong retraction fixes every original suffix point at every
time, including its actual inner boundary circle. -/
def gluedChainSuffixDeformationRetraction
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    (ContinuousMap.id ↥(P.gluedChainSuffixNeighborhood k)).HomotopyRel
      ((P.gluedChainSuffixInclusion k).comp (P.gluedChainSuffixRetraction k))
      {x | x.1 ∈ P.gluedChainSuffix k} :=
  Internal.GluingChainCollarRetractionHelpers.chainSideDeformationRetraction P k false

/-- The prefix collar homotopy at cut `j` stays inside every actual later
prefix `k`, provided it starts in that prefix. The moved locus is precisely
the actual seam neighborhood at `j`, whose two incident component images
are already contained in the later prefix. -/
theorem gluedChainPrefixDeformationRetraction_preserves_laterPrefix
    (P : ExerciseGluingPreparation C g n genera X) (j k : Fin (n - 1))
    (hjk : j.val < k.val) (t : I)
    (x : ↥(P.gluedChainPrefixNeighborhood j))
    (hx : x.1 ∈ P.gluedChainPrefix k) :
    ((P.gluedChainPrefixDeformationRetraction j).toHomotopy (t, x)).1 ∈
      P.gluedChainPrefix k := by
  classical
  change Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn P j true (t, x) ∈ P.gluedChainPrefix k
  unfold Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn
  split_ifs with hseam
  · exact P.gluedMk_image_seamNeighborhood_subset_prefix_of_lt j k hjk
      (Internal.GluingChainCollarRetractionHelpers.seamHalfRadialMap P j true (t, ⟨x.1, hseam⟩)).2
  · exact hx

/-- The suffix collar homotopy at cut `j` has the same preservation property
for every later actual prefix. Its points on the moving locus remain in the
earlier seam neighborhood, and points off that locus are fixed. -/
theorem gluedChainSuffixDeformationRetraction_preserves_laterPrefix
    (P : ExerciseGluingPreparation C g n genera X) (j k : Fin (n - 1))
    (hjk : j.val < k.val) (t : I)
    (x : ↥(P.gluedChainSuffixNeighborhood j))
    (hx : x.1 ∈ P.gluedChainPrefix k) :
    ((P.gluedChainSuffixDeformationRetraction j).toHomotopy (t, x)).1 ∈
      P.gluedChainPrefix k := by
  classical
  change Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn P j false (t, x) ∈ P.gluedChainPrefix k
  unfold Internal.GluingChainCollarRetractionHelpers.chainCollarHomotopyFn
  split_ifs with hseam
  · exact P.gluedMk_image_seamNeighborhood_subset_prefix_of_lt j k hjk
      (Internal.GluingChainCollarRetractionHelpers.seamHalfRadialMap P j false (t, ⟨x.1, hseam⟩)).2
  · exact hx

/-- At consecutive cuts, the later closed prefix and earlier closed suffix
meet in exactly the intervening original component image. This is the actual
target of restricting the suffix retraction to the later prefix. -/
theorem gluedChainPrefix_inter_suffix_eq_componentImage
    (P : ExerciseGluingPreparation C g n genera X) (j k : Fin (n - 1))
    (hjk : j.val + 1 = k.val) :
    P.gluedChainPrefix k ∩ P.gluedChainSuffix j =
      P.gluedComponentImage (gluingChainEdgeLeft k) := by
  have hcomponent (a : P.ChainPieces) (ha : a.1 = gluingChainEdgeLeft k) :
      P.gluedMk a ∈ P.gluedComponentImage (gluingChainEdgeLeft k) := by
    rcases a with ⟨i, x⟩
    change i = gluingChainEdgeLeft k at ha
    subst i
    exact ⟨x, rfl⟩
  ext q
  constructor
  · rintro ⟨⟨a, ha, haq⟩, ⟨b, hb, hbq⟩⟩
    have hab : P.gluedMk a = P.gluedMk b := haq.trans hbq.symm
    rcases (P.gluedMk_eq_iff a b).mp hab with heq | hrel | hrev
    · have hidx : a.1 = b.1 := congrArg Sigma.fst heq
      change a.1.val ≤ k.val at ha
      change j.val < b.1.val at hb
      have hright : j.val < a.1.val := by simpa only [← hidx] using hb
      have hval : a.1.val = k.val := by
        have hleft : a.1.val ≤ k.val := ha
        omega
      have hidxk : a.1 = gluingChainEdgeLeft k := Fin.ext (by
        change a.1.val = k.val
        exact hval)
      rw [← haq]
      exact hcomponent a hidxk
    · obtain ⟨l, z, rfl, rfl⟩ := hrel
      change l.val ≤ k.val at ha
      change j.val < l.val + 1 at hb
      by_cases hlj : l.val = j.val
      · have hl : l = j := Fin.ext hlj
        subst l
        have hright : gluingChainEdgeRight j = gluingChainEdgeLeft k := Fin.ext (by
          dsimp [gluingChainEdgeRight, gluingChainEdgeLeft]
          omega)
        rw [← hbq]
        apply hcomponent
        change gluingChainEdgeRight j = gluingChainEdgeLeft k
        exact hright
      · have hlk : l.val = k.val := by omega
        have hl : l = k := Fin.ext hlk
        subst l
        rw [← haq]
        apply hcomponent
        rfl
    · obtain ⟨l, z, rfl, rfl⟩ := hrev
      change l.val + 1 ≤ k.val at ha
      change j.val < l.val at hb
      omega
  · rintro ⟨x, rfl⟩
    constructor
    · exact ⟨⟨gluingChainEdgeLeft k, x⟩, by
        change (gluingChainEdgeLeft k).val ≤ k.val
        rfl, rfl⟩
    · exact ⟨⟨gluingChainEdgeLeft k, x⟩, by
        change j.val < k.val
        omega, rfl⟩

/-- Removing the added half-collar preserves the homotopy type of the
actual retained prefix, through its literal inclusion and retraction. -/
def gluedChainPrefixHomotopyEquiv
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    ↥(P.gluedChainPrefixNeighborhood k) ≃ₕ ↥(P.gluedChainPrefix k) where
  toFun := P.gluedChainPrefixRetraction k
  invFun := P.gluedChainPrefixInclusion k
  left_inv := ⟨(P.gluedChainPrefixDeformationRetraction k).toHomotopy.symm⟩
  right_inv := by
    have h : (P.gluedChainPrefixRetraction k).comp (P.gluedChainPrefixInclusion k) =
        ContinuousMap.id ↥(P.gluedChainPrefix k) := by
      apply ContinuousMap.ext
      intro x
      exact P.gluedChainPrefixRetraction_inclusion k x
    rw [h]

/-- The symmetric actual suffix homotopy equivalence fixes its full
retained side, including the original identified inner circle. -/
def gluedChainSuffixHomotopyEquiv
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    ↥(P.gluedChainSuffixNeighborhood k) ≃ₕ ↥(P.gluedChainSuffix k) where
  toFun := P.gluedChainSuffixRetraction k
  invFun := P.gluedChainSuffixInclusion k
  left_inv := ⟨(P.gluedChainSuffixDeformationRetraction k).toHomotopy.symm⟩
  right_inv := by
    have h : (P.gluedChainSuffixRetraction k).comp (P.gluedChainSuffixInclusion k) =
        ContinuousMap.id ↥(P.gluedChainSuffix k) := by
      apply ContinuousMap.ext
      intro x
      exact P.gluedChainSuffixRetraction_inclusion k x
    rw [h]

#print axioms seamCylinderHomeomorph_apply_of_nonpos
#print axioms seamCylinderHomeomorph_apply_of_nonneg
#print axioms seamCylinderHomeomorph_mem_seamCircle_iff
#print axioms seamCylinderHomeomorph_mem_prefix_iff
#print axioms seamCylinderHomeomorph_mem_suffix_iff
#print axioms gluedChainPrefixDeformationRetraction
#print axioms gluedChainSuffixDeformationRetraction
#print axioms gluedMk_image_seamNeighborhood_subset_prefix_of_lt
#print axioms gluedChainPrefix_subset_of_le
#print axioms gluedChainPrefixNeighborhood_subset_laterPrefix
#print axioms gluedChainPrefixDeformationRetraction_preserves_laterPrefix
#print axioms gluedChainSuffixDeformationRetraction_preserves_laterPrefix
#print axioms gluedChainPrefix_inter_suffix_eq_componentImage
#print axioms gluedChainPrefixRetraction_inclusion
#print axioms gluedChainSuffixRetraction_inclusion
#print axioms gluedChainPrefixHomotopyEquiv
#print axioms gluedChainSuffixHomotopyEquiv

end

end SystolicGrowth.ExerciseGluingPreparation

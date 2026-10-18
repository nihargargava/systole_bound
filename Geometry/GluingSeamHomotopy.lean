module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSeamCharts
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section

/-!
# The homotopy type of an actual seam neighborhood

The proved signed-cylinder chart retracts the original open seam neighborhood
onto its middle circle. The radial homotopy fixes that circle at every time.
This supplies the actual overlap homotopy type for the later surface-group
marking; no genus or fundamental-group presentation is assumed here.
-/

open Set
open scoped ContinuousMap unitInterval

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The middle circle included in the actual original seam neighborhood. -/
def gluedSeamCircleInclusion (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) : C(Circle, ↥(P.gluedMk '' P.seamNeighborhood k)) where
  toFun θ := P.seamCylinderHomeomorph k
    (θ, ⟨0, neg_lt_zero.mpr P.depth_pos, P.depth_pos⟩)
  continuous_toFun := (P.seamCylinderHomeomorph k).continuous.comp
    (continuous_id.prodMk continuous_const)

/-- The inclusion is the original outgoing inner-circle map, not a different
circle introduced by the homotopy equivalence. -/
theorem gluedSeamCircleInclusion_eq_outgoing
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    P.gluedSeamCircleInclusion k θ = P.seamNeighborhoodProjection k
      ⟨P.seamOutgoingPolarPoint k
          (θ, ⟨gluingRadius C g, le_rfl, P.radius_lt_embeddedRadius⟩),
        P.seamOutgoingPolarPoint_mem k _⟩ := by
  apply (P.seamCylinderHomeomorph k).symm.injective
  change (P.seamCylinderHomeomorph k).symm
      (P.seamCylinderHomeomorph k
        (θ, ⟨0, neg_lt_zero.mpr P.depth_pos, P.depth_pos⟩)) = _
  rw [Homeomorph.symm_apply_apply, P.seamCylinderHomeomorph_symm_outgoing]
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp

/-- Every included circle point belongs to the original identified seam set. -/
theorem gluedSeamCircleInclusion_mem
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    (P.gluedSeamCircleInclusion k θ).1 ∈ P.gluedSeamCircle k := by
  rw [P.gluedSeamCircleInclusion_eq_outgoing k θ]
  let z : Metric.sphere (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) :=
    ⟨gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2 θ (gluingRadius C g), by
      rw [Metric.mem_sphere, dist_comm, dist_gluingPolarPoint _ θ P.radius_pos.le]⟩
  refine ⟨z, ?_⟩
  change P.gluedMk (P.seamSource k z) = P.gluedMk (P.seamOutgoingPolarPoint k _)
  apply congrArg P.gluedMk
  apply Sigma.ext rfl
  apply heq_of_eq
  apply Subtype.ext
  rfl

/-- The included middle circle is exactly the entire original seam circle. -/
theorem range_gluedSeamCircleInclusion
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Set.range (fun θ : Circle => (P.gluedSeamCircleInclusion k θ).1) =
      P.gluedSeamCircle k := by
  apply Set.Subset.antisymm
  · rintro q ⟨θ, rfl⟩
    exact P.gluedSeamCircleInclusion_mem k θ
  · rintro q ⟨z, rfl⟩
    let o := (P.centers (gluingChainEdgeLeft k)).2
    have hz : dist o z.1 = gluingRadius C g := by
      simpa only [Metric.mem_sphere, dist_comm] using z.property
    let a : ↥(Metric.ball o (gluingEmbeddedRadius C g) \
        Metric.ball o (gluingRadius C g)) := ⟨z.1, by
      constructor
      · rw [Metric.mem_ball, dist_comm, hz]
        exact P.radius_lt_embeddedRadius
      · rw [Metric.mem_ball, dist_comm, hz]
        exact lt_irrefl _⟩
    let h := gluingHalfAnnulusPolarHomeomorph o (gluingRadius C g)
      (gluingEmbeddedRadius C g) P.radius_pos
    let θ : Circle := (h a).1
    have hpoint : gluingPolarPoint o θ (gluingRadius C g) = z.1 := by
      have hinv := congrArg Subtype.val (h.symm_apply_apply a)
      change gluingPolarPoint o θ (dist o z.1) = z.1 at hinv
      rwa [hz] at hinv
    refine ⟨θ, ?_⟩
    change (P.gluedSeamCircleInclusion k θ).1 = P.gluedMk (P.seamSource k z)
    rw [P.gluedSeamCircleInclusion_eq_outgoing k θ]
    change P.gluedMk (P.seamOutgoingPolarPoint k _) = P.gluedMk (P.seamSource k z)
    apply congrArg P.gluedMk
    unfold seamOutgoingPolarPoint seamSource
    apply congrArg (Sigma.mk (gluingChainEdgeLeft k))
    apply Subtype.ext
    change (Quotient.mk'' (gluingPolarPoint o θ (gluingRadius C g)) :
      (X (gluingChainEdgeLeft k)).Carrier) = Quotient.mk'' z.1
    rw [hpoint]

/-- Retraction takes the genuine angular coordinate in the original seam chart. -/
def gluedSeamCircleRetraction (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) : C(↥(P.gluedMk '' P.seamNeighborhood k), Circle) where
  toFun x := ((P.seamCylinderHomeomorph k).symm x).1
  continuous_toFun := (P.seamCylinderHomeomorph k).symm.continuous.fst

@[simp] theorem gluedSeamCircleRetraction_inclusion
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    P.gluedSeamCircleRetraction k (P.gluedSeamCircleInclusion k θ) = θ := by
  exact congrArg Prod.fst ((P.seamCylinderHomeomorph k).symm_apply_apply
    (θ, ⟨0, neg_lt_zero.mpr P.depth_pos, P.depth_pos⟩))

theorem Internal.GluingSeamHomotopyHelpers.seamRadialScale_mem
    (P : ExerciseGluingPreparation C g n genera X) (t : unitInterval)
    (r : Ioo (-gluingDepth C g) (gluingDepth C g)) :
    (t : ℝ) * (r : ℝ) ∈ Ioo (-gluingDepth C g) (gluingDepth C g) := by
  have hzero : (0 : ℝ) ∈ Ioo (-gluingDepth C g) (gluingDepth C g) :=
    ⟨neg_lt_zero.mpr P.depth_pos, P.depth_pos⟩
  have hm := (convex_Ioo (-gluingDepth C g) (gluingDepth C g)) hzero r.property
    (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
  simpa only [smul_eq_mul, mul_zero, zero_add] using hm

/-- The explicit radial homotopy expands the middle-circle retraction to the
identity inside the actual open seam neighborhood. -/
def gluedSeamRadialHomotopy
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    ((P.gluedSeamCircleInclusion k).comp (P.gluedSeamCircleRetraction k)).Homotopy
      (ContinuousMap.id ↥(P.gluedMk '' P.seamNeighborhood k)) where
  toFun p := P.seamCylinderHomeomorph k
    (((P.seamCylinderHomeomorph k).symm p.2).1,
      ⟨(p.1 : ℝ) * (((P.seamCylinderHomeomorph k).symm p.2).2 : ℝ),
        Internal.GluingSeamHomotopyHelpers.seamRadialScale_mem P p.1 ((P.seamCylinderHomeomorph k).symm p.2).2⟩)
  continuous_toFun := by
    apply (P.seamCylinderHomeomorph k).continuous.comp
    apply Continuous.prodMk
    · exact ((P.seamCylinderHomeomorph k).symm.continuous.comp continuous_snd).fst
    · exact ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp
          ((P.seamCylinderHomeomorph k).symm.continuous.comp continuous_snd).snd)).subtype_mk _
  map_zero_left := by
    intro x
    apply congrArg (P.seamCylinderHomeomorph k)
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp
  map_one_left := by
    intro x
    have hpair :
        (((P.seamCylinderHomeomorph k).symm x).1,
            (⟨(1 : unitInterval).val * (((P.seamCylinderHomeomorph k).symm x).2 : ℝ),
              Internal.GluingSeamHomotopyHelpers.seamRadialScale_mem P 1 ((P.seamCylinderHomeomorph k).symm x).2⟩ :
                Ioo (-gluingDepth C g) (gluingDepth C g))) =
          (P.seamCylinderHomeomorph k).symm x := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp
    exact (congrArg (P.seamCylinderHomeomorph k) hpair).trans
      ((P.seamCylinderHomeomorph k).apply_symm_apply x)

/-- No point on the included middle circle moves during the radial homotopy. -/
@[simp] theorem gluedSeamRadialHomotopy_inclusion
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (t : unitInterval) (θ : Circle) :
    P.gluedSeamRadialHomotopy k (t, P.gluedSeamCircleInclusion k θ) =
      P.gluedSeamCircleInclusion k θ := by
  change P.seamCylinderHomeomorph k _ = P.seamCylinderHomeomorph k _
  apply congrArg (P.seamCylinderHomeomorph k)
  simp only [gluedSeamCircleInclusion, ContinuousMap.coe_mk,
    Homeomorph.symm_apply_apply]
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simp

/-- A strong deformation retraction in the original carrier: the homotopy
starts at the identity, ends at inclusion after retraction, and fixes every
point of the entire actual seam circle throughout. -/
def gluedSeamDeformationRetraction
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    (ContinuousMap.id ↥(P.gluedMk '' P.seamNeighborhood k)).HomotopyRel
      ((P.gluedSeamCircleInclusion k).comp (P.gluedSeamCircleRetraction k))
      {x | x.1 ∈ P.gluedSeamCircle k} where
  toHomotopy := (P.gluedSeamRadialHomotopy k).symm
  prop' := by
    intro t x hx
    have hxrange : x.1 ∈ Set.range (fun θ : Circle => (P.gluedSeamCircleInclusion k θ).1) := by
      rw [P.range_gluedSeamCircleInclusion k]
      exact hx
    obtain ⟨θ, hθ⟩ := hxrange
    have hincl : P.gluedSeamCircleInclusion k θ = x := Subtype.ext hθ
    rw [← hincl]
    exact P.gluedSeamRadialHomotopy_inclusion k (unitInterval.symm t) θ

/-- The actual open seam overlap is homotopy equivalent to its circle. -/
def gluedSeamCircleHomotopyEquiv
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    ↥(P.gluedMk '' P.seamNeighborhood k) ≃ₕ Circle where
  toFun := P.gluedSeamCircleRetraction k
  invFun := P.gluedSeamCircleInclusion k
  left_inv := ⟨P.gluedSeamRadialHomotopy k⟩
  right_inv := by
    have hcomp : (P.gluedSeamCircleRetraction k).comp (P.gluedSeamCircleInclusion k) =
        ContinuousMap.id Circle := by
      apply ContinuousMap.ext
      intro θ
      exact P.gluedSeamCircleRetraction_inclusion k θ
    rw [hcomp]

#print axioms gluedSeamCircleHomotopyEquiv
#print axioms gluedSeamRadialHomotopy_inclusion
#print axioms gluedSeamCircleInclusion_mem
#print axioms range_gluedSeamCircleInclusion
#print axioms gluedSeamDeformationRetraction

end

end SystolicGrowth.ExerciseGluingPreparation

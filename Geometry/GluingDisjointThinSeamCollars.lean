module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSeamOverlap
public import Geometry.GluingSeamHomotopy

@[expose] public section

/-!
# Disjoint compactly contained native thin seam collars

The original outer collars need not be disjoint. These smaller strips use
one quarter of the original depth. Actual center separation and native
quotient incidence prove that their closed strips are disjoint.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

theorem thinSeamWidth_pos (P : ExerciseGluingPreparation C g n genera X) :
    0 < gluingThinSeamWidth C g := by
  unfold gluingThinSeamWidth
  linarith [P.depth_pos]

theorem twice_thinSeamWidth_lt_depth (P : ExerciseGluingPreparation C g n genera X) :
    2 * gluingThinSeamWidth C g < gluingDepth C g := by
  unfold gluingThinSeamWidth
  linarith [P.depth_pos]

theorem thinSeamWidth_lt_depth (P : ExerciseGluingPreparation C g n genera X) :
    gluingThinSeamWidth C g < gluingDepth C g := by
  linarith [P.thinSeamWidth_pos, P.twice_thinSeamWidth_lt_depth]

private theorem carrier_dist_polarPoint_center
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) (u : Circle)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hR : ρ < gluingEmbeddedRadius C g) :
    dist (Quotient.mk'' (gluingPolarPoint o u ρ) : (X i).Carrier)
      (Quotient.mk'' o) = ρ := by
  rw [dist_comm, (X i).carrier_dist_mk_center_eq_of_mem_closedBall o
    (gluingEmbeddedRadius C g) (P.twice_outer_lt_systole i)]
  · exact dist_gluingPolarPoint o u hρ
  · simpa only [mem_closedBall, dist_comm, dist_gluingPolarPoint o u hρ] using hR.le

private theorem thin_outgoing_incoming_interior_ne
    (P : ExerciseGluingPreparation C g n genera X) (i j : Fin n)
    (a : P.componentInteriorSet i) (b : P.componentInteriorSet j)
    (ha : dist a.1 (Quotient.mk'' (P.centers i).2) ≤
      gluingRadius C g + gluingThinSeamWidth C g)
    (hb : dist b.1 (Quotient.mk'' (P.centers j).1) ≤
      gluingRadius C g + gluingThinSeamWidth C g) :
    P.gluedMk (P.componentInteriorPoint i a) ≠
      P.gluedMk (P.componentInteriorPoint j b) := by
  intro h
  have heq := P.gluedMk_eq_of_not_mem_chainSeamSet
    (P.componentInteriorPoint_not_mem_chainSeamSet i a) h
  have hij : i = j := congrArg Sigma.fst heq
  subst j
  have hab : a = b := (P.componentInteriorPoint_isOpenEmbedding i).injective heq
  subst b
  have htri := dist_triangle (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
    a.1 (Quotient.mk'' (P.centers i).2)
  rw [dist_comm (Quotient.mk'' (P.centers i).1 : (X i).Carrier) a.1] at htri
  have hsep := P.carrier_centers_outer_add_inner_le_dist i
  change gluingRadius C g + gluingDepth C g + gluingRadius C g ≤ _ at hsep
  linarith [P.twice_thinSeamWidth_lt_depth]

private theorem thin_angular_outgoing_rep
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) (hp : p.1.1 < 0)
    (hthin : |p.1.1| ≤ gluingThinSeamWidth C g) :
    ∃ q : P.componentInteriorSet (gluingChainEdgeLeft k),
      P.seamAngularPoint k θ p = P.gluedMk (P.componentInteriorPoint _ q) ∧
      dist q.1 (Quotient.mk'' (P.centers (gluingChainEdgeLeft k)).2) ≤
        gluingRadius C g + gluingThinSeamWidth C g := by
  have hR : gluingRadius C g - p.1.1 < gluingEmbeddedRadius C g := by
    change gluingRadius C g - p.1.1 < gluingRadius C g + gluingDepth C g
    linarith [p.1.2.1]
  refine ⟨⟨Quotient.mk'' (gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2
      (Circle.exp p.2.1) (gluingRadius C g - p.1.1)),
    P.outgoing_polarPoint_mem_componentInteriorSet _ _ (by linarith) hR⟩, ?_, ?_⟩
  · rw [P.seamAngularPoint_of_nonpos k θ p hp.le]
    apply congrArg P.gluedMk
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Subtype.ext
    rfl
  · rw [carrier_dist_polarPoint_center P _ _ _ (by linarith [P.radius_pos]) hR]
    rw [abs_of_neg hp] at hthin
    linarith

private theorem thin_angular_incoming_rep
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) (hp : 0 < p.1.1)
    (hthin : |p.1.1| ≤ gluingThinSeamWidth C g) :
    ∃ q : P.componentInteriorSet (gluingChainEdgeRight k),
      P.seamAngularPoint k θ p = P.gluedMk (P.componentInteriorPoint _ q) ∧
      dist q.1 (Quotient.mk'' (P.centers (gluingChainEdgeRight k)).1) ≤
        gluingRadius C g + gluingThinSeamWidth C g := by
  have hR : gluingRadius C g + p.1.1 < gluingEmbeddedRadius C g := by
    change gluingRadius C g + p.1.1 < gluingRadius C g + gluingDepth C g
    linarith [p.1.2.2]
  refine ⟨⟨Quotient.mk'' (gluingPolarPoint (P.centers (gluingChainEdgeRight k)).1
      (Circle.exp p.2.1)⁻¹ (gluingRadius C g + p.1.1)),
    P.incoming_polarPoint_mem_componentInteriorSet _ _ (by linarith) hR⟩, ?_, ?_⟩
  · rw [P.seamAngularPoint_of_nonneg k θ p hp.le]
    apply congrArg P.gluedMk
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Subtype.ext
    rfl
  · rw [carrier_dist_polarPoint_center P _ _ _ (by linarith [P.radius_pos]) hR]
    rw [abs_of_pos hp] at hthin
    linarith

/-- Genuine thin-strip points in two different angular seam charts cannot
coincide in the actual glued quotient. -/
theorem seamAngularPoint_ne_distinct_of_abs_radial_le_thinWidth
    (P : ExerciseGluingPreparation C g n genera X) (k l : Fin (n - 1))
    (hkl : k ≠ l) (θ ψ : ℝ) (p : GluingSeamAngularDomain C g θ)
    (q : GluingSeamAngularDomain C g ψ)
    (hp : |p.1.1| ≤ gluingThinSeamWidth C g)
    (hq : |q.1.1| ≤ gluingThinSeamWidth C g) :
    P.seamAngularPoint k θ p ≠ P.seamAngularPoint l ψ q := by
  intro h
  have hn := P.seamAngularPoint_eq_distinct_nonzero k l hkl θ ψ p q h
  rcases lt_or_gt_of_ne hn.1 with hpneg | hppos <;>
    rcases lt_or_gt_of_ne hn.2 with hqneg | hqpos
  · obtain ⟨a, ha, _⟩ := thin_angular_outgoing_rep P k θ p hpneg hp
    obtain ⟨b, hb, _⟩ := thin_angular_outgoing_rep P l ψ q hqneg hq
    have heq := P.gluedMk_eq_of_not_mem_chainSeamSet
      (P.componentInteriorPoint_not_mem_chainSeamSet _ a) (ha.symm.trans (h.trans hb))
    have hi := congrArg (fun a : P.ChainPieces => a.1.1) heq
    exact hkl (Fin.ext hi)
  · obtain ⟨a, ha, hda⟩ := thin_angular_outgoing_rep P k θ p hpneg hp
    obtain ⟨b, hb, hdb⟩ := thin_angular_incoming_rep P l ψ q hqpos hq
    exact thin_outgoing_incoming_interior_ne P _ _ a b hda hdb
      (ha.symm.trans (h.trans hb))
  · obtain ⟨a, ha, hda⟩ := thin_angular_incoming_rep P k θ p hppos hp
    obtain ⟨b, hb, hdb⟩ := thin_angular_outgoing_rep P l ψ q hqneg hq
    exact thin_outgoing_incoming_interior_ne P _ _ b a hdb hda
      (hb.symm.trans (h.symm.trans ha))
  · obtain ⟨a, ha, _⟩ := thin_angular_incoming_rep P k θ p hppos hp
    obtain ⟨b, hb, _⟩ := thin_angular_incoming_rep P l ψ q hqpos hq
    have heq := P.gluedMk_eq_of_not_mem_chainSeamSet
      (P.componentInteriorPoint_not_mem_chainSeamSet _ a) (ha.symm.trans (h.trans hb))
    have hi := congrArg (fun a : P.ChainPieces => a.1.1) heq
    apply hkl
    apply Fin.ext
    change k.1 + 1 = l.1 + 1 at hi
    omega

/-- The actual open cylinder strip used for localized seam smoothing. -/
def thinSeamCollar (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) : Set P.GluedCarrier :=
  (fun p : GluingSeamCylinder C g => (P.seamCylinderHomeomorph k p).1) ''
    {p | |p.2.1| < gluingThinSeamWidth C g}

theorem thinSeamCollar_isOpen (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) : IsOpen (P.thinSeamCollar k) := by
  apply ((P.gluedSeamNeighborhood_isOpen k).isOpenEmbedding_subtypeVal.comp
    (P.seamCylinderHomeomorph k).isOpenEmbedding).isOpenMap
  exact isOpen_lt (continuous_subtype_val.comp continuous_snd).abs continuous_const

theorem seamCylinderHomeomorph_mem_thinSeamCollar_iff
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : GluingSeamCylinder C g) :
    (P.seamCylinderHomeomorph k p).1 ∈ P.thinSeamCollar k ↔
      |p.2.1| < gluingThinSeamWidth C g := by
  constructor
  · rintro ⟨q, hq, heq⟩
    have hqp := (P.seamCylinderHomeomorph k).injective (Subtype.ext heq)
    exact hqp ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem seamCylinderHomeomorph_mem_closedThinSeamCollar_iff
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (p : GluingSeamCylinder C g) :
    (P.seamCylinderHomeomorph k p).1 ∈ P.closedThinSeamCollar k ↔
      |p.2.1| ≤ gluingThinSeamWidth C g := by
  constructor
  · rintro ⟨q, hq, heq⟩
    have hqp := (P.seamCylinderHomeomorph k).injective (Subtype.ext heq)
    exact hqp ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem gluedSeamCircle_subset_thinSeamCollar
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedSeamCircle k ⊆ P.thinSeamCollar k := by
  rw [← P.range_gluedSeamCircleInclusion k]
  rintro y ⟨u, rfl⟩
  apply (P.seamCylinderHomeomorph_mem_thinSeamCollar_iff k
    (u, ⟨0, neg_lt_zero.mpr P.depth_pos, P.depth_pos⟩)).mpr
  simpa only [abs_zero] using P.thinSeamWidth_pos

private theorem signed_closed_thin_strip_isCompact
    (P : ExerciseGluingPreparation C g n genera X) :
    IsCompact {p : GluingSeamCylinder C g | |p.2.1| ≤ gluingThinSeamWidth C g} := by
  have hrad : IsCompact {t : Ioo (-gluingDepth C g) (gluingDepth C g) |
      |t.1| ≤ gluingThinSeamWidth C g} := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    have heq : Subtype.val '' {t : Ioo (-gluingDepth C g) (gluingDepth C g) |
        |t.1| ≤ gluingThinSeamWidth C g} =
        Icc (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g) := by
      ext t
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact abs_le.mp hu
      · intro ht
        refine ⟨⟨t, ?_⟩, abs_le.mpr ht, rfl⟩
        constructor <;> linarith [P.thinSeamWidth_lt_depth, ht.1, ht.2]
    rw [heq]
    exact isCompact_Icc
  have heq : {p : GluingSeamCylinder C g | |p.2.1| ≤ gluingThinSeamWidth C g} =
      (univ : Set Circle) ×ˢ
        {t : Ioo (-gluingDepth C g) (gluingDepth C g) | |t.1| ≤ gluingThinSeamWidth C g} := by
    ext p
    simp
  rw [heq]
  exact (isCompact_univ : IsCompact (univ : Set Circle)).prod hrad

theorem closedThinSeamCollar_isCompact
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsCompact (P.closedThinSeamCollar k) :=
  (signed_closed_thin_strip_isCompact P).image
    (continuous_subtype_val.comp (P.seamCylinderHomeomorph k).continuous)

theorem thinSeamCollar_subset_closedThinSeamCollar
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.thinSeamCollar k ⊆ P.closedThinSeamCollar k := by
  apply image_mono
  intro p hp
  exact (show |p.2.1| < gluingThinSeamWidth C g from hp).le

theorem closure_thinSeamCollar_subset_closedThinSeamCollar
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    closure (P.thinSeamCollar k) ⊆ P.closedThinSeamCollar k :=
  closure_minimal (P.thinSeamCollar_subset_closedThinSeamCollar k)
    (P.closedThinSeamCollar_isCompact k).isClosed

theorem closure_thinSeamCollar_isCompact
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    IsCompact (closure (P.thinSeamCollar k)) :=
  (P.closedThinSeamCollar_isCompact k).of_isClosed_subset isClosed_closure
    (P.closure_thinSeamCollar_subset_closedThinSeamCollar k)

theorem closure_thinSeamCollar_subset_original_collar
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    closure (P.thinSeamCollar k) ⊆ P.gluedMk '' P.seamNeighborhood k :=
  (P.closure_thinSeamCollar_subset_closedThinSeamCollar k).trans
    (P.closedThinSeamCollar_subset_original_collar k)

/-- Closed thin strips at distinct seams are disjoint in the actual native
carrier; no disjointness of the original outer collars is used. -/
theorem closedThinSeamCollar_disjoint
    (P : ExerciseGluingPreparation C g n genera X) {k l : Fin (n - 1)} (hkl : k ≠ l) :
    Disjoint (P.closedThinSeamCollar k) (P.closedThinSeamCollar l) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨p, hp, rfl⟩ ⟨q, hq, heq⟩
  let θ := Complex.arg (p.1 : ℂ)
  let ψ := Complex.arg (q.1 : ℂ)
  let a : GluingSeamAngularDomain C g θ :=
    (p.2, ⟨θ, by constructor <;> linarith [Real.pi_pos]⟩)
  let b : GluingSeamAngularDomain C g ψ :=
    (q.2, ⟨ψ, by constructor <;> linarith [Real.pi_pos]⟩)
  have ha : P.seamAngularPoint k θ a = (P.seamCylinderHomeomorph k p).1 := by
    change (P.seamCylinderHomeomorph k (Circle.exp (Complex.arg (p.1 : ℂ)), p.2)).1 = _
    rw [Circle.exp_arg]
  have hb : P.seamAngularPoint l ψ b = (P.seamCylinderHomeomorph l q).1 := by
    change (P.seamCylinderHomeomorph l (Circle.exp (Complex.arg (q.1 : ℂ)), q.2)).1 = _
    rw [Circle.exp_arg]
  exact P.seamAngularPoint_ne_distinct_of_abs_radial_le_thinWidth k l hkl θ ψ a b hp hq
    (ha.trans (heq.symm.trans hb.symm))

theorem closure_thinSeamCollar_disjoint
    (P : ExerciseGluingPreparation C g n genera X) {k l : Fin (n - 1)} (hkl : k ≠ l) :
    Disjoint (closure (P.thinSeamCollar k)) (closure (P.thinSeamCollar l)) :=
  (P.closedThinSeamCollar_disjoint hkl).mono
    (P.closure_thinSeamCollar_subset_closedThinSeamCollar k)
    (P.closure_thinSeamCollar_subset_closedThinSeamCollar l)

#print axioms closedThinSeamCollar_disjoint
#print axioms closure_thinSeamCollar_isCompact
#print axioms closure_thinSeamCollar_subset_original_collar
#print axioms closure_thinSeamCollar_disjoint
#print axioms seamAngularPoint_ne_distinct_of_abs_radial_le_thinWidth

end
end ExerciseGluingPreparation
end SystolicGrowth

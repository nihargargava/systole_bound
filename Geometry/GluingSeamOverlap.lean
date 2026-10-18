module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChartEvaluations

@[expose] public section

/-!
# Actual interior points on overlaps of different seams

The strict radial part of each actual collar avoids both closed inner disks
in the original surface metric. Thus a nonzero signed seam point is an
original component interior point. Saturation and the actual seam-index
test exclude signed radius zero on overlaps of distinct seam charts. No
disjointness of outer collars, smooth atlas, or glued metric is assumed.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Avoiding both actual closed inner disks gives an original interior
point, also at the endpoints where only one disk is deleted. -/
theorem mem_componentInteriorSet_of_radius_lt_dist
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (q : (X i).Carrier)
    (hl : gluingRadius C g < dist q (Quotient.mk'' (P.centers i).1))
    (hr : gluingRadius C g < dist q (Quotient.mk'' (P.centers i).2)) :
    q ∈ P.componentInteriorSet i := by
  let U : Set (X i).Carrier :=
    (closedBall (Quotient.mk'' (P.centers i).1) (gluingRadius C g))ᶜ ∩
      (closedBall (Quotient.mk'' (P.centers i).2) (gluingRadius C g))ᶜ
  have hU : IsOpen U :=
    Metric.isClosed_closedBall.isOpen_compl.inter Metric.isClosed_closedBall.isOpen_compl
  have hsub : U ⊆ (X i).puncturedComponentSet (P.centers i).1 (P.centers i).2
      (gluingRadius C g) i := by
    rintro a ⟨hal, har⟩ (ha | ha)
    · change a ∈ (if 0 < i.1 then (X i).orbitBall _ _ else ∅) at ha
      split_ifs at ha
      · apply hal
        apply ball_subset_closedBall
        simpa only [(X i).carrier_ball_eq_orbitBall] using ha
      · exact ha.elim
    · change a ∈ (if i.1 + 1 < n then (X i).orbitBall _ _ else ∅) at ha
      split_ifs at ha
      · apply har
        apply ball_subset_closedBall
        simpa only [(X i).carrier_ball_eq_orbitBall] using ha
      · exact ha.elim
  exact interior_maximal hsub hU ⟨not_le_of_gt hl, not_le_of_gt hr⟩

/-- Full-orbit separation implies separation of the actual surface centers. -/
theorem carrier_centers_outer_add_inner_le_dist
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    gluingEmbeddedRadius C g + gluingRadius C g ≤
      dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
        (Quotient.mk'' (P.centers i).2) := by
  rw [(X i).carrier_dist_eq_orbitDist, (X i).orbitDist_mk]
  obtain ⟨γ, hγ⟩ := (X i).exists_liftOrbitDist_eq_dist (P.centers i).1 (P.centers i).2
  rw [hγ]
  exact P.separated_outer_add_inner i γ

private theorem carrier_dist_polarPoint_center
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (o : ℍ) (u : Circle)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hR : ρ < gluingEmbeddedRadius C g) :
    dist (Quotient.mk'' (gluingPolarPoint o u ρ) : (X i).Carrier)
      (Quotient.mk'' o) = ρ := by
  rw [dist_comm]
  rw [(X i).carrier_dist_mk_center_eq_of_mem_closedBall o (gluingEmbeddedRadius C g)
    (P.twice_outer_lt_systole i)]
  · exact dist_gluingPolarPoint o u hρ
  · simpa only [mem_closedBall, dist_comm, dist_gluingPolarPoint o u hρ] using hR.le

/-- The strict outgoing half-annulus consists of actual original interior points. -/
theorem outgoing_polarPoint_mem_componentInteriorSet
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (u : Circle)
    {ρ : ℝ} (hr : gluingRadius C g < ρ) (hR : ρ < gluingEmbeddedRadius C g) :
    (Quotient.mk'' (gluingPolarPoint (P.centers i).2 u ρ) : (X i).Carrier) ∈
      P.componentInteriorSet i := by
  have hown := carrier_dist_polarPoint_center P i (P.centers i).2 u
    (P.radius_pos.le.trans hr.le) hR
  apply P.mem_componentInteriorSet_of_radius_lt_dist
  · have htri := dist_triangle (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
      (Quotient.mk'' (gluingPolarPoint (P.centers i).2 u ρ))
      (Quotient.mk'' (P.centers i).2)
    rw [hown] at htri
    have hcomm : dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
        (Quotient.mk'' (gluingPolarPoint (P.centers i).2 u ρ)) =
        dist (Quotient.mk'' (gluingPolarPoint (P.centers i).2 u ρ) : (X i).Carrier)
          (Quotient.mk'' (P.centers i).1) := dist_comm _ _
    rw [hcomm] at htri
    linarith [P.carrier_centers_outer_add_inner_le_dist i]
  · simpa only [hown] using hr

/-- The strict incoming half-annulus also avoids the other closed inner disk. -/
theorem incoming_polarPoint_mem_componentInteriorSet
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (u : Circle)
    {ρ : ℝ} (hr : gluingRadius C g < ρ) (hR : ρ < gluingEmbeddedRadius C g) :
    (Quotient.mk'' (gluingPolarPoint (P.centers i).1 u ρ) : (X i).Carrier) ∈
      P.componentInteriorSet i := by
  have hown := carrier_dist_polarPoint_center P i (P.centers i).1 u
    (P.radius_pos.le.trans hr.le) hR
  apply P.mem_componentInteriorSet_of_radius_lt_dist
  · simpa only [hown] using hr
  · have htri := dist_triangle (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
      (Quotient.mk'' (gluingPolarPoint (P.centers i).1 u ρ))
      (Quotient.mk'' (P.centers i).2)
    have hcomm : dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
        (Quotient.mk'' (gluingPolarPoint (P.centers i).1 u ρ)) = ρ :=
      (dist_comm _ _).trans hown
    rw [hcomm] at htri
    linarith [P.carrier_centers_outer_add_inner_le_dist i]

/-- Negative signed radius lies in the original outgoing component interior. -/
theorem seamAngularPoint_exists_outgoingInterior
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) (hp : p.1.1 < 0) :
    ∃ q : P.componentInteriorSet (gluingChainEdgeLeft k),
      P.seamAngularPoint k θ p =
        P.gluedMk (P.componentInteriorPoint (gluingChainEdgeLeft k) q) := by
  have hR : gluingRadius C g - p.1.1 < gluingEmbeddedRadius C g := by
    change gluingRadius C g - p.1.1 < gluingRadius C g + gluingDepth C g
    linarith [p.1.2.1]
  refine ⟨⟨Quotient.mk'' (gluingPolarPoint (P.centers (gluingChainEdgeLeft k)).2
    (Circle.exp p.2.1) (gluingRadius C g - p.1.1)),
    P.outgoing_polarPoint_mem_componentInteriorSet _ _ (by linarith) hR⟩, ?_⟩
  rw [P.seamAngularPoint_of_nonpos k θ p hp.le]
  apply congrArg P.gluedMk
  apply Sigma.ext rfl
  apply heq_of_eq
  apply Subtype.ext
  rfl

/-- Positive signed radius lies in the original incoming component interior,
with the prescribed reflected angular coordinate. -/
theorem seamAngularPoint_exists_incomingInterior
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) (hp : 0 < p.1.1) :
    ∃ q : P.componentInteriorSet (gluingChainEdgeRight k),
      P.seamAngularPoint k θ p =
        P.gluedMk (P.componentInteriorPoint (gluingChainEdgeRight k) q) := by
  have hR : gluingRadius C g + p.1.1 < gluingEmbeddedRadius C g := by
    change gluingRadius C g + p.1.1 < gluingRadius C g + gluingDepth C g
    linarith [p.1.2.2]
  refine ⟨⟨Quotient.mk'' (gluingPolarPoint (P.centers (gluingChainEdgeRight k)).1
    (Circle.exp p.2.1)⁻¹ (gluingRadius C g + p.1.1)),
    P.incoming_polarPoint_mem_componentInteriorSet _ _ (by linarith) hR⟩, ?_⟩
  rw [P.seamAngularPoint_of_nonneg k θ p hp.le]
  apply congrArg P.gluedMk
  apply Sigma.ext rfl
  apply heq_of_eq
  apply Subtype.ext
  rfl

private theorem seamAngularPoint_mem_seamNeighborhood_image
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) :
    P.seamAngularPoint k θ p ∈ P.gluedMk '' P.seamNeighborhood k :=
  (P.seamCylinderHomeomorph k (Circle.exp p.2.1, p.1)).2

/-- Actual points of distinct seam charts have nonzero signed radius in
both charts; this uses circle incidence, not disjointness of outer collars. -/
theorem seamAngularPoint_eq_distinct_nonzero
    (P : ExerciseGluingPreparation C g n genera X) (k l : Fin (n - 1))
    (hkl : k ≠ l) (θ ψ : ℝ) (p : GluingSeamAngularDomain C g θ)
    (q : GluingSeamAngularDomain C g ψ)
    (h : P.seamAngularPoint k θ p = P.seamAngularPoint l ψ q) :
    p.1.1 ≠ 0 ∧ q.1.1 ≠ 0 := by
  have hz (k l : Fin (n - 1)) (θ ψ : ℝ) (p : GluingSeamAngularDomain C g θ)
      (q : GluingSeamAngularDomain C g ψ)
      (h : P.seamAngularPoint k θ p = P.seamAngularPoint l ψ q)
      (hp : p.1.1 = 0) : k = l := by
    have hm := seamAngularPoint_mem_seamNeighborhood_image P l ψ q
    rw [← h, P.seamAngularPoint_of_zero k θ p hp] at hm
    change P.seamSource k _ ∈ P.gluedMk ⁻¹' (P.gluedMk '' P.seamNeighborhood l) at hm
    rw [P.preimage_gluedMk_image_seamNeighborhood l] at hm
    exact (P.seamSource_mem_seamNeighborhood_iff l k _).mp hm
  exact ⟨fun hp => hkl (hz k l θ ψ p q h hp),
    fun hq => hkl (hz l k ψ θ q p h.symm hq).symm⟩

/-- On the exact native overlap of two distinct seam charts, both the
input and output signed radial coordinates are nonzero. -/
theorem seamAngularComplexChart_distinct_transition_nonzero
    (P : ExerciseGluingPreparation C g n genera X) (k l : Fin (n - 1))
    (hkl : k ≠ l) (θ ψ : ℝ) {z : ℂ}
    (hz : z ∈ ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart l ψ)).source) :
    z.re ≠ 0 ∧
      (P.seamAngularComplexChart l ψ ((P.seamAngularComplexChart k θ).symm z)).re ≠ 0 := by
  change z ∈ (P.seamAngularComplexChart k θ).target ∧
    (P.seamAngularComplexChart k θ).symm z ∈
      (P.seamAngularComplexChart l ψ).source at hz
  have ht := hz.1
  rw [P.seamAngularComplexChart_target] at ht
  obtain ⟨p, rfl⟩ := ht
  have hs := hz.2
  rw [P.seamAngularComplexChart_symm_apply, P.seamAngularComplexChart_source] at hs
  obtain ⟨q, hq⟩ := hs
  have hn := P.seamAngularPoint_eq_distinct_nonzero k l hkl θ ψ p q hq.symm
  simpa only [P.seamAngularComplexChart_symm_apply, ← hq,
    P.seamAngularComplexChart_apply, gluingSeamAngularModel_re] using hn

/-- Every point in an overlap of distinct actual seam charts has an
original interior representative, so genuine interior charts can mediate it. -/
theorem seamAngularPoint_eq_distinct_exists_interior
    (P : ExerciseGluingPreparation C g n genera X) (k l : Fin (n - 1))
    (hkl : k ≠ l) (θ ψ : ℝ) (p : GluingSeamAngularDomain C g θ)
    (q : GluingSeamAngularDomain C g ψ)
    (h : P.seamAngularPoint k θ p = P.seamAngularPoint l ψ q) :
    ∃ (i : Fin n) (a : P.componentInteriorSet i),
      P.seamAngularPoint k θ p = P.gluedMk (P.componentInteriorPoint i a) := by
  have hp := (P.seamAngularPoint_eq_distinct_nonzero k l hkl θ ψ p q h).1
  rcases lt_or_gt_of_ne hp with hp | hp
  · obtain ⟨a, ha⟩ := P.seamAngularPoint_exists_outgoingInterior k θ p hp
    exact ⟨_, a, ha⟩
  · obtain ⟨a, ha⟩ := P.seamAngularPoint_exists_incomingInterior k θ p hp
    exact ⟨_, a, ha⟩

/-- The exact native distinct-seam overlap has an original interior
representative, with no auxiliary overlap domain. -/
theorem seamAngularComplexChart_distinct_overlap_exists_interior
    (P : ExerciseGluingPreparation C g n genera X) (k l : Fin (n - 1))
    (hkl : k ≠ l) (θ ψ : ℝ) {z : ℂ}
    (hz : z ∈ ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart l ψ)).source) :
    ∃ (i : Fin n) (a : P.componentInteriorSet i),
      (P.seamAngularComplexChart k θ).symm z =
        P.gluedMk (P.componentInteriorPoint i a) := by
  change z ∈ (P.seamAngularComplexChart k θ).target ∧
    (P.seamAngularComplexChart k θ).symm z ∈
      (P.seamAngularComplexChart l ψ).source at hz
  have ht := hz.1
  rw [P.seamAngularComplexChart_target] at ht
  obtain ⟨p, rfl⟩ := ht
  have hs := hz.2
  rw [P.seamAngularComplexChart_symm_apply, P.seamAngularComplexChart_source] at hs
  obtain ⟨q, hq⟩ := hs
  simpa only [P.seamAngularComplexChart_symm_apply] using
    P.seamAngularPoint_eq_distinct_exists_interior k l hkl θ ψ p q hq.symm

/-- A genuine original interior ball chart mediates each distinct-seam
overlap point, so transition factorization need not assume such a chart. -/
theorem seamAngularComplexChart_distinct_overlap_exists_interior_chart
    (P : ExerciseGluingPreparation C g n genera X) (k l : Fin (n - 1))
    (hkl : k ≠ l) (θ ψ : ℝ) {z : ℂ}
    (hz : z ∈ ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart l ψ)).source) :
    ∃ e : OpenPartialHomeomorph P.GluedCarrier ℂ,
      P.IsGluedInteriorComplexChart e ∧ (P.seamAngularComplexChart k θ).symm z ∈ e.source := by
  obtain ⟨i, a, ha⟩ :=
    P.seamAngularComplexChart_distinct_overlap_exists_interior k l hkl θ ψ hz
  obtain ⟨w, ρ, hρ, h4, hw, hq, hf⟩ := P.exists_gluedComponentInterior_ball_chart i a
  refine ⟨P.gluedInteriorComplexChart i w ρ hρ hq hf,
    ⟨i, w, ρ, hρ, h4, hq, hf, rfl⟩, ?_⟩
  rw [ha, P.gluedInteriorComplexChart_source]
  refine ⟨⟨w, by simpa using hρ⟩, ?_⟩
  simp only [hw]

#print axioms seamAngularPoint_exists_outgoingInterior
#print axioms seamAngularPoint_exists_incomingInterior
#print axioms seamAngularPoint_eq_distinct_nonzero
#print axioms seamAngularComplexChart_distinct_transition_nonzero
#print axioms seamAngularPoint_eq_distinct_exists_interior
#print axioms seamAngularComplexChart_distinct_overlap_exists_interior_chart

end SystolicGrowth.ExerciseGluingPreparation

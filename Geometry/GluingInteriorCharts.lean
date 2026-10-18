module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainTopology
public import Geometry.SurfaceOrbitLocalIsometry

@[expose] public section

/-!
# Actual quotient charts away from the seams

The seam set consists exactly of points participating in one of the concrete
chain identifications. Any open subset avoiding this set is saturated for
the actual quotient relation. Its quotient map is an open embedding, so
interior charts survive gluing without an assumed quotient-chart field.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- A genuine hyperbolic boundary circle is approached from its inner disk. -/
theorem hyperbolic_sphere_subset_closure_ball (o : ℍ) {r : ℝ} (hr : 0 < r) :
    Metric.sphere o r ⊆ closure (Metric.ball o r) := by
  intro z hz
  have hrad : dist o z = r := by simpa only [Metric.mem_sphere, dist_comm] using hz
  have hpair : Continuous (fun t : ℝ => (o, z, t)) := by fun_prop
  have hf : Continuous (fun t : ℝ => Vendored.RiemannDynamics.geodInterp o z t) :=
    Vendored.RiemannDynamics.continuous_geodInterp.comp hpair
  have hsub : Vendored.RiemannDynamics.geodInterp o z '' Ico (0 : ℝ) 1 ⊆
      Metric.ball o r := by
    rintro y ⟨t, ht, rfl⟩
    rw [Metric.mem_ball, dist_comm,
      Vendored.RiemannDynamics.dist_geodInterp_left o z ⟨ht.1, ht.2.le⟩, hrad]
    nlinarith [ht.2]
  apply closure_mono hsub
  apply image_closure_subset_closure_image hf
  refine ⟨1, ?_, Vendored.RiemannDynamics.geodInterp_one o z⟩
  rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
  norm_num

/-- The actual downstairs boundary also lies in the closure of its inner disk. -/
theorem punctureCircle_subset_closure_orbitBall {k : ℕ}
    (Y : ClosedHyperbolicSurface k) (o : ℍ) {r : ℝ} (hr : 0 < r) :
    Y.punctureCircle o r ⊆ closure (Y.orbitBall o r) := by
  exact (Set.image_mono (hyperbolic_sphere_subset_closure_ball o hr)).trans
    (image_closure_subset_closure_image continuous_quotient_mk')

/-- A circle whose open disk is genuinely deleted cannot lie in the interior
of the retained component, in the original surface topology. -/
theorem punctureCircle_not_mem_interior {k m : ℕ}
    (Y : ClosedHyperbolicSurface k) (left right o : ℍ) {r : ℝ}
    (hr : 0 < r) (i : Fin m)
    (hball : Y.orbitBall o r ⊆ Y.punctureDeletedSet left right r i)
    {q : Y.Carrier} (hq : q ∈ Y.punctureCircle o r) :
    q ∉ interior (Y.puncturedComponentSet left right r i) := by
  have hc := closure_mono hball (punctureCircle_subset_closure_orbitBall Y o hr hq)
  intro hi
  have hnot : q ∉ closure (Y.punctureDeletedSet left right r i) := by
    simpa only [ClosedHyperbolicSurface.puncturedComponentSet, interior_compl,
      Set.mem_compl_iff] using hi
  exact hnot hc

/-- Points participating in an actual incoming or outgoing identification. -/
def chainSeamSet (P : ExerciseGluingPreparation C g n genera X) : Set P.ChainPieces :=
  {a | ∃ b, P.chainRelation a b ∨ P.chainRelation b a}

/-- The actual finite seam set is closed, as the two projections of the
compact actual seam-pair relation. -/
theorem chainSeamSet_isClosed (P : ExerciseGluingPreparation C g n genera X) :
    IsClosed P.chainSeamSet := by
  let R : Set (P.ChainPieces × P.ChainPieces) := {p | P.chainRelation p.1 p.2}
  have heq : P.chainSeamSet = Prod.fst '' R ∪ Prod.snd '' R := by
    ext a
    constructor
    · rintro ⟨b, hab | hba⟩
      · exact Or.inl ⟨(a, b), hab, rfl⟩
      · exact Or.inr ⟨(b, a), hba, rfl⟩
    · rintro (⟨⟨a', b⟩, hab, rfl⟩ | ⟨⟨b, a'⟩, hba, rfl⟩)
      · exact ⟨b, Or.inl hab⟩
      · exact ⟨b, Or.inr hba⟩
  rw [heq]
  have hR : IsCompact R := P.chainRelation_isClosed.isCompact
  exact ((hR.image continuous_fst).union (hR.image continuous_snd)).isClosed

/-- Away from the actual seams, every quotient fiber is a singleton. -/
theorem gluedMk_eq_of_not_mem_chainSeamSet
    (P : ExerciseGluingPreparation C g n genera X) {a b : P.ChainPieces}
    (ha : a ∉ P.chainSeamSet) (h : P.gluedMk a = P.gluedMk b) : a = b := by
  rcases (P.gluedMk_eq_iff a b).mp h with hab | hab | hba
  · exact hab
  · exact (ha ⟨b, Or.inl hab⟩).elim
  · exact (ha ⟨b, Or.inr hba⟩).elim

/-- Every actual seam-free subset is saturated for the glued quotient. -/
theorem preimage_gluedMk_image_of_disjoint_seams
    (P : ExerciseGluingPreparation C g n genera X) {s : Set P.ChainPieces}
    (hs : s ⊆ P.chainSeamSetᶜ) : P.gluedMk ⁻¹' (P.gluedMk '' s) = s := by
  ext a
  constructor
  · rintro ⟨b, hb, hba⟩
    have h := P.gluedMk_eq_of_not_mem_chainSeamSet (hs hb) hba
    exact h ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- Images of actual seam-free open sets are open in the glued topology. -/
theorem isOpen_gluedMk_image_of_disjoint_seams
    (P : ExerciseGluingPreparation C g n genera X) {s : Set P.ChainPieces}
    (hs : IsOpen s) (hseam : s ⊆ P.chainSeamSetᶜ) : IsOpen (P.gluedMk '' s) := by
  apply (isQuotientMap_quotient_mk'.isOpen_preimage).mp
  change IsOpen (P.gluedMk ⁻¹' (P.gluedMk '' s))
  rw [P.preimage_gluedMk_image_of_disjoint_seams hseam]
  exact hs

/-- Actual open charts avoiding the seams embed openly into the quotient. -/
theorem gluedMk_restrict_isOpenEmbedding
    (P : ExerciseGluingPreparation C g n genera X) {s : Set P.ChainPieces}
    (hs : IsOpen s) (hseam : s ⊆ P.chainSeamSetᶜ) :
    Topology.IsOpenEmbedding (fun a : s => P.gluedMk a.1) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact P.gluedMk_continuous.comp continuous_subtype_val
  · intro a b hab
    exact Subtype.ext (P.gluedMk_eq_of_not_mem_chainSeamSet (hseam a.2) hab)
  · intro u hu
    have hv : IsOpen (Subtype.val '' u : Set P.ChainPieces) :=
      hs.isOpenMap_subtype_val u hu
    have hsub : (Subtype.val '' u : Set P.ChainPieces) ⊆ P.chainSeamSetᶜ := by
      rintro a ⟨b, _, rfl⟩
      exact hseam b.2
    simpa only [← Set.image_comp, Function.comp_def] using
      P.isOpen_gluedMk_image_of_disjoint_seams hv hsub

/-- The whole actual seam complement embeds openly into the glued carrier. -/
theorem gluedInterior_isOpenEmbedding (P : ExerciseGluingPreparation C g n genera X) :
    Topology.IsOpenEmbedding (fun a : ↥(P.chainSeamSetᶜ) => P.gluedMk a.1) :=
  P.gluedMk_restrict_isOpenEmbedding P.chainSeamSet_isClosed.isOpen_compl (subset_refl _)

/-- The interior of a retained piece is taken in its original surface carrier. -/
def componentInteriorSet (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Set (X i).Carrier :=
  interior ((X i).puncturedComponentSet (P.centers i).1 (P.centers i).2
    (gluingRadius C g) i)

/-- The actual inclusion of a component interior in the disjoint union. -/
def componentInteriorPoint (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.componentInteriorSet i) : P.ChainPieces :=
  ⟨i, ⟨q.1, interior_subset q.2⟩⟩

theorem componentInteriorPoint_isOpenEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Topology.IsOpenEmbedding (P.componentInteriorPoint i) := by
  have hinc := Topology.IsOpenEmbedding.inclusion
    (interior_subset : P.componentInteriorSet i ⊆
      (X i).puncturedComponentSet (P.centers i).1 (P.centers i).2 (gluingRadius C g) i)
    (isOpen_interior.preimage continuous_subtype_val)
  exact Topology.IsOpenEmbedding.sigmaMk.comp hinc

/-- Only circles of genuinely deleted disks participate in the chain relation,
so every original component interior avoids every actual seam. -/
theorem componentInteriorPoint_not_mem_chainSeamSet
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.componentInteriorSet i) : P.componentInteriorPoint i q ∉ P.chainSeamSet := by
  rintro ⟨b, hrel | hrel⟩
  · have hi : i.1 + 1 < n := by
      obtain ⟨k, z, ha, _⟩ := hrel
      have hv := congrArg (fun a : P.ChainPieces => a.1.1) ha
      change i.1 = k.1 at hv
      have := k.2
      omega
    obtain ⟨z, hz⟩ := P.chainRelation_source_mem_rightCircle hrel
    have hq : q.1 ∈ (X i).punctureCircle (P.centers i).2 (gluingRadius C g) := by
      have hval := congrArg Subtype.val hz
      exact ⟨z.1, z.2, hval⟩
    have hball : (X i).orbitBall (P.centers i).2 (gluingRadius C g) ⊆
        (X i).punctureDeletedSet (P.centers i).1 (P.centers i).2 (gluingRadius C g) i := by
      intro a ha
      simp only [ClosedHyperbolicSurface.punctureDeletedSet, if_pos hi, Set.mem_union]
      exact Or.inr ha
    exact punctureCircle_not_mem_interior (X i) _ _ _ P.radius_pos i hball hq q.2
  · have hi : 0 < i.1 := by
      obtain ⟨k, z, _, ha⟩ := hrel
      have hv := congrArg (fun a : P.ChainPieces => a.1.1) ha
      change i.1 = k.1 + 1 at hv
      omega
    obtain ⟨z, hz⟩ := P.chainRelation_target_mem_leftCircle hrel
    have hq : q.1 ∈ (X i).punctureCircle (P.centers i).1 (gluingRadius C g) := by
      have hval := congrArg Subtype.val hz
      exact ⟨z.1, z.2, hval⟩
    have hball : (X i).orbitBall (P.centers i).1 (gluingRadius C g) ⊆
        (X i).punctureDeletedSet (P.centers i).1 (P.centers i).2 (gluingRadius C g) i := by
      intro a ha
      simp only [ClosedHyperbolicSurface.punctureDeletedSet, if_pos hi, Set.mem_union]
      exact Or.inl ha
    exact punctureCircle_not_mem_interior (X i) _ _ _ P.radius_pos i hball hq q.2

/-- Original interior charts genuinely survive in the prescribed glued carrier. -/
theorem gluedComponentInterior_isOpenEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Topology.IsOpenEmbedding
      (fun q : P.componentInteriorSet i => P.gluedMk (P.componentInteriorPoint i q)) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact P.gluedMk_continuous.comp (P.componentInteriorPoint_isOpenEmbedding i).continuous
  · intro a b hab
    exact (P.componentInteriorPoint_isOpenEmbedding i).injective
      (P.gluedMk_eq_of_not_mem_chainSeamSet
        (P.componentInteriorPoint_not_mem_chainSeamSet i a) hab)
  · intro s hs
    have hopen := (P.componentInteriorPoint_isOpenEmbedding i).isOpenMap s hs
    have hsub : P.componentInteriorPoint i '' s ⊆ P.chainSeamSetᶜ := by
      rintro a ⟨q, _, rfl⟩
      exact P.componentInteriorPoint_not_mem_chainSeamSet i q
    simpa only [← Set.image_comp, Function.comp_def] using
      P.isOpen_gluedMk_image_of_disjoint_seams hopen hsub

/-- Every genuine component-interior point has an actual hyperbolic ball
chart in the glued carrier. The radius also satisfies the stronger bound
needed for upstairs distances to agree with the original component metric. -/
theorem exists_gluedComponentInterior_ball_chart
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (q : P.componentInteriorSet i) :
    ∃ (z : ℍ) (ρ : ℝ), 0 < ρ ∧ 4 * ρ < (X i).systole ∧
      (Quotient.mk'' z : (X i).Carrier) = q.1 ∧
      ∃ hq : ∀ w : Metric.ball z ρ,
          (Quotient.mk'' w.1 : (X i).Carrier) ∈ P.componentInteriorSet i,
        Topology.IsOpenEmbedding (fun w : Metric.ball z ρ =>
          P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq w⟩)) := by
  obtain ⟨z, hz⟩ := Quotient.mk_surjective q.1
  have hopen : IsOpen ((fun w : ℍ => (Quotient.mk'' w : (X i).Carrier)) ⁻¹'
      P.componentInteriorSet i) := isOpen_interior.preimage continuous_quotient_mk'
  have hzin : (Quotient.mk'' z : (X i).Carrier) ∈ P.componentInteriorSet i := by
    simpa only [hz] using q.2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen z hzin
  let ρ := min (ε / 2) (targetSystole C g / 8)
  have hρ : 0 < ρ := lt_min (by positivity) (div_pos P.target_pos (by norm_num))
  have hρε : ρ < ε := (min_le_left _ _).trans_lt (by linarith)
  have h4 : 4 * ρ < (X i).systole := by
    have hbudget : ρ ≤ targetSystole C g / 8 := min_le_right _ _
    have hsys := P.component_systole i
    linarith [P.target_pos]
  have hq : ∀ w : Metric.ball z ρ,
      (Quotient.mk'' w.1 : (X i).Carrier) ∈ P.componentInteriorSet i := by
    intro w
    exact hball (Metric.ball_subset_ball hρε.le w.2)
  refine ⟨z, ρ, hρ, h4, hz, hq, ?_⟩
  have hproj := (X i).quotientBall_isOpenEmbedding z ρ (by linarith)
  have hrestricted : Topology.IsOpenEmbedding
      (fun w : Metric.ball z ρ =>
        (⟨Quotient.mk'' w.1, hq w⟩ : P.componentInteriorSet i)) :=
    Topology.IsOpenEmbedding.of_isEmbedding_isOpenMap
      (hproj.isEmbedding.codRestrict _ hq) (hproj.isOpenMap.codRestrict hq)
  exact (P.gluedComponentInterior_isOpenEmbedding i).comp hrestricted

#print axioms gluedMk_eq_of_not_mem_chainSeamSet
#print axioms gluedMk_restrict_isOpenEmbedding
#print axioms gluedInterior_isOpenEmbedding
#print axioms gluedComponentInterior_isOpenEmbedding
#print axioms exists_gluedComponentInterior_ball_chart

end SystolicGrowth.ExerciseGluingPreparation

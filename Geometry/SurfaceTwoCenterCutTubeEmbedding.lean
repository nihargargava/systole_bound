module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterCutNeighborhood

@[expose] public section

/-!
# The actual two-center cut tube descends to the surface

The disjoint-translate estimate for the compact lifted cut is shrunk below the
actual puncture radius. The restricted orbit projection is then an open
embedding, and its image avoids the two actual deleted centers. This uses the
native quotient carrier and the literal lifted cut; no abstract collar or
regular-neighborhood data is introduced.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane unitInterval

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Shrink the uniformly separated tube below the actual puncture radius. -/
theorem exists_componentTwoCenterLiftedCutTube_radius
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ ε : ℝ, 0 < ε ∧ ε < gluingRadius C g ∧
      ∀ γ : (X i).deckGroup, γ ≠ 1 →
        Disjoint ((fun z : ℍ => γ • z) '' P.componentTwoCenterLiftedCutTube i ε)
          (P.componentTwoCenterLiftedCutTube i ε) := by
  obtain ⟨ε₀, hε₀, hdisj⟩ := P.exists_componentTwoCenterLiftedCutTube_disjoint_translates i
  let ε := min ε₀ (gluingRadius C g / 2)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hε₀ (by linarith [P.radius_pos])
  have hεradius : ε < gluingRadius C g := by
    dsimp [ε]
    exact (min_le_right _ _).trans_lt (by linarith [P.radius_pos])
  have htube : P.componentTwoCenterLiftedCutTube i ε ⊆
      P.componentTwoCenterLiftedCutTube i ε₀ := by
    intro z hz
    change Metric.infDist z (P.componentTwoCenterLiftedCutSet i) < ε at hz
    change Metric.infDist z (P.componentTwoCenterLiftedCutSet i) < ε₀
    exact lt_of_lt_of_le hz (min_le_left _ _)
  refine ⟨ε, hε, hεradius, ?_⟩
  intro γ hγ
  exact (hdisj γ hγ).mono (Set.image_mono htube) htube

/-- The actual lifted cut lies in every positive-radius cut tube. -/
theorem componentTwoCenterLiftedCutSet_subset_tube
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {ε : ℝ} (hε : 0 < ε) :
    P.componentTwoCenterLiftedCutSet i ⊆ P.componentTwoCenterLiftedCutTube i ε := by
  intro z hz
  change Metric.infDist z (P.componentTwoCenterLiftedCutSet i) < ε
  rw [Metric.infDist_zero_of_mem hz]
  exact hε

/-- The literal lift of the cut stays at least one deleted-disk radius from
every translate of the left puncture center. -/
theorem componentTwoCenterLiftedCutPoint_dist_ge_radius_left
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (t : I)
    (γ : (X i).deckGroup) :
    gluingRadius C g ≤ dist (P.componentTwoCenterLiftedCutPoint i t)
      (γ • (P.centers i).1) := by
  have hcut : gluingRadius C g ≤ dist (P.componentTwoCenterCutPoint i t)
      (Quotient.mk'' (P.centers i).1 : (X i).Carrier) := by
    rw [P.componentTwoCenterCutPoint_dist_left i t]
    nlinarith [P.carrier_centers_outer_add_inner_le_dist i,
      P.radius_lt_embeddedRadius, t.2.1]
  have hcut' : gluingRadius C g ≤ dist
      (Quotient.mk'' (P.componentTwoCenterLiftedCutPoint i t) : (X i).Carrier)
      (Quotient.mk'' (P.centers i).1 : (X i).Carrier) := by
    simpa only [← P.componentTwoCenterLiftedCutPoint_project i t] using hcut
  have hquot : gluingRadius C g ≤
      (X i).liftOrbitDist (P.componentTwoCenterLiftedCutPoint i t) (P.centers i).1 := by
    simpa only [(X i).carrier_dist_eq_orbitDist, (X i).orbitDist_mk] using hcut'
  exact hquot.trans ((X i).liftOrbitDist_le
    (P.componentTwoCenterLiftedCutPoint i t) (P.centers i).1 γ)

/-- The same lower bound holds for every translate of the right center. -/
theorem componentTwoCenterLiftedCutPoint_dist_ge_radius_right
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (t : I)
    (γ : (X i).deckGroup) :
    gluingRadius C g ≤ dist (P.componentTwoCenterLiftedCutPoint i t)
      (γ • (P.centers i).2) := by
  have hcut : gluingRadius C g ≤ dist (P.componentTwoCenterCutPoint i t)
      (Quotient.mk'' (P.centers i).2 : (X i).Carrier) := by
    rw [P.componentTwoCenterCutPoint_dist_right i t]
    nlinarith [P.carrier_centers_outer_add_inner_le_dist i,
      P.radius_lt_embeddedRadius, t.2.2]
  have hcut' : gluingRadius C g ≤ dist
      (Quotient.mk'' (P.componentTwoCenterLiftedCutPoint i t) : (X i).Carrier)
      (Quotient.mk'' (P.centers i).2 : (X i).Carrier) := by
    simpa only [← P.componentTwoCenterLiftedCutPoint_project i t] using hcut
  have hquot : gluingRadius C g ≤
      (X i).liftOrbitDist (P.componentTwoCenterLiftedCutPoint i t) (P.centers i).2 := by
    simpa only [(X i).carrier_dist_eq_orbitDist, (X i).orbitDist_mk] using hcut'
  exact hquot.trans ((X i).liftOrbitDist_le
    (P.componentTwoCenterLiftedCutPoint i t) (P.centers i).2 γ)

private theorem componentTwoCenterLiftedCutTube_projection_ne_of_separated
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ)
    (center : ℍ)
    (hsep : ∀ γ : (X i).deckGroup, ∀ x ∈ P.componentTwoCenterLiftedCutSet i,
      gluingRadius C g ≤ dist x (γ • center))
    (hε : ε < gluingRadius C g)
    (z : P.componentTwoCenterLiftedCutTube i ε) :
    (Quotient.mk'' z.1 : (X i).Carrier) ≠ Quotient.mk'' center := by
  intro hz
  have hrel : MulAction.orbitRel (X i).deckGroup ℍ z.1 center := Quotient.exact hz
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
  obtain ⟨x, hx, hzx⟩ :=
    (Metric.infDist_lt_iff (P.componentTwoCenterLiftedCutSet_nonempty i)).mp z.2
  rcases hx with ⟨t, rfl⟩
  have hnear : dist (P.componentTwoCenterLiftedCutPoint i t) (γ • center) < ε := by
    calc
      dist (P.componentTwoCenterLiftedCutPoint i t) (γ • center) =
          dist (γ • center) (P.componentTwoCenterLiftedCutPoint i t) := dist_comm _ _
      _ = dist z.1 (P.componentTwoCenterLiftedCutPoint i t) := by rw [← hγ]
      _ < ε := hzx
  exact (not_lt_of_ge (hsep γ _ ⟨t, rfl⟩)) (hnear.trans hε)

/-- Actual quotient projection, restricted to the open lifted tube. -/
def componentTwoCenterLiftedCutTubeProjection
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ) :
    P.componentTwoCenterLiftedCutTube i ε → (X i).Carrier :=
  fun z => (Quotient.mk'' z.1 : (X i).Carrier)

/-- The restricted projection is literally the original quotient map on representatives. -/
@[simp]
theorem componentTwoCenterLiftedCutTubeProjection_apply
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ)
    (z : P.componentTwoCenterLiftedCutTube i ε) :
    P.componentTwoCenterLiftedCutTubeProjection i ε z = Quotient.mk'' z.1 := rfl

/-- With the separated radius, quotient projection embeds the actual open tube. -/
theorem componentTwoCenterLiftedCutTubeProjection_isOpenEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ)
    (hdisj : ∀ γ : (X i).deckGroup, γ ≠ 1 →
      Disjoint ((fun z : ℍ => γ • z) '' P.componentTwoCenterLiftedCutTube i ε)
        (P.componentTwoCenterLiftedCutTube i ε)) :
    Topology.IsOpenEmbedding (P.componentTwoCenterLiftedCutTubeProjection i ε) := by
  have hU : IsOpen (P.componentTwoCenterLiftedCutTube i ε) := by
    change IsOpen ((fun z : ℍ => Metric.infDist z (P.componentTwoCenterLiftedCutSet i)) ⁻¹'
      Set.Iio ε)
    exact isOpen_Iio.preimage (Metric.continuous_infDist_pt _)
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_quotient_mk'.comp continuous_subtype_val
  · intro z w hzw
    have hrel : MulAction.orbitRel (X i).deckGroup ℍ z.1 w.1 := by
      apply Quotient.exact
      simpa only [componentTwoCenterLiftedCutTubeProjection_apply] using hzw
    obtain ⟨γ, hact⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
    by_cases hγ : γ = 1
    · subst γ
      apply Subtype.ext
      simpa using hact.symm
    · exfalso
      exact (Set.disjoint_left.mp (hdisj γ hγ))
        ⟨w.1, w.2, hact⟩ z.2
  · exact isOpenMap_quotient_mk'_mul.comp hU.isOpenMap_subtype_val

/-- Every point of the actual tube projects away from the left deleted center. -/
theorem componentTwoCenterLiftedCutTubeProjection_ne_left
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ)
    (hε : ε < gluingRadius C g)
    (z : P.componentTwoCenterLiftedCutTube i ε) :
    P.componentTwoCenterLiftedCutTubeProjection i ε z ≠
      Quotient.mk'' (P.centers i).1 := by
  have hbase := P.componentTwoCenterLiftedCutTube_projection_ne_of_separated
    i ε (P.centers i).1
    (fun γ x hx => by
      rcases hx with ⟨t, rfl⟩
      exact P.componentTwoCenterLiftedCutPoint_dist_ge_radius_left i t γ) hε z
  simpa only [componentTwoCenterLiftedCutTubeProjection_apply] using hbase

/-- Every point of the actual tube projects away from the right deleted center. -/
theorem componentTwoCenterLiftedCutTubeProjection_ne_right
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ)
    (hε : ε < gluingRadius C g)
    (z : P.componentTwoCenterLiftedCutTube i ε) :
    P.componentTwoCenterLiftedCutTubeProjection i ε z ≠
      Quotient.mk'' (P.centers i).2 := by
  have hbase := P.componentTwoCenterLiftedCutTube_projection_ne_of_separated
    i ε (P.centers i).2
    (fun γ x hx => by
      rcases hx with ⟨t, rfl⟩
      exact P.componentTwoCenterLiftedCutPoint_dist_ge_radius_right i t γ) hε z
  simpa only [componentTwoCenterLiftedCutTubeProjection_apply] using hbase

theorem componentTwoCenterLiftedCutTubeProjection_mem_centerPuncturedSet
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ)
    (hε : ε < gluingRadius C g)
    (z : P.componentTwoCenterLiftedCutTube i ε) :
    P.componentTwoCenterLiftedCutTubeProjection i ε z ∈ P.componentCenterPuncturedSet i := by
  change ∀ b : Bool, (if b then 0 < i.1 else i.1 + 1 < n) →
    P.componentTwoCenterLiftedCutTubeProjection i ε z ≠
      Quotient.mk'' (if b then (P.centers i).1 else (P.centers i).2)
  intro b hb
  cases b
  · exact P.componentTwoCenterLiftedCutTubeProjection_ne_right i ε hε z
  · exact P.componentTwoCenterLiftedCutTubeProjection_ne_left i ε hε z

/-- The same literal representative map, now landing in the actual carrier
with the active puncture centers deleted. -/
def componentTwoCenterLiftedCutTubePuncturedProjection
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ)
    (hε : ε < gluingRadius C g) :
    P.componentTwoCenterLiftedCutTube i ε → P.CenterPuncturedChainComponent i :=
  fun z => ⟨P.componentTwoCenterLiftedCutTubeProjection i ε z,
    P.componentTwoCenterLiftedCutTubeProjection_mem_centerPuncturedSet i ε hε z⟩

/-- The quotient projection also embeds openly into the genuine center-punctured
component, not merely into the unpunctured carrier. -/
theorem componentTwoCenterLiftedCutTubePuncturedProjection_isOpenEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ)
    (hε : ε < gluingRadius C g)
    (hdisj : ∀ γ : (X i).deckGroup, γ ≠ 1 →
      Disjoint ((fun z : ℍ => γ • z) '' P.componentTwoCenterLiftedCutTube i ε)
        (P.componentTwoCenterLiftedCutTube i ε)) :
    Topology.IsOpenEmbedding (P.componentTwoCenterLiftedCutTubePuncturedProjection i ε hε) := by
  let hproj := P.componentTwoCenterLiftedCutTubeProjection_isOpenEmbedding i ε hdisj
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · apply Continuous.subtype_mk
    exact hproj.continuous
  · intro z w hzw
    exact hproj.injective (congrArg Subtype.val hzw)
  · intro v hv
    have himage : IsOpen
        (P.componentTwoCenterLiftedCutTubeProjection i ε '' v : Set (X i).Carrier) :=
      hproj.isOpenMap v hv
    have hpre : IsOpen
        ((Subtype.val : P.CenterPuncturedChainComponent i → (X i).Carrier) ⁻¹'
          (P.componentTwoCenterLiftedCutTubeProjection i ε '' v)) :=
      himage.preimage continuous_subtype_val
    have hset :
        (P.componentTwoCenterLiftedCutTubePuncturedProjection i ε hε '' v :
          Set (P.CenterPuncturedChainComponent i)) =
        ((Subtype.val : P.CenterPuncturedChainComponent i → (X i).Carrier) ⁻¹'
          (P.componentTwoCenterLiftedCutTubeProjection i ε '' v)) := by
      ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, hqz⟩
        refine ⟨z, hz, ?_⟩
        apply Subtype.ext
        exact hqz
    rw [hset]
    exact hpre

/-- Each actual point of the cut is represented in the tube by its prescribed lift. -/
theorem componentTwoCenterCutPoint_mem_liftedCutTubeProjection_range
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ)
    (hε : 0 < ε) (t : I) :
    P.componentTwoCenterCutPoint i t ∈
      Set.range (P.componentTwoCenterLiftedCutTubeProjection i ε) := by
  refine ⟨⟨P.componentTwoCenterLiftedCutPoint i t, ?_⟩, ?_⟩
  · exact P.componentTwoCenterLiftedCutSet_subset_tube i hε ⟨t, rfl⟩
  · simp

/-- The actual cut likewise lands in the punctured tube image. -/
theorem componentTwoCenterCutPoint_mem_puncturedLiftedCutTubeProjection_range
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (ε : ℝ)
    (hε : 0 < ε) (hεradius : ε < gluingRadius C g) (t : I) :
    (⟨P.componentTwoCenterCutPoint i t,
      P.componentRetained_subset_centerPunctured i
        (P.componentTwoCenterCutPoint_mem_retained i t)⟩ :
      P.CenterPuncturedChainComponent i) ∈
        Set.range (P.componentTwoCenterLiftedCutTubePuncturedProjection i ε hεradius) := by
  refine ⟨⟨P.componentTwoCenterLiftedCutPoint i t, ?_⟩, ?_⟩
  · exact P.componentTwoCenterLiftedCutSet_subset_tube i hε ⟨t, rfl⟩
  · apply Subtype.ext
    change P.componentTwoCenterLiftedCutTubeProjection i ε
      ⟨P.componentTwoCenterLiftedCutPoint i t, _⟩ = P.componentTwoCenterCutPoint i t
    simp

#print axioms componentTwoCenterLiftedCutTubeProjection_isOpenEmbedding
#print axioms componentTwoCenterLiftedCutTubePuncturedProjection_isOpenEmbedding

end

end SystolicGrowth.ExerciseGluingPreparation

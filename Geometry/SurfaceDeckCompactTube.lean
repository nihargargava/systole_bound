module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceDeckCovering
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-!
# Uniform deck separation around an actual compact lift

Proper discontinuity makes only finitely many translates approach a compact
set. If none of the nonidentity translates intersects the set, a positive
metric neighborhood is still disjoint from every such translate. This is
used for the full minimizing center segment, not only its truncated cut.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth.ClosedHyperbolicSurface

noncomputable section

variable {g : ℕ} (X : ClosedHyperbolicSurface g)

private theorem compact_translate_distance_pos (K : Set ℍ) (hK : IsCompact K)
    (γ : X.deckGroup) (hdisj : Disjoint K ((fun z : ℍ => γ • z) '' K)) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ K, ∀ y ∈ K, d ≤ dist x (γ • y) := by
  have hγK : IsCompact ((fun z : ℍ => γ • z) '' K) :=
    hK.image (isometry_smul ℍ γ).continuous
  obtain ⟨r, hr, hdist⟩ := Metric.exists_pos_forall_lt_edist hK hγK.isClosed hdisj
  refine ⟨r, hr, ?_⟩
  intro x hx y hy
  have h : (r : ENNReal) < ENNReal.ofReal (dist x (γ • y)) := by
    simpa only [edist_dist] using hdist x hx (γ • y) (Set.mem_image_of_mem _ hy)
  rw [ENNReal.coe_nnreal_eq r] at h
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp h).1.le

private theorem finite_translate_distance_pos (K : Set ℍ) (F : Finset X.deckGroup)
    (hsep : ∀ γ ∈ F, γ ≠ 1 →
      ∃ d : ℝ, 0 < d ∧ ∀ x ∈ K, ∀ y ∈ K, d ≤ dist x (γ • y)) :
    ∃ d : ℝ, 0 < d ∧ ∀ γ ∈ F, γ ≠ 1 →
      ∀ x ∈ K, ∀ y ∈ K, d ≤ dist x (γ • y) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert a F ha ih =>
    obtain ⟨d, hd, hF⟩ := ih (fun γ hγ => hsep γ (Finset.mem_insert_of_mem hγ))
    by_cases haone : a = 1
    · refine ⟨d, hd, ?_⟩
      intro γ hγ hγone x hx y hy
      rcases Finset.mem_insert.mp hγ with rfl | hγF
      · exact (hγone haone).elim
      · exact hF γ hγF hγone x hx y hy
    · obtain ⟨e, he, hae⟩ := hsep a (Finset.mem_insert_self a F) haone
      refine ⟨min d e, lt_min hd he, ?_⟩
      intro γ hγ hγone x hx y hy
      rcases Finset.mem_insert.mp hγ with rfl | hγF
      · exact (min_le_right _ _).trans (hae x hx y hy)
      · exact (min_le_left _ _).trans (hF γ hγF hγone x hx y hy)

/-- A compact injective lift has a positive uniform distance from all its
nonidentity deck translates. -/
theorem exists_compact_deck_translate_separation (K : Set ℍ) (hK : IsCompact K)
    (hKne : K.Nonempty)
    (hdisj : ∀ γ : X.deckGroup, γ ≠ 1 →
      Disjoint K ((fun z : ℍ => γ • z) '' K)) :
    ∃ d : ℝ, 0 < d ∧ ∀ γ : X.deckGroup, γ ≠ 1 →
      ∀ x ∈ K, ∀ y ∈ K, d ≤ dist x (γ • y) := by
  classical
  obtain ⟨c, hc⟩ := hKne
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall c
  let L := Metric.closedBall c (R + 1)
  have hL : IsCompact L := isCompact_closedBall c (R + 1)
  let FSet : Set X.deckGroup := {γ | ((fun z : ℍ => γ • z) '' K ∩ L).Nonempty}
  have hFSet : FSet.Finite :=
    finite_disjoint_inter_image (Γ := X.deckGroup) (K := K) (L := L) hK hL
  let F : Finset X.deckGroup := hFSet.toFinset
  have hnear : ∀ γ : X.deckGroup, γ ∉ F →
      ∀ x ∈ K, ∀ y ∈ K, 1 ≤ dist x (γ • y) := by
    intro γ hγF x hx y hy
    by_contra hnot
    have hlt : dist x (γ • y) < 1 := lt_of_not_ge hnot
    have hyL : γ • y ∈ L := Metric.mem_closedBall.mpr <| by
      calc
        dist (γ • y) c = dist c (γ • y) := dist_comm _ _
        _ ≤ dist c x + dist x (γ • y) := dist_triangle _ _ _
        _ ≤ R + 1 := add_le_add (by simpa [dist_comm] using hKR hx) hlt.le
    have hγFSet : γ ∈ FSet := ⟨γ • y, ⟨y, hy, rfl⟩, hyL⟩
    exact hγF (hFSet.mem_toFinset.mpr hγFSet)
  obtain ⟨d, hd, hFsep⟩ := X.finite_translate_distance_pos K F
    (fun γ _ hγ => X.compact_translate_distance_pos K hK γ (hdisj γ hγ))
  refine ⟨min d 1, lt_min hd zero_lt_one, ?_⟩
  intro γ hγ x hx y hy
  by_cases hγF : γ ∈ F
  · exact (min_le_left _ _).trans (hFsep γ hγF hγ x hx y hy)
  · exact (min_le_right _ _).trans (hnear γ hγF x hx y hy)

/-- The positive metric tube around a compact lift also has disjoint
nonidentity deck translates. -/
theorem exists_compact_deck_tube_disjoint_translates (K : Set ℍ) (hK : IsCompact K)
    (hKne : K.Nonempty)
    (hdisj : ∀ γ : X.deckGroup, γ ≠ 1 →
      Disjoint K ((fun z : ℍ => γ • z) '' K)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ γ : X.deckGroup, γ ≠ 1 →
      Disjoint ((fun z : ℍ => γ • z) '' {z | Metric.infDist z K < ε})
        {z | Metric.infDist z K < ε} := by
  obtain ⟨d, hd, hsep⟩ := X.exists_compact_deck_translate_separation K hK hKne hdisj
  refine ⟨d / 2, by linarith, ?_⟩
  intro γ hγ
  apply Set.disjoint_left.mpr
  rintro z ⟨w, hwTube, rfl⟩ hzTube
  obtain ⟨x, hx, hzx⟩ := (Metric.infDist_lt_iff hKne).mp hzTube
  obtain ⟨y, hy, hwy⟩ := (Metric.infDist_lt_iff hKne).mp hwTube
  have hnear : dist x (γ • y) < d := by
    calc
      dist x (γ • y) ≤ dist x (γ • w) + dist (γ • w) (γ • y) := dist_triangle _ _ _
      _ < d / 2 + d / 2 := add_lt_add (by simpa [dist_comm] using hzx)
        (by simpa [dist_smul] using hwy)
      _ = d := by ring
  exact (not_lt_of_ge (hsep γ hγ x hx y hy)) hnear

/-- On a separated open set the literal quotient projection is an open embedding. -/
theorem orbitProjection_restrict_isOpenEmbedding (U : Set ℍ) (hU : IsOpen U)
    (hdisj : ∀ γ : X.deckGroup, γ ≠ 1 →
      Disjoint ((fun z : ℍ => γ • z) '' U) U) :
    Topology.IsOpenEmbedding (fun z : U => X.orbitProjection z.1) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_quotient_mk'.comp continuous_subtype_val
  · intro z w hzw
    have hrel : MulAction.orbitRel X.deckGroup ℍ z.1 w.1 := Quotient.exact hzw
    obtain ⟨γ, hact⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
    by_cases hγ : γ = 1
    · subst γ
      apply Subtype.ext
      simpa using hact.symm
    · exfalso
      exact (Set.disjoint_left.mp (hdisj γ hγ)) ⟨w.1, w.2, hact⟩ z.2
  · exact isOpenMap_quotient_mk'_mul.comp hU.isOpenMap_subtype_val

#print axioms exists_compact_deck_translate_separation
#print axioms exists_compact_deck_tube_disjoint_translates
#print axioms orbitProjection_restrict_isOpenEmbedding

end

end SystolicGrowth.ClosedHyperbolicSurface

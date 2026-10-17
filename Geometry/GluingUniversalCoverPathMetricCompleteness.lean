module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingUniversalCoverPathMetric
public import Mathlib.Topology.MetricSpace.Cauchy

@[expose] public section

/-!
# Completeness of the canonical native cover path metric

Use compactness of the actual glued carrier and the actual deck translates
that attain projected distance. A Cauchy sequence can only approach one
translate in a fixed fiber, by the positive systole gap.
-/

open Filter
open scoped ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Distinct points in one actual cover fiber are separated by the target
systole in the constructed native path metric. -/
theorem targetSystole_le_gluedUniversalCoverPathMetric_dist_of_same_fiber_ne
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e₀ e₁ : P.basedTopologicalUniversalCover x)
    (hproj : P.gluedUniversalCoverProjection x e₀ =
      P.gluedUniversalCoverProjection x e₁) (hne : e₀ ≠ e₁) :
    letI := P.gluedUniversalCoverPathMetricSpace x
    targetSystole C g ≤ dist e₀ e₁ := by
  letI := P.gluedUniversalCoverPathMetricSpace x
  have hne' : e₁ ≠ e₀ := fun h => hne h.symm
  have h := P.target_le_gluedUniversalCoverPathDistance_of_same_fiber_ne
    x hproj.symm hne'
  change ENNReal.ofReal (targetSystole C g) ≤ edist e₀ e₁ at h
  rw [edist_dist] at h
  exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp h

/-- A metric ball of radius at most half the target systole meets each fiber
of the native universal-cover projection in at most one point. This is the
covering-space injectivity step needed before comparing an embedded disk's
area; it uses the already-proved separation of distinct points in a fiber. -/
theorem gluedUniversalCoverProjection_injOn_ball_of_two_mul_radius_le_target
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (c : P.basedTopologicalUniversalCover x) (r : ℝ)
    (hr : 2 * r ≤ targetSystole C g) :
    letI := P.gluedUniversalCoverPathMetricSpace x
    Set.InjOn (P.gluedUniversalCoverProjection x) (Metric.ball c r) := by
  letI : MetricSpace (P.basedTopologicalUniversalCover x) :=
    P.gluedUniversalCoverPathMetricSpace x
  intro e₀ he₀ e₁ he₁ hproj
  by_contra hne
  have hgap := P.targetSystole_le_gluedUniversalCoverPathMetric_dist_of_same_fiber_ne
    x e₀ e₁ hproj hne
  have h₀ : dist e₀ c < r := Metric.mem_ball.mp he₀
  have h₁ : dist c e₁ < r := by
    simpa only [dist_comm] using (Metric.mem_ball.mp he₁)
  have hdist : dist e₀ e₁ < 2 * r := by
    calc
      dist e₀ e₁ ≤ dist e₀ c + dist c e₁ := dist_triangle e₀ c e₁
      _ < r + r := add_lt_add h₀ h₁
      _ = 2 * r := by ring
  linarith

/-- The actual finite path metric on the native universal cover is complete.
Projecting a Cauchy sequence gives a limit in the compact base. Each term is
at exactly the projected distance from some deck translate of a fixed lift
of that limit. The systole gap forces those translates to stabilize. -/
theorem gluedUniversalCoverPathMetric_completeSpace
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    letI := P.gluedUniversalCoverPathMetricSpace x
    CompleteSpace (P.basedTopologicalUniversalCover x) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  letI : CompactSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace_compact
  letI : MetricSpace (P.basedTopologicalUniversalCover x) :=
    P.gluedUniversalCoverPathMetricSpace x
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  let π := P.gluedUniversalCoverProjection x
  have hπlip : LipschitzWith 1 π := by
    simpa only using P.gluedUniversalCoverProjection_pathMetric_lipschitz x
  have hπcauchy : CauchySeq (π ∘ u) := hπlip.cauchySeq_comp hu
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hπcauchy
  obtain ⟨f, hf⟩ := P.gluedUniversalCoverProjection_surjective x y
  choose τ hτ using fun k : ℕ =>
    P.exists_gluedUniversalCoverDeck_dist_eq_projection_dist x (u k) f
  let ε : ℝ := targetSystole C g / 4
  have hε : 0 < ε := by
    dsimp [ε]
    exact div_pos P.target_pos (by norm_num)
  obtain ⟨N₁, hN₁⟩ := (Metric.cauchySeq_iff.mp hu) ε hε
  have hbaseEventually : ∀ᶠ k : ℕ in atTop,
      dist (π (u k)) y < ε := (Metric.tendsto_nhds.mp hy) ε hε
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hbaseEventually
  let N := max N₁ N₂
  have hN₁N : N₁ ≤ N := le_max_left _ _
  have hN₂N : N₂ ≤ N := le_max_right _ _
  have hbaseN (k : ℕ) (hk : N ≤ k) : dist (π (u k)) y < ε :=
    hN₂ k (le_trans hN₂N hk)
  have hseqN (k l : ℕ) (hk : N ≤ k) (hl : N ≤ l) :
      dist (u k) (u l) < ε :=
    hN₁ k (le_trans hN₁N hk) l (le_trans hN₁N hl)
  have htranslates_close (k l : ℕ) (hk : N ≤ k) (hl : N ≤ l) :
      dist ((τ k).val f) ((τ l).val f) < targetSystole C g := by
    calc
      dist ((τ k).val f) ((τ l).val f) ≤
          dist ((τ k).val f) (u k) + dist (u k) ((τ l).val f) := dist_triangle _ _ _
      _ ≤ dist ((τ k).val f) (u k) +
          (dist (u k) (u l) + dist (u l) ((τ l).val f)) :=
        add_le_add_right (dist_triangle _ _ _) _
      _ < ε + (ε + ε) := by
        rw [dist_comm ((τ k).val f) (u k), hτ k, hf, hτ l, hf]
        exact add_lt_add (hbaseN k hk)
          (add_lt_add (hseqN k l hk hl) (hbaseN l hl))
      _ < targetSystole C g := by
        dsimp [ε]
        linarith [P.target_pos]
  have hprojectTranslate (k : ℕ) :
      π ((τ k).val f) = y := by
    change P.gluedUniversalCoverProjection x ((τ k).val f) = y
    rw [P.gluedUniversalCoverDeck_projection x (τ k) f, hf]
  have htranslate_eq (k l : ℕ) (hk : N ≤ k) (hl : N ≤ l) :
      (τ k).val f = (τ l).val f := by
    by_cases heq : (τ k).val f = (τ l).val f
    · exact heq
    · have hgap := P.targetSystole_le_gluedUniversalCoverPathMetric_dist_of_same_fiber_ne
        x ((τ k).val f) ((τ l).val f)
        (by
          change π ((τ k).val f) = π ((τ l).val f)
          rw [hprojectTranslate k, hprojectTranslate l]) heq
      exact False.elim (not_lt_of_ge hgap (htranslates_close k l hk hl))
  let limit := (τ N).val f
  have hdist_limit (k : ℕ) (hk : N ≤ k) :
      dist (u k) limit = dist (π (u k)) y := by
    change dist (u k) ((τ N).val f) = dist (π (u k)) y
    rw [← htranslate_eq k N hk le_rfl, hτ k, hf]
  refine ⟨limit, ?_⟩
  rw [Metric.tendsto_nhds]
  intro δ hδ
  filter_upwards [
    (Metric.tendsto_nhds.mp hy) δ hδ,
    eventually_atTop.2 ⟨N, fun k hk => hk⟩] with k hkbase hkN
  rw [hdist_limit k hkN]
  exact hkbase

#print axioms targetSystole_le_gluedUniversalCoverPathMetric_dist_of_same_fiber_ne
#print axioms gluedUniversalCoverProjection_injOn_ball_of_two_mul_radius_le_target
#print axioms gluedUniversalCoverPathMetric_completeSpace

end SystolicGrowth.ExerciseGluingPreparation

module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedSystoleUpper
public import Geometry.GluingUniversalCoverCocompact
public import Geometry.GluingUniversalCoverProper
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# Attainment of the actual smooth fiber systole

The native compact orbit set and native proper metric give compactness for
bounded smooth displacement. Positive fiber separation removes the diagonal
from a closed compact minimization set. Actual smooth deck isometries compare
its minimum to every nontrivial same-fiber pair.
-/

open Set Metric
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The actual smooth cover metric is proper: each smooth closed
ball is closed in the unchanged topology and lies in a native compact ball. -/
theorem gluedCurvatureBoundedUniversalCoverMetricSpace_proper
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    ProperSpace (P.basedTopologicalUniversalCover x) := by
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  refine ⟨fun a R => ?_⟩
  let d : P.basedTopologicalUniversalCover x → P.basedTopologicalUniversalCover x → ℝ :=
    dist
  let s := closedBall a R
  have hs : IsClosed s := isClosed_closedBall
  have hdom (y : P.basedTopologicalUniversalCover x) :
      letI := P.gluedUniversalCoverPathMetricSpace x
      dist y a ≤ d y a := by
    have h := ENNReal.toReal_mono (edist_ne_top y a)
      (P.gluedCurvatureBoundedUniversalCover_edist_ge_native x y a)
    exact h
  letI := P.gluedUniversalCoverPathMetricSpace x
  letI := P.gluedUniversalCoverPathMetric_properSpace x
  apply (isCompact_closedBall a R).of_isClosed_subset hs
  intro y hy
  exact (hdom y).trans hy

/-- **Math.** A distinct pair in one actual projection fiber realizes the
extended-valued smooth systole. No shortest-loop or compactness input is supplied. -/
theorem exists_gluedCurvatureBoundedFiberSystole_attaining_pair
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) :
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    ∃ a b : P.basedTopologicalUniversalCover x,
      P.gluedUniversalCoverProjection x a = P.gluedUniversalCoverProjection x b ∧
        a ≠ b ∧ edist a b = P.gluedCurvatureBoundedFiberSystole x := by
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace_proper x
  have hex := P.gluedCurvatureBoundedFiberSystole_lt_top x hn hsum
  simp only [gluedCurvatureBoundedFiberSystole, iInf_lt_iff] at hex
  obtain ⟨a₀, b₀, hproj₀, hne₀, _⟩ := hex
  let K := P.gluedUniversalCoverCompactSet x
  let D := dist a₀ b₀
  let π := P.gluedUniversalCoverProjection x
  let S : Set (P.basedTopologicalUniversalCover x × P.basedTopologicalUniversalCover x) :=
    {z | z.1 ∈ K ∧ z.2 ∈ cthickening D K ∧ π z.1 = π z.2 ∧
      targetSystole C g ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ D}
  have hK : IsCompact K := P.gluedUniversalCoverCompactSet_isCompact x
  have hπ : Continuous π := (P.gluedUniversalCoverProjection_isCoveringMap x).continuous
  have hdist : Continuous (fun z : P.basedTopologicalUniversalCover x ×
      P.basedTopologicalUniversalCover x => dist z.1 z.2) := continuous_fst.dist continuous_snd
  have hclosed : IsClosed {z : P.basedTopologicalUniversalCover x ×
      P.basedTopologicalUniversalCover x | π z.1 = π z.2 ∧
        targetSystole C g ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ D} :=
    (isClosed_eq (hπ.comp continuous_fst) (hπ.comp continuous_snd)).inter
      ((isClosed_le continuous_const hdist).inter (isClosed_le hdist continuous_const))
  have hS : IsCompact S := by
    have hSclosed : IsClosed S :=
      (hK.isClosed.preimage continuous_fst).inter
        ((isClosed_cthickening.preimage continuous_snd).inter hclosed)
    apply (hK.prod (hK.cthickening (r := D))).of_isClosed_subset hSclosed
    exact fun _ hz => ⟨hz.1, hz.2.1⟩
  have hnormalize (a b : P.basedTopologicalUniversalCover x)
      (hp : π a = π b) (hne : a ≠ b) (hD : dist a b ≤ D) :
      ∃ z ∈ S, dist z.1 z.2 = dist a b := by
    obtain ⟨τ, hτ⟩ := P.gluedUniversalCoverCompactSet_meets_orbit x a
    have hiso := P.gluedCurvatureBoundedUniversalCover_deck_isometry x τ
    have hpair : dist (τ.val a) (τ.val b) = dist a b := hiso.dist_eq a b
    have hp' : π (τ.val a) = π (τ.val b) :=
      (τ.property a).trans (hp.trans (τ.property b).symm)
    have hne' : τ.val a ≠ τ.val b := fun h => hne (τ.val.injective h)
    refine ⟨(τ.val a, τ.val b), ⟨hτ, ?_, hp', ?_, hpair.le.trans hD⟩, hpair⟩
    · apply closedBall_subset_cthickening hτ D
      rw [mem_closedBall, dist_comm, hpair]
      exact hD
    · exact P.targetSystole_le_gluedCurvatureBoundedUniversalCover_dist_of_same_fiber_ne
        x (τ.val a) (τ.val b) hp' hne'
  obtain ⟨z₀, hz₀, _⟩ := hnormalize a₀ b₀ hproj₀ hne₀ le_rfl
  obtain ⟨z, hz, hmin⟩ := hS.exists_isMinOn ⟨z₀, hz₀⟩ hdist.continuousOn
  have hne : z.1 ≠ z.2 := by
    intro heq
    have hgap := hz.2.2.2.1
    rw [heq, dist_self] at hgap
    exact (not_le_of_gt P.target_pos) hgap
  have hglobal (a b : P.basedTopologicalUniversalCover x)
      (hp : π a = π b) (hab : a ≠ b) : dist z.1 z.2 ≤ dist a b := by
    by_cases hD : dist a b ≤ D
    · obtain ⟨w, hw, heq⟩ := hnormalize a b hp hab hD
      exact (hmin hw).trans_eq heq
    · exact hz.2.2.2.2.trans (le_of_not_ge hD)
  refine ⟨z.1, z.2, hz.2.2.1, hne, le_antisymm ?_ ?_⟩
  · apply le_iInf
    intro a
    apply le_iInf
    intro b
    apply le_iInf
    intro hp
    apply le_iInf
    intro hab
    rw [edist_dist, edist_dist]
    exact ENNReal.ofReal_le_ofReal (hglobal a b hp hab)
  · exact P.gluedCurvatureBoundedFiberSystole_le_edist x z.1 z.2 hz.2.2.1 hne

/-- **Math.** The same actual pair attains the real systole, whose finiteness
was established from actual area rather than assumed. -/
theorem exists_gluedCurvatureBoundedFiberSystole_toReal_attaining_pair
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) :
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    ∃ a b : P.basedTopologicalUniversalCover x,
      P.gluedUniversalCoverProjection x a = P.gluedUniversalCoverProjection x b ∧
        a ≠ b ∧ dist a b = (P.gluedCurvatureBoundedFiberSystole x).toReal := by
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  obtain ⟨a, b, hp, hne, heq⟩ :=
    P.exists_gluedCurvatureBoundedFiberSystole_attaining_pair x hn hsum
  exact ⟨a, b, hp, hne, congrArg ENNReal.toReal heq⟩

#print axioms gluedCurvatureBoundedUniversalCoverMetricSpace_proper
#print axioms exists_gluedCurvatureBoundedFiberSystole_attaining_pair
#print axioms exists_gluedCurvatureBoundedFiberSystole_toReal_attaining_pair

end SystolicGrowth.ExerciseGluingPreparation

end

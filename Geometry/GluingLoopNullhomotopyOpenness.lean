module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingLocalContractibility
public import Vendored.TauCeti.AlgebraicTopology.SemilocallySimplyConnected.On

@[expose] public section

/-!
# Openness of nullhomotopy for loops with varying basepoints

Nearby loop basepoints are connected to the original basepoint by the actual
continuous small-ball interpolation. Conjugating gives a continuous family
of based loops. The attributed fixed-basepoint openness theorem then proves
openness in the genuine closed-loop space, without fixing loop basepoints.
-/

open Set Metric
open scoped Topology unitInterval

namespace SystolicGrowth

/-- Actual continuous closed loop maps; the basepoint is allowed to vary. -/
def closedLoopMapSet (M : Type*) [TopologicalSpace M] : Set C(unitInterval, M) :=
  {f | f 0 = f 1}

/-- The based path of a closed loop map, at its actual initial value. -/
def closedLoopPath {M : Type*} [TopologicalSpace M] (f : closedLoopMapSet M) :
    Path (f.1 0) (f.1 0) where
  toFun := f.1
  continuous_toFun := f.1.continuous
  source' := rfl
  target' := f.2.symm

private theorem anchored_loop_nullhomotopic_iff
    {M : Type*} [TopologicalSpace M] {x y : M} (α : Path x y) (β : Path y y) :
    ((α.trans β).trans α.symm).Homotopic (Path.refl x) ↔
      β.Homotopic (Path.refl y) := by
  constructor
  · exact Path.Homotopic.of_conj_nullhomotopic
  · intro hβ
    exact ((Path.Homotopic.trans_right_of_nullhomotopic hβ).hcomp
      (.refl α.symm)).trans (Path.Homotopic.trans_symm α)

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Nullhomotopy is open among actual closed loop maps, even when their
basepoints move. The connecting paths and their continuity are constructed
from native small-ball metric segments. -/
theorem gluedIntrinsicMetric_isOpen_nullhomotopic_closedLoopMapSet
    (P : ExerciseGluingPreparation C g n genera X) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    IsOpen {f : closedLoopMapSet P.GluedCarrier |
      (closedLoopPath f).Homotopic (Path.refl (f.1 0))} := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  letI : CompactSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace_compact
  apply isOpen_iff_forall_mem_open.mpr
  intro f hf
  let x := f.1 0
  obtain ⟨ε, hε, hcomparison⟩ :=
    P.gluedIntrinsicMetric_locally_closedBall_midpoint_cosh_all_test x
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hδε : δ < ε := by dsimp only [δ]; linarith
  letI : IsClosed (closedBall x δ) := isClosed_closedBall
  obtain ⟨G, hG0, hG1, _⟩ :=
    exists_continuous_metric_interpolation_of_midpoint_cosh_all_test
      (hcomparison δ hδ.le hδε)
  let c : closedBall x δ := ⟨x, mem_closedBall_self hδ.le⟩
  let U : Set (closedLoopMapSet P.GluedCarrier) := {g | g.1 0 ∈ ball x δ}
  have hU : IsOpen U := Metric.isOpen_ball.preimage
    ((continuous_eval_const 0).comp continuous_subtype_val)
  have hfU : f ∈ U := Metric.mem_ball_self hδ
  let q : U → closedBall x δ := fun g => ⟨g.1.1 0, ball_subset_closedBall g.2⟩
  have hq : Continuous q :=
    ((continuous_eval_const 0).comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  let α : ∀ g : U, Path x (g.1.1 0) := fun g =>
    { toFun := fun t => (G ((c, q g), t)).1
      continuous_toFun := continuous_subtype_val.comp
        (G.continuous.comp (continuous_const.prodMk continuous_id))
      source' := congrArg Subtype.val (hG0 c (q g))
      target' := congrArg Subtype.val (hG1 c (q g)) }
  have hα : Continuous ↿α := by
    change Continuous (fun p : U × unitInterval => (G ((c, q p.1), p.2)).1)
    exact continuous_subtype_val.comp (G.continuous.comp
      ((continuous_const.prodMk (hq.comp continuous_fst)).prodMk continuous_snd))
  have hloops : Continuous ↿fun g : U => closedLoopPath g.1 := by
    change Continuous (fun p : U × unitInterval => p.1.1.1 p.2)
    exact continuous_eval.comp
      ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd)
  let anchored : U → Path x x := fun g =>
    ((α g).trans (closedLoopPath g.1)).trans (α g).symm
  have hanchored : Continuous anchored := by
    apply Path.continuous_uncurry_iff.mp
    exact Path.trans_continuous_family
      (fun g => (α g).trans (closedLoopPath g.1))
      (Path.trans_continuous_family α hα (fun g => closedLoopPath g.1) hloops)
      (fun g => (α g).symm) (Path.symm_continuous_family α hα)
  let V : Set U := anchored ⁻¹' {p : Path x x | p.Homotopic (Path.refl x)}
  have hV : IsOpen V :=
    (Path.isOpen_setOf_homotopic (Path.refl x)).preimage hanchored
  refine ⟨Subtype.val '' V, ?_, hU.isOpenMap_subtype_val _ hV, ?_⟩
  · rintro g ⟨u, hu, rfl⟩
    exact (anchored_loop_nullhomotopic_iff (α u) (closedLoopPath u.1)).mp hu
  · refine ⟨⟨f, hfU⟩, ?_, rfl⟩
    exact (anchored_loop_nullhomotopic_iff (α ⟨f, hfU⟩) (closedLoopPath f)).mpr hf

#print axioms gluedIntrinsicMetric_isOpen_nullhomotopic_closedLoopMapSet

end ExerciseGluingPreparation

end SystolicGrowth

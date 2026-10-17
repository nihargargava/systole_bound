module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingLocalComparison
public import Geometry.MetricSegmentContinuity
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.LocallyContractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

@[expose] public section

/-!
# Contractible native small closed balls

The constructed continuous metric interpolation contracts each sufficiently
small actual intrinsic closed ball to its center. This retains the original
quotient topology and metric. Loops confined to that ball are consequently
nullhomotopic in the original glued carrier, with their basepoints fixed.
-/

open Set Metric
open scoped Topology unitInterval

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Every sufficiently small native intrinsic closed ball is contractible.
The contraction is built from genuine continuously varying metric segments,
not postulated as an additional geometric input. -/
theorem gluedIntrinsicMetric_locally_contractible_closedBall
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ ε > 0, ∀ δ : ℝ, 0 ≤ δ → δ < ε → ContractibleSpace (closedBall x δ) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  letI : CompactSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace_compact
  obtain ⟨ε, hε, hcomparison⟩ :=
    P.gluedIntrinsicMetric_locally_closedBall_midpoint_cosh_all_test x
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδε
  letI : IsClosed (closedBall x δ) := isClosed_closedBall
  obtain ⟨G, hG0, hG1, _⟩ :=
    exists_continuous_metric_interpolation_of_midpoint_cosh_all_test (hcomparison δ hδ hδε)
  let c : closedBall x δ := ⟨x, mem_closedBall_self hδ⟩
  apply (contractible_iff_id_nullhomotopic (closedBall x δ)).2
  refine ⟨c, ⟨?_⟩⟩
  exact
    { toFun := fun p => G ((p.2, c), p.1)
      continuous_toFun := G.continuous.comp
        ((continuous_snd.prodMk continuous_const).prodMk continuous_fst)
      map_zero_left := fun y => hG0 y c
      map_one_left := fun y => hG1 y c }

/-- Actual loops confined to any sufficiently small native closed ball are
nullhomotopic in the original carrier, without changing their basepoint. -/
theorem gluedIntrinsicMetric_locally_nullhomotopic_loops_in_closedBall
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ ε > 0, ∀ δ : ℝ, 0 ≤ δ → δ < ε →
      ∀ y : P.GluedCarrier, y ∈ closedBall x δ →
        ∀ β : Path y y, (∀ t : unitInterval, β t ∈ closedBall x δ) →
          β.Homotopic (Path.refl y) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨ε, hε, hcontract⟩ := P.gluedIntrinsicMetric_locally_contractible_closedBall x
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδε y hy β hball
  letI : ContractibleSpace (closedBall x δ) := hcontract δ hδ hδε
  let c : closedBall x δ := ⟨y, hy⟩
  let β' : Path c c :=
    { toFun := fun t => ⟨β t, hball t⟩
      continuous_toFun := β.continuous.subtype_mk hball
      source' := Subtype.ext β.source
      target' := Subtype.ext β.target }
  have hβ := SimplyConnectedSpace.paths_homotopic β' (Path.refl c)
  have hmap : β'.map continuous_subtype_val = β := by
    apply Path.ext
    funext t
    rfl
  have hrefl : (Path.refl c).map continuous_subtype_val = Path.refl y := rfl
  simpa only [hmap, hrefl] using
    hβ.map (⟨Subtype.val, continuous_subtype_val⟩ : C(closedBall x δ, P.GluedCarrier))

/-- The original quotient topology has a basis of genuine contractible
intrinsic neighborhoods. In particular, Mathlib supplies local path
connectedness and the imported cover machinery can use this same carrier. -/
instance gluedCarrierStronglyLocallyContractibleSpace
    (P : ExerciseGluingPreparation C g n genera X) :
    StronglyLocallyContractibleSpace P.GluedCarrier := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  refine ⟨fun x => ?_⟩
  rw [Filter.hasBasis_self]
  intro U hU
  obtain ⟨ε, hε, hcontract⟩ := P.gluedIntrinsicMetric_locally_contractible_closedBall x
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hU
  let δ := min r (ε / 2)
  have hδ : 0 < δ := lt_min hr (by linarith)
  have hδε : δ < ε := (min_le_right _ _).trans_lt (by linarith)
  refine ⟨closedBall x δ, Metric.closedBall_mem_nhds x hδ,
    hcontract δ hδ.le hδε, ?_⟩
  exact (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hsub

#print axioms gluedIntrinsicMetric_locally_contractible_closedBall
#print axioms gluedIntrinsicMetric_locally_nullhomotopic_loops_in_closedBall
#print axioms gluedCarrierStronglyLocallyContractibleSpace

end SystolicGrowth.ExerciseGluingPreparation

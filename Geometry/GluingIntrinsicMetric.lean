module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingRiemannianMetric
public import Geometry.GluingConnected
public import Mathlib.Geometry.Manifold.Riemannian.Basic

@[expose] public section

/-!
# The intrinsic Riemannian extended distance on the actual glued carrier

The constructed continuous tangent metric defines the infimum of lengths
of native C¹ paths. The proved connectivity of the actual quotient makes
all intrinsic distances finite, giving a metric with the original quotient
topology. No ambient component/chord distance is substituted. Length
comparisons, geodesic existence and curvature remain separate obligations.
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology Bundle ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The infimum of actual C¹ path lengths for the constructed tangent metric. -/
noncomputable def gluedIntrinsicEDist
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier) : ℝ≥0∞ := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  exact riemannianEDist (modelWithCornersSelf ℝ ℂ) x y

/-- The actual intrinsic extended metric, with the original quotient topology. -/
@[instance_reducible]
noncomputable def gluedCarrierIntrinsicEMetricSpace
    (P : ExerciseGluingPreparation C g n genera X) : EMetricSpace P.GluedCarrier := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  exact EMetricSpace.ofRiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier

theorem gluedCarrierIntrinsicEMetricSpace_edist
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier) :
    letI := P.gluedCarrierIntrinsicEMetricSpace
    edist x y = P.gluedIntrinsicEDist x y := rfl

/-- The native distance-identification predicate holds for the constructed
metric itself, with its actual tangent norm and not an assumed distance. -/
theorem gluedCarrierIntrinsicEMetricSpace_isRiemannian
    (P : ExerciseGluingPreparation C g n genera X) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    letI := P.gluedCarrierIntrinsicEMetricSpace
    IsRiemannianManifold (modelWithCornersSelf ℝ ℂ) P.GluedCarrier := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  letI : EMetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicEMetricSpace
  exact ⟨fun _ _ => rfl⟩

/-- Any actual C¹ path gives an upper bound for the constructed intrinsic
distance. Subsequent excursion estimates must use this tangent norm. -/
theorem gluedIntrinsicEDist_le_pathELength
    (P : ExerciseGluingPreparation C g n genera X) {γ : ℝ → P.GluedCarrier} {a b : ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ (Icc a b))
    (hab : a ≤ b) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    P.gluedIntrinsicEDist (γ a) (γ b) ≤ pathELength (modelWithCornersSelf ℝ ℂ) γ a b := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  exact riemannianEDist_le_pathELength hγ rfl rfl hab

/-- Definitional preservation of the existing topology prevents a topology diamond. -/
theorem gluedCarrierIntrinsicEMetricSpace_topology
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedCarrierIntrinsicEMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace P.GluedCarrier) := rfl

/-- Original quotient compactness also holds for the constructed intrinsic extended metric. -/
theorem gluedCarrierIntrinsicEMetricSpace_compact
    (P : ExerciseGluingPreparation C g n genera X) :
    letI := P.gluedCarrierIntrinsicEMetricSpace
    CompactSpace P.GluedCarrier := inferInstance

/-- Genuine intrinsic distances are locally finite; this does not assume or
assert connectivity of the retained components. -/
theorem eventually_gluedIntrinsicEDist_lt_top
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    ∀ᶠ y in 𝓝 x, P.gluedIntrinsicEDist x y < ⊤ := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  exact eventually_riemannianEDist_lt (modelWithCornersSelf ℝ ℂ) x (by simp)

/-- Connectivity is constructed for the actual retained chain. Its finite-
distance class is nonempty and clopen, hence the whole original quotient. -/
theorem gluedIntrinsicEDist_lt_top
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier) :
    P.gluedIntrinsicEDist x y < ⊤ := by
  letI : EMetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicEMetricSpace
  letI : PreconnectedSpace P.GluedCarrier := P.gluedCarrierPreconnectedSpace
  have hc : IsClopen (Metric.eball x (⊤ : ℝ≥0∞)) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have heq : Metric.eball x (⊤ : ℝ≥0∞) = univ :=
    hc.eq_univ ⟨x, by simp⟩
  have hy : y ∈ Metric.eball x (⊤ : ℝ≥0∞) := heq.symm ▸ mem_univ y
  have hxy : edist x y < ⊤ := by
    simpa only [Metric.mem_eball, edist_comm] using hy
  rw [P.gluedCarrierIntrinsicEMetricSpace_edist] at hxy
  exact hxy

/-- The finite intrinsic path distance as a genuine metric, preserving
the already constructed quotient topology and extended distance. -/
@[instance_reducible]
noncomputable def gluedCarrierIntrinsicMetricSpace
    (P : ExerciseGluingPreparation C g n genera X) : MetricSpace P.GluedCarrier := by
  letI : EMetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicEMetricSpace
  exact EMetricSpace.toMetricSpace (fun x y => by
    rw [P.gluedCarrierIntrinsicEMetricSpace_edist]
    exact (P.gluedIntrinsicEDist_lt_top x y).ne)

theorem gluedCarrierIntrinsicMetricSpace_edist
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    edist x y = P.gluedIntrinsicEDist x y := rfl

theorem gluedCarrierIntrinsicMetricSpace_topology
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedCarrierIntrinsicMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace P.GluedCarrier) := rfl

theorem gluedCarrierIntrinsicMetricSpace_compact
    (P : ExerciseGluingPreparation C g n genera X) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    CompactSpace P.GluedCarrier := inferInstance

#print axioms gluedCarrierIntrinsicEMetricSpace
#print axioms gluedCarrierIntrinsicEMetricSpace_edist
#print axioms gluedCarrierIntrinsicEMetricSpace_isRiemannian
#print axioms gluedIntrinsicEDist_le_pathELength
#print axioms gluedCarrierIntrinsicEMetricSpace_topology
#print axioms gluedCarrierIntrinsicEMetricSpace_compact
#print axioms eventually_gluedIntrinsicEDist_lt_top
#print axioms gluedIntrinsicEDist_lt_top
#print axioms gluedCarrierIntrinsicMetricSpace
#print axioms gluedCarrierIntrinsicMetricSpace_edist
#print axioms gluedCarrierIntrinsicMetricSpace_topology
#print axioms gluedCarrierIntrinsicMetricSpace_compact

end SystolicGrowth.ExerciseGluingPreparation

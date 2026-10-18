module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingUniversalCoverApproximateMidpoints
public import Geometry.GluingUniversalCoverLocalCompactness
public import Geometry.GluingUniversalCoverCocompact
public import Geometry.ProperMidpoints
public import Geometry.GluingGeodesics
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

/-!
# Properness of the actual native glued universal cover

A compact set meeting all deck orbits and local compactness give a common
radius whose closed balls are compact. Approximate midpoints enlarge this
radius by a factor of `5/4`; iteration makes every closed ball compact.
The proof uses the constructed native metric, not an assumed geodesic or
curvature structure.
-/

open Set Metric

namespace SystolicGrowth

/-- Uniform compactness of balls of one positive radius propagates to a
larger radius in a metric space with actual approximate midpoints. -/
theorem isCompact_closedBall_five_quarters_of_approximate_midpoints
    {M : Type*} [MetricSpace M]
    (hmid : ∀ x y : M, ∀ ε : ℝ, 0 < ε → ∃ z : M,
      dist x z ≤ dist x y / 2 + ε ∧ dist z y ≤ dist x y / 2 + ε)
    {r : ℝ} (hr : 0 < r) (hcompact : ∀ x : M, IsCompact (closedBall x r))
    (x : M) : IsCompact (closedBall x (5 / 4 * r)) := by
  classical
  have hε : 0 < r / 8 := by linarith
  obtain ⟨t, ht⟩ := (hcompact x).elim_finite_subcover
    (fun y : M => ball y (r / 8)) (fun _ => isOpen_ball) (by
      intro y _
      exact mem_iUnion.mpr ⟨y, mem_ball_self hε⟩)
  have hUnion : IsCompact (⋃ y ∈ t, closedBall y r) :=
    t.finite_toSet.isCompact_biUnion fun y _ => hcompact y
  refine hUnion.of_isClosed_subset isClosed_closedBall ?_
  intro y hy
  have hxy : dist x y ≤ 5 / 4 * r := by
    simpa only [mem_closedBall, dist_comm y x] using hy
  obtain ⟨z, hxz, hzy⟩ := hmid x y (r / 8) hε
  have hz : z ∈ closedBall x r := by
    rw [mem_closedBall, dist_comm z x]
    linarith
  obtain ⟨a, hat, hza⟩ := mem_iUnion₂.mp (ht hz)
  have haz : dist a z < r / 8 := by
    simpa only [mem_ball, dist_comm z a] using hza
  refine mem_iUnion₂.mpr ⟨a, hat, ?_⟩
  rw [mem_closedBall, dist_comm y a]
  have htriangle := dist_triangle a z y
  linarith

/-- A uniform compact-ball radius and approximate midpoints imply
properness. The radii `r * (5/4)^n` grow without bound. -/
theorem properSpace_of_uniform_compact_closedBalls_approximate_midpoints
    {M : Type*} [MetricSpace M]
    (hmid : ∀ x y : M, ∀ ε : ℝ, 0 < ε → ∃ z : M,
      dist x z ≤ dist x y / 2 + ε ∧ dist z y ≤ dist x y / 2 + ε)
    (hbase : ∃ r : ℝ, 0 < r ∧ ∀ x : M, IsCompact (closedBall x r)) :
    ProperSpace M := by
  obtain ⟨r, hr, hcompact⟩ := hbase
  have hiterate (n : ℕ) (x : M) : IsCompact (closedBall x (r * (5 / 4 : ℝ) ^ n)) := by
    induction n generalizing x with
    | zero => simpa using hcompact x
    | succ n ih =>
      have hrn : 0 < r * (5 / 4 : ℝ) ^ n := mul_pos hr (pow_pos (by norm_num) _)
      have hstep := isCompact_closedBall_five_quarters_of_approximate_midpoints
        hmid hrn ih x
      have hscale : r * (5 / 4 : ℝ) ^ (n + 1) =
          5 / 4 * (r * (5 / 4 : ℝ) ^ n) := by
        rw [pow_succ]
        ring
      rw [hscale]
      exact hstep
  refine ⟨fun x R => ?_⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (R / r) (show (1 : ℝ) < 5 / 4 by norm_num)
  have hRn : R ≤ r * (5 / 4 : ℝ) ^ n := by
    have h := (div_lt_iff₀ hr).mp hn
    nlinarith
  exact (hiterate n x).of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hRn)

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Local compactness near the chosen compact deck-orbit cover supplies one
positive radius whose native closed balls are compact at every cover point. -/
theorem exists_gluedUniversalCover_uniform_compact_closedBall_radius
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    letI := P.gluedUniversalCoverPathMetricSpace x
    ∃ r : ℝ, 0 < r ∧ ∀ e : P.basedTopologicalUniversalCover x,
      IsCompact (closedBall e r) := by
  letI := P.gluedUniversalCoverPathMetricSpace x
  obtain ⟨r, hr, hK⟩ :=
    (P.gluedUniversalCoverCompactSet_isCompact x).exists_isCompact_cthickening
  refine ⟨r, hr, ?_⟩
  intro e
  obtain ⟨τ, hτ⟩ := P.gluedUniversalCoverCompactSet_meets_orbit x e
  have hball : IsCompact (closedBall (τ.val e) r) :=
    hK.of_isClosed_subset isClosed_closedBall (closedBall_subset_cthickening hτ r)
  have hpre : IsCompact (τ.val ⁻¹' closedBall (τ.val e) r) :=
    τ.val.isCompact_preimage.mpr hball
  simpa only [(P.gluedUniversalCoverDeck_pathMetric_isometry x τ).preimage_closedBall e r]
    using hpre

/-- Every closed ball in the canonical native cover metric is compact.
Its properness is derived from actual deck cocompactness, local compactness
and approximate midpoints, without assuming upstairs global compactness. -/
theorem gluedUniversalCoverPathMetric_properSpace
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    letI := P.gluedUniversalCoverPathMetricSpace x
    ProperSpace (P.basedTopologicalUniversalCover x) := by
  letI := P.gluedUniversalCoverPathMetricSpace x
  apply properSpace_of_uniform_compact_closedBalls_approximate_midpoints
    (fun e f ε hε => P.exists_gluedUniversalCover_approximate_midpoint x e f ε hε)
  exact P.exists_gluedUniversalCover_uniform_compact_closedBall_radius x

/-- Compact native upstairs balls turn the actual approximate midpoints
into exact midpoints for the same canonical path metric. -/
theorem gluedUniversalCoverPathMetric_exists_midpoint
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e f : P.basedTopologicalUniversalCover x) :
    letI := P.gluedUniversalCoverPathMetricSpace x
    ∃ z : P.basedTopologicalUniversalCover x,
      dist e z = dist e f / 2 ∧ dist z f = dist e f / 2 := by
  letI := P.gluedUniversalCoverPathMetricSpace x
  letI := P.gluedUniversalCoverPathMetric_properSpace x
  exact exists_midpoint_of_proper_approximate_midpoints e f
    (fun ε hε => P.exists_gluedUniversalCover_approximate_midpoint x e f ε hε)

/-- Exact midpoint grids extend to a genuine constant-speed minimizing
path in the actual native cover, including coincident endpoints. -/
theorem gluedUniversalCoverPathMetric_exists_metric_path
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e f : P.basedTopologicalUniversalCover x) :
    letI := P.gluedUniversalCoverPathMetricSpace x
    ∃ Γ : Path e f, ∀ s t : unitInterval,
      dist (Γ s) (Γ t) = dist e f * |(s : ℝ) - (t : ℝ)| := by
  letI := P.gluedUniversalCoverPathMetricSpace x
  letI := P.gluedUniversalCoverPathMetric_properSpace x
  let m : P.basedTopologicalUniversalCover x →
      P.basedTopologicalUniversalCover x → P.basedTopologicalUniversalCover x :=
    fun a b => (P.gluedUniversalCoverPathMetric_exists_midpoint x a b).choose
  have hm : ∀ a b, dist a (m a b) = dist a b / 2 ∧ dist (m a b) b = dist a b / 2 :=
    fun a b => (P.gluedUniversalCoverPathMetric_exists_midpoint x a b).choose_spec
  exact exists_midpoint_metric_path m hm e f

/-- Every two points of the native universal cover are joined by an actual
isometric distance interval, without a geodesic structure assumption. -/
theorem gluedUniversalCoverPathMetric_exists_isometric_segment
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e f : P.basedTopologicalUniversalCover x) :
    letI := P.gluedUniversalCoverPathMetricSpace x
    ∃ σ : Icc (0 : ℝ) (dist e f) → P.basedTopologicalUniversalCover x, Isometry σ ∧
      σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = e ∧
      σ ⟨dist e f, ⟨dist_nonneg, le_rfl⟩⟩ = f := by
  letI := P.gluedUniversalCoverPathMetricSpace x
  obtain ⟨Γ, hΓ⟩ := P.gluedUniversalCoverPathMetric_exists_metric_path x e f
  exact metric_path_exists_isometric_interval Γ hΓ

#print axioms exists_gluedUniversalCover_uniform_compact_closedBall_radius
#print axioms gluedUniversalCoverPathMetric_properSpace
#print axioms gluedUniversalCoverPathMetric_exists_midpoint
#print axioms gluedUniversalCoverPathMetric_exists_metric_path
#print axioms gluedUniversalCoverPathMetric_exists_isometric_segment

end ExerciseGluingPreparation

end SystolicGrowth

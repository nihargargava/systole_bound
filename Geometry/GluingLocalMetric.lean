module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurveLength

@[expose] public section

/-!
# Local coordinate bounds for the actual intrinsic metric

Original topology preservation supplies an intrinsic ball inside each
actual chart. Native prefix-length bounds prevent sufficiently short C¹
paths from exiting this ball. The verified collar integral estimates then
apply to genuinely contained near-minimizers and descend to local radial
and angular Lipschitz bounds for the actual intrinsic distance. No path
containment, C¹ regularity of metric segments or chord-distance identity
is assumed.
-/

open Set Metric Bundle Manifold
open scoped Manifold Topology Bundle ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- An actual chart contains every sufficiently short native C¹ path
starting in a smaller intrinsic ball. The ball is obtained from the proved
original topology of the constructed intrinsic metric. -/
theorem gluedChart_exists_short_path_barrier
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (x : P.GluedCarrier)
    (hx : x ∈ e.source) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ R > 0, ball x R ⊆ e.source ∧
      ∀ γ : ℝ → P.GluedCarrier,
        ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ (Icc 0 1) →
        dist x (γ 0) < R / 4 →
        pathELength (modelWithCornersSelf ℝ ℂ) γ 0 1 < ENNReal.ofReal (3 * R / 4) →
        MapsTo γ (Icc 0 1) e.source := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.1 (e.open_source.mem_nhds hx)
  refine ⟨R, hR, hball, ?_⟩
  intro γ hγ hstart hlen t ht
  have hp := P.gluedIntrinsicEDist_le_pathELength
    (hγ.mono (Icc_subset_Icc le_rfl ht.2)) ht.1
  change edist (γ 0) (γ t) ≤ pathELength (modelWithCornersSelf ℝ ℂ) γ 0 t at hp
  have hsub : edist (γ 0) (γ t) < ENNReal.ofReal (3 * R / 4) :=
    hp.trans_lt ((pathELength_mono le_rfl ht.2).trans_lt hlen)
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by linarith)] at hsub
  have htR : dist x (γ t) < R := by
    have := dist_triangle x (γ 0) (γ t)
    linarith
  apply hball
  simpa only [Metric.mem_ball, dist_comm] using htR

/-- On a constructed small intrinsic ball in every actual seam chart,
signed radius is 1-Lipschitz and lifted angle is controlled by the seam's
own `sinh(radius)` coefficient, including signed-radius zero. -/
theorem gluedIntrinsicMetric_seam_coordinates_locally_lipschitz
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (x : P.GluedCarrier) (hx : x ∈ (P.seamAngularComplexChart k θ).source) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ ρ > 0, ball x ρ ⊆ (P.seamAngularComplexChart k θ).source ∧
      ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
        |(P.seamAngularComplexChart k θ y).re - (P.seamAngularComplexChart k θ z).re| ≤
          dist y z ∧
        Real.sinh (gluingRadius C g) *
          |(P.seamAngularComplexChart k θ y).im - (P.seamAngularComplexChart k θ z).im| ≤
          dist y z := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨R, hR, hball, hbarrier⟩ :=
    P.gluedChart_exists_short_path_barrier (P.seamAngularComplexChart k θ) x hx
  refine ⟨R / 8, by linarith, ?_, ?_⟩
  · intro y hy
    apply hball
    simp only [Metric.mem_ball] at hy ⊢
    linarith
  intro y hy z hz
  have hxy : dist x y < R / 8 := by simpa only [Metric.mem_ball, dist_comm] using hy
  have hxz : dist x z < R / 8 := by simpa only [Metric.mem_ball, dist_comm] using hz
  have hd : dist y z < R / 4 := by
    have := dist_triangle y x z
    rw [dist_comm y x] at this
    linarith
  have hbound (ε : ℝ) (hε : 0 < ε) :
      |(P.seamAngularComplexChart k θ y).re - (P.seamAngularComplexChart k θ z).re| ≤
        dist y z + ε ∧
      Real.sinh (gluingRadius C g) *
        |(P.seamAngularComplexChart k θ y).im - (P.seamAngularComplexChart k θ z).im| ≤
        dist y z + ε := by
    let δ := min ε (R / 4)
    have hδ : 0 < δ := lt_min hε (by linarith)
    have hδε : δ ≤ ε := min_le_left _ _
    have hδR : δ ≤ R / 4 := min_le_right _ _
    have hdist : 0 ≤ dist y z := dist_nonneg
    have hr : riemannianEDist (modelWithCornersSelf ℝ ℂ) y z <
        ENNReal.ofReal (dist y z + δ) := by
      change edist y z < ENNReal.ofReal (dist y z + δ)
      rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by linarith)]
      linarith
    obtain ⟨γ, hγ0, hγ1, hγ, hlen, _, _⟩ :=
      exists_lt_locally_constant_of_riemannianEDist_lt hr (show (0 : ℝ) < 1 by norm_num)
    have hlenR : pathELength (modelWithCornersSelf ℝ ℂ) γ 0 1 <
        ENNReal.ofReal (3 * R / 4) :=
      hlen.trans_le (ENNReal.ofReal_le_ofReal (by linarith))
    have hstart : dist x (γ 0) < R / 4 := by rw [hγ0]; linarith
    have hmap := hbarrier γ hγ.contMDiffOn hstart hlenR
    have hrad := (P.gluedCurve_seam_radial_enorm_sub_le_pathELength k θ
      hγ.contMDiffOn hmap zero_le_one).trans hlen.le
    rw [hγ0, hγ1, ← ofReal_norm, Real.norm_eq_abs, abs_sub_comm] at hrad
    have hradReal := (ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ dist y z + δ)).1 hrad
    have hang := (P.gluedCurve_seam_angular_enorm_sub_le_pathELength k θ
      hγ.contMDiffOn hmap zero_le_one).trans hlen.le
    rw [hγ0, hγ1, ← ofReal_norm, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.sinh_pos_iff.mpr P.radius_pos), abs_sub_comm] at hang
    have hangReal := (ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ dist y z + δ)).1 hang
    constructor <;> linarith
  exact ⟨le_of_forall_pos_le_add (fun ε hε => (hbound ε hε).1),
    le_of_forall_pos_le_add (fun ε hε => (hbound ε hε).2)⟩

#print axioms gluedChart_exists_short_path_barrier
#print axioms gluedIntrinsicMetric_seam_coordinates_locally_lipschitz

end SystolicGrowth.ExerciseGluingPreparation

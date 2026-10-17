module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainSmoothMetric
public import Geometry.GluingCollarLocalizedSmoothMetric
public import Geometry.GluingIntrinsicMetric
public import Mathlib.Topology.UniformSpace.UniformConvergence

@[expose] public section

/-!
# Actual smooth metrics converging to the native glued metric

Disjoint native thin strips give the same multiplicative bound as one
collar, without a factor depending on the number of seams. The constructed
positive bundle defines actual C¹-path metrics on the original carrier.
-/

open Set Filter Bundle Manifold ContinuousLinearMap MeasureTheory
open scoped Manifold Topology Bundle ENNReal NNReal

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

set_option backward.isDefEq.respectTransparency false in
/-- The global tensor has the one-collar bound because actual thin supports
are pairwise disjoint. -/
theorem gluedSmoothTangentInner_bounds
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 ≤ ε)
    (p : P.GluedCarrier) (v : TangentSpace (modelWithCornersSelf ℝ ℂ) p) :
    P.gluedTangentInner p v v ≤ P.gluedSmoothTangentInner ε p v v ∧
      P.gluedSmoothTangentInner ε p v v ≤
        gluingCollarSmoothMetricFactor (gluingRadius C g) ε ^ 2 * P.gluedTangentInner p v v := by
  classical
  refine ⟨P.gluedTangentInner_le_gluedSmoothTangentInner hε p v, ?_⟩
  by_cases hthin : ∃ k : Fin (n - 1), p ∈ P.thinSeamCollar k
  · obtain ⟨k, hk⟩ := hthin
    have hc : p ∈ P.gluedMk '' P.seamNeighborhood k :=
      P.closedThinSeamCollar_subset_original_collar k
        (P.thinSeamCollar_subset_closedThinSeamCollar k hk)
    let θ := P.seamSmoothingAngle k ⟨p, hc⟩
    have hp : p ∈ (P.seamAngularComplexChart k θ).source :=
      P.mem_seamSmoothingAngle_chart k ⟨p, hc⟩
    let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    let i : atlas ℂ P.GluedCarrier := ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
    let w := (Z.localTriv i).continuousLinearMapAt ℝ p v
    have hv : (Z.localTriv i).symmL ℝ p w = v :=
      (Z.localTriv i).symmL_continuousLinearMapAt (by exact hp) v
    rw [← hv, P.gluedSmoothTangentInner_in_thin_seam_chart ε k θ p hp hk w w,
      P.gluedTangentInner_in_chart _ (Or.inr ⟨k, θ, rfl⟩) p hp w w,
      P.gluingChartTangentForm_seam]
    have h := (gluingComplexCollarLocalizedSmoothTangentForm_bounds
      (b := P.seamSmoothingCutoff) P.radius_pos hε
      (P.seamAngularComplexChart k θ p) w).2
    simpa only [gluingComplexCollarLocalizedSmoothTangentForm_apply] using h
  · have hout : ∀ k : Fin (n - 1), p ∉ P.thinSeamCollar k := by
      simpa only [not_exists] using hthin
    rw [P.gluedSmoothTangentInner_eq_native_of_outside_thinCollars ε p hout]
    have hv : 0 ≤ P.gluedTangentInner p v v := by
      by_cases h : v = 0
      · simp [h]
      · exact (P.gluedTangentInner_pos p v h).le
    have hK := gluingCollarSmoothMetricFactor_ge_one P.radius_pos hε
    have hsq : 1 ≤ gluingCollarSmoothMetricFactor (gluingRadius C g) ε ^ 2 := by
      nlinarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq hv

theorem gluedSmoothTangentInner_sqrt_bounds
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 ≤ ε)
    (p : P.GluedCarrier) (v : TangentSpace (modelWithCornersSelf ℝ ℂ) p) :
    Real.sqrt (P.gluedTangentInner p v v) ≤ Real.sqrt (P.gluedSmoothTangentInner ε p v v) ∧
      Real.sqrt (P.gluedSmoothTangentInner ε p v v) ≤
        gluingCollarSmoothMetricFactor (gluingRadius C g) ε * Real.sqrt (P.gluedTangentInner p v v) := by
  obtain ⟨hlo, hhi⟩ := P.gluedSmoothTangentInner_bounds hε p v
  refine ⟨Real.sqrt_le_sqrt hlo, ?_⟩
  calc
    _ ≤ Real.sqrt (gluingCollarSmoothMetricFactor (gluingRadius C g) ε ^ 2 *
        P.gluedTangentInner p v v) := Real.sqrt_le_sqrt hhi
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq
        (zero_le_one.trans (gluingCollarSmoothMetricFactor_ge_one P.radius_pos hε))]

/-- Explicit actual bundle data, without replacing any ambient instance. -/
@[instance_reducible]
def gluedSmoothRiemannianBundle (P : ExerciseGluingPreparation C g n genera X)
    (ε : ℝ) (hε : 0 ≤ ε) :
    RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
  ⟨(P.gluedSmoothContinuousRiemannianMetric ε hε).toRiemannianMetric⟩

/-- The genuine native tangent path length, retained for comparison. -/
def gluedNativePathELength (P : ExerciseGluingPreparation C g n genera X)
    (γ : ℝ → P.GluedCarrier) (a b : ℝ) : ℝ≥0∞ := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  exact pathELength (modelWithCornersSelf ℝ ℂ) γ a b

/-- Length in the actual globally patched bundle. -/
def gluedSmoothPathELength (P : ExerciseGluingPreparation C g n genera X)
    (ε : ℝ) (hε : 0 ≤ ε) (γ : ℝ → P.GluedCarrier) (a b : ℝ) : ℝ≥0∞ := by
  letI := P.gluedSmoothRiemannianBundle ε hε
  exact pathELength (modelWithCornersSelf ℝ ℂ) γ a b

set_option backward.isDefEq.respectTransparency false in
theorem gluedNativePathELength_eq_lintegral
    (P : ExerciseGluingPreparation C g n genera X)
    (γ : ℝ → P.GluedCarrier) (a b : ℝ) :
    P.gluedNativePathELength γ a b = ∫⁻ t in Icc a b, ENNReal.ofReal
      (Real.sqrt (P.gluedTangentInner (γ t)
        (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1)
        (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1))) := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  unfold gluedNativePathELength
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t _
  dsimp only
  have hsq : ‖mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1‖ ^ 2 =
      P.gluedTangentInner (γ t)
        (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1)
        (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1) :=
    (real_inner_self_eq_norm_sq _).symm
  rw [← hsq, Real.sqrt_sq (norm_nonneg _), ofReal_norm]

set_option backward.isDefEq.respectTransparency false in
theorem gluedSmoothPathELength_eq_lintegral
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 ≤ ε)
    (γ : ℝ → P.GluedCarrier) (a b : ℝ) :
    P.gluedSmoothPathELength ε hε γ a b = ∫⁻ t in Icc a b, ENNReal.ofReal
      (Real.sqrt (P.gluedSmoothTangentInner ε (γ t)
        (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1)
        (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1))) := by
  letI := P.gluedSmoothRiemannianBundle ε hε
  unfold gluedSmoothPathELength
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t _
  dsimp only
  have hsq : ‖mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1‖ ^ 2 =
      P.gluedSmoothTangentInner ε (γ t)
        (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1)
        (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1) :=
    (real_inner_self_eq_norm_sq _).symm
  rw [← hsq, Real.sqrt_sq (norm_nonneg _), ofReal_norm]

/-- The same factor compares all literal native and smooth curve lengths. -/
theorem gluedSmoothPathELength_bounds
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 ≤ ε)
    (γ : ℝ → P.GluedCarrier) (a b : ℝ) :
    P.gluedNativePathELength γ a b ≤ P.gluedSmoothPathELength ε hε γ a b ∧
      P.gluedSmoothPathELength ε hε γ a b ≤
        ENNReal.ofReal (gluingCollarSmoothMetricFactor (gluingRadius C g) ε) *
          P.gluedNativePathELength γ a b := by
  rw [P.gluedNativePathELength_eq_lintegral, P.gluedSmoothPathELength_eq_lintegral]
  have hK : 0 ≤ gluingCollarSmoothMetricFactor (gluingRadius C g) ε :=
    zero_le_one.trans (gluingCollarSmoothMetricFactor_ge_one P.radius_pos hε)
  constructor
  · apply lintegral_mono
    intro t
    exact ENNReal.ofReal_le_ofReal (P.gluedSmoothTangentInner_sqrt_bounds hε (γ t) _).1
  · calc
      _ ≤ ∫⁻ t in Icc a b, ENNReal.ofReal (gluingCollarSmoothMetricFactor (gluingRadius C g) ε) *
          ENNReal.ofReal (Real.sqrt (P.gluedTangentInner (γ t)
            (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1)
            (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1))) := by
        apply lintegral_mono
        intro t
        dsimp only
        rw [← ENNReal.ofReal_mul hK]
        exact ENNReal.ofReal_le_ofReal (P.gluedSmoothTangentInner_sqrt_bounds hε (γ t) _).2
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Actual intrinsic distance of the globally patched native bundle. -/
def gluedSmoothIntrinsicEDist (P : ExerciseGluingPreparation C g n genera X)
    (ε : ℝ) (hε : 0 ≤ ε) (x y : P.GluedCarrier) : ℝ≥0∞ := by
  letI := P.gluedSmoothRiemannianBundle ε hε
  exact riemannianEDist (modelWithCornersSelf ℝ ℂ) x y

/-- Native topology retained by the genuine Riemannian extended metric. -/
@[instance_reducible]
def gluedSmoothIntrinsicEMetricSpace (P : ExerciseGluingPreparation C g n genera X)
    (ε : ℝ) (hε : 0 ≤ ε) : EMetricSpace P.GluedCarrier := by
  letI := P.gluedSmoothRiemannianBundle ε hε
  exact EMetricSpace.ofRiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier

theorem gluedSmoothIntrinsicEMetricSpace_edist
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 ≤ ε)
    (x y : P.GluedCarrier) :
    letI := P.gluedSmoothIntrinsicEMetricSpace ε hε
    edist x y = P.gluedSmoothIntrinsicEDist ε hε x y := rfl

theorem gluedSmoothIntrinsicEDist_le_pathELength
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 ≤ ε)
    {γ : ℝ → P.GluedCarrier} {a b : ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ (Icc a b))
    (hab : a ≤ b) :
    P.gluedSmoothIntrinsicEDist ε hε (γ a) (γ b) ≤ P.gluedSmoothPathELength ε hε γ a b := by
  letI := P.gluedSmoothRiemannianBundle ε hε
  exact riemannianEDist_le_pathELength hγ rfl rfl hab

/-- Near-minimizing genuine C¹ curves turn the proved tensor comparison
into a two-sided comparison of the constructed intrinsic distances. -/
theorem gluedSmoothIntrinsicEDist_bounds
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 ≤ ε)
    (x y : P.GluedCarrier) :
    P.gluedIntrinsicEDist x y ≤ P.gluedSmoothIntrinsicEDist ε hε x y ∧
      P.gluedSmoothIntrinsicEDist ε hε x y ≤
        ENNReal.ofReal (gluingCollarSmoothMetricFactor (gluingRadius C g) ε) *
          P.gluedIntrinsicEDist x y := by
  constructor
  · by_contra h
    have hlt : P.gluedSmoothIntrinsicEDist ε hε x y < P.gluedIntrinsicEDist x y := lt_of_not_ge h
    letI := P.gluedSmoothRiemannianBundle ε hε
    change riemannianEDist (modelWithCornersSelf ℝ ℂ) x y < P.gluedIntrinsicEDist x y at hlt
    obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hlt
    change P.gluedSmoothPathELength ε hε γ 0 1 < P.gluedIntrinsicEDist x y at hlen
    have hold : P.gluedIntrinsicEDist (γ 0) (γ 1) ≤ P.gluedNativePathELength γ 0 1 := by
      letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
        ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
      exact P.gluedIntrinsicEDist_le_pathELength hγ zero_le_one
    rw [h0, h1] at hold
    exact (not_lt_of_ge (hold.trans (P.gluedSmoothPathELength_bounds ε hε γ 0 1).1)) hlen
  · have hKpos : 0 < gluingCollarSmoothMetricFactor (gluingRadius C g) ε :=
      zero_lt_one.trans_le (gluingCollarSmoothMetricFactor_ge_one P.radius_pos hε)
    have hK0 : ENNReal.ofReal (gluingCollarSmoothMetricFactor (gluingRadius C g) ε) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hKpos).ne'
    have hKfin : ENNReal.ofReal (gluingCollarSmoothMetricFactor (gluingRadius C g) ε) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    by_contra h
    have hlt : ENNReal.ofReal (gluingCollarSmoothMetricFactor (gluingRadius C g) ε) *
        P.gluedIntrinsicEDist x y < P.gluedSmoothIntrinsicEDist ε hε x y := lt_of_not_ge h
    have hnear : P.gluedIntrinsicEDist x y < P.gluedSmoothIntrinsicEDist ε hε x y /
        ENNReal.ofReal (gluingCollarSmoothMetricFactor (gluingRadius C g) ε) :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl hK0) (Or.inl hKfin)).mpr
        (by simpa only [mul_comm] using hlt)
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    change riemannianEDist (modelWithCornersSelf ℝ ℂ) x y <
      P.gluedSmoothIntrinsicEDist ε hε x y /
        ENNReal.ofReal (gluingCollarSmoothMetricFactor (gluingRadius C g) ε) at hnear
    obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hnear
    change P.gluedNativePathELength γ 0 1 < P.gluedSmoothIntrinsicEDist ε hε x y /
      ENNReal.ofReal (gluingCollarSmoothMetricFactor (gluingRadius C g) ε) at hlen
    have hnew := P.gluedSmoothIntrinsicEDist_le_pathELength ε hε hγ zero_le_one
    rw [h0, h1] at hnew
    have hbound := hnew.trans (P.gluedSmoothPathELength_bounds ε hε γ 0 1).2
    have hstrict := ENNReal.mul_lt_mul_right hK0 hKfin hlen
    rw [ENNReal.mul_div_cancel hK0 hKfin] at hstrict
    exact (not_lt_of_ge hbound) hstrict

theorem gluedSmoothIntrinsicEDist_lt_top
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 ≤ ε)
    (x y : P.GluedCarrier) : P.gluedSmoothIntrinsicEDist ε hε x y < ⊤ :=
  lt_of_le_of_lt (P.gluedSmoothIntrinsicEDist_bounds ε hε x y).2
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (P.gluedIntrinsicEDist_lt_top x y))

/-- A finite genuine metric on the original glued carrier. -/
@[instance_reducible]
def gluedSmoothIntrinsicMetricSpace (P : ExerciseGluingPreparation C g n genera X)
    (ε : ℝ) (hε : 0 ≤ ε) : MetricSpace P.GluedCarrier := by
  letI := P.gluedSmoothIntrinsicEMetricSpace ε hε
  exact EMetricSpace.toMetricSpace (fun x y => (P.gluedSmoothIntrinsicEDist_lt_top ε hε x y).ne)

theorem gluedSmoothIntrinsicMetricSpace_topology
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 ≤ ε) :
    (P.gluedSmoothIntrinsicMetricSpace ε hε).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace P.GluedCarrier) := rfl

theorem gluedSmoothIntrinsicMetricSpace_compact
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 ≤ ε) :
    letI := P.gluedSmoothIntrinsicMetricSpace ε hε
    CompactSpace P.GluedCarrier := inferInstance

/-- The actual finite metric's extended distance is exactly the distance
of the constructed native Riemannian bundle, not an imposed identification. -/
theorem gluedSmoothIntrinsicMetricSpace_isRiemannian
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 ≤ ε) :
    letI := P.gluedSmoothRiemannianBundle ε hε
    letI := P.gluedSmoothIntrinsicMetricSpace ε hε
    IsRiemannianManifold (modelWithCornersSelf ℝ ℂ) P.GluedCarrier := by
  letI := P.gluedSmoothRiemannianBundle ε hε
  letI := P.gluedSmoothIntrinsicMetricSpace ε hε
  exact ⟨fun _ _ => rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem gluedSmoothIntrinsicMetricSpace_dist
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 ≤ ε)
    (x y : P.GluedCarrier) :
    @dist P.GluedCarrier (P.gluedSmoothIntrinsicMetricSpace ε hε).toDist x y =
      (P.gluedSmoothIntrinsicEDist ε hε x y).toReal := rfl

theorem gluedSmoothIntrinsicDist_bounds
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 ≤ ε)
    (x y : P.GluedCarrier) :
    @dist P.GluedCarrier P.gluedCarrierIntrinsicMetricSpace.toDist x y ≤
      @dist P.GluedCarrier (P.gluedSmoothIntrinsicMetricSpace ε hε).toDist x y ∧
      @dist P.GluedCarrier (P.gluedSmoothIntrinsicMetricSpace ε hε).toDist x y ≤
        gluingCollarSmoothMetricFactor (gluingRadius C g) ε *
          @dist P.GluedCarrier P.gluedCarrierIntrinsicMetricSpace.toDist x y := by
  change (P.gluedIntrinsicEDist x y).toReal ≤ (P.gluedSmoothIntrinsicEDist ε hε x y).toReal ∧
    (P.gluedSmoothIntrinsicEDist ε hε x y).toReal ≤
      gluingCollarSmoothMetricFactor (gluingRadius C g) ε * (P.gluedIntrinsicEDist x y).toReal
  obtain ⟨hlo, hhi⟩ := P.gluedSmoothIntrinsicEDist_bounds ε hε x y
  refine ⟨ENNReal.toReal_mono (P.gluedSmoothIntrinsicEDist_lt_top ε hε x y).ne hlo, ?_⟩
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (P.gluedIntrinsicEDist_lt_top x y).ne) hhi
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (zero_le_one.trans (gluingCollarSmoothMetricFactor_ge_one P.radius_pos hε))] using h

/-- The actual original compact metric's diameter. -/
def gluedIntrinsicDiameter (P : ExerciseGluingPreparation C g n genera X) : ℝ := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  exact Metric.diam (univ : Set P.GluedCarrier)

theorem gluedIntrinsicDist_le_diameter
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier) :
    @dist P.GluedCarrier P.gluedCarrierIntrinsicMetricSpace.toDist x y ≤ P.gluedIntrinsicDiameter := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  letI : CompactSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace_compact
  exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)

/-- Explicit global uniform error; its constant is from the original
constructed compact metric and does not depend on smoothing. -/
theorem gluedSmoothIntrinsicDist_uniform_bound
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 ≤ ε)
    (x y : P.GluedCarrier) :
    |@dist P.GluedCarrier (P.gluedSmoothIntrinsicMetricSpace ε hε).toDist x y -
      @dist P.GluedCarrier P.gluedCarrierIntrinsicMetricSpace.toDist x y| ≤
        (Real.cosh (gluingRadius C g) / Real.sinh (gluingRadius C g)) * ε * P.gluedIntrinsicDiameter := by
  obtain ⟨hlo, hhi⟩ := P.gluedSmoothIntrinsicDist_bounds ε hε x y
  have hq : 0 ≤ (Real.cosh (gluingRadius C g) / Real.sinh (gluingRadius C g)) * ε :=
    mul_nonneg (div_nonneg (Real.cosh_pos _).le (Real.sinh_pos_iff.mpr P.radius_pos).le) hε
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  have hmul := mul_le_mul_of_nonneg_left (P.gluedIntrinsicDist_le_diameter x y) hq
  unfold gluingCollarSmoothMetricFactor at hhi
  nlinarith only [hhi, hmul]

/-- The actual constructed finite distances converge uniformly on every
endpoint pair as the nonnegative smoothing parameter tends to zero. -/
theorem gluedSmoothIntrinsicDist_tendstoUniformly
    (P : ExerciseGluingPreparation C g n genera X) :
    TendstoUniformly
      (fun ε : ℝ≥0 => fun xy : P.GluedCarrier × P.GluedCarrier =>
        @dist P.GluedCarrier (P.gluedSmoothIntrinsicMetricSpace (ε : ℝ) ε.property).toDist xy.1 xy.2)
      (fun xy : P.GluedCarrier × P.GluedCarrier =>
        @dist P.GluedCarrier P.gluedCarrierIntrinsicMetricSpace.toDist xy.1 xy.2)
      (𝓝 0) := by
  have hlim : Tendsto (fun ε : ℝ≥0 =>
      (Real.cosh (gluingRadius C g) / Real.sinh (gluingRadius C g)) * (ε : ℝ) *
        P.gluedIntrinsicDiameter) (𝓝 0) (𝓝 0) := by
    simpa using ((NNReal.continuous_coe.tendsto (0 : ℝ≥0)).const_mul
      (Real.cosh (gluingRadius C g) / Real.sinh (gluingRadius C g))).mul_const P.gluedIntrinsicDiameter
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with ε hε xy
  rw [Real.dist_eq, abs_sub_comm]
  exact (P.gluedSmoothIntrinsicDist_uniform_bound (ε : ℝ) ε.property xy.1 xy.2).trans_lt hε

#print axioms gluedSmoothTangentInner_bounds
#print axioms gluedSmoothPathELength_bounds
#print axioms gluedSmoothIntrinsicEDist_bounds
#print axioms gluedSmoothIntrinsicMetricSpace
#print axioms gluedSmoothIntrinsicMetricSpace_topology
#print axioms gluedSmoothIntrinsicMetricSpace_isRiemannian
#print axioms gluedSmoothIntrinsicDist_uniform_bound
#print axioms gluedSmoothIntrinsicDist_tendstoUniformly

end
end SystolicGrowth.ExerciseGluingPreparation

module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainSmoothMetric
public import Geometry.GluingChainSmoothDistance
public import Geometry.GluingChainSmoothRegularity
public import Geometry.GluingCurvatureBoundedWarp
public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

@[expose] public section

/-!
# The ODE collar warp as a metric on the original glued surface

Use the normalized forcing profile, rather than the preliminary localized
approximation, as the angular coefficient in the actual native tangent
bundle. The patch is supported in the existing disjoint seam collars.
-/

open Set Filter Bundle Manifold ContinuousLinearMap MeasureTheory
open scoped Manifold Topology ContDiff ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Difference of squared angular coefficients for the ODE collar and native
hyperbolic collar. -/
def seamCurvatureCorrectionWeight (P : ExerciseGluingPreparation C g n genera X)
    (t : ℝ) : ℝ :=
  gluingCurvatureBoundedWarp (gluingRadius C g) (gluingThinSeamWidth C g)
    P.thinSeamWidth_pos t ^ 2 - gluingCollarWarp (gluingRadius C g) t ^ 2

theorem seamCurvatureCorrectionWeight_nonneg
    (P : ExerciseGluingPreparation C g n genera X) (t : ℝ) :
    0 ≤ P.seamCurvatureCorrectionWeight t := by
  have hn := gluingCollarWarp_pos P.radius_pos t
  have hb := gluingCurvatureBoundedWarp_ge_native_all (gluingRadius C g)
    (gluingThinSeamWidth C g) P.thinSeamWidth_pos t
  unfold seamCurvatureCorrectionWeight
  nlinarith

theorem seamCurvatureCorrectionWeight_eq_zero
    (P : ExerciseGluingPreparation C g n genera X) {t : ℝ}
    (ht : gluingThinSeamWidth C g ≤ |t|) :
    P.seamCurvatureCorrectionWeight t = 0 := by
  unfold seamCurvatureCorrectionWeight
  rw [gluingCurvatureBoundedWarp_eq_native_of_abs_ge_strip
    (gluingRadius C g) (gluingThinSeamWidth C g) P.thinSeamWidth_pos ht, sub_self]

theorem seamCurvatureCorrectionWeight_continuous
    (P : ExerciseGluingPreparation C g n genera X) :
    Continuous P.seamCurvatureCorrectionWeight := by
  unfold seamCurvatureCorrectionWeight
  exact ((gluingCurvatureBoundedWarp_contDiff (gluingRadius C g)
      (gluingThinSeamWidth C g) P.thinSeamWidth_pos).continuous.pow 2).sub
    ((gluingCollarWarp_continuous _).pow 2)

/-- The radial coordinate in the real angular chart agrees with the
corresponding coordinate in the seam-cylinder homeomorphism. -/
private theorem curvature_seam_chart_radial_eq_cylinder
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source)
    (hc : b ∈ P.gluedMk '' P.seamNeighborhood k) :
    (P.seamAngularComplexChart k θ b).re =
      ((P.seamCylinderHomeomorph k).symm ⟨b, hc⟩).2.1 := by
  rw [P.seamAngularComplexChart_source] at hb
  obtain ⟨p, rfl⟩ := hb
  rw [P.seamAngularComplexChart_apply, gluingSeamAngularModel_re]
  have heq : (⟨P.seamAngularPoint k θ p, hc⟩ : P.gluedMk '' P.seamNeighborhood k) =
      P.seamCylinderHomeomorph k (Circle.exp p.2.1, p.1) := Subtype.ext rfl
  rw [heq, Homeomorph.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Native angular rank-one correction using the ODE-profile coefficient. -/
def seamCurvatureTangentCorrection
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (b : P.GluedCarrier) : TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ := by
  classical
  exact if hb : b ∈ P.gluedMk '' P.seamNeighborhood k then
    let c : P.gluedMk '' P.seamNeighborhood k := ⟨b, hb⟩
    let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    let j := P.seamSmoothingChartIndex k c
    let L : TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ :=
      Complex.imCLM.comp (Z.coordChange (achart ℂ b) j b)
    P.seamCurvatureCorrectionWeight ((P.seamCylinderHomeomorph k).symm c).2.1 •
      L.smulRight L
  else 0

set_option backward.isDefEq.respectTransparency false in
theorem seamCurvatureTangentCorrection_apply_of_mem
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (b : P.GluedCarrier) (hb : b ∈ P.gluedMk '' P.seamNeighborhood k)
    (v u : TangentSpace (modelWithCornersSelf ℝ ℂ) b) :
    P.seamCurvatureTangentCorrection k b v u =
      P.seamCurvatureCorrectionWeight ((P.seamCylinderHomeomorph k).symm ⟨b, hb⟩).2.1 *
        (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).coordChange
          (achart ℂ b) (P.seamSmoothingChartIndex k ⟨b, hb⟩) b v).im *
        ((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).coordChange
          (achart ℂ b) (P.seamSmoothingChartIndex k ⟨b, hb⟩) b u).im) := by
  classical
  unfold seamCurvatureTangentCorrection
  rw [dif_pos hb]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem seamCurvatureTangentCorrection_symm
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (b : P.GluedCarrier) (v u : TangentSpace (modelWithCornersSelf ℝ ℂ) b) :
    P.seamCurvatureTangentCorrection k b v u =
      P.seamCurvatureTangentCorrection k b u v := by
  classical
  by_cases hb : b ∈ P.gluedMk '' P.seamNeighborhood k
  · rw [P.seamCurvatureTangentCorrection_apply_of_mem k b hb,
      P.seamCurvatureTangentCorrection_apply_of_mem k b hb]
    ring
  · simp [seamCurvatureTangentCorrection, hb]

set_option backward.isDefEq.respectTransparency false in
theorem seamCurvatureTangentCorrection_nonneg
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (b : P.GluedCarrier) (v : TangentSpace (modelWithCornersSelf ℝ ℂ) b) :
    0 ≤ P.seamCurvatureTangentCorrection k b v v := by
  classical
  by_cases hb : b ∈ P.gluedMk '' P.seamNeighborhood k
  · rw [P.seamCurvatureTangentCorrection_apply_of_mem k b hb]
    exact mul_nonneg (P.seamCurvatureCorrectionWeight_nonneg _)
      (mul_self_nonneg _)
  · simp [seamCurvatureTangentCorrection, hb]

set_option backward.isDefEq.respectTransparency false in
theorem seamCurvatureTangentCorrection_eq_zero_of_not_mem_thinSeamCollar
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (b : P.GluedCarrier) (hb : b ∉ P.thinSeamCollar k) :
    P.seamCurvatureTangentCorrection k b = 0 := by
  classical
  by_cases hc : b ∈ P.gluedMk '' P.seamNeighborhood k
  · have hr : gluingThinSeamWidth C g ≤
        |((P.seamCylinderHomeomorph k).symm ⟨b, hc⟩).2.1| := by
      by_contra h
      apply hb
      have hh := (P.seamCylinderHomeomorph_mem_thinSeamCollar_iff k
        ((P.seamCylinderHomeomorph k).symm ⟨b, hc⟩)).mpr (lt_of_not_ge h)
      simpa only [Homeomorph.apply_symm_apply] using hh
    ext v u
    rw [P.seamCurvatureTangentCorrection_apply_of_mem k b hc,
      P.seamCurvatureCorrectionWeight_eq_zero hr]
    simp
  · simp [seamCurvatureTangentCorrection, hc]

set_option backward.isDefEq.respectTransparency false in
theorem seamCurvatureTangentCorrection_in_seam_chart
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source)
    (v u : ℂ) :
    let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    let i : atlas ℂ P.GluedCarrier :=
      ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
    P.seamCurvatureTangentCorrection k b ((Z.localTriv i).symmL ℝ b v)
      ((Z.localTriv i).symmL ℝ b u) =
      P.seamCurvatureCorrectionWeight (P.seamAngularComplexChart k θ b).re * v.im * u.im := by
  classical
  dsimp only
  have hc : b ∈ P.gluedMk '' P.seamNeighborhood k := by
    rw [P.seamAngularComplexChart_source] at hb
    obtain ⟨p, rfl⟩ := hb
    exact (P.seamCylinderHomeomorph k (Circle.exp p.2.1, p.1)).2
  let c : P.gluedMk '' P.seamNeighborhood k := ⟨b, hc⟩
  let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
  let i : atlas ℂ P.GluedCarrier :=
    ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
  let j := P.seamSmoothingChartIndex k c
  have hj : b ∈ j.1.source := P.mem_seamSmoothingAngle_chart k c
  have hx : P.seamAngularComplexChart k θ b ∈
      ((P.seamAngularComplexChart k θ).symm.trans
        (P.seamAngularComplexChart k (P.seamSmoothingAngle k c))).source := by
    refine ⟨(P.seamAngularComplexChart k θ).map_source hb, ?_⟩
    change (P.seamAngularComplexChart k θ).symm (P.seamAngularComplexChart k θ b) ∈ j.1.source
    rw [(P.seamAngularComplexChart k θ).left_inv hb]
    exact hj
  have hD : Z.coordChange i j b = ContinuousLinearMap.id ℝ ℂ := by
    rw [P.gluedTangentCoordChange_eq_fderiv]
    exact (P.seamAngularComplexChart_transition_hasFDerivAt k θ
      (P.seamSmoothingAngle k c) hx).fderiv
  have hs (w : ℂ) :
      Z.coordChange (achart ℂ b) j b ((Z.localTriv i).symmL ℝ b w) = w := by
    rw [Z.localTriv_symmL (by exact hb)]
    change Z.coordChange (achart ℂ b) j b (Z.coordChange i (achart ℂ b) b w) = w
    rw [Z.coordChange_comp i (achart ℂ b) j b
      ⟨⟨hb, mem_chart_source ℂ b⟩, hj⟩, hD, ContinuousLinearMap.id_apply]
  rw [P.seamCurvatureTangentCorrection_apply_of_mem k b hc]
  change P.seamCurvatureCorrectionWeight ((P.seamCylinderHomeomorph k).symm c).2.1 *
      ((Z.coordChange (achart ℂ b) j b ((Z.localTriv i).symmL ℝ b v)).im *
      (Z.coordChange (achart ℂ b) j b ((Z.localTriv i).symmL ℝ b u)).im) = _
  rw [hs v, hs u, curvature_seam_chart_radial_eq_cylinder P k θ b hb hc]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem seamCurvatureTangentCorrection_in_chart_of_seam
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source)
    (hseam : b ∈ (P.seamAngularComplexChart k θ).source) (v u : ℂ) :
    let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    let i : atlas ℂ P.GluedCarrier := ⟨e, he⟩
    let j : atlas ℂ P.GluedCarrier :=
      ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
    P.seamCurvatureTangentCorrection k b ((Z.localTriv i).symmL ℝ b v)
      ((Z.localTriv i).symmL ℝ b u) =
      P.seamCurvatureCorrectionWeight (P.seamAngularComplexChart k θ b).re *
        (Z.coordChange i j b v).im * (Z.coordChange i j b u).im := by
  dsimp only
  let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
  let i : atlas ℂ P.GluedCarrier := ⟨e, he⟩
  let j : atlas ℂ P.GluedCarrier :=
    ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
  have hs (w : ℂ) : (Z.localTriv i).symmL ℝ b w =
      (Z.localTriv j).symmL ℝ b (Z.coordChange i j b w) := by
    rw [Z.localTriv_symmL (by exact hb), Z.localTriv_symmL (by exact hseam)]
    change Z.coordChange i (achart ℂ b) b w =
      Z.coordChange j (achart ℂ b) b (Z.coordChange i j b w)
    exact (Z.coordChange_comp i j (achart ℂ b) b
      ⟨⟨hb, hseam⟩, mem_chart_source ℂ b⟩ w).symm
  change P.seamCurvatureTangentCorrection k b ((Z.localTriv i).symmL ℝ b v)
    ((Z.localTriv i).symmL ℝ b u) = _
  rw [hs v, hs u]
  exact P.seamCurvatureTangentCorrection_in_seam_chart k θ b hseam _ _

set_option backward.isDefEq.respectTransparency false in
private theorem seamCurvatureTangentCorrection_in_preferred_coordinates
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b₀ b : P.GluedCarrier) (hb : b ∈ (chartAt ℂ b₀).source)
    (hseam : b ∈ (P.seamAngularComplexChart k θ).source) :
    inCoordinates ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)
      (ℂ →L[ℝ] ℝ) (fun b => TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ)
      b₀ b b₀ b (P.seamCurvatureTangentCorrection k b) =
      let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
      let j : atlas ℂ P.GluedCarrier :=
        ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
      let L := Complex.imCLM.comp (Z.coordChange (achart ℂ b₀) j b)
      P.seamCurvatureCorrectionWeight (P.seamAngularComplexChart k θ b).re • L.smulRight L := by
  dsimp only
  have ht : b ∈ (trivializationAt ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) b₀).baseSet := hb
  ext v u
  rw [inCoordinates_apply_eq₂ ht ht (mem_univ b)]
  have hr (a : ℝ) :
      (trivializationAt ℝ (fun _ : P.GluedCarrier => ℝ) b₀).linearMapAt ℝ b a = a := by
    change (Bundle.Trivial.trivialization P.GluedCarrier ℝ).linearMapAt ℝ b a = a
    rw [Bundle.Trivial.linearMapAt_trivialization]
    rfl
  rw [hr]
  have hs (w : ℂ) :
      (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) b₀).symm b w =
      ((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
        (achart ℂ b₀)).symmL ℝ b w := by
    exact ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) b₀).symmL_apply ht w).symm
  rw [hs v, hs u]
  have h := P.seamCurvatureTangentCorrection_in_chart_of_seam k θ (chartAt ℂ b₀)
    (chart_mem_atlas ℂ b₀) b hb hseam v u
  apply h.trans
  change _ = P.seamCurvatureCorrectionWeight (P.seamAngularComplexChart k θ b).re *
    (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).coordChange
      (achart ℂ b₀) ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩ b v).im *
    ((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).coordChange
      (achart ℂ b₀) ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩ b u).im)
  simp only [achart]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem seamCurvatureTangentCorrection_continuous_section
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    Continuous (fun b : P.GluedCarrier => TotalSpace.mk' (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
      b (P.seamCurvatureTangentCorrection k b)) := by
  rw [continuous_iff_continuousAt]
  intro b₀
  by_cases hc : b₀ ∈ P.gluedMk '' P.seamNeighborhood k
  · let θ := P.seamSmoothingAngle k ⟨b₀, hc⟩
    have hs : b₀ ∈ (P.seamAngularComplexChart k θ).source :=
      P.mem_seamSmoothingAngle_chart k ⟨b₀, hc⟩
    let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    let j : atlas ℂ P.GluedCarrier :=
      ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
    have hD : ContinuousAt (Z.coordChange (achart ℂ b₀) j) b₀ :=
      (Z.continuousOn_coordChange (achart ℂ b₀) j).continuousAt
        (((Z.isOpen_baseSet (achart ℂ b₀)).inter (Z.isOpen_baseSet j)).mem_nhds
          ⟨mem_chart_source ℂ b₀, hs⟩)
    have hL : ContinuousAt
        (fun b => Complex.imCLM.comp (Z.coordChange (achart ℂ b₀) j b)) b₀ :=
      continuousAt_const.clm_comp hD
    have hR : Continuous
        (fun p : (ℂ →L[ℝ] ℝ) × (ℂ →L[ℝ] ℝ) => p.1.smulRight p.2) :=
      (isBoundedBilinearMap_smulRight (𝕜 := ℝ)).continuous
    have hW : ContinuousAt (fun b : P.GluedCarrier =>
        P.seamCurvatureCorrectionWeight (P.seamAngularComplexChart k θ b).re) b₀ :=
      (P.seamCurvatureCorrectionWeight_continuous).continuousAt.comp
        (Complex.continuous_re.continuousAt.comp
          ((P.seamAngularComplexChart k θ).continuousAt hs))
    have hform := hW.smul (hR.continuousAt.comp (hL.prodMk hL))
    rw [FiberBundle.continuousAt_section]
    apply hform.congr_of_eventuallyEq
    filter_upwards [(chartAt ℂ b₀).open_source.mem_nhds (mem_chart_source ℂ b₀),
      (P.seamAngularComplexChart k θ).open_source.mem_nhds hs] with b hb hseam
    rw [hom_trivializationAt_apply]
    exact P.seamCurvatureTangentCorrection_in_preferred_coordinates k θ b₀ b hb hseam
  · have hclosed : b₀ ∉ P.closedThinSeamCollar k := fun h =>
      hc (P.closedThinSeamCollar_subset_original_collar k h)
    letI : ∀ b : P.GluedCarrier, AddCommMonoid
        (TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ]
          TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ) := fun _ =>
      inferInstanceAs (AddCommMonoid (ℂ →L[ℝ] ℂ →L[ℝ] ℝ))
    letI : ∀ b : P.GluedCarrier, ContinuousAdd
        (TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ) := fun _ =>
      inferInstanceAs (ContinuousAdd (ℂ →L[ℝ] ℝ))
    have hz : Continuous (fun b : P.GluedCarrier =>
        TotalSpace.mk' (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) b
          (0 : TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ]
            TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ)) :=
      Bundle.Trivialization.continuous_zeroSection ℝ
    apply hz.continuousAt.congr_of_eventuallyEq
    filter_upwards [(P.closedThinSeamCollar_isCompact k).isClosed.isOpen_compl.mem_nhds hclosed]
      with b hb
    rw [P.seamCurvatureTangentCorrection_eq_zero_of_not_mem_thinSeamCollar k b
      (fun h => hb (P.thinSeamCollar_subset_closedThinSeamCollar k h))]

set_option backward.isDefEq.respectTransparency false in
def gluedCurvatureTangentInner (P : ExerciseGluingPreparation C g n genera X)
    (b : P.GluedCarrier) : TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ :=
  P.gluedTangentInner b + ∑ k : Fin (n - 1), P.seamCurvatureTangentCorrection k b

set_option backward.isDefEq.respectTransparency false in
theorem gluedCurvatureTangentInner_symm
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier)
    (v u : TangentSpace (modelWithCornersSelf ℝ ℂ) b) :
    P.gluedCurvatureTangentInner b v u = P.gluedCurvatureTangentInner b u v := by
  simp only [gluedCurvatureTangentInner, add_apply, sum_apply]
  rw [P.gluedTangentInner_symm b v u]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact P.seamCurvatureTangentCorrection_symm k b v u

set_option backward.isDefEq.respectTransparency false in
theorem gluedTangentInner_le_gluedCurvatureTangentInner
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier)
    (v : TangentSpace (modelWithCornersSelf ℝ ℂ) b) :
    P.gluedTangentInner b v v ≤ P.gluedCurvatureTangentInner b v v := by
  simp only [gluedCurvatureTangentInner, add_apply, sum_apply, le_add_iff_nonneg_right]
  exact Finset.sum_nonneg (fun k _ => P.seamCurvatureTangentCorrection_nonneg k b v)

set_option backward.isDefEq.respectTransparency false in
theorem gluedCurvatureTangentInner_pos
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier)
    (v : TangentSpace (modelWithCornersSelf ℝ ℂ) b) (hv : v ≠ 0) :
    0 < P.gluedCurvatureTangentInner b v v :=
  (P.gluedTangentInner_pos b v hv).trans_le
    (P.gluedTangentInner_le_gluedCurvatureTangentInner b v)

set_option backward.isDefEq.respectTransparency false in
theorem gluedCurvatureTangentInner_isVonNBounded
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    Bornology.IsVonNBounded ℝ
      {v : TangentSpace (modelWithCornersSelf ℝ ℂ) b | P.gluedCurvatureTangentInner b v v < 1} :=
  (P.gluedTangentInner_isVonNBounded b).subset (fun v hv =>
    (P.gluedTangentInner_le_gluedCurvatureTangentInner b v).trans_lt hv)

set_option backward.isDefEq.respectTransparency false in
theorem gluedCurvatureTangentInner_eq_native_of_outside_thinCollars
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier)
    (hb : ∀ k : Fin (n - 1), b ∉ P.thinSeamCollar k) :
    P.gluedCurvatureTangentInner b = P.gluedTangentInner b := by
  unfold gluedCurvatureTangentInner
  have hz : (∑ k : Fin (n - 1), P.seamCurvatureTangentCorrection k b) = 0 :=
    Finset.sum_eq_zero (fun k _ =>
      P.seamCurvatureTangentCorrection_eq_zero_of_not_mem_thinSeamCollar k b (hb k))
  rw [hz]
  ext v u
  change P.gluedTangentInner b v u + 0 = _
  exact add_zero _

set_option backward.isDefEq.respectTransparency false in
theorem gluedCurvatureTangentInner_in_thin_seam_chart
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source)
    (hthin : b ∈ P.thinSeamCollar k) (v u : ℂ) :
    let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    let i : atlas ℂ P.GluedCarrier :=
      ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
    P.gluedCurvatureTangentInner b ((Z.localTriv i).symmL ℝ b v)
      ((Z.localTriv i).symmL ℝ b u) = v.re * u.re +
        gluingCurvatureBoundedWarp (gluingRadius C g) (gluingThinSeamWidth C g)
          P.thinSeamWidth_pos (P.seamAngularComplexChart k θ b).re ^ 2 * v.im * u.im := by
  classical
  dsimp only
  have hsum : (∑ l : Fin (n - 1), P.seamCurvatureTangentCorrection l b) =
      P.seamCurvatureTangentCorrection k b := by
    apply Finset.sum_eq_single k
    · intro l _ hlk
      apply P.seamCurvatureTangentCorrection_eq_zero_of_not_mem_thinSeamCollar
      intro hl
      exact Set.disjoint_left.mp (P.closedThinSeamCollar_disjoint hlk)
        (P.thinSeamCollar_subset_closedThinSeamCollar l hl)
        (P.thinSeamCollar_subset_closedThinSeamCollar k hthin)
    · simp
  unfold gluedCurvatureTangentInner
  rw [hsum]
  simp only [add_apply]
  rw [P.gluedTangentInner_in_chart (P.seamAngularComplexChart k θ)
      (Or.inr ⟨k, θ, rfl⟩) b hb v u,
    P.seamCurvatureTangentCorrection_in_seam_chart k θ b hb v u,
    P.gluingChartTangentForm_seam,
    gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_apply]
  unfold seamCurvatureCorrectionWeight
  ring

set_option backward.isDefEq.respectTransparency false in
theorem gluedCurvatureTangentInner_continuous_section
    (P : ExerciseGluingPreparation C g n genera X) :
    Continuous (fun b : P.GluedCarrier => TotalSpace.mk' (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
      b (P.gluedCurvatureTangentInner b)) := by
  letI : ContinuousAdd (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :=
    @IsTopologicalAddGroup.toContinuousAdd (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) _
      (inferInstanceAs (AddGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)))
      (inferInstanceAs (IsTopologicalAddGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)))
  letI : ∀ b : P.GluedCarrier, ContinuousAdd
      (TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ) := fun _ =>
    inferInstanceAs (ContinuousAdd (ℂ →L[ℝ] ℝ))
  rw [continuous_iff_continuousAt]
  intro b₀
  let E : P.GluedCarrier → Type := fun b =>
    TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ
  let t := trivializationAt (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) E b₀
  have hnative : ContinuousAt (fun b : P.GluedCarrier => (t ⟨b, P.gluedTangentInner b⟩).2) b₀ :=
    (FiberBundle.continuousAt_section (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) b₀).mp
      P.gluedTangentInner_continuous_section.continuousAt
  have hcor (k : Fin (n - 1)) : ContinuousAt
      (fun b : P.GluedCarrier => (t ⟨b, P.seamCurvatureTangentCorrection k b⟩).2) b₀ :=
    (FiberBundle.continuousAt_section (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) b₀).mp
      (P.seamCurvatureTangentCorrection_continuous_section k).continuousAt
  have hsum : ContinuousAt (fun b : P.GluedCarrier =>
      ∑ k : Fin (n - 1), (t ⟨b, P.seamCurvatureTangentCorrection k b⟩).2) b₀ :=
    tendsto_finsetSum Finset.univ (fun k _ => hcor k)
  rw [FiberBundle.continuousAt_section]
  apply (hnative.add hsum).congr_of_eventuallyEq
  filter_upwards [(chartAt ℂ b₀).open_source.mem_nhds (mem_chart_source ℂ b₀)] with b hb
  have ht : b ∈ (trivializationAt ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) b₀).baseSet := hb
  change (t ⟨b, P.gluedCurvatureTangentInner b⟩).2 = _
  change inCoordinates ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) (ℂ →L[ℝ] ℝ)
      (fun b => TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ)
      b₀ b b₀ b (P.gluedCurvatureTangentInner b) =
    inCoordinates ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) (ℂ →L[ℝ] ℝ)
      (fun b => TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ)
      b₀ b b₀ b (P.gluedTangentInner b) +
    ∑ k : Fin (n - 1), inCoordinates ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ))
      (ℂ →L[ℝ] ℝ) (fun b => TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ)
      b₀ b b₀ b (P.seamCurvatureTangentCorrection k b)
  ext v u
  simp only [add_apply, sum_apply]
  simp_rw [inCoordinates_apply_eq₂ (F₃ := ℝ) (E₃ := fun _ : P.GluedCarrier => ℝ)
    ht ht (mem_univ b)]
  have hr (a : ℝ) :
      (trivializationAt ℝ (fun _ : P.GluedCarrier => ℝ) b₀).linearMapAt ℝ b a = a := by
    change (Bundle.Trivial.trivialization P.GluedCarrier ℝ).linearMapAt ℝ b a = a
    rw [Bundle.Trivial.linearMapAt_trivialization]
    rfl
  simp only [hr, gluedCurvatureTangentInner, add_apply, sum_apply]

/-- The positive continuous metric on the actual original glued carrier whose
seam-chart coefficient is the normalized ODE warp. -/
def gluedCurvatureBoundedContinuousRiemannianMetric
    (P : ExerciseGluingPreparation C g n genera X) :
    Bundle.ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) where
  inner := P.gluedCurvatureTangentInner
  symm := P.gluedCurvatureTangentInner_symm
  pos := P.gluedCurvatureTangentInner_pos
  isVonNBounded := P.gluedCurvatureTangentInner_isVonNBounded
  continuous := P.gluedCurvatureTangentInner_continuous_section

@[simp] theorem gluedCurvatureBoundedContinuousRiemannianMetric_inner
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    (P.gluedCurvatureBoundedContinuousRiemannianMetric).inner b =
      P.gluedCurvatureTangentInner b := rfl

theorem gluedCurvatureBoundedContinuousRiemannianMetric_eq_native_of_outside_thinCollars
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier)
    (hb : ∀ k : Fin (n - 1), b ∉ P.thinSeamCollar k) :
    (P.gluedCurvatureBoundedContinuousRiemannianMetric).inner b =
      P.gluedTangentInner b := by
  rw [gluedCurvatureBoundedContinuousRiemannianMetric_inner]
  exact P.gluedCurvatureTangentInner_eq_native_of_outside_thinCollars b hb

theorem gluedCurvatureBoundedContinuousRiemannianMetric_in_thin_seam_chart
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source)
    (hthin : b ∈ P.thinSeamCollar k) (v u : ℂ) :
    let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    let i : atlas ℂ P.GluedCarrier :=
      ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
    (P.gluedCurvatureBoundedContinuousRiemannianMetric).inner b
      ((Z.localTriv i).symmL ℝ b v) ((Z.localTriv i).symmL ℝ b u) =
      v.re * u.re +
        gluingCurvatureBoundedWarp (gluingRadius C g) (gluingThinSeamWidth C g)
          P.thinSeamWidth_pos (P.seamAngularComplexChart k θ b).re ^ 2 * v.im * u.im := by
  rw [gluedCurvatureBoundedContinuousRiemannianMetric_inner]
  exact P.gluedCurvatureTangentInner_in_thin_seam_chart k θ b hb hthin v u

/-- The ODE collar tensor in its real complex-coordinate chart. -/
noncomputable def gluingComplexCurvatureBoundedTangentForm (r δ : ℝ)
    (hδ : 0 < δ) (z : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  Complex.reCLM.smulRight Complex.reCLM +
    (gluingCurvatureBoundedWarp r δ hδ z.re) ^ 2 •
      Complex.imCLM.smulRight Complex.imCLM

@[simp] theorem gluingComplexCurvatureBoundedTangentForm_apply
    (r δ : ℝ) (hδ : 0 < δ) (z v u : ℂ) :
    gluingComplexCurvatureBoundedTangentForm r δ hδ z v u =
      v.re * u.re + gluingCurvatureBoundedWarp r δ hδ z.re ^ 2 * v.im * u.im := by
  simp [gluingComplexCurvatureBoundedTangentForm, mul_assoc]

theorem gluingComplexCurvatureBoundedTangentForm_contDiff
    (r δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ ∞ (gluingComplexCurvatureBoundedTangentForm r δ hδ) := by
  letI : IsBoundedSMul ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :=
    @NormedSpace.toIsBoundedSMul ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) _ _
      (inferInstanceAs (NormedSpace ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)))
  unfold gluingComplexCurvatureBoundedTangentForm
  have hw : ContDiff ℝ ∞
      (fun z : ℂ => gluingCurvatureBoundedWarp r δ hδ z.re ^ 2) := by
    simpa only [Function.comp_apply, Complex.reCLM_apply] using
      ((gluingCurvatureBoundedWarp_contDiff r δ hδ).comp
        Complex.reCLM.contDiff).pow 2
  exact contDiff_const.add (hw.smul contDiff_const)

set_option backward.isDefEq.respectTransparency false in
/-- On an isolated seam chart, including the cutoff boundary, the patched
tensor has exactly the ODE-warp coefficient. -/
theorem gluedCurvatureTangentInner_in_isolated_seam_chart
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source)
    (hother : ∀ l : Fin (n - 1), l ≠ k → b ∉ P.thinSeamCollar l) (v u : ℂ) :
    let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    let i : atlas ℂ P.GluedCarrier :=
      ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
    P.gluedCurvatureTangentInner b ((Z.localTriv i).symmL ℝ b v)
      ((Z.localTriv i).symmL ℝ b u) =
      v.re * u.re + gluingCurvatureBoundedWarp (gluingRadius C g)
        (gluingThinSeamWidth C g) P.thinSeamWidth_pos
        (P.seamAngularComplexChart k θ b).re ^ 2 * v.im * u.im := by
  classical
  dsimp only
  have hsum : (∑ l : Fin (n - 1), P.seamCurvatureTangentCorrection l b) =
      P.seamCurvatureTangentCorrection k b := by
    apply Finset.sum_eq_single k
    · intro l _ hlk
      exact P.seamCurvatureTangentCorrection_eq_zero_of_not_mem_thinSeamCollar
        l b (hother l hlk)
    · simp
  unfold gluedCurvatureTangentInner
  rw [hsum]
  simp only [add_apply]
  rw [P.gluedTangentInner_in_chart (P.seamAngularComplexChart k θ)
      (Or.inr ⟨k, θ, rfl⟩) b hb v u,
    P.seamCurvatureTangentCorrection_in_seam_chart k θ b hb v u,
    P.gluingChartTangentForm_seam,
    gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_apply]
  unfold seamCurvatureCorrectionWeight
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The patched tensor has a smooth coordinate form near every point. Closed
thin collars use the ODE seam chart; their complement uses a hyperbolic
interior chart. -/
theorem gluedCurvatureTangentInner_exists_smooth_chart
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    ∃ (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas),
      b ∈ e.source ∧ ∃ G : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
        ContDiffAt ℝ ∞ G (e b) ∧
        ∀ᶠ c in 𝓝 b, c ∈ e.source ∧ ∀ v u : ℂ,
          P.gluedCurvatureTangentInner c
            (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
              (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ c v)
            (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
              (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ c u) = G (e c) v u := by
  classical
  by_cases hc : ∃ k : Fin (n - 1), b ∈ P.closedThinSeamCollar k
  · obtain ⟨k, hk⟩ := hc
    have hb := P.closedThinSeamCollar_subset_original_collar k hk
    let θ := P.seamSmoothingAngle k ⟨b, hb⟩
    have hs : b ∈ (P.seamAngularComplexChart k θ).source :=
      P.mem_seamSmoothingAngle_chart k ⟨b, hb⟩
    refine ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩, hs,
      gluingComplexCurvatureBoundedTangentForm (gluingRadius C g)
        (gluingThinSeamWidth C g) P.thinSeamWidth_pos,
      (gluingComplexCurvatureBoundedTangentForm_contDiff (gluingRadius C g)
        (gluingThinSeamWidth C g) P.thinSeamWidth_pos).contDiffAt (x :=
          P.seamAngularComplexChart k θ b), ?_⟩
    have hother : ∀ᶠ c in 𝓝 b, ∀ l : Fin (n - 1),
        l ≠ k → c ∉ P.thinSeamCollar l := by
      rw [Filter.eventually_all]
      intro l
      by_cases hl : l = k
      · exact Filter.Eventually.of_forall (fun _ h => (h hl).elim)
      · have hn : b ∉ P.closedThinSeamCollar l := fun h =>
          Set.disjoint_left.mp (P.closedThinSeamCollar_disjoint hl) h hk
        filter_upwards [(P.closedThinSeamCollar_isCompact l).isClosed.isOpen_compl.mem_nhds hn]
          with c hc _ hthin
        exact hc (P.thinSeamCollar_subset_closedThinSeamCollar l hthin)
    filter_upwards [(P.seamAngularComplexChart k θ).open_source.mem_nhds hs, hother]
      with c hcs hco
    refine ⟨hcs, fun v u => ?_⟩
    rw [P.gluedCurvatureTangentInner_in_isolated_seam_chart k θ c hcs hco,
      gluingComplexCurvatureBoundedTangentForm_apply]
  · have hn : ∀ k : Fin (n - 1), b ∉ P.closedThinSeamCollar k := by
      simpa only [not_exists] using hc
    obtain ⟨e, he, hs⟩ := P.exists_interior_chart_of_outside_closedThinSeamCollars b hn
    refine ⟨e, Or.inl he, hs, gluingComplexHalfPlaneTangentForm,
      (gluingComplexHalfPlaneTangentForm_contDiffAt
        (P.gluedInteriorComplexChart_target_im_pos e he (e.map_source hs))).of_le le_top, ?_⟩
    have hout : ∀ᶠ c in 𝓝 b, ∀ k : Fin (n - 1), c ∉ P.thinSeamCollar k := by
      rw [Filter.eventually_all]
      intro k
      filter_upwards [(P.closedThinSeamCollar_isCompact k).isClosed.isOpen_compl.mem_nhds (hn k)]
        with c hc hthin
      exact hc (P.thinSeamCollar_subset_closedThinSeamCollar k hthin)
    filter_upwards [e.open_source.mem_nhds hs, hout] with c hcs hco
    refine ⟨hcs, fun v u => ?_⟩
    rw [P.gluedCurvatureTangentInner_eq_native_of_outside_thinCollars c hco,
      P.gluedTangentInner_in_chart e (Or.inl he) c hcs v u,
      P.gluingChartTangentForm_interior e he]

set_option backward.isDefEq.respectTransparency false in
/-- The patched ODE tensor is a genuine smooth section on the original
manifold structure. -/
theorem gluedCurvatureTangentInner_contMDiff_section
    (P : ExerciseGluingPreparation C g n genera X) :
    ContMDiff (modelWithCornersSelf ℝ ℂ)
      ((modelWithCornersSelf ℝ ℂ).prod (modelWithCornersSelf ℝ
        (ℂ →L[ℝ] ℂ →L[ℝ] ℝ))) ∞
      (fun b : P.GluedCarrier => TotalSpace.mk' (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
        b (P.gluedCurvatureTangentInner b)) := by
  intro b
  obtain ⟨e, he, hs, G, hG, hform⟩ := P.gluedCurvatureTangentInner_exists_smooth_chart b
  exact contMDiffAt_native_bilinear_section_of_chart P P.gluedCurvatureTangentInner
    b e he hs G hG hform

/-- The curvature-controlled patch is a smooth positive Riemannian metric on
the unchanged glued topology. -/
def gluedCurvatureBoundedSmoothRiemannianMetric
    (P : ExerciseGluingPreparation C g n genera X) :
    Bundle.ContMDiffRiemannianMetric (modelWithCornersSelf ℝ ℂ) ∞ ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) where
  inner := P.gluedCurvatureTangentInner
  symm := P.gluedCurvatureTangentInner_symm
  pos := P.gluedCurvatureTangentInner_pos
  isVonNBounded := P.gluedCurvatureTangentInner_isVonNBounded
  contMDiff := P.gluedCurvatureTangentInner_contMDiff_section

@[simp] theorem gluedCurvatureBoundedSmoothRiemannianMetric_inner
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    (P.gluedCurvatureBoundedSmoothRiemannianMetric).inner b =
      P.gluedCurvatureTangentInner b := rfl

@[simp] theorem gluedCurvatureBoundedSmoothRiemannianMetric_toContinuousRiemannianMetric
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedCurvatureBoundedSmoothRiemannianMetric.toContinuousRiemannianMetric =
      P.gluedCurvatureBoundedContinuousRiemannianMetric := rfl

/-- The genuine Riemannian bundle determined by the ODE-patched metric. -/
@[instance_reducible] def gluedCurvatureBoundedRiemannianBundle
    (P : ExerciseGluingPreparation C g n genera X) :
    RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
  ⟨P.gluedCurvatureBoundedContinuousRiemannianMetric.toRiemannianMetric⟩

/-- Length of a curve in the curvature-controlled metric. -/
def gluedCurvatureBoundedPathELength
    (P : ExerciseGluingPreparation C g n genera X) (γ : ℝ → P.GluedCarrier)
    (a b : ℝ) : ℝ≥0∞ := by
  letI := P.gluedCurvatureBoundedRiemannianBundle
  exact Manifold.pathELength (modelWithCornersSelf ℝ ℂ) γ a b

set_option backward.isDefEq.respectTransparency false in
theorem gluedCurvatureBoundedPathELength_eq_lintegral
    (P : ExerciseGluingPreparation C g n genera X)
    (γ : ℝ → P.GluedCarrier) (a b : ℝ) :
    P.gluedCurvatureBoundedPathELength γ a b = ∫⁻ t in Icc a b, ENNReal.ofReal
      (Real.sqrt (P.gluedCurvatureTangentInner (γ t)
        (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1)
        (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1))) := by
  letI := P.gluedCurvatureBoundedRiemannianBundle
  unfold gluedCurvatureBoundedPathELength
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t _
  dsimp only
  have hsq : ‖mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1‖ ^ 2 =
      P.gluedCurvatureTangentInner (γ t)
        (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1)
        (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1) :=
    (real_inner_self_eq_norm_sq _).symm
  rw [← hsq, Real.sqrt_sq (norm_nonneg _), ofReal_norm]

/-- Increasing the tensor pointwise increases the length of every curve,
without any regularity or seam-avoidance restriction on the curve. -/
theorem gluedCurvatureBoundedPathELength_ge_native
    (P : ExerciseGluingPreparation C g n genera X)
    (γ : ℝ → P.GluedCarrier) (a b : ℝ) :
    P.gluedNativePathELength γ a b ≤ P.gluedCurvatureBoundedPathELength γ a b := by
  rw [P.gluedNativePathELength_eq_lintegral,
    P.gluedCurvatureBoundedPathELength_eq_lintegral]
  apply lintegral_mono
  intro t
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  exact P.gluedTangentInner_le_gluedCurvatureTangentInner (γ t) _

/-- Intrinsic distance for the ODE-patched metric, as the infimum of its
actual Riemannian path lengths. -/
def gluedCurvatureBoundedIntrinsicEDist
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier) : ℝ≥0∞ := by
  letI := P.gluedCurvatureBoundedRiemannianBundle
  exact Manifold.riemannianEDist (modelWithCornersSelf ℝ ℂ) x y

/-- The pointwise tensor domination implies intrinsic distance domination,
because every admissible C¹ curve has at least its native length. -/
theorem gluedCurvatureBoundedIntrinsicEDist_ge_native
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier) :
    P.gluedIntrinsicEDist x y ≤ P.gluedCurvatureBoundedIntrinsicEDist x y := by
  by_contra h
  have hlt : P.gluedCurvatureBoundedIntrinsicEDist x y < P.gluedIntrinsicEDist x y :=
    lt_of_not_ge h
  letI := P.gluedCurvatureBoundedRiemannianBundle
  change Manifold.riemannianEDist (modelWithCornersSelf ℝ ℂ) x y <
    P.gluedIntrinsicEDist x y at hlt
  obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hlt
  change P.gluedCurvatureBoundedPathELength γ 0 1 < P.gluedIntrinsicEDist x y at hlen
  have hnative : P.gluedIntrinsicEDist (γ 0) (γ 1) ≤
      P.gluedNativePathELength γ 0 1 := by
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
        P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    exact P.gluedIntrinsicEDist_le_pathELength hγ zero_le_one
  rw [h0, h1] at hnative
  have hle := hnative.trans (P.gluedCurvatureBoundedPathELength_ge_native γ 0 1)
  exact (not_lt_of_ge hle) hlen

#print axioms gluedCurvatureBoundedContinuousRiemannianMetric
#print axioms gluedCurvatureTangentInner_continuous_section
#print axioms seamCurvatureTangentCorrection_continuous_section
#print axioms gluedCurvatureTangentInner_in_thin_seam_chart
#print axioms gluedCurvatureBoundedContinuousRiemannianMetric_eq_native_of_outside_thinCollars
#print axioms gluedCurvatureBoundedSmoothRiemannianMetric
#print axioms gluedCurvatureTangentInner_contMDiff_section
#print axioms gluedCurvatureTangentInner_exists_smooth_chart
#print axioms gluedCurvatureBoundedPathELength_eq_lintegral
#print axioms gluedCurvatureBoundedPathELength_ge_native
#print axioms gluedCurvatureBoundedIntrinsicEDist_ge_native

end
end SystolicGrowth.ExerciseGluingPreparation

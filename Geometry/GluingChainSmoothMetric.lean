module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingRiemannianMetric
public import Geometry.GluingDisjointThinSeamCollars
public import Geometry.GluingCollarLocalizedSmoothWarp

@[expose] public section

/-!
# Localized smoothing on the original native tangent bundle

The finite sum of angular rank-one corrections uses genuine native collar
coordinates. Same-seam differential identities and the actual tangent
bundle cocycle make this independent of the chosen angular lift. The
localized warp leaves the original tensor unchanged outside thin strips.
-/

open Set Filter Bundle ContinuousLinearMap
open scoped Manifold Topology

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual cutoff inside the proved disjoint native thin strips. -/
def seamSmoothingCutoff (P : ExerciseGluingPreparation C g n genera X) :
    ContDiffBump (0 : ℝ) :=
  gluingCollarSmoothingCutoff (gluingThinSeamWidth C g) P.thinSeamWidth_pos

/-- The coefficient of the added angular tensor in original radial coordinates. -/
def seamSmoothCorrectionWeight (P : ExerciseGluingPreparation C g n genera X)
    (ε t : ℝ) : ℝ :=
  gluingCollarLocalizedSmoothWarp (gluingRadius C g) ε P.seamSmoothingCutoff t ^ 2 -
    gluingCollarWarp (gluingRadius C g) t ^ 2

theorem seamSmoothCorrectionWeight_nonneg
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    0 ≤ P.seamSmoothCorrectionWeight ε t := by
  have h := (gluingCollarLocalizedSmoothWarp_sub_warp_bounds
    (gluingRadius C g) hε P.seamSmoothingCutoff t).1
  have hf := gluingCollarWarp_pos P.radius_pos t
  unfold seamSmoothCorrectionWeight
  nlinarith

theorem seamSmoothCorrectionWeight_eq_zero
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) {t : ℝ}
    (ht : gluingThinSeamWidth C g ≤ |t|) : P.seamSmoothCorrectionWeight ε t = 0 := by
  unfold seamSmoothCorrectionWeight
  rw [gluingCollarLocalizedSmoothWarp_eq_native _ _ _ ht, sub_self]

theorem seamSmoothCorrectionWeight_continuous
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) :
    Continuous (P.seamSmoothCorrectionWeight ε) :=
  ((gluingCollarLocalizedSmoothWarp_continuous _ _ _).pow 2).sub
    ((gluingCollarWarp_continuous _).pow 2)

/-- A real angular lift selected only to define the tensor; compatibility
below removes this choice from its native coordinate expression. -/
def seamSmoothingAngle (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (b : P.gluedMk '' P.seamNeighborhood k) : ℝ :=
  Complex.arg (((P.seamCylinderHomeomorph k).symm b).1 : ℂ)

def seamSmoothingChartIndex (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (b : P.gluedMk '' P.seamNeighborhood k) : atlas ℂ P.GluedCarrier :=
  ⟨P.seamAngularComplexChart k (P.seamSmoothingAngle k b), Or.inr ⟨k, _, rfl⟩⟩

theorem mem_seamSmoothingAngle_chart
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (b : P.gluedMk '' P.seamNeighborhood k) :
    b.1 ∈ (P.seamAngularComplexChart k (P.seamSmoothingAngle k b)).source := by
  rw [P.seamAngularComplexChart_source]
  let q := (P.seamCylinderHomeomorph k).symm b
  let θ := P.seamSmoothingAngle k b
  refine ⟨(q.2, ⟨θ, by constructor <;> linarith [Real.pi_pos]⟩), ?_⟩
  change (P.seamCylinderHomeomorph k
    (Circle.exp (Complex.arg (q.1 : ℂ)), q.2)).1 = b.1
  rw [Circle.exp_arg]
  exact congrArg Subtype.val ((P.seamCylinderHomeomorph k).apply_symm_apply b)

private theorem seam_chart_radial_eq_cylinder
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
/-- A genuine native bilinear correction, extended by zero outside the
original collar. Its support is proved to lie in the smaller thin strip. -/
def seamSmoothTangentCorrection
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1))
    (b : P.GluedCarrier) : TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ := by
  classical
  exact if hb : b ∈ P.gluedMk '' P.seamNeighborhood k then
    let c : P.gluedMk '' P.seamNeighborhood k := ⟨b, hb⟩
    let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    let j := P.seamSmoothingChartIndex k c
    let L : TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ :=
      Complex.imCLM.comp (Z.coordChange (achart ℂ b) j b)
    P.seamSmoothCorrectionWeight ε ((P.seamCylinderHomeomorph k).symm c).2.1 •
      L.smulRight L
  else 0

set_option backward.isDefEq.respectTransparency false in
theorem seamSmoothTangentCorrection_apply_of_mem
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1))
    (b : P.GluedCarrier) (hb : b ∈ P.gluedMk '' P.seamNeighborhood k)
    (v u : TangentSpace (modelWithCornersSelf ℝ ℂ) b) :
    P.seamSmoothTangentCorrection ε k b v u =
      P.seamSmoothCorrectionWeight ε ((P.seamCylinderHomeomorph k).symm ⟨b, hb⟩).2.1 *
        (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).coordChange
          (achart ℂ b) (P.seamSmoothingChartIndex k ⟨b, hb⟩) b v).im *
        ((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).coordChange
          (achart ℂ b) (P.seamSmoothingChartIndex k ⟨b, hb⟩) b u).im) := by
  classical
  unfold seamSmoothTangentCorrection
  rw [dif_pos hb]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem seamSmoothTangentCorrection_symm
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1))
    (b : P.GluedCarrier) (v u : TangentSpace (modelWithCornersSelf ℝ ℂ) b) :
    P.seamSmoothTangentCorrection ε k b v u =
      P.seamSmoothTangentCorrection ε k b u v := by
  classical
  by_cases hb : b ∈ P.gluedMk '' P.seamNeighborhood k
  · rw [P.seamSmoothTangentCorrection_apply_of_mem ε k b hb,
      P.seamSmoothTangentCorrection_apply_of_mem ε k b hb]
    ring
  · simp [seamSmoothTangentCorrection, hb]

set_option backward.isDefEq.respectTransparency false in
theorem seamSmoothTangentCorrection_nonneg
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 ≤ ε)
    (k : Fin (n - 1)) (b : P.GluedCarrier)
    (v : TangentSpace (modelWithCornersSelf ℝ ℂ) b) :
    0 ≤ P.seamSmoothTangentCorrection ε k b v v := by
  classical
  by_cases hb : b ∈ P.gluedMk '' P.seamNeighborhood k
  · rw [P.seamSmoothTangentCorrection_apply_of_mem ε k b hb]
    exact mul_nonneg (P.seamSmoothCorrectionWeight_nonneg hε _)
      (mul_self_nonneg _)
  · simp [seamSmoothTangentCorrection, hb]

set_option backward.isDefEq.respectTransparency false in
theorem seamSmoothTangentCorrection_eq_zero_of_not_mem_thinSeamCollar
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1))
    (b : P.GluedCarrier) (hb : b ∉ P.thinSeamCollar k) :
    P.seamSmoothTangentCorrection ε k b = 0 := by
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
    rw [P.seamSmoothTangentCorrection_apply_of_mem ε k b hc,
      P.seamSmoothCorrectionWeight_eq_zero ε hr]
    simp
  · simp [seamSmoothTangentCorrection, hc]

set_option backward.isDefEq.respectTransparency false in
/-- Exact fixed-chart expression in any actual angular chart of this seam.
The native tangent cocycle and actual same-seam derivative identity derive
the compatibility; it is not supplied as a tensor hypothesis. -/
theorem seamSmoothTangentCorrection_in_seam_chart
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source) (v u : ℂ) :
    let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    let i : atlas ℂ P.GluedCarrier := ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
    P.seamSmoothTangentCorrection ε k b ((Z.localTriv i).symmL ℝ b v)
      ((Z.localTriv i).symmL ℝ b u) =
      P.seamSmoothCorrectionWeight ε (P.seamAngularComplexChart k θ b).re * v.im * u.im := by
  classical
  dsimp only
  have hc : b ∈ P.gluedMk '' P.seamNeighborhood k := by
    rw [P.seamAngularComplexChart_source] at hb
    obtain ⟨p, rfl⟩ := hb
    exact (P.seamCylinderHomeomorph k (Circle.exp p.2.1, p.1)).2
  let c : P.gluedMk '' P.seamNeighborhood k := ⟨b, hc⟩
  let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
  let i : atlas ℂ P.GluedCarrier := ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
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
  rw [P.seamSmoothTangentCorrection_apply_of_mem ε k b hc]
  change P.seamSmoothCorrectionWeight ε ((P.seamCylinderHomeomorph k).symm c).2.1 *
      ((Z.coordChange (achart ℂ b) j b ((Z.localTriv i).symmL ℝ b v)).im *
      (Z.coordChange (achart ℂ b) j b ((Z.localTriv i).symmL ℝ b u)).im) = _
  rw [hs v, hs u, seam_chart_radial_eq_cylinder P k θ b hb hc]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem seamSmoothTangentCorrection_in_chart_of_seam
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1)) (θ : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source)
    (hseam : b ∈ (P.seamAngularComplexChart k θ).source) (v u : ℂ) :
    let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    let i : atlas ℂ P.GluedCarrier := ⟨e, he⟩
    let j : atlas ℂ P.GluedCarrier := ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
    P.seamSmoothTangentCorrection ε k b ((Z.localTriv i).symmL ℝ b v)
      ((Z.localTriv i).symmL ℝ b u) =
      P.seamSmoothCorrectionWeight ε (P.seamAngularComplexChart k θ b).re *
        (Z.coordChange i j b v).im * (Z.coordChange i j b u).im := by
  dsimp only
  let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
  let i : atlas ℂ P.GluedCarrier := ⟨e, he⟩
  let j : atlas ℂ P.GluedCarrier := ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
  have hs (w : ℂ) : (Z.localTriv i).symmL ℝ b w =
      (Z.localTriv j).symmL ℝ b (Z.coordChange i j b w) := by
    rw [Z.localTriv_symmL (by exact hb), Z.localTriv_symmL (by exact hseam)]
    change Z.coordChange i (achart ℂ b) b w =
      Z.coordChange j (achart ℂ b) b (Z.coordChange i j b w)
    exact (Z.coordChange_comp i j (achart ℂ b) b
      ⟨⟨hb, hseam⟩, mem_chart_source ℂ b⟩ w).symm
  change P.seamSmoothTangentCorrection ε k b ((Z.localTriv i).symmL ℝ b v)
    ((Z.localTriv i).symmL ℝ b u) = _
  rw [hs v, hs u]
  exact P.seamSmoothTangentCorrection_in_seam_chart ε k θ b hseam _ _

set_option backward.isDefEq.respectTransparency false in
private theorem seamSmoothTangentCorrection_in_preferred_coordinates
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1)) (θ : ℝ)
    (b₀ b : P.GluedCarrier) (hb : b ∈ (chartAt ℂ b₀).source)
    (hseam : b ∈ (P.seamAngularComplexChart k θ).source) :
    inCoordinates ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)
      (ℂ →L[ℝ] ℝ) (fun b => TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ)
      b₀ b b₀ b (P.seamSmoothTangentCorrection ε k b) =
      let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
      let j : atlas ℂ P.GluedCarrier := ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
      let L := Complex.imCLM.comp (Z.coordChange (achart ℂ b₀) j b)
      P.seamSmoothCorrectionWeight ε (P.seamAngularComplexChart k θ b).re • L.smulRight L := by
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
  have h := P.seamSmoothTangentCorrection_in_chart_of_seam ε k θ (chartAt ℂ b₀)
    (chart_mem_atlas ℂ b₀) b hb hseam v u
  apply h.trans
  change _ = P.seamSmoothCorrectionWeight ε (P.seamAngularComplexChart k θ b).re *
    (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).coordChange
      (achart ℂ b₀) ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩ b v).im *
    ((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).coordChange
      (achart ℂ b₀) ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩ b u).im)
  simp only [achart]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Each angular correction is continuous in the original native tensor
bundle; compactly contained support handles the outer collar boundary. -/
theorem seamSmoothTangentCorrection_continuous_section
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1)) :
    Continuous (fun b : P.GluedCarrier => TotalSpace.mk' (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
      b (P.seamSmoothTangentCorrection ε k b)) := by
  rw [continuous_iff_continuousAt]
  intro b₀
  by_cases hc : b₀ ∈ P.gluedMk '' P.seamNeighborhood k
  · let θ := P.seamSmoothingAngle k ⟨b₀, hc⟩
    have hs : b₀ ∈ (P.seamAngularComplexChart k θ).source :=
      P.mem_seamSmoothingAngle_chart k ⟨b₀, hc⟩
    let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    let j : atlas ℂ P.GluedCarrier := ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
    have hD : ContinuousAt (Z.coordChange (achart ℂ b₀) j) b₀ :=
      (Z.continuousOn_coordChange (achart ℂ b₀) j).continuousAt
        (((Z.isOpen_baseSet (achart ℂ b₀)).inter (Z.isOpen_baseSet j)).mem_nhds
          ⟨mem_chart_source ℂ b₀, hs⟩)
    have hL : ContinuousAt (fun b => Complex.imCLM.comp (Z.coordChange (achart ℂ b₀) j b)) b₀ :=
      continuousAt_const.clm_comp hD
    have hR : Continuous (fun p : (ℂ →L[ℝ] ℝ) × (ℂ →L[ℝ] ℝ) => p.1.smulRight p.2) :=
      (isBoundedBilinearMap_smulRight (𝕜 := ℝ)).continuous
    have hW : ContinuousAt (fun b : P.GluedCarrier =>
        P.seamSmoothCorrectionWeight ε (P.seamAngularComplexChart k θ b).re) b₀ :=
      (P.seamSmoothCorrectionWeight_continuous ε).continuousAt.comp
        (Complex.continuous_re.continuousAt.comp
          ((P.seamAngularComplexChart k θ).continuousAt hs))
    have hform := hW.smul (hR.continuousAt.comp (hL.prodMk hL))
    rw [FiberBundle.continuousAt_section]
    apply hform.congr_of_eventuallyEq
    filter_upwards [(chartAt ℂ b₀).open_source.mem_nhds (mem_chart_source ℂ b₀),
      (P.seamAngularComplexChart k θ).open_source.mem_nhds hs] with b hb hseam
    rw [hom_trivializationAt_apply]
    exact P.seamSmoothTangentCorrection_in_preferred_coordinates ε k θ b₀ b hb hseam
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
    rw [P.seamSmoothTangentCorrection_eq_zero_of_not_mem_thinSeamCollar ε k b
      (fun h => hb (P.thinSeamCollar_subset_closedThinSeamCollar k h))]

set_option backward.isDefEq.respectTransparency false in
/-- The localized tensor is on the original native tangent fiber, not a
replacement surface or a supplied globally compatible tensor. -/
def gluedSmoothTangentInner (P : ExerciseGluingPreparation C g n genera X)
    (ε : ℝ) (b : P.GluedCarrier) :
    TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ :=
  P.gluedTangentInner b + ∑ k : Fin (n - 1), P.seamSmoothTangentCorrection ε k b

set_option backward.isDefEq.respectTransparency false in
theorem gluedSmoothTangentInner_symm
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (b : P.GluedCarrier)
    (v u : TangentSpace (modelWithCornersSelf ℝ ℂ) b) :
    P.gluedSmoothTangentInner ε b v u = P.gluedSmoothTangentInner ε b u v := by
  simp only [gluedSmoothTangentInner, add_apply, sum_apply]
  rw [P.gluedTangentInner_symm b v u]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact P.seamSmoothTangentCorrection_symm ε k b v u

set_option backward.isDefEq.respectTransparency false in
theorem gluedTangentInner_le_gluedSmoothTangentInner
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 ≤ ε)
    (b : P.GluedCarrier) (v : TangentSpace (modelWithCornersSelf ℝ ℂ) b) :
    P.gluedTangentInner b v v ≤ P.gluedSmoothTangentInner ε b v v := by
  simp only [gluedSmoothTangentInner, add_apply, sum_apply, le_add_iff_nonneg_right]
  exact Finset.sum_nonneg (fun k _ => P.seamSmoothTangentCorrection_nonneg hε k b v)

set_option backward.isDefEq.respectTransparency false in
theorem gluedSmoothTangentInner_pos
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 ≤ ε)
    (b : P.GluedCarrier) (v : TangentSpace (modelWithCornersSelf ℝ ℂ) b) (hv : v ≠ 0) :
    0 < P.gluedSmoothTangentInner ε b v v :=
  (P.gluedTangentInner_pos b v hv).trans_le (P.gluedTangentInner_le_gluedSmoothTangentInner hε b v)

set_option backward.isDefEq.respectTransparency false in
theorem gluedSmoothTangentInner_isVonNBounded
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 ≤ ε)
    (b : P.GluedCarrier) :
    Bornology.IsVonNBounded ℝ
      {v : TangentSpace (modelWithCornersSelf ℝ ℂ) b | P.gluedSmoothTangentInner ε b v v < 1} :=
  (P.gluedTangentInner_isVonNBounded b).subset (fun v hv =>
    (P.gluedTangentInner_le_gluedSmoothTangentInner hε b v).trans_lt hv)

set_option backward.isDefEq.respectTransparency false in
theorem gluedSmoothTangentInner_eq_native_of_outside_thinCollars
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (b : P.GluedCarrier)
    (hb : ∀ k : Fin (n - 1), b ∉ P.thinSeamCollar k) :
    P.gluedSmoothTangentInner ε b = P.gluedTangentInner b := by
  unfold gluedSmoothTangentInner
  have hz : (∑ k : Fin (n - 1), P.seamSmoothTangentCorrection ε k b) = 0 :=
    Finset.sum_eq_zero (fun k _ =>
      P.seamSmoothTangentCorrection_eq_zero_of_not_mem_thinSeamCollar ε k b (hb k))
  rw [hz]
  ext v u
  change P.gluedTangentInner b v u + 0 = _
  exact add_zero _

set_option backward.isDefEq.respectTransparency false in
/-- Inside a genuine thin strip the globally patched native tensor has
exactly the localized warped-coordinate form. -/
theorem gluedSmoothTangentInner_in_thin_seam_chart
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source)
    (hthin : b ∈ P.thinSeamCollar k) (v u : ℂ) :
    let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    let i : atlas ℂ P.GluedCarrier := ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
    P.gluedSmoothTangentInner ε b ((Z.localTriv i).symmL ℝ b v)
      ((Z.localTriv i).symmL ℝ b u) = v.re * u.re +
        gluingCollarLocalizedSmoothWarp (gluingRadius C g) ε P.seamSmoothingCutoff
          (P.seamAngularComplexChart k θ b).re ^ 2 * v.im * u.im := by
  classical
  dsimp only
  have hsum : (∑ l : Fin (n - 1), P.seamSmoothTangentCorrection ε l b) =
      P.seamSmoothTangentCorrection ε k b := by
    apply Finset.sum_eq_single k
    · intro l _ hlk
      apply P.seamSmoothTangentCorrection_eq_zero_of_not_mem_thinSeamCollar
      intro hl
      exact Set.disjoint_left.mp (P.closedThinSeamCollar_disjoint hlk)
        (P.thinSeamCollar_subset_closedThinSeamCollar l hl)
        (P.thinSeamCollar_subset_closedThinSeamCollar k hthin)
    · simp
  unfold gluedSmoothTangentInner
  rw [hsum]
  simp only [add_apply]
  rw [P.gluedTangentInner_in_chart (P.seamAngularComplexChart k θ)
      (Or.inr ⟨k, θ, rfl⟩) b hb v u,
    P.seamSmoothTangentCorrection_in_seam_chart ε k θ b hb v u,
    P.gluingChartTangentForm_seam,
    gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_apply]
  unfold seamSmoothCorrectionWeight
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The finite native patch is continuous in the unchanged original
bilinear-form bundle, with no compatibility field taken as an input. -/
theorem gluedSmoothTangentInner_continuous_section
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) :
    Continuous (fun b : P.GluedCarrier => TotalSpace.mk' (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
      b (P.gluedSmoothTangentInner ε b)) := by
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
      (fun b : P.GluedCarrier => (t ⟨b, P.seamSmoothTangentCorrection ε k b⟩).2) b₀ :=
    (FiberBundle.continuousAt_section (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) b₀).mp
      (P.seamSmoothTangentCorrection_continuous_section ε k).continuousAt
  have hsum : ContinuousAt (fun b : P.GluedCarrier =>
      ∑ k : Fin (n - 1), (t ⟨b, P.seamSmoothTangentCorrection ε k b⟩).2) b₀ :=
    tendsto_finsetSum Finset.univ (fun k _ => hcor k)
  rw [FiberBundle.continuousAt_section]
  apply (hnative.add hsum).congr_of_eventuallyEq
  filter_upwards [(chartAt ℂ b₀).open_source.mem_nhds (mem_chart_source ℂ b₀)] with b hb
  have ht : b ∈ (trivializationAt ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) b₀).baseSet := hb
  change (t ⟨b, P.gluedSmoothTangentInner ε b⟩).2 = _
  change inCoordinates ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) (ℂ →L[ℝ] ℝ)
      (fun b => TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ)
      b₀ b b₀ b (P.gluedSmoothTangentInner ε b) =
    inCoordinates ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) (ℂ →L[ℝ] ℝ)
      (fun b => TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ)
      b₀ b b₀ b (P.gluedTangentInner b) +
    ∑ k : Fin (n - 1), inCoordinates ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ))
      (ℂ →L[ℝ] ℝ) (fun b => TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ)
      b₀ b b₀ b (P.seamSmoothTangentCorrection ε k b)
  ext v u
  simp only [add_apply, sum_apply]
  simp_rw [inCoordinates_apply_eq₂ (F₃ := ℝ) (E₃ := fun _ : P.GluedCarrier => ℝ)
    ht ht (mem_univ b)]
  have hr (a : ℝ) :
      (trivializationAt ℝ (fun _ : P.GluedCarrier => ℝ) b₀).linearMapAt ℝ b a = a := by
    change (Bundle.Trivial.trivialization P.GluedCarrier ℝ).linearMapAt ℝ b a = a
    rw [Bundle.Trivial.linearMapAt_trivialization]
    rfl
  simp only [hr, gluedSmoothTangentInner, add_apply, sum_apply]

/-- A genuine continuous positive Riemannian metric on the original
native tangent bundle, with the actual fixed thin-support cutoff. -/
def gluedSmoothContinuousRiemannianMetric
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 ≤ ε) :
    Bundle.ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) where
  inner := P.gluedSmoothTangentInner ε
  symm := P.gluedSmoothTangentInner_symm ε
  pos := P.gluedSmoothTangentInner_pos hε
  isVonNBounded := P.gluedSmoothTangentInner_isVonNBounded hε
  continuous := P.gluedSmoothTangentInner_continuous_section ε

@[simp] theorem gluedSmoothContinuousRiemannianMetric_inner
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 ≤ ε) (b : P.GluedCarrier) :
    (P.gluedSmoothContinuousRiemannianMetric ε hε).inner b = P.gluedSmoothTangentInner ε b := rfl

#print axioms gluedSmoothContinuousRiemannianMetric
#print axioms gluedSmoothTangentInner_continuous_section
#print axioms seamSmoothTangentCorrection_continuous_section
#print axioms gluedSmoothTangentInner_in_thin_seam_chart
#print axioms gluedSmoothTangentInner_pos
#print axioms gluedSmoothTangentInner_eq_native_of_outside_thinCollars
#print axioms seamSmoothTangentCorrection_in_seam_chart
#print axioms seamSmoothTangentCorrection_nonneg
#print axioms seamSmoothTangentCorrection_eq_zero_of_not_mem_thinSeamCollar

end
end SystolicGrowth.ExerciseGluingPreparation

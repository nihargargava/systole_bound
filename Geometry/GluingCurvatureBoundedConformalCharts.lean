module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SmoothWarpConformalCoordinates
public import Geometry.GluingChainBoundedCurvatureCurvature
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

@[expose] public section

/-!
# Conformal coordinates of the actual smooth ODE seam metric

These coordinate changes use the genuine smooth curvature-bounded warp,
not the native absolute-value warp. They belong to the maximal atlas of
the original glued smooth structure. Their inverse differentials give the
literal conformal tensor of the same existing Riemannian metric.
-/

open Set Filter Bundle Manifold IsManifold
open scoped Manifold Topology ContDiff

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The actual ODE warp used by the existing smooth metric. -/
def gluedCurvatureBoundedConformalWarp (P : ExerciseGluingPreparation C g n genera X) : ℝ → ℝ :=
  gluingCurvatureBoundedWarp (gluingRadius C g) (gluingThinSeamWidth C g) P.thinSeamWidth_pos

theorem gluedCurvatureBoundedConformalWarp_contDiff
    (P : ExerciseGluingPreparation C g n genera X) :
    ContDiff ℝ ∞ P.gluedCurvatureBoundedConformalWarp :=
  gluingCurvatureBoundedWarp_contDiff (gluingRadius C g) (gluingThinSeamWidth C g) P.thinSeamWidth_pos

theorem gluedCurvatureBoundedConformalWarp_pos
    (P : ExerciseGluingPreparation C g n genera X) (t : ℝ) :
    0 < P.gluedCurvatureBoundedConformalWarp t :=
  gluingCurvatureBoundedWarp_pos P.radius_pos P.thinSeamWidth_pos t

/-- **Math.** The constructed smooth coordinate change on the unchanged seam model. -/
def gluedCurvatureBoundedSeamConformalChange
    (P : ExerciseGluingPreparation C g n genera X) : OpenPartialHomeomorph ℂ ℂ :=
  smoothWarpConformalChart P.gluedCurvatureBoundedConformalWarp_contDiff.continuous
    P.gluedCurvatureBoundedConformalWarp_pos

@[simp] theorem gluedCurvatureBoundedSeamConformalChange_source
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedCurvatureBoundedSeamConformalChange.source = univ :=
  smoothWarpConformalChart_source _ _

theorem gluedCurvatureBoundedSeamConformalChange_contDiff
    (P : ExerciseGluingPreparation C g n genera X) :
    ContDiff ℝ ∞ (P.gluedCurvatureBoundedSeamConformalChange : ℂ → ℂ) := by
  have hf : (P.gluedCurvatureBoundedSeamConformalChange : ℂ → ℂ) =
      smoothWarpConformalCoordinate P.gluedCurvatureBoundedConformalWarp :=
    funext (smoothWarpConformalChart_apply _ _)
  rw [hf]
  exact smoothWarpConformalCoordinate_contDiff P.gluedCurvatureBoundedConformalWarp_contDiff
    P.gluedCurvatureBoundedConformalWarp_pos

theorem gluedCurvatureBoundedSeamConformalChange_symm_contDiffOn
    (P : ExerciseGluingPreparation C g n genera X) :
    ContDiffOn ℝ ∞ P.gluedCurvatureBoundedSeamConformalChange.symm
      P.gluedCurvatureBoundedSeamConformalChange.target :=
  smoothWarpConformalChart_symm_contDiffOn P.gluedCurvatureBoundedConformalWarp_contDiff
    P.gluedCurvatureBoundedConformalWarp_pos

/-- **Math.** The actual new seam coordinate, still on the original smooth carrier. -/
def gluedCurvatureBoundedSeamConformalChart
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    OpenPartialHomeomorph P.GluedCarrier ℂ :=
  (P.seamAngularComplexChart k θ).trans P.gluedCurvatureBoundedSeamConformalChange

@[simp] theorem gluedCurvatureBoundedSeamConformalChart_source
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    (P.gluedCurvatureBoundedSeamConformalChart k θ).source =
      (P.seamAngularComplexChart k θ).source := by
  simp [gluedCurvatureBoundedSeamConformalChart]

/-- **Math.** Both directions of the constructed seam coordinate are smooth
for the original atlas, not for an independently supplied smooth structure. -/
theorem gluedCurvatureBoundedSeamConformalChart_mem_maximalAtlas
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    P.gluedCurvatureBoundedSeamConformalChart k θ ∈
      IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞ P.GluedCarrier := by
  let e := P.seamAngularComplexChart k θ
  let ψ := P.gluedCurvatureBoundedSeamConformalChange
  have he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞ P.GluedCarrier :=
    IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℝ ℂ) (n := ∞)
      (show e ∈ atlas ℂ P.GluedCarrier from Or.inr ⟨k, θ, rfl⟩)
  have hψ : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞ ψ :=
    P.gluedCurvatureBoundedSeamConformalChange_contDiff.contMDiff
  have hψinv : ContMDiffOn (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞ ψ.symm ψ.target :=
    P.gluedCurvatureBoundedSeamConformalChange_symm_contDiffOn.contMDiffOn
  apply (e.trans ψ).mem_maximalAtlas_of_contMDiffOn
  · rw [OpenPartialHomeomorph.coe_trans]
    exact hψ.comp_contMDiffOn ((contMDiffOn_of_mem_maximalAtlas he).mono
      (fun _ hx => hx.1))
  · rw [OpenPartialHomeomorph.coe_trans_symm]
    exact (contMDiffOn_symm_of_mem_maximalAtlas he).comp
      (hψinv.mono (fun _ hx => hx.1)) (fun _ hx => hx.2)

/-- **Math.** The actual smooth positive Euclidean conformal coefficient. -/
def gluedCurvatureBoundedSeamConformalFactor
    (P : ExerciseGluingPreparation C g n genera X) (z : ℂ) : ℝ :=
  smoothWarpConformalFactor P.gluedCurvatureBoundedConformalWarp_contDiff.continuous
    P.gluedCurvatureBoundedConformalWarp_pos z.re

theorem gluedCurvatureBoundedSeamConformalFactor_pos
    (P : ExerciseGluingPreparation C g n genera X) (z : ℂ) :
    0 < P.gluedCurvatureBoundedSeamConformalFactor z :=
  smoothWarpConformalFactor_pos _ _ _

theorem gluedCurvatureBoundedSeamConformalFactor_contDiffOn
    (P : ExerciseGluingPreparation C g n genera X) :
    ContDiffOn ℝ ∞ P.gluedCurvatureBoundedSeamConformalFactor
      P.gluedCurvatureBoundedSeamConformalChange.target := by
  intro z hz
  rw [gluedCurvatureBoundedSeamConformalChange, smoothWarpConformalChart_target] at hz
  have hf := (smoothWarpConformalFactor_contDiffOn P.gluedCurvatureBoundedConformalWarp_contDiff
    P.gluedCurvatureBoundedConformalWarp_pos).contDiffAt
      ((smoothWarpConformalRadialChart P.gluedCurvatureBoundedConformalWarp_contDiff.continuous
        P.gluedCurvatureBoundedConformalWarp_pos).open_target.mem_nhds hz)
  exact (hf.comp z Complex.reCLM.contDiff.contDiffAt).contDiffWithinAt

/-- **Math.** The proved derivative of the actual inverse coordinate. -/
def gluedCurvatureBoundedSeamConformalInverseDerivative
    (P : ExerciseGluingPreparation C g n genera X) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  smoothWarpConformalInverseDerivative P.gluedCurvatureBoundedConformalWarp_contDiff.continuous
    P.gluedCurvatureBoundedConformalWarp_pos z

theorem gluedCurvatureBoundedSeamConformalChange_symm_hasFDerivAt
    (P : ExerciseGluingPreparation C g n genera X) {z : ℂ}
    (hz : z ∈ P.gluedCurvatureBoundedSeamConformalChange.target) :
    HasFDerivAt P.gluedCurvatureBoundedSeamConformalChange.symm
      (P.gluedCurvatureBoundedSeamConformalInverseDerivative z) z :=
  smoothWarpConformalChart_symm_hasFDerivAt _ _ hz

/-- **Math.** The SAME existing smooth metric, evaluated on the actual
inverse-coordinate differential, has exactly the Euclidean conformal
tensor on every isolated seam point, including smoothing boundaries. -/
theorem gluedCurvatureBoundedSmoothMetric_in_conformal_seam_chart
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source)
    (hother : ∀ l : Fin (n - 1), l ≠ k → b ∉ P.thinSeamCollar l) (v w : ℂ) :
    let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    let i : atlas ℂ P.GluedCarrier := ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
    let z := P.gluedCurvatureBoundedSeamConformalChart k θ b
    P.gluedCurvatureBoundedSmoothRiemannianMetric.inner b
      ((Z.localTriv i).symmL ℝ b (P.gluedCurvatureBoundedSeamConformalInverseDerivative z v))
      ((Z.localTriv i).symmL ℝ b (P.gluedCurvatureBoundedSeamConformalInverseDerivative z w)) =
      P.gluedCurvatureBoundedSeamConformalFactor z ^ 2 * (v.re * w.re + v.im * w.im) := by
  dsimp only
  rw [gluedCurvatureBoundedSmoothRiemannianMetric_inner,
    P.gluedCurvatureTangentInner_in_isolated_seam_chart k θ b hb hother]
  have h := smoothWarpTangentForm_inverse_eq_conformal
    P.gluedCurvatureBoundedConformalWarp_contDiff.continuous
    P.gluedCurvatureBoundedConformalWarp_pos
    (P.gluedCurvatureBoundedSeamConformalChange (P.seamAngularComplexChart k θ b)) v w
  have hinv := P.gluedCurvatureBoundedSeamConformalChange.left_inv
    (show P.seamAngularComplexChart k θ b ∈ P.gluedCurvatureBoundedSeamConformalChange.source by simp)
  change (smoothWarpConformalChart P.gluedCurvatureBoundedConformalWarp_contDiff.continuous
    P.gluedCurvatureBoundedConformalWarp_pos).symm
      (P.gluedCurvatureBoundedSeamConformalChange (P.seamAngularComplexChart k θ b)) =
        P.seamAngularComplexChart k θ b at hinv
  rw [hinv] at h
  exact h

/-- **Math.** On every unchanged interior point the SAME patched metric
has the positive smooth Poincaré conformal coefficient `1 / Im z`. -/
theorem gluedCurvatureBoundedSmoothMetric_in_conformal_interior_chart
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    (b : P.GluedCarrier) (hb : b ∈ e.source)
    (hout : ∀ k : Fin (n - 1), b ∉ P.thinSeamCollar k) (v w : ℂ) :
    let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    let i : atlas ℂ P.GluedCarrier := ⟨e, Or.inl he⟩
    P.gluedCurvatureBoundedSmoothRiemannianMetric.inner b
      ((Z.localTriv i).symmL ℝ b v) ((Z.localTriv i).symmL ℝ b w) =
      ((e b).im)⁻¹ ^ 2 * (v.re * w.re + v.im * w.im) := by
  dsimp only
  rw [(P.gluedCurvatureBoundedSmoothMetric_interior_chart e he b hb hout).2 v w,
    gluingComplexHalfPlaneTangentForm_apply]
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, div_eq_mul_inv]
  ring

/-- **Math.** Around every actual carrier point choose an original atlas
chart and its genuine smooth conformal coordinate change. The new chart
belongs to the ORIGINAL maximal atlas; its positive coefficient is smooth
on the real target, and its inverse differential transforms the SAME
existing Riemannian metric into the literal Euclidean conformal tensor on
a neighborhood. No new metric, atlas, coordinate inverse, or tensor
identity is supplied as a hypothesis. -/
theorem exists_gluedCurvatureBounded_conformal_chart
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    ∃ (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
      (ψ : OpenPartialHomeomorph ℂ ℂ) (a : ℂ → ℝ) (D : ℂ → ℂ →L[ℝ] ℂ),
      ψ.source = univ ∧ ContDiff ℝ ∞ (ψ : ℂ → ℂ) ∧
      b ∈ (e.trans ψ).source ∧
      e.trans ψ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞ P.GluedCarrier ∧
      ContDiffOn ℝ ∞ a (e.trans ψ).target ∧
      (∀ z ∈ (e.trans ψ).target, 0 < a z) ∧
      (∀ z ∈ ψ.target, HasFDerivAt ψ.symm (D z) z) ∧
      ∀ᶠ c in 𝓝 b, c ∈ (e.trans ψ).source ∧ ∀ v w : ℂ,
        P.gluedCurvatureBoundedSmoothRiemannianMetric.inner c
          (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
            (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ c (D ((e.trans ψ) c) v))
          (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
            (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ c (D ((e.trans ψ) c) w)) =
          a ((e.trans ψ) c) ^ 2 * (v.re * w.re + v.im * w.im) := by
  classical
  by_cases hc : ∃ k : Fin (n - 1), b ∈ P.closedThinSeamCollar k
  · obtain ⟨k, hk⟩ := hc
    have hb := P.closedThinSeamCollar_subset_original_collar k hk
    let θ := P.seamSmoothingAngle k ⟨b, hb⟩
    have hs : b ∈ (P.seamAngularComplexChart k θ).source :=
      P.mem_seamSmoothingAngle_chart k ⟨b, hb⟩
    refine ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩,
      P.gluedCurvatureBoundedSeamConformalChange, P.gluedCurvatureBoundedSeamConformalFactor,
      P.gluedCurvatureBoundedSeamConformalInverseDerivative,
      P.gluedCurvatureBoundedSeamConformalChange_source,
      P.gluedCurvatureBoundedSeamConformalChange_contDiff, ?_,
      P.gluedCurvatureBoundedSeamConformalChart_mem_maximalAtlas k θ, ?_,
      fun z _ => P.gluedCurvatureBoundedSeamConformalFactor_pos z,
      fun z hz => P.gluedCurvatureBoundedSeamConformalChange_symm_hasFDerivAt hz, ?_⟩
    · simpa using hs
    · exact P.gluedCurvatureBoundedSeamConformalFactor_contDiffOn.mono (fun _ hz => hz.1)
    · have hother : ∀ᶠ c in 𝓝 b, ∀ l : Fin (n - 1),
          l ≠ k → c ∉ P.thinSeamCollar l := by
        rw [Filter.eventually_all]
        intro l
        by_cases hl : l = k
        · exact Filter.Eventually.of_forall (fun _ h => (h hl).elim)
        · have hn : b ∉ P.closedThinSeamCollar l := fun h =>
            Set.disjoint_left.mp (P.closedThinSeamCollar_disjoint hl) h hk
          filter_upwards [(P.closedThinSeamCollar_isCompact l).isClosed.isOpen_compl.mem_nhds hn]
            with c hcl _ hthin
          exact hcl (P.thinSeamCollar_subset_closedThinSeamCollar l hthin)
      filter_upwards [(P.seamAngularComplexChart k θ).open_source.mem_nhds hs, hother]
        with c hcs hco
      refine ⟨by simpa using hcs, ?_⟩
      exact fun v w => P.gluedCurvatureBoundedSmoothMetric_in_conformal_seam_chart k θ c hcs hco v w
  · have hn : ∀ k : Fin (n - 1), b ∉ P.closedThinSeamCollar k := by
      simpa only [not_exists] using hc
    obtain ⟨e, he, hs⟩ := P.exists_interior_chart_of_outside_closedThinSeamCollars b hn
    refine ⟨e, Or.inl he, OpenPartialHomeomorph.refl ℂ, fun z => z.im⁻¹,
      fun _ => ContinuousLinearMap.id ℝ ℂ, rfl, contDiff_id, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hs
    · have heMax : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞ P.GluedCarrier :=
        IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℝ ℂ) (n := ∞)
          (show e ∈ atlas ℂ P.GluedCarrier from Or.inl he)
      simpa using heMax
    · simp only [OpenPartialHomeomorph.trans_refl]
      convert! Complex.imCLM.contDiff.contDiffOn.inv
        (fun z hz => (P.gluedInteriorComplexChart_target_im_pos e he hz).ne') using 1
    · intro z hz
      exact inv_pos.mpr (P.gluedInteriorComplexChart_target_im_pos e he (by simpa using hz))
    · intro z _
      exact hasFDerivAt_id z
    · have hout : ∀ᶠ c in 𝓝 b, ∀ k : Fin (n - 1), c ∉ P.thinSeamCollar k := by
        rw [Filter.eventually_all]
        intro k
        filter_upwards [(P.closedThinSeamCollar_isCompact k).isClosed.isOpen_compl.mem_nhds (hn k)]
          with c hck hthin
        exact hck (P.thinSeamCollar_subset_closedThinSeamCollar k hthin)
      filter_upwards [e.open_source.mem_nhds hs, hout] with c hcs hco
      refine ⟨by simpa using hcs, ?_⟩
      intro v w
      simpa using P.gluedCurvatureBoundedSmoothMetric_in_conformal_interior_chart e he c hcs hco v w

#print axioms gluedCurvatureBoundedSeamConformalChart_mem_maximalAtlas
#print axioms gluedCurvatureBoundedSeamConformalFactor_contDiffOn
#print axioms gluedCurvatureBoundedSmoothMetric_in_conformal_seam_chart
#print axioms gluedCurvatureBoundedSmoothMetric_in_conformal_interior_chart
#print axioms exists_gluedCurvatureBounded_conformal_chart

end

end SystolicGrowth.ExerciseGluingPreparation

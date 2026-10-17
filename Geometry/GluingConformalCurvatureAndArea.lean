module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedConformalCharts
public import Geometry.GluingIntrinsicCurvature
public import Geometry.GluingCurvatureBoundedAreaCharts
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# The actual smooth curvature scalar of the conformal input metric

The assembled Gaussian field agrees with the same smooth ODE expression
through both cutoff boundaries. Consequently it is a smooth function on the
original glued atlas, with uniform negative bounds on the compact carrier.
-/

open Set Filter Bundle Manifold IsManifold
open scoped Manifold Topology ContDiff

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

/-- **Math.** The local ODE Gaussian formula is smooth on the entire seam
coordinate plane, including the two smoothing boundaries. -/
theorem gluedCurvatureBoundedSeamGaussian_contDiff
    (P : ExerciseGluingPreparation C g n genera X) :
    ContDiff ℝ ∞ (gluedCurvatureBoundedSeamGaussian P) := by
  let W := P.gluedCurvatureBoundedConformalWarp
  have hW : ContDiff ℝ ∞ W := P.gluedCurvatureBoundedConformalWarp_contDiff
  have hW2 : ContDiff ℝ 2 W := hW.of_le (by
    exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hf : gluedCurvatureBoundedSeamGaussian P =
      fun z : ℂ => -deriv (deriv W) z.re / W z.re := by
    funext z
    exact gluingWarpedGaussianCurvature_eq hW2
      (P.gluedCurvatureBoundedConformalWarp_pos z.re)
  rw [hf]
  exact ((hW.deriv'.deriv'.neg).comp Complex.reCLM.contDiff).div
    (hW.comp Complex.reCLM.contDiff)
    (fun z => (P.gluedCurvatureBoundedConformalWarp_pos z.re).ne')

/-- **Math.** Where the normalized forcing vanishes, the ODE curvature
equals the unchanged hyperbolic value, including the support endpoints. -/
theorem gluedCurvatureBoundedSeamGaussian_eq_neg_one_of_abs_ge
    (P : ExerciseGluingPreparation C g n genera X) (z : ℂ)
    (hz : gluingThinSeamWidth C g ≤ |z.re|) :
    gluedCurvatureBoundedSeamGaussian P z = -1 := by
  let r := gluingRadius C g
  let δ := gluingThinSeamWidth C g
  let W := gluingCurvatureBoundedWarp r δ P.thinSeamWidth_pos
  have hW : ContDiff ℝ 2 W :=
    (gluingCurvatureBoundedWarp_contDiff r δ P.thinSeamWidth_pos).of_le (by
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hpos : 0 < W z.re :=
    gluingCurvatureBoundedWarp_pos P.radius_pos P.thinSeamWidth_pos z.re
  have hcut : gluingCollarSmoothingCutoff δ P.thinSeamWidth_pos z.re = 0 :=
    (gluingCollarSmoothingCutoff δ P.thinSeamWidth_pos).zero_of_le_dist
      (by simpa [Real.dist_eq, gluingCollarSmoothingCutoff, δ] using hz)
  have hforce : gluingCurvatureForcing r δ P.thinSeamWidth_pos z.re = 0 := by
    simp only [gluingCurvatureForcing, hcut, mul_zero]
  have hODE := gluingCurvatureBoundedWarp_deriv_sub_eq_forcing
    r δ P.thinSeamWidth_pos z.re
  rw [hforce] at hODE
  change gluingWarpedGaussianCurvature W (z.re, z.im) = -1
  rw [gluingWarpedGaussianCurvature_eq hW hpos]
  change -deriv (deriv W) z.re / W z.re = -1
  have hsecond : deriv (deriv W) z.re = W z.re := sub_eq_zero.mp hODE
  rw [hsecond, neg_div, div_self hpos.ne']

theorem gluedCurvatureBoundedGaussian_seamAngularPoint
    (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ) (a : GluingSeamAngularDomain C g θ)
    (hthin : P.seamAngularPoint k θ a ∈ P.thinSeamCollar k) :
    P.gluedCurvatureBoundedGaussian (P.seamAngularPoint k θ a) =
      gluedCurvatureBoundedSeamGaussian P (gluingSeamAngularModel C g θ a) := by
  have hrad : |a.1.1| < gluingThinSeamWidth C g :=
    (P.seamCylinderHomeomorph_mem_thinSeamCollar_iff k (Circle.exp a.2.1, a.1)).mp hthin
  let p : Circle × Ioo (-gluingThinSeamWidth C g) (gluingThinSeamWidth C g) :=
    (Circle.exp a.2.1, ⟨a.1.1, abs_lt.mp hrad⟩)
  change P.gluedCurvatureBoundedGaussian (P.thinSeamCylinderMap k p) = _
  rw [P.gluedCurvatureBoundedGaussian_thinSeamCylinderMap]
  let W := P.gluedCurvatureBoundedConformalWarp
  have hW : ContDiff ℝ 2 W :=
    P.gluedCurvatureBoundedConformalWarp_contDiff.of_le (by
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hpos := P.gluedCurvatureBoundedConformalWarp_pos a.1.1
  change gluingWarpedGaussianCurvature W (a.1.1, 0) =
    gluingWarpedGaussianCurvature W (a.1.1, a.2.1)
  rw [gluingWarpedGaussianCurvature_eq hW hpos,
    gluingWarpedGaussianCurvature_eq hW hpos]

/-- **Math.** The already assembled global scalar is exactly the true
smooth warp curvature everywhere in an isolated original seam chart. -/
theorem gluedCurvatureBoundedGaussian_in_isolated_seam_chart
    (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ) (b : P.GluedCarrier)
    (hb : b ∈ (P.seamAngularComplexChart k θ).source)
    (hother : ∀ l : Fin (n - 1), l ≠ k → b ∉ P.thinSeamCollar l) :
    P.gluedCurvatureBoundedGaussian b =
      gluedCurvatureBoundedSeamGaussian P (P.seamAngularComplexChart k θ b) := by
  by_cases hthin : b ∈ P.thinSeamCollar k
  · have hsource := hb
    rw [P.seamAngularComplexChart_source] at hsource
    obtain ⟨a, rfl⟩ := hsource
    rw [P.seamAngularComplexChart_apply]
    exact P.gluedCurvatureBoundedGaussian_seamAngularPoint k θ a hthin
  · have hout : ∀ l : Fin (n - 1), b ∉ P.thinSeamCollar l := by
      intro l
      by_cases hl : l = k
      · simpa only [hl] using hthin
      · exact hother l hl
    have hrad : gluingThinSeamWidth C g ≤ |(P.seamAngularComplexChart k θ b).re| := by
      have h := (P.seamAngularComplexChart_symm_mem_thinSeamCollar_iff k θ
        ((P.seamAngularComplexChart k θ).map_source hb)).not
      rw [(P.seamAngularComplexChart k θ).left_inv hb] at h
      exact le_of_not_gt (h.mp hthin)
    rw [P.gluedCurvatureBoundedGaussian_eq_neg_one_of_outside b hout,
      P.gluedCurvatureBoundedSeamGaussian_eq_neg_one_of_abs_ge _ hrad]

/-- **Math.** The literal global Gaussian scalar of the existing smooth
metric is infinitely differentiable in the original glued smooth atlas. -/
theorem gluedCurvatureBoundedGaussian_contMDiff
    (P : ExerciseGluingPreparation C g n genera X) :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞
      P.gluedCurvatureBoundedGaussian := by
  intro b
  by_cases hc : ∃ k : Fin (n - 1), b ∈ P.closedThinSeamCollar k
  · obtain ⟨k, hk⟩ := hc
    have hb := P.closedThinSeamCollar_subset_original_collar k hk
    let θ := P.seamSmoothingAngle k ⟨b, hb⟩
    have hs : b ∈ (P.seamAngularComplexChart k θ).source :=
      P.mem_seamSmoothingAngle_chart k ⟨b, hb⟩
    have he : P.seamAngularComplexChart k θ ∈
        maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞ P.GluedCarrier :=
      subset_maximalAtlas (I := modelWithCornersSelf ℝ ℂ) (n := ∞)
        (show P.seamAngularComplexChart k θ ∈ atlas ℂ P.GluedCarrier from
          Or.inr ⟨k, θ, rfl⟩)
    have hlocal := P.gluedCurvatureBoundedSeamGaussian_contDiff.contMDiff.contMDiffAt.comp b
      (contMDiffAt_of_mem_maximalAtlas he hs)
    apply hlocal.congr_of_eventuallyEq
    have hother : ∀ᶠ c in 𝓝 b, ∀ l : Fin (n - 1), l ≠ k → c ∉ P.thinSeamCollar l := by
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
    exact P.gluedCurvatureBoundedGaussian_in_isolated_seam_chart k θ c hcs hco
  · have hn : ∀ k : Fin (n - 1), b ∉ P.closedThinSeamCollar k := by
      simpa only [not_exists] using hc
    apply (contMDiffAt_const (c := (-1 : ℝ))).congr_of_eventuallyEq
    have hout : ∀ᶠ c in 𝓝 b, ∀ k : Fin (n - 1), c ∉ P.thinSeamCollar k := by
      rw [Filter.eventually_all]
      intro k
      filter_upwards [(P.closedThinSeamCollar_isCompact k).isClosed.isOpen_compl.mem_nhds (hn k)]
        with c hck hthin
      exact hck (P.thinSeamCollar_subset_closedThinSeamCollar k hthin)
    filter_upwards [hout] with c hco
    exact P.gluedCurvatureBoundedGaussian_eq_neg_one_of_outside c hco

/-- **Math.** Compactness supplies one genuine finite curvature bound for
the fixed constructed metric, with no bound supplied as an extra input. -/
theorem exists_gluedCurvatureBoundedGaussian_uniform_bound
    (P : ExerciseGluingPreparation C g n genera X) :
    ∃ B : ℝ, 1 < B ∧ ∀ b : P.GluedCarrier,
      1 ≤ -P.gluedCurvatureBoundedGaussian b ∧ -P.gluedCurvatureBoundedGaussian b ≤ B := by
  have hbounded := (isCompact_univ : IsCompact (univ : Set P.GluedCarrier)).bddAbove_image
    P.gluedCurvatureBoundedGaussian_contMDiff.continuous.neg.continuousOn
  obtain ⟨B, hB⟩ := hbounded
  refine ⟨max B 1 + 1, by linarith [le_max_right B 1], fun b => ⟨?_, ?_⟩⟩
  · linarith [P.gluedCurvatureBoundedGaussian_le_neg_one b]
  · have hb : -P.gluedCurvatureBoundedGaussian b ≤ B := hB ⟨b, mem_univ b, rfl⟩
    linarith [le_max_left B 1]

/-- **Math.** The assembled smooth scalar equals the actual Levi-Civita
sectional curvature of the canonical chart frame on the original carrier. -/
theorem gluedCurvatureBoundedGaussian_eq_sectionalCurvature_chartFrame
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
    let τ := trivializationAt ℂ (TangentSpace I) b
    letI : Bundle.RiemannianBundle (fun q : P.GluedCarrier => TangentSpace I q) :=
      ⟨metric.toRiemannianMetric⟩
    P.gluedCurvatureBoundedGaussian b =
      Riemannian.sectionalCurvature
        ((Riemannian.RiemannianMetric.leviCivitaConnection metric).curvatureFormAt metric b)
        (τ.symmL ℝ b (1 : ℂ)) (τ.symmL ℝ b Complex.I) := by
  dsimp only
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  letI : Bundle.RiemannianBundle (fun q : P.GluedCarrier => TangentSpace I q) :=
    ⟨P.gluedCurvatureBoundedSmoothRiemannianMetric.toRiemannianMetric⟩
  let y : ℂ := (extChartAt I b) b
  have hy : y ∈ (extChartAt I b).target := mem_extChartAt_target b
  have hpoint : (extChartAt I b).symm y = b :=
    (extChartAt I b).left_inv (mem_extChartAt_source b)
  have hseam (k : Fin (n - 1)) (θ : ℝ)
      (hchart : chartAt ℂ b = P.seamAngularComplexChart k θ)
      (hother : ∀ l : Fin (n - 1), l ≠ k → b ∉ P.closedThinSeamCollar l) :
      P.gluedCurvatureBoundedGaussian b =
        Riemannian.sectionalCurvature
          ((Riemannian.RiemannianMetric.leviCivitaConnection
            P.gluedCurvatureBoundedSmoothRiemannianMetric).curvatureFormAt
            P.gluedCurvatureBoundedSmoothRiemannianMetric b)
          ((trivializationAt ℂ (TangentSpace I) b).symmL ℝ b (1 : ℂ))
          ((trivializationAt ℂ (TangentSpace I) b).symmL ℝ b Complex.I) := by
    have hs : b ∈ (P.seamAngularComplexChart k θ).source := by
      rw [← hchart]
      exact mem_chart_source ℂ b
    have hother' : ∀ l : Fin (n - 1), l ≠ k →
        (extChartAt I b).symm y ∉ P.closedThinSeamCollar l := by
      simpa only [hpoint] using hother
    have h := P.gluedCurvatureBoundedSeam_sectionalCurvature_eq k θ b hchart.symm hy hother'
    dsimp only [I, y] at h
    rw [extChartAt_to_inv] at h
    have hcoord : (extChartAt (modelWithCornersSelf ℝ ℂ) b) b =
        P.seamAngularComplexChart k θ b := by
      simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_apply, id_eq, hchart]
    rw [hcoord] at h
    rw [P.gluedCurvatureBoundedGaussian_in_isolated_seam_chart k θ b hs
      (fun l hl hthin => hother l hl
        (P.thinSeamCollar_subset_closedThinSeamCollar l hthin)), h]
    have hW : ContDiff ℝ 2 P.gluedCurvatureBoundedConformalWarp :=
      P.gluedCurvatureBoundedConformalWarp_contDiff.of_le (by
        exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
    change gluingWarpedGaussianCurvature P.gluedCurvatureBoundedConformalWarp
        ((P.seamAngularComplexChart k θ b).re, (P.seamAngularComplexChart k θ b).im) = _
    rw [gluingWarpedGaussianCurvature_eq hW
      (P.gluedCurvatureBoundedConformalWarp_pos _), neg_div]
    rfl
  by_cases hc : ∃ k : Fin (n - 1), b ∈ P.closedThinSeamCollar k
  · obtain ⟨k, hk⟩ := hc
    obtain ⟨θ, hchart⟩ :=
      P.gluedCurvatureBounded_chartAt_eq_seam_of_mem_closedThinSeamCollar b k hk
    exact hseam k θ hchart (fun l hl hbl =>
      Set.disjoint_left.mp (P.closedThinSeamCollar_disjoint hl) hbl hk)
  · have houtside : ∀ k : Fin (n - 1), b ∉ P.closedThinSeamCollar k := by
      simpa only [not_exists] using hc
    rcases P.gluedCurvatureBounded_chartAt_is_seam_or_interior b with hi | ⟨k, θ, hchart⟩
    · have houtside' : ∀ k : Fin (n - 1),
          (extChartAt I b).symm y ∉ P.closedThinSeamCollar k := by
        simpa only [hpoint] using houtside
      have h := P.gluedCurvatureBoundedInterior_sectionalCurvature_eq_neg_one b hi hy houtside'
      dsimp only [I, y] at h
      rw [extChartAt_to_inv] at h
      rw [h, P.gluedCurvatureBoundedGaussian_eq_neg_one_of_outside b
        (fun k hthin => houtside k (P.thinSeamCollar_subset_closedThinSeamCollar k hthin))]
    · exact hseam k θ hchart (fun l _ => houtside l)

/-- **Math.** The actual intrinsic sectional curvature on every nondegenerate
tangent plane equals the SAME globally smooth Gaussian scalar. -/
theorem gluedCurvatureBounded_sectionalCurvature_eq_gaussian
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
    letI : Bundle.RiemannianBundle (fun q : P.GluedCarrier => TangentSpace I q) :=
      ⟨metric.toRiemannianMetric⟩
    ∀ u v : TangentSpace I b, 0 < Riemannian.wedgeSq u v →
      Riemannian.sectionalCurvature
        ((Riemannian.RiemannianMetric.leviCivitaConnection metric).curvatureFormAt metric b)
        u v = P.gluedCurvatureBoundedGaussian b := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
  let τ := trivializationAt ℂ (TangentSpace I) b
  letI : Bundle.RiemannianBundle (fun q : P.GluedCarrier => TangentSpace I q) :=
    ⟨metric.toRiemannianMetric⟩
  have hbBase : b ∈ τ.baseSet := mem_chart_source ℂ b
  let e : Module.Basis (Fin 2) ℝ (TangentSpace I b) :=
    Complex.basisOneI.map (τ.continuousLinearEquivAt ℝ b hbBase).symm.toLinearEquiv
  have he0 : e 0 = τ.symmL ℝ b (1 : ℂ) := by
    simp only [e, Module.Basis.map_apply, Complex.coe_basisOneI,
      Matrix.cons_val_zero, ContinuousLinearEquiv.coe_toLinearEquiv,
      Bundle.Trivialization.symm_continuousLinearEquivAt_eq]
  have he1 : e 1 = τ.symmL ℝ b Complex.I := by
    simp only [e, Module.Basis.map_apply, Complex.coe_basisOneI,
      Matrix.cons_val_one, Matrix.cons_val_zero,
      ContinuousLinearEquiv.coe_toLinearEquiv,
      Bundle.Trivialization.symm_continuousLinearEquivAt_eq]
  have hlin : LinearIndependent ℝ ![e 0, e 1] := by
    convert e.linearIndependent using 1
    ext i
    fin_cases i <;> rfl
  have harea : 0 < Riemannian.wedgeSq (e 0) (e 1) :=
    (Riemannian.wedgeSq_pos_iff_linearIndependent (e 0) (e 1)).2 hlin
  let connection := Riemannian.RiemannianMetric.leviCivitaConnection
    (I := I) (M := P.GluedCarrier) metric
  have hLC : connection.IsLeviCivita metric :=
    connection.isLeviCivita_of_koszulDual metric
      (fun A B Z q => Riemannian.RiemannianMetric.koszulDualSection_dual metric A B Z q)
  have hB := connection.isAlgCurvatureForm_curvatureFormAt metric hLC b
  have hsectional : Riemannian.sectionalCurvature (connection.curvatureFormAt metric b)
      (e 0) (e 1) = P.gluedCurvatureBoundedGaussian b := by
    rw [he0, he1]
    exact (P.gluedCurvatureBoundedGaussian_eq_sectionalCurvature_chartFrame b).symm
  have hbase : connection.curvatureFormAt metric b (e 0) (e 1) (e 0) (e 1) =
      P.gluedCurvatureBoundedGaussian b * Riemannian.wedgeSq (e 0) (e 1) :=
    (div_eq_iff harea.ne').mp hsectional
  dsimp only
  intro u v huv
  have hdiag : connection.curvatureFormAt metric b u v u v =
      P.gluedCurvatureBoundedGaussian b * Riemannian.wedgeSq u v := by
    rw [hB.diag_eq_det_sq_mul_basis e u v,
      Riemannian.wedgeSq_eq_det_sq_mul_basis e u v, hbase]
    ring
  change connection.curvatureFormAt metric b u v u v / Riemannian.wedgeSq u v = _
  rw [hdiag, mul_div_cancel_right₀ _ huv.ne']

#print axioms gluedCurvatureBoundedGaussian_in_isolated_seam_chart
#print axioms gluedCurvatureBoundedGaussian_contMDiff
#print axioms exists_gluedCurvatureBoundedGaussian_uniform_bound
#print axioms gluedCurvatureBoundedGaussian_eq_sectionalCurvature_chartFrame
#print axioms gluedCurvatureBounded_sectionalCurvature_eq_gaussian

end

end SystolicGrowth.ExerciseGluingPreparation

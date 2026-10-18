module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainSmoothMetric
public import Geometry.GluingCollarLocalizedSmoothMetric
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

@[expose] public section

/-!
# Smoothness of the actual global localized metric

The closed thin collars, rather than their open interiors, handle the
cutoff boundary. Near one closed strip the other corrections vanish, and
the actual native tensor has the genuine smooth localized coordinate form.
Away from all closed strips an original hyperbolic interior chart supplies
the smooth form. All bundle and smooth structures are the original ones.
-/

open Set Filter Bundle ContinuousLinearMap
open scoped Manifold Topology ContDiff

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Outside the closed thin strips every native point has a genuine
hyperbolic interior chart, not merely an arbitrary seam chart. -/
theorem exists_interior_chart_of_outside_closedThinSeamCollars
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier)
    (hb : ∀ k : Fin (n - 1), b ∉ P.closedThinSeamCollar k) :
    ∃ e : OpenPartialHomeomorph P.GluedCarrier ℂ,
      P.IsGluedInteriorComplexChart e ∧ b ∈ e.source := by
  have hrep : ∃ (i : Fin n) (q : P.componentInteriorSet i),
      b = P.gluedMk (P.componentInteriorPoint i q) := by
    rcases P.gluedPoint_mem_interior_or_seamNeighborhood b with h | ⟨k, hc⟩
    · exact h
    · let θ := P.seamSmoothingAngle k ⟨b, hc⟩
      have hs := P.mem_seamSmoothingAngle_chart k ⟨b, hc⟩
      change b ∈ (P.seamAngularComplexChart k θ).source at hs
      rw [P.seamAngularComplexChart_source] at hs
      obtain ⟨p, hp⟩ := hs
      have hn : p.1.1 ≠ 0 := by
        intro hz
        apply hb k
        refine ⟨(Circle.exp p.2.1, p.1), ?_, hp⟩
        change |p.1.1| ≤ gluingThinSeamWidth C g
        simpa only [hz, abs_zero] using P.thinSeamWidth_pos.le
      rcases lt_or_gt_of_ne hn with hn | hn
      · obtain ⟨q, hq⟩ := P.seamAngularPoint_exists_outgoingInterior k θ p hn
        exact ⟨_, q, hp.symm.trans hq⟩
      · obtain ⟨q, hq⟩ := P.seamAngularPoint_exists_incomingInterior k θ p hn
        exact ⟨_, q, hp.symm.trans hq⟩
  obtain ⟨i, q, rfl⟩ := hrep
  obtain ⟨z, ρ, hρ, h4, hz, hq, hf⟩ := P.exists_gluedComponentInterior_ball_chart i q
  refine ⟨P.gluedInteriorComplexChart i z ρ hρ hq hf,
    ⟨i, z, ρ, hρ, h4, hq, hf, rfl⟩, ?_⟩
  simp only [gluedInteriorComplexChart, gluingChartFromOpenEmbeddings_source]
  refine ⟨⟨z, by simpa using hρ⟩, ?_⟩
  simp only [hz]

set_option backward.isDefEq.respectTransparency false in
/-- The localized formula remains exact on any part of a seam chart
which avoids the other thin strips, including its own cutoff boundary. -/
theorem gluedSmoothTangentInner_in_isolated_seam_chart
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (k : Fin (n - 1)) (θ : ℝ)
    (b : P.GluedCarrier) (hb : b ∈ (P.seamAngularComplexChart k θ).source)
    (hother : ∀ l : Fin (n - 1), l ≠ k → b ∉ P.thinSeamCollar l) (v u : ℂ) :
    let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    let i : atlas ℂ P.GluedCarrier := ⟨P.seamAngularComplexChart k θ, Or.inr ⟨k, θ, rfl⟩⟩
    P.gluedSmoothTangentInner ε b ((Z.localTriv i).symmL ℝ b v)
      ((Z.localTriv i).symmL ℝ b u) =
      gluingComplexCollarLocalizedSmoothTangentForm (b := P.seamSmoothingCutoff)
        (gluingRadius C g) ε (P.seamAngularComplexChart k θ b) v u := by
  classical
  dsimp only
  have hsum : (∑ l : Fin (n - 1), P.seamSmoothTangentCorrection ε l b) =
      P.seamSmoothTangentCorrection ε k b := by
    apply Finset.sum_eq_single k
    · intro l _ hlk
      exact P.seamSmoothTangentCorrection_eq_zero_of_not_mem_thinSeamCollar ε l b
        (hother l hlk)
    · simp
  unfold gluedSmoothTangentInner
  rw [hsum]
  simp only [add_apply]
  rw [P.gluedTangentInner_in_chart (P.seamAngularComplexChart k θ)
      (Or.inr ⟨k, θ, rfl⟩) b hb v u,
    P.seamSmoothTangentCorrection_in_seam_chart ε k θ b hb v u,
    P.gluingChartTangentForm_seam,
    gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_apply,
    gluingComplexCollarLocalizedSmoothTangentForm_apply]
  unfold seamSmoothCorrectionWeight
  ring

/-- The true hyperbolic interior form is smooth wherever its height is positive. -/
theorem gluingComplexHalfPlaneTangentForm_contDiffAt {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ⊤ gluingComplexHalfPlaneTangentForm z := by
  letI : IsBoundedSMul ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :=
    @NormedSpace.toIsBoundedSMul ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) _ _
      (inferInstanceAs (NormedSpace ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)))
  unfold gluingComplexHalfPlaneTangentForm
  exact ((Complex.imCLM.contDiff.contDiffAt.pow 2).inv (pow_ne_zero 2 hz.ne')).smul
    contDiffAt_const

set_option backward.isDefEq.respectTransparency false in
/-- Actual native charts cover the global tensor by genuinely smooth
coordinate forms. The neighborhood identity is proved, not supplied. -/
theorem gluedSmoothTangentInner_exists_smooth_chart
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 < ε)
    (b : P.GluedCarrier) :
    ∃ (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas),
      b ∈ e.source ∧ ∃ G : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
        ContDiffAt ℝ ∞ G (e b) ∧
        ∀ᶠ c in 𝓝 b, c ∈ e.source ∧ ∀ v u : ℂ,
          P.gluedSmoothTangentInner ε c
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
      gluingComplexCollarLocalizedSmoothTangentForm (b := P.seamSmoothingCutoff)
        (gluingRadius C g) ε,
      (gluingComplexCollarLocalizedSmoothTangentForm_contDiff
        (b := P.seamSmoothingCutoff) (gluingRadius C g) hε ⊤).contDiffAt, ?_⟩
    have hother : ∀ᶠ c in 𝓝 b, ∀ l : Fin (n - 1),
        l ≠ k → c ∉ P.thinSeamCollar l := by
      apply Filter.eventually_all.mpr
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
    exact ⟨hcs, P.gluedSmoothTangentInner_in_isolated_seam_chart ε k θ c hcs hco⟩
  · have hn : ∀ k : Fin (n - 1), b ∉ P.closedThinSeamCollar k := by
      simpa only [not_exists] using hc
    obtain ⟨e, he, hs⟩ := P.exists_interior_chart_of_outside_closedThinSeamCollars b hn
    refine ⟨e, Or.inl he, hs, gluingComplexHalfPlaneTangentForm,
      (gluingComplexHalfPlaneTangentForm_contDiffAt
        (P.gluedInteriorComplexChart_target_im_pos e he (e.map_source hs))).of_le le_top, ?_⟩
    have hout : ∀ᶠ c in 𝓝 b, ∀ k : Fin (n - 1), c ∉ P.thinSeamCollar k := by
      apply Filter.eventually_all.mpr
      intro k
      filter_upwards [(P.closedThinSeamCollar_isCompact k).isClosed.isOpen_compl.mem_nhds (hn k)]
        with c hc hthin
      exact hc (P.thinSeamCollar_subset_closedThinSeamCollar k hthin)
    filter_upwards [e.open_source.mem_nhds hs, hout] with c hcs hco
    refine ⟨hcs, fun v u => ?_⟩
    rw [P.gluedSmoothTangentInner_eq_native_of_outside_thinCollars ε c hco,
      P.gluedTangentInner_in_chart e (Or.inl he) c hcs v u,
      P.gluingChartTangentForm_interior e he]

set_option backward.isDefEq.respectTransparency false in
/-- A native bilinear tensor is smooth when one chart gives a smooth local
coordinate form near each point. -/
theorem contMDiffAt_native_bilinear_section_of_chart
    (P : ExerciseGluingPreparation C g n genera X)
    (s : ∀ b : P.GluedCarrier, TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ)
    (b : P.GluedCarrier) (e : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : e ∈ P.gluedComplexAtlas) (hs : b ∈ e.source)
    (G : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (hG : ContDiffAt ℝ ∞ G (e b))
    (hform : ∀ᶠ c in 𝓝 b, c ∈ e.source ∧ ∀ v u : ℂ,
      s c (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
        (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ c v)
        (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
        (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ c u) = G (e c) v u) :
    ContMDiffAt (modelWithCornersSelf ℝ ℂ)
      ((modelWithCornersSelf ℝ ℂ).prod (modelWithCornersSelf ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)))
      ∞ (fun c => TotalSpace.mk' (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) c (s c)) b := by
  let t := (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
    (⟨e, he⟩ : atlas ℂ P.GluedCarrier)
  letI : MemTrivializationAtlas t := ⟨⟨⟨e, he⟩, rfl⟩⟩
  letI : ContMDiffVectorBundle ∞ ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)
      (modelWithCornersSelf ℝ ℂ) := inferInstance
  letI : ContMDiffVectorBundle ∞ ℂ
      (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).Fiber
      (modelWithCornersSelf ℝ ℂ) := inferInstanceAs
    (ContMDiffVectorBundle ∞ ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)
      (modelWithCornersSelf ℝ ℂ))
  let tR := trivializationAt ℝ (fun _ : P.GluedCarrier => ℝ) b
  let t₂ := t.continuousLinearMap (RingHom.id ℝ) tR
  let t₃ := t.continuousLinearMap (RingHom.id ℝ) t₂
  have ht : b ∈ t₃.baseSet := by
    change b ∈ e.source ∩ (e.source ∩ univ)
    exact ⟨hs, hs, mem_univ b⟩
  rw [t₃.contMDiffAt_section_iff ht]
  have hchart : ContMDiffAt (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞ e b :=
    contMDiffAt_of_mem_maximalAtlas
      (StructureGroupoid.subset_maximalAtlas _ he) hs
  apply (hG.contMDiffAt.comp b hchart).congr_of_eventuallyEq
  filter_upwards [hform] with c hc
  ext v u
  change ((t₃ ⟨c, s c⟩).2 v) u = G (e c) v u
  simp only [t₃, t₂, Bundle.Trivialization.continuousLinearMap_apply, comp_apply]
  change (t₂.continuousLinearMapAt ℝ c (s c (t.symmL ℝ c v))) u = _
  rw [Bundle.Trivialization.continuousLinearMapAt_apply]
  rw [t₂.coe_linearMapAt_of_mem (by exact ⟨hc.1, mem_univ c⟩)]
  simp only [t₂, Bundle.Trivialization.continuousLinearMap_apply, comp_apply]
  rw [Bundle.Trivialization.continuousLinearMapAt_apply]
  change tR.linearMapAt ℝ c (s c (t.symmL ℝ c v) (t.symmL ℝ c u)) = _
  have hr (a : ℝ) : tR.linearMapAt ℝ c a = a := by
    change (Bundle.Trivial.trivialization P.GluedCarrier ℝ).linearMapAt ℝ c a = a
    rw [Bundle.Trivial.linearMapAt_trivialization]
    rfl
  exact (hr _).trans (hc.2 v u)

set_option backward.isDefEq.respectTransparency false in
/-- Genuine global C∞ regularity of the constructed native tangent tensor. -/
theorem gluedSmoothTangentInner_contMDiff_section
    (P : ExerciseGluingPreparation C g n genera X) {ε : ℝ} (hε : 0 < ε) :
    ContMDiff (modelWithCornersSelf ℝ ℂ)
      ((modelWithCornersSelf ℝ ℂ).prod (modelWithCornersSelf ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)))
      ∞ (fun b : P.GluedCarrier => TotalSpace.mk' (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
        b (P.gluedSmoothTangentInner ε b)) := by
  intro b
  obtain ⟨e, he, hs, G, hG, hform⟩ := P.gluedSmoothTangentInner_exists_smooth_chart hε b
  exact contMDiffAt_native_bilinear_section_of_chart P (P.gluedSmoothTangentInner ε)
    b e he hs G hG hform

/-- The actual localized approximation is a smooth positive Riemannian
metric on the unchanged original native tangent bundle. -/
def gluedSmoothRiemannianMetric
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 < ε) :
    Bundle.ContMDiffRiemannianMetric (modelWithCornersSelf ℝ ℂ) ∞ ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) where
  inner := P.gluedSmoothTangentInner ε
  symm := P.gluedSmoothTangentInner_symm ε
  pos := P.gluedSmoothTangentInner_pos hε.le
  isVonNBounded := P.gluedSmoothTangentInner_isVonNBounded hε.le
  contMDiff := P.gluedSmoothTangentInner_contMDiff_section hε

@[simp] theorem gluedSmoothRiemannianMetric_inner
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 < ε)
    (b : P.GluedCarrier) :
    (P.gluedSmoothRiemannianMetric ε hε).inner b = P.gluedSmoothTangentInner ε b := rfl

/-- Forgetting smooth regularity gives exactly the continuous metric
used to construct the native approximating distance. -/
@[simp] theorem gluedSmoothRiemannianMetric_toContinuousRiemannianMetric
    (P : ExerciseGluingPreparation C g n genera X) (ε : ℝ) (hε : 0 < ε) :
    (P.gluedSmoothRiemannianMetric ε hε).toContinuousRiemannianMetric =
      P.gluedSmoothContinuousRiemannianMetric ε hε.le := rfl

#print axioms gluedSmoothRiemannianMetric
#print axioms gluedSmoothRiemannianMetric_toContinuousRiemannianMetric
#print axioms gluedSmoothTangentInner_contMDiff_section
#print axioms gluedSmoothTangentInner_exists_smooth_chart
#print axioms gluedSmoothTangentInner_in_isolated_seam_chart
#print axioms exists_interior_chart_of_outside_closedThinSeamCollars

end
end SystolicGrowth.ExerciseGluingPreparation

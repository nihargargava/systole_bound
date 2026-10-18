module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingAtlasMetric
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

@[expose] public section

/-!
# The continuous metric on the actual native glued tangent bundle

At each basepoint, the native tangent fiber uses the model coordinates of
its preferred chart. We use that actual chart's positive bilinear form.
The full atlas transition identity identifies its expression in every
other actual chart, yielding continuity in the original native bundle
topology. No replacement fiber topology, tensor-compatibility premise or
distance-identification claim is introduced.
-/

open Set Filter Bundle ContinuousLinearMap
open scoped Manifold Topology

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

set_option backward.isDefEq.respectTransparency false in
/-- The actual tangent fiber's preferred-chart expression. The native fiber
topology and linear structure are retained. -/
noncomputable def gluedTangentInner
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ :=
  P.gluingChartTangentForm (chartAt ℂ b) (chartAt ℂ b b)

set_option backward.isDefEq.respectTransparency false in
theorem gluedTangentInner_symm
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier)
    (v u : TangentSpace (modelWithCornersSelf ℝ ℂ) b) :
    P.gluedTangentInner b v u = P.gluedTangentInner b u v := by
  exact P.gluingChartTangentForm_symm (chartAt ℂ b) (chartAt ℂ b b) v u

set_option backward.isDefEq.respectTransparency false in
theorem gluedTangentInner_pos
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier)
    (v : TangentSpace (modelWithCornersSelf ℝ ℂ) b) (hv : v ≠ 0) :
    0 < P.gluedTangentInner b v v := by
  exact P.gluingChartTangentForm_pos (chartAt ℂ b)
    ((chartAt ℂ b).map_source (mem_chart_source ℂ b)) v hv

set_option backward.isDefEq.respectTransparency false in
theorem gluedTangentInner_isVonNBounded
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    Bornology.IsVonNBounded ℝ
      {v : TangentSpace (modelWithCornersSelf ℝ ℂ) b | P.gluedTangentInner b v v < 1} := by
  change Bornology.IsVonNBounded ℝ
    {v : ℂ | P.gluingChartTangentForm (chartAt ℂ b) (chartAt ℂ b b) v v < 1}
  exact P.gluingChartTangentForm_isVonNBounded (chartAt ℂ b)
    ((chartAt ℂ b).map_source (mem_chart_source ℂ b))

/-- In the actual boundaryless complex model, the native tangent bundle's
coordinate changes are precisely the true derivatives of native chart transitions. -/
theorem gluedTangentCoordChange_eq_fderiv
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : atlas ℂ P.GluedCarrier) (b : P.GluedCarrier) :
    (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).coordChange e e' b =
      fderiv ℝ (e.1.symm.trans e'.1) (e.1 b) := by
  rw [tangentBundleCore_coordChange]
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.range_id, fderivWithin_univ]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The global form agrees with every actual atlas chart in the native
tangent-bundle trivialization associated to that chart. -/
theorem gluedTangentInner_in_chart
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (v u : ℂ) :
    let t := (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
      (⟨e, he⟩ : atlas ℂ P.GluedCarrier)
    P.gluedTangentInner b (t.symmL ℝ b v) (t.symmL ℝ b u) =
      P.gluingChartTangentForm e (e b) v u := by
  dsimp only
  let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
  let i : atlas ℂ P.GluedCarrier := ⟨e, he⟩
  have hs (w : ℂ) : (Z.localTriv i).symmL ℝ b w =
      Z.coordChange i (achart ℂ b) b w := by
    exact congrArg (fun f : ℂ →L[ℝ] Z.Fiber b => f w)
      (Z.localTriv_symmL (by exact hb))
  apply (congrArg₂ (fun a c : Z.Fiber b => P.gluedTangentInner b a c) (hs v) (hs u)).trans
  change P.gluingChartTangentForm (chartAt ℂ b) (chartAt ℂ b b)
    (Z.coordChange i (achart ℂ b) b v) (Z.coordChange i (achart ℂ b) b u) = _
  rw [P.gluedTangentCoordChange_eq_fderiv]
  have hx : e b ∈ (e.symm.trans (chartAt ℂ b)).source := by
    refine ⟨e.map_source hb, ?_⟩
    change e.symm (e b) ∈ (chartAt ℂ b).source
    rw [e.left_inv hb]
    exact mem_chart_source ℂ b
  simpa only [i, achart_val, OpenPartialHomeomorph.trans_apply, e.left_inv hb] using
    P.gluingChartTangentForm_transition_pullback e (chartAt ℂ b)
      he (chart_mem_atlas ℂ b) hx v u

set_option backward.isDefEq.respectTransparency false in
/-- In a fixed preferred trivialization, the actual global bilinear field
is exactly that fixed chart's continuous coordinate form. -/
theorem gluedTangentInner_in_preferred_coordinates
    (P : ExerciseGluingPreparation C g n genera X) (b₀ b : P.GluedCarrier)
    (hb : b ∈ (chartAt ℂ b₀).source) :
    inCoordinates ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)
      (ℂ →L[ℝ] ℝ) (fun b => TangentSpace (modelWithCornersSelf ℝ ℂ) b →L[ℝ] ℝ)
      b₀ b b₀ b (P.gluedTangentInner b) =
      P.gluingChartTangentForm (chartAt ℂ b₀) (chartAt ℂ b₀ b) := by
  have ht : b ∈ (trivializationAt ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) b₀).baseSet := hb
  ext v u
  rw [inCoordinates_apply_eq₂ ht ht (Set.mem_univ b)]
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
    change (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) b₀).symm b w =
      (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) b₀).symmL ℝ b w
    exact ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) b₀).symmL_apply ht w).symm
  have hi := congrArg₂ (fun a c : TangentSpace (modelWithCornersSelf ℝ ℂ) b =>
    P.gluedTangentInner b a c) (hs v) (hs u)
  exact hi.trans (P.gluedTangentInner_in_chart (chartAt ℂ b₀)
    (chart_mem_atlas ℂ b₀) b hb v u)

set_option backward.isDefEq.respectTransparency false in
/-- Continuity is in the original native bilinear-form bundle, including
the original tangent-bundle topology above every signed-radius zero seam. -/
theorem gluedTangentInner_continuous_section
    (P : ExerciseGluingPreparation C g n genera X) :
    Continuous (fun b : P.GluedCarrier =>
      TotalSpace.mk' (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) b (P.gluedTangentInner b)) := by
  rw [continuous_iff_continuousAt]
  intro b₀
  rw [FiberBundle.continuousAt_section]
  have hlocal : ContinuousAt (fun b : P.GluedCarrier =>
      P.gluingChartTangentForm (chartAt ℂ b₀) (chartAt ℂ b₀ b)) b₀ :=
    ((P.gluingChartTangentForm_continuousOn (chartAt ℂ b₀)).continuousAt
      ((chartAt ℂ b₀).open_target.mem_nhds
        ((chartAt ℂ b₀).map_source (mem_chart_source ℂ b₀)))).comp
      ((chartAt ℂ b₀).continuousAt (mem_chart_source ℂ b₀))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [(chartAt ℂ b₀).open_source.mem_nhds (mem_chart_source ℂ b₀)] with b hb
  rw [hom_trivializationAt_apply]
  exact P.gluedTangentInner_in_preferred_coordinates b₀ b hb

/-- The actual continuous positive Riemannian metric on the original
native tangent bundle. No global bundle instance is registered here. -/
noncomputable def gluedContinuousRiemannianMetric
    (P : ExerciseGluingPreparation C g n genera X) :
    Bundle.ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) where
  inner := P.gluedTangentInner
  symm := P.gluedTangentInner_symm
  pos := P.gluedTangentInner_pos
  isVonNBounded := P.gluedTangentInner_isVonNBounded
  continuous := P.gluedTangentInner_continuous_section

@[simp] theorem gluedContinuousRiemannianMetric_inner
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    P.gluedContinuousRiemannianMetric.inner b = P.gluedTangentInner b := rfl

#print axioms gluedTangentInner_symm
#print axioms gluedTangentInner_pos
#print axioms gluedTangentInner_isVonNBounded
#print axioms gluedTangentCoordChange_eq_fderiv
#print axioms gluedTangentInner_in_chart
#print axioms gluedTangentInner_in_preferred_coordinates
#print axioms gluedTangentInner_continuous_section
#print axioms gluedContinuousRiemannianMetric
#print axioms gluedContinuousRiemannianMetric_inner

end SystolicGrowth.ExerciseGluingPreparation

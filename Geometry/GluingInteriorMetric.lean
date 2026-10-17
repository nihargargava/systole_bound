module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingDeckMetric

@[expose] public section

/-!
# Actual interior-atlas tangent compatibility

Every transition between two genuine interior atlas entries is locally one
fixed deck transformation. This local identity, derived from the actual
seam-free quotient fibers and concrete chart inverses, transfers the proved
deck invariance to the true derivative of the native coordinate transition.
The conclusion holds on its literal overlap source and arbitrary pairs of
tangent vectors; no derivative or tensor-compatibility premise is supplied.
-/

open Set Metric UpperHalfPlane Filter
open scoped UpperHalfPlane MatrixGroups Topology ComplexConjugate

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- An arbitrary pair of actual interior atlas entries has, at each point
of its literal native overlap, one genuine local deck expression. -/
theorem gluedInteriorComplexAtlas_transition_eventually_eq_deck
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : P.IsGluedInteriorComplexChart e) (he' : P.IsGluedInteriorComplexChart e')
    (x : ℂ) (hx : x ∈ (e.symm.trans e').source) :
    0 < x.im ∧ ∃ γ : SL(2, ℝ),
      (e.symm.trans e' : ℂ → ℂ) =ᶠ[𝓝 x] gluingDeckComplex γ := by
  obtain ⟨i, z, ρ, hρ, _h4, hq, hf, rfl⟩ := he
  obtain ⟨j, z', ρ', hρ', _h4', hq', hf', rfl⟩ := he'
  change x ∈ (P.gluedInteriorComplexChart i z ρ hρ hq hf).target ∧
    (P.gluedInteriorComplexChart i z ρ hρ hq hf).symm x ∈
      (P.gluedInteriorComplexChart j z' ρ' hρ' hq' hf').source at hx
  have htarget := hx.1
  rw [gluedInteriorComplexChart_target] at htarget
  obtain ⟨u, hu⟩ := htarget
  have hsource := hx.2
  rw [gluedInteriorComplexChart_source] at hsource
  obtain ⟨v, hv⟩ := hsource
  have hxu : (P.gluedInteriorComplexChart i z ρ hρ hq hf).symm x =
      P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' u.1, hq u⟩) := by
    rw [← hu, gluedInteriorComplexChart_symm_apply]
  have hpieces := P.gluedMk_eq_of_not_mem_chainSeamSet
    (P.componentInteriorPoint_not_mem_chainSeamSet i ⟨Quotient.mk'' u.1, hq u⟩)
    (hxu.symm.trans hv.symm)
  have hij : i = j := congrArg (fun a : P.ChainPieces => a.1) hpieces
  subst j
  have hxim : 0 < x.im := by
    rw [← hu]
    exact u.1.im_pos
  have hF : ∀ᶠ y in 𝓝 x, ∃ hy :
      (Quotient.mk'' (UpperHalfPlane.ofComplex y) : (X i).Carrier) ∈
        P.componentInteriorSet i,
      (P.gluedInteriorComplexChart i z ρ hρ hq hf).symm y =
        P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' (UpperHalfPlane.ofComplex y), hy⟩) := by
    filter_upwards [(P.gluedInteriorComplexChart i z ρ hρ hq hf).open_target.mem_nhds hx.1]
      with y hy
    rw [gluedInteriorComplexChart_target] at hy
    obtain ⟨w, rfl⟩ := hy
    simpa only [UpperHalfPlane.ofComplex_apply] using
      (show ∃ hw : (Quotient.mk'' w.1 : (X i).Carrier) ∈ P.componentInteriorSet i,
        (P.gluedInteriorComplexChart i z ρ hρ hq hf).symm (w.1 : ℂ) =
          P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hw⟩) from
        ⟨hq w, P.gluedInteriorComplexChart_symm_apply i z ρ hρ hq hf w⟩)
  obtain ⟨γ, hγ⟩ := P.gluedInteriorComplexChart_eventually_eq_deck i z' ρ' hρ' hq' hf'
    UpperHalfPlane.ofComplex (P.gluedInteriorComplexChart i z ρ hρ hq hf).symm x
    (UpperHalfPlane.contMDiffAt_ofComplex (n := ⊤) hxim).continuousAt hx.2 hF
  refine ⟨hxim, γ.1, ?_⟩
  filter_upwards [hγ, UpperHalfPlane.eventuallyEq_coe_comp_ofComplex hxim] with y hy hy'
  exact hy.trans ((gluingDeckComplex_coe γ.1 _).symm.trans
    (congrArg (gluingDeckComplex γ.1) hy'))

/-- Both coordinates of an actual interior transition lie in the genuine
upper half-plane, rather than the fallback branch of `ofComplex`. -/
theorem gluedInteriorComplexAtlas_transition_im_pos
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : P.IsGluedInteriorComplexChart e) (he' : P.IsGluedInteriorComplexChart e')
    (x : ℂ) (hx : x ∈ (e.symm.trans e').source) :
    0 < x.im ∧ 0 < ((e.symm.trans e') x).im := by
  obtain ⟨hxim, γ, hγ⟩ := P.gluedInteriorComplexAtlas_transition_eventually_eq_deck e e' he he' x hx
  refine ⟨hxim, ?_⟩
  have hy : (e.symm.trans e') x = ((γ • (⟨x, hxim⟩ : ℍ) : ℍ) : ℂ) :=
    hγ.eq_of_nhds.trans (gluingDeckComplex_coe γ ⟨x, hxim⟩)
  rw [hy]
  exact (γ • (⟨x, hxim⟩ : ℍ) : ℍ).im_pos

/-- Actual interior-atlas coordinate transitions preserve the half-plane
Poincare tangent form using their true real analytic derivative. -/
theorem gluedInteriorComplexAtlas_transition_tangentForm_pullback
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : P.IsGluedInteriorComplexChart e) (he' : P.IsGluedInteriorComplexChart e')
    (x : ℂ) (hx : x ∈ (e.symm.trans e').source) (v u : ℂ) :
    gluingHalfPlaneTangentForm (UpperHalfPlane.ofComplex ((e.symm.trans e') x))
      (fderiv ℝ (e.symm.trans e') x v) (fderiv ℝ (e.symm.trans e') x u) =
      gluingHalfPlaneTangentForm (UpperHalfPlane.ofComplex x) v u := by
  obtain ⟨hxim, γ, hγ⟩ := P.gluedInteriorComplexAtlas_transition_eventually_eq_deck e e' he he' x hx
  let z : ℍ := ⟨x, hxim⟩
  have hy : (e.symm.trans e') x = ((γ • z : ℍ) : ℂ) :=
    hγ.eq_of_nhds.trans (gluingDeckComplex_coe γ z)
  rw [hγ.fderiv_eq, hy, UpperHalfPlane.ofComplex_apply,
    UpperHalfPlane.ofComplex_apply_of_im_pos hxim]
  exact gluingDeckComplex_fderiv_tangentForm_pullback γ z v u

/-- The same native compatibility in literal complex coordinates, ready
for coordinate tensor descent without any totalization of the basepoint. -/
theorem gluedInteriorComplexAtlas_transition_poincare_pullback
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : P.IsGluedInteriorComplexChart e) (he' : P.IsGluedInteriorComplexChart e')
    (x : ℂ) (hx : x ∈ (e.symm.trans e').source) (v u : ℂ) :
    ((fderiv ℝ (e.symm.trans e') x v) * conj (fderiv ℝ (e.symm.trans e') x u)).re /
      ((e.symm.trans e') x).im ^ 2 = (v * conj u).re / x.im ^ 2 := by
  have hp := P.gluedInteriorComplexAtlas_transition_im_pos e e' he he' x hx
  simpa only [gluingHalfPlaneTangentForm,
    UpperHalfPlane.ofComplex_apply_of_im_pos hp.1,
    UpperHalfPlane.ofComplex_apply_of_im_pos hp.2, UpperHalfPlane.mk_im] using
    P.gluedInteriorComplexAtlas_transition_tangentForm_pullback e e' he he' x hx v u

#print axioms gluedInteriorComplexAtlas_transition_eventually_eq_deck
#print axioms gluedInteriorComplexAtlas_transition_im_pos
#print axioms gluedInteriorComplexAtlas_transition_tangentForm_pullback
#print axioms gluedInteriorComplexAtlas_transition_poincare_pullback

end SystolicGrowth.ExerciseGluingPreparation

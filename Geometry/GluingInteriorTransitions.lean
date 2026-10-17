module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChartEvaluations
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

@[expose] public section

/-!
# Actual local deck transformations in the glued interior charts

Interior coordinate changes are locally the actual action of one fixed
element of the original component's deck group. Their smoothness follows
from its explicit Moebius action; no smooth-transition hypothesis is used.
-/

open Set Metric UpperHalfPlane Filter
open scoped UpperHalfPlane MatrixGroups Topology

namespace SystolicGrowth

/-- The actual rational expression of an orientation-preserving deck action. -/
noncomputable def gluingDeckComplex (γ : SL(2, ℝ)) (z : ℂ) : ℂ :=
  ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ))

@[simp] theorem gluingDeckComplex_coe (γ : SL(2, ℝ)) (z : ℍ) :
    gluingDeckComplex γ z = ((γ • z : ℍ) : ℂ) := by
  simpa [gluingDeckComplex] using (coe_specialLinearGroup_apply γ z).symm

/-- The denominator is nonzero on the actual upper half-plane. -/
theorem gluingDeckComplex_denom_ne_zero (γ : SL(2, ℝ)) {z : ℂ} (hz : 0 < z.im) :
    (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) ≠ 0 := by
  have h := denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) (⟨z, hz⟩ : ℍ)
  simpa [denom] using h

/-- Actual deck transformations are real-smooth at every upper-half-plane point. -/
theorem gluingDeckComplex_contDiffAt (γ : SL(2, ℝ)) {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ⊤ (gluingDeckComplex γ) z := by
  change ContDiffAt ℝ ⊤ (fun w : ℂ =>
    ((γ 0 0 : ℂ) * w + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * w + (γ 1 1 : ℂ))) z
  simp only [div_eq_mul_inv]
  exact (contDiffAt_const.mul contDiffAt_id |>.add contDiffAt_const).mul
    ((contDiffAt_const.mul contDiffAt_id |>.add contDiffAt_const).inv
      (gluingDeckComplex_denom_ne_zero γ hz))

/-- The actual complex derivative coefficient of the deck action. -/
noncomputable def gluingDeckComplexDeriv (γ : SL(2, ℝ)) (z : ℂ) : ℂ :=
  1 / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ 2

theorem gluingDeckComplex_hasDerivAt (γ : SL(2, ℝ)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (gluingDeckComplex γ) (gluingDeckComplexDeriv γ z) z := by
  have hdetR : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = (1 : ℝ) := by
    simpa only [Matrix.det_fin_two] using γ.property
  have hdet : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
    exact_mod_cast hdetR
  have h := (((hasDerivAt_id z).const_mul (γ 0 0 : ℂ)).add_const (γ 0 1 : ℂ)).div
    (((hasDerivAt_id z).const_mul (γ 1 0 : ℂ)).add_const (γ 1 1 : ℂ))
    (gluingDeckComplex_denom_ne_zero γ hz)
  convert h using 1 <;> try rfl
  simp only [gluingDeckComplexDeriv, mul_one, id_eq]
  congr 1
  linear_combination -hdet

/-- The actual derivative is an invertible real-linear map. -/
noncomputable def gluingDeckComplexDerivEquiv (γ : SL(2, ℝ)) (z : ℂ)
    (hz : 0 < z.im) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ)
    (Units.mk0 (gluingDeckComplexDeriv γ z)
      (one_div_ne_zero (pow_ne_zero 2 (gluingDeckComplex_denom_ne_zero γ hz))))

theorem gluingDeckComplex_hasFDerivAt_equiv (γ : SL(2, ℝ)) {z : ℂ} (hz : 0 < z.im) :
    HasFDerivAt (gluingDeckComplex γ) (gluingDeckComplexDerivEquiv γ z hz : ℂ →L[ℝ] ℂ) z := by
  apply ((gluingDeckComplex_hasDerivAt γ hz).hasFDerivAt.restrictScalars ℝ).congr_fderiv
  ext v
  change v * gluingDeckComplexDeriv γ z = gluingDeckComplexDeriv γ z * v
  exact mul_comm _ _

/-- Actual deck translates represent the same point of the original component quotient. -/
theorem gluingQuotientMk_smul_eq {g : ℕ} (X : ClosedHyperbolicSurface g)
    (γ : X.deckGroup) (z : ℍ) :
    (Quotient.mk'' (γ • z) : X.Carrier) = Quotient.mk'' z := by
  apply Quotient.sound
  exact MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨γ, rfl⟩)

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- An actual continuous local lift into a component is evaluated by an
interior chart using one fixed deck element on a genuine neighborhood. -/
theorem gluedInteriorComplexChart_eventually_eq_deck
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (z : ℍ) (ρ : ℝ) (hρ : 0 < ρ)
    (hq : ∀ w : ball z ρ,
      (Quotient.mk'' w.1 : (X i).Carrier) ∈ P.componentInteriorSet i)
    (he : Topology.IsOpenEmbedding (fun w : ball z ρ =>
      P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq w⟩)))
    {A : Type*} [TopologicalSpace A] (f : A → ℍ) (F : A → P.GluedCarrier) (a : A)
    (hf : ContinuousAt f a)
    (ha : F a ∈ (P.gluedInteriorComplexChart i z ρ hρ hq he).source)
    (hF : ∀ᶠ x in 𝓝 a, ∃ hfx : (Quotient.mk'' (f x) : (X i).Carrier) ∈
        P.componentInteriorSet i,
      F x = P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' (f x), hfx⟩)) :
    ∃ γ : (X i).deckGroup, ∀ᶠ x in 𝓝 a,
      P.gluedInteriorComplexChart i z ρ hρ hq he (F x) = ((γ • f x : ℍ) : ℂ) := by
  obtain ⟨hfa, hFa⟩ := hF.self_of_nhds
  rw [gluedInteriorComplexChart_source] at ha
  obtain ⟨w, hw⟩ := ha
  have hsub : (⟨Quotient.mk'' w.1, hq w⟩ : P.componentInteriorSet i) =
      ⟨Quotient.mk'' (f a), hfa⟩ :=
    (P.gluedComponentInterior_isOpenEmbedding i).injective (hw.trans hFa)
  have hquot := congrArg Subtype.val hsub
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.exact hquot))
  have hc : ContinuousAt (fun x => (γ • f x : ℍ)) a :=
    (continuous_const_smul γ).continuousAt.comp hf
  have hball : ∀ᶠ x in 𝓝 a, (γ • f x : ℍ) ∈ ball z ρ :=
    hc.eventually (isOpen_ball.mem_nhds (by simpa only [hγ] using w.2))
  refine ⟨γ, ?_⟩
  filter_upwards [hF, hball] with x hx hb
  obtain ⟨hfx, hFx⟩ := hx
  let u : ball z ρ := ⟨γ • f x, hb⟩
  have hqeq : (Quotient.mk'' u.1 : (X i).Carrier) = Quotient.mk'' (f x) :=
    gluingQuotientMk_smul_eq (X i) γ (f x)
  have hpoint : P.componentInteriorPoint i ⟨Quotient.mk'' u.1, hq u⟩ =
      P.componentInteriorPoint i ⟨Quotient.mk'' (f x), hfx⟩ := by
    congr 1
    exact Subtype.ext hqeq
  rw [hFx, ← hpoint, gluedInteriorComplexChart_apply]

/-- Every actual transition between two interior atlas charts is smooth on
its exact native overlap. Different component interiors cannot acquire an
identification across a seam. -/
theorem gluedInteriorComplexAtlas_transition_contDiffOn
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : P.IsGluedInteriorComplexChart e) (he' : P.IsGluedInteriorComplexChart e') :
    ContDiffOn ℝ ⊤ (e.symm.trans e') (e.symm.trans e').source := by
  obtain ⟨i, z, ρ, hρ, _h4, hq, hf, rfl⟩ := he
  obtain ⟨j, z', ρ', hρ', _h4', hq', hf', rfl⟩ := he'
  intro x hx
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
  have hcoe : ∀ᶠ y in 𝓝 x, ((γ • UpperHalfPlane.ofComplex y : ℍ) : ℂ) =
      gluingDeckComplex γ.1 y := by
    filter_upwards [UpperHalfPlane.eventuallyEq_coe_comp_ofComplex hxim] with y hy
    calc
      ((γ • UpperHalfPlane.ofComplex y : ℍ) : ℂ) =
          gluingDeckComplex γ.1 (UpperHalfPlane.ofComplex y) :=
        (gluingDeckComplex_coe γ.1 _).symm
      _ = gluingDeckComplex γ.1 y :=
        congrArg (gluingDeckComplex γ.1) hy
  have hlocal : (fun y => P.gluedInteriorComplexChart i z' ρ' hρ' hq' hf'
      ((P.gluedInteriorComplexChart i z ρ hρ hq hf).symm y)) =ᶠ[𝓝 x]
      gluingDeckComplex γ.1 := by
    filter_upwards [hγ, hcoe] with y hy hy'
    exact hy.trans hy'
  exact ((gluingDeckComplex_contDiffAt γ.1 hxim).congr_of_eventuallyEq hlocal).contDiffWithinAt

end ExerciseGluingPreparation

#print axioms gluingDeckComplex_contDiffAt
#print axioms gluingQuotientMk_smul_eq
#print axioms gluingDeckComplex_hasFDerivAt_equiv
#print axioms ExerciseGluingPreparation.gluedInteriorComplexChart_eventually_eq_deck
#print axioms ExerciseGluingPreparation.gluedInteriorComplexAtlas_transition_contDiffOn

end SystolicGrowth

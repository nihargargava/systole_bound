module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingPolarDiffeomorph
public import Geometry.GluingInteriorTransitions

@[expose] public section

/-!
# Actual smooth seam-to-interior transitions

The outgoing and reflected incoming coordinate maps are the explicit
affine maps `(r - re z, im z)` and `(r + re z, -im z)`. Composing their
actual homeomorphisms with the constructed positive-radius local polar
homeomorphism gives genuine smooth local inverses. Actual quotient chart
evaluations then identify every native seam-to-interior transition locally
with one deck map composed with the correct signed polar branch. The overlap
determines its adjacent component and excludes signed radius zero. Both
smoothness and an invertible differential are derived; no orientation or
gluing-distance assertion is made.
-/

open Set Metric UpperHalfPlane Filter
open scoped UpperHalfPlane Topology MatrixGroups

namespace SystolicGrowth

/-- Actual outgoing signed seam coordinates, read in hyperbolic polar parameters. -/
def gluingOutgoingPolarCoordinates (r : ℝ) (z : ℂ) : ℝ × ℝ := (r - z.re, z.im)

/-- Actual incoming signed seam coordinates, with the reflected angular direction. -/
def gluingIncomingPolarCoordinates (r : ℝ) (z : ℂ) : ℝ × ℝ := (r + z.re, -z.im)

theorem gluingOutgoingPolarCoordinates_contDiff (r : ℝ) :
    ContDiff ℝ ⊤ (gluingOutgoingPolarCoordinates r) :=
  (contDiff_const.sub Complex.reCLM.contDiff).prodMk Complex.imCLM.contDiff

theorem gluingIncomingPolarCoordinates_contDiff (r : ℝ) :
    ContDiff ℝ ⊤ (gluingIncomingPolarCoordinates r) :=
  (contDiff_const.add Complex.reCLM.contDiff).prodMk Complex.imCLM.contDiff.neg

/-- The explicit outgoing affine coordinate homeomorphism. -/
noncomputable def gluingOutgoingPolarCoordinateHomeomorph (r : ℝ) : ℂ ≃ₜ ℝ × ℝ where
  toFun := gluingOutgoingPolarCoordinates r
  invFun p := Complex.equivRealProdCLM.symm (r - p.1, p.2)
  left_inv z := by
    apply Complex.ext <;> simp [gluingOutgoingPolarCoordinates,
      Complex.equivRealProdCLM_symm_apply]
  right_inv p := by
    apply Prod.ext <;> simp [gluingOutgoingPolarCoordinates,
      Complex.equivRealProdCLM_symm_apply]
  continuous_toFun := (gluingOutgoingPolarCoordinates_contDiff r).continuous
  continuous_invFun := Complex.equivRealProdCLM.symm.continuous.comp
    ((continuous_const.sub continuous_fst).prodMk continuous_snd)

/-- The explicit reflected incoming affine coordinate homeomorphism. -/
noncomputable def gluingIncomingPolarCoordinateHomeomorph (r : ℝ) : ℂ ≃ₜ ℝ × ℝ where
  toFun := gluingIncomingPolarCoordinates r
  invFun p := Complex.equivRealProdCLM.symm (p.1 - r, -p.2)
  left_inv z := by
    apply Complex.ext <;> simp [gluingIncomingPolarCoordinates,
      Complex.equivRealProdCLM_symm_apply]
  right_inv p := by
    apply Prod.ext <;> simp [gluingIncomingPolarCoordinates,
      Complex.equivRealProdCLM_symm_apply]
  continuous_toFun := (gluingIncomingPolarCoordinates_contDiff r).continuous
  continuous_invFun := Complex.equivRealProdCLM.symm.continuous.comp
    ((continuous_fst.sub continuous_const).prodMk continuous_snd.neg)

theorem gluingOutgoingPolarCoordinateHomeomorph_symm_contDiff (r : ℝ) :
    ContDiff ℝ ⊤ (gluingOutgoingPolarCoordinateHomeomorph r).symm :=
  Complex.equivRealProdCLM.symm.contDiff.comp
    ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd)

theorem gluingIncomingPolarCoordinateHomeomorph_symm_contDiff (r : ℝ) :
    ContDiff ℝ ⊤ (gluingIncomingPolarCoordinateHomeomorph r).symm :=
  Complex.equivRealProdCLM.symm.contDiff.comp
    ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd.neg)

/-- The actual outgoing lifted half-plane coordinate expression. -/
noncomputable def gluingOutgoingPolarLift (o : ℍ) (r : ℝ) (z : ℂ) : ℂ :=
  gluingPolarLift o (gluingOutgoingPolarCoordinates r z)

/-- The actual reflected incoming lifted half-plane coordinate expression. -/
noncomputable def gluingIncomingPolarLift (o : ℍ) (r : ℝ) (z : ℂ) : ℂ :=
  gluingPolarLift o (gluingIncomingPolarCoordinates r z)

theorem gluingOutgoingPolarLift_contDiff (o : ℍ) (r : ℝ) :
    ContDiff ℝ ⊤ (gluingOutgoingPolarLift o r) :=
  (gluingPolarLift_contDiff o).comp (gluingOutgoingPolarCoordinates_contDiff r)

theorem gluingIncomingPolarLift_contDiff (o : ℍ) (r : ℝ) :
    ContDiff ℝ ⊤ (gluingIncomingPolarLift o r) :=
  (gluingPolarLift_contDiff o).comp (gluingIncomingPolarCoordinates_contDiff r)

/-- The invertible linear part of the actual outgoing affine coordinates. -/
noncomputable def gluingOutgoingPolarCoordinateDeriv : ℂ ≃L[ℝ] ℝ × ℝ :=
  Complex.equivRealProdCLM.trans
    ((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
      (Units.mk0 (-1 : ℝ) (by norm_num))).prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))

/-- The invertible linear part of the reflected incoming affine coordinates. -/
noncomputable def gluingIncomingPolarCoordinateDeriv : ℂ ≃L[ℝ] ℝ × ℝ :=
  Complex.equivRealProdCLM.trans
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
      (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
        (Units.mk0 (-1 : ℝ) (by norm_num))))

theorem gluingOutgoingPolarCoordinates_hasFDerivAt (r : ℝ) (z : ℂ) :
    HasFDerivAt (gluingOutgoingPolarCoordinates r)
      (gluingOutgoingPolarCoordinateDeriv : ℂ →L[ℝ] ℝ × ℝ) z := by
  have h := ((Complex.reCLM.hasFDerivAt (x := z)).const_sub r).prodMk
    (Complex.imCLM.hasFDerivAt (x := z))
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [gluingOutgoingPolarCoordinateDeriv, ContinuousLinearEquiv.smulLeft]

theorem gluingIncomingPolarCoordinates_hasFDerivAt (r : ℝ) (z : ℂ) :
    HasFDerivAt (gluingIncomingPolarCoordinates r)
      (gluingIncomingPolarCoordinateDeriv : ℂ →L[ℝ] ℝ × ℝ) z := by
  have h := ((Complex.reCLM.hasFDerivAt (x := z)).const_add r).prodMk
    (Complex.imCLM.hasFDerivAt (x := z)).neg
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [gluingIncomingPolarCoordinateDeriv, ContinuousLinearEquiv.smulLeft]

/-- The actual outgoing lift has an invertible derivative at positive polar radius. -/
noncomputable def gluingOutgoingPolarLiftDerivEquiv (o : ℍ) (r : ℝ) (z : ℂ)
    (hz : 0 < r - z.re) : ℂ ≃L[ℝ] ℂ :=
  gluingOutgoingPolarCoordinateDeriv.trans
    (gluingPolarLiftDerivEquiv o (gluingOutgoingPolarCoordinates r z) hz)

noncomputable def gluingIncomingPolarLiftDerivEquiv (o : ℍ) (r : ℝ) (z : ℂ)
    (hz : 0 < r + z.re) : ℂ ≃L[ℝ] ℂ :=
  gluingIncomingPolarCoordinateDeriv.trans
    (gluingPolarLiftDerivEquiv o (gluingIncomingPolarCoordinates r z) hz)

theorem gluingOutgoingPolarLift_hasFDerivAt_equiv (o : ℍ) (r : ℝ) (z : ℂ)
    (hz : 0 < r - z.re) :
    HasFDerivAt (gluingOutgoingPolarLift o r)
      (gluingOutgoingPolarLiftDerivEquiv o r z hz : ℂ →L[ℝ] ℂ) z := by
  change HasFDerivAt (gluingPolarLift o ∘ gluingOutgoingPolarCoordinates r)
    ((gluingPolarLiftDerivEquiv o (gluingOutgoingPolarCoordinates r z) hz :
      (ℝ × ℝ) →L[ℝ] ℂ).comp (gluingOutgoingPolarCoordinateDeriv : ℂ →L[ℝ] ℝ × ℝ)) z
  exact (gluingPolarLift_hasFDerivAt_equiv o _ hz).comp z
    (gluingOutgoingPolarCoordinates_hasFDerivAt r z)

/-- The actual reflected incoming lift has an invertible derivative at positive polar radius. -/
theorem gluingIncomingPolarLift_hasFDerivAt_equiv (o : ℍ) (r : ℝ) (z : ℂ)
    (hz : 0 < r + z.re) :
    HasFDerivAt (gluingIncomingPolarLift o r)
      (gluingIncomingPolarLiftDerivEquiv o r z hz : ℂ →L[ℝ] ℂ) z := by
  change HasFDerivAt (gluingPolarLift o ∘ gluingIncomingPolarCoordinates r)
    ((gluingPolarLiftDerivEquiv o (gluingIncomingPolarCoordinates r z) hz :
      (ℝ × ℝ) →L[ℝ] ℂ).comp (gluingIncomingPolarCoordinateDeriv : ℂ →L[ℝ] ℝ × ℝ)) z
  exact (gluingPolarLift_hasFDerivAt_equiv o _ hz).comp z
    (gluingIncomingPolarCoordinates_hasFDerivAt r z)

/-- A native local outgoing transition chart using the actual positive-radius polar inverse. -/
noncomputable def gluingOutgoingPolarLocalHomeomorph (o : ℍ) (r : ℝ) (z : ℂ)
    (hz : 0 < r - z.re) : OpenPartialHomeomorph ℂ ℂ :=
  (gluingOutgoingPolarCoordinateHomeomorph r).toOpenPartialHomeomorph.trans
    (gluingPolarLiftLocalHomeomorph o (gluingOutgoingPolarCoordinates r z) hz)

/-- A native local incoming transition chart using the actual positive-radius polar inverse. -/
noncomputable def gluingIncomingPolarLocalHomeomorph (o : ℍ) (r : ℝ) (z : ℂ)
    (hz : 0 < r + z.re) : OpenPartialHomeomorph ℂ ℂ :=
  (gluingIncomingPolarCoordinateHomeomorph r).toOpenPartialHomeomorph.trans
    (gluingPolarLiftLocalHomeomorph o (gluingIncomingPolarCoordinates r z) hz)

@[simp] theorem gluingOutgoingPolarLocalHomeomorph_apply (o : ℍ) (r : ℝ) (z x : ℂ)
    (hz : 0 < r - z.re) :
    gluingOutgoingPolarLocalHomeomorph o r z hz x = gluingOutgoingPolarLift o r x := rfl

@[simp] theorem gluingIncomingPolarLocalHomeomorph_apply (o : ℍ) (r : ℝ) (z x : ℂ)
    (hz : 0 < r + z.re) :
    gluingIncomingPolarLocalHomeomorph o r z hz x = gluingIncomingPolarLift o r x := rfl

theorem gluingOutgoingPolarLocalHomeomorph_mem_source (o : ℍ) (r : ℝ) (z : ℂ)
    (hz : 0 < r - z.re) : z ∈ (gluingOutgoingPolarLocalHomeomorph o r z hz).source := by
  exact ⟨Set.mem_univ _, gluingPolarLiftLocalHomeomorph_mem_source o _ hz⟩

theorem gluingIncomingPolarLocalHomeomorph_mem_source (o : ℍ) (r : ℝ) (z : ℂ)
    (hz : 0 < r + z.re) : z ∈ (gluingIncomingPolarLocalHomeomorph o r z hz).source := by
  exact ⟨Set.mem_univ _, gluingPolarLiftLocalHomeomorph_mem_source o _ hz⟩

/-- The genuine outgoing local inverse is smooth at its actual polar image. -/
theorem gluingOutgoingPolarLocalHomeomorph_symm_contDiffAt (o : ℍ) (r : ℝ) (z : ℂ)
    (hz : 0 < r - z.re) :
    ContDiffAt ℝ ⊤ (gluingOutgoingPolarLocalHomeomorph o r z hz).symm
      (gluingOutgoingPolarLift o r z) :=
  (gluingOutgoingPolarCoordinateHomeomorph_symm_contDiff r).contDiffAt.comp _
    (gluingPolarLiftLocalHomeomorph_symm_contDiffAt o _ hz)

/-- The genuine reflected incoming local inverse is smooth at its actual polar image. -/
theorem gluingIncomingPolarLocalHomeomorph_symm_contDiffAt (o : ℍ) (r : ℝ) (z : ℂ)
    (hz : 0 < r + z.re) :
    ContDiffAt ℝ ⊤ (gluingIncomingPolarLocalHomeomorph o r z hz).symm
      (gluingIncomingPolarLift o r z) :=
  (gluingIncomingPolarCoordinateHomeomorph_symm_contDiff r).contDiffAt.comp _
    (gluingPolarLiftLocalHomeomorph_symm_contDiffAt o _ hz)

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

private theorem retained_mem_interior_of_chart_source
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (z : ℍ) (ρ : ℝ) (hρ : 0 < ρ)
    (hq : ∀ w : ball z ρ,
      (Quotient.mk'' w.1 : (X i).Carrier) ∈ P.componentInteriorSet i)
    (he : Topology.IsOpenEmbedding (fun w : ball z ρ =>
      P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' w.1, hq w⟩)))
    (b : P.ChainComponent i)
    (hb : P.gluedMk ⟨i, b⟩ ∈ (P.gluedInteriorComplexChart i z ρ hρ hq he).source) :
    b.1 ∈ P.componentInteriorSet i := by
  rw [gluedInteriorComplexChart_source] at hb
  obtain ⟨w, hw⟩ := hb
  have hh := P.gluedMk_eq_of_not_mem_chainSeamSet
    (P.componentInteriorPoint_not_mem_chainSeamSet i ⟨Quotient.mk'' w.1, hq w⟩) hw
  have hv : (⟨Quotient.mk'' w.1, interior_subset (hq w)⟩ : P.ChainComponent i) = b :=
    eq_of_heq (Sigma.mk.inj hh).2
  rw [← hv]
  exact hq w

/-- The actual outgoing seam/interior transition is smooth at every negative signed overlap. -/
theorem outgoingSeamInteriorTransition_eventually_eq_deck
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (z : ℍ) (ρ : ℝ) (hρ : 0 < ρ)
    (hq : ∀ w : ball z ρ,
      (Quotient.mk'' w.1 : (X (gluingChainEdgeLeft k)).Carrier) ∈
        P.componentInteriorSet (gluingChainEdgeLeft k))
    (he : Topology.IsOpenEmbedding (fun w : ball z ρ =>
      P.gluedMk (P.componentInteriorPoint (gluingChainEdgeLeft k)
        ⟨Quotient.mk'' w.1, hq w⟩)))
    (a : ℂ) (ha : a ∈ (P.seamAngularComplexChart k θ).target) (ht : a.re < 0)
    (hi : (P.seamAngularComplexChart k θ).symm a ∈
      (P.gluedInteriorComplexChart (gluingChainEdgeLeft k) z ρ hρ hq he).source) :
    ∃ γ : (X (gluingChainEdgeLeft k)).deckGroup,
      (fun x => P.gluedInteriorComplexChart (gluingChainEdgeLeft k) z ρ hρ hq he
        ((P.seamAngularComplexChart k θ).symm x)) =ᶠ[𝓝 a]
          gluingDeckComplex γ.1 ∘ gluingOutgoingPolarLift
            (P.centers (gluingChainEdgeLeft k)).2 (gluingRadius C g) := by
  let i := gluingChainEdgeLeft k
  let o := (P.centers i).2
  let r := gluingRadius C g
  let f : ℂ → ℍ := fun x => gluingPolarPoint o (Circle.exp x.im) (r - x.re)
  let F : ℂ → P.GluedCarrier := (P.seamAngularComplexChart k θ).symm
  have hf : Continuous f := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    exact (gluingOutgoingPolarLift_contDiff o r).continuous
  have hs : ∀ᶠ x in 𝓝 a, x ∈ (P.seamAngularComplexChart k θ).target ∧ x.re < 0 ∧
      F x ∈ (P.gluedInteriorComplexChart i z ρ hρ hq he).source := by
    filter_upwards [(P.seamAngularComplexChart k θ).open_target.mem_nhds ha,
      Complex.continuous_re.continuousAt.eventually (Iio_mem_nhds ht),
      ((P.seamAngularComplexChart k θ).continuousAt_symm ha).eventually
        ((P.gluedInteriorComplexChart i z ρ hρ hq he).open_source.mem_nhds hi)] with x hx hxt hxi
    exact ⟨hx, hxt, hxi⟩
  have hF : ∀ᶠ x in 𝓝 a, ∃ hfx : (Quotient.mk'' (f x) : (X i).Carrier) ∈
      P.componentInteriorSet i,
      F x = P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' (f x), hfx⟩) := by
    filter_upwards [hs] with x hx
    obtain ⟨hxt, hxθ⟩ := (P.mem_seamAngularComplexChart_target k θ x).mp hx.1
    let p : GluingSeamAngularDomain C g θ := (⟨x.re, hxt⟩, ⟨x.im, hxθ⟩)
    have hm : gluingSeamAngularModel C g θ p = x := Complex.ext rfl rfl
    have hp : F x = P.gluedMk (P.seamOutgoingPolarPoint k
        (Circle.exp p.2.1, ⟨r - p.1.1, by
          constructor
          · dsimp [p]; linarith [hx.2.1]
          · change r - p.1.1 < r + gluingDepth C g
            linarith [p.1.2.1]⟩)) := by
      exact (congrArg F hm.symm).trans
        ((P.seamAngularComplexChart_symm_apply k θ p).trans
          (P.seamAngularPoint_of_nonpos k θ p hx.2.1.le))
    let b : P.ChainComponent i := (P.seamOutgoingPolarPoint k
      (Circle.exp p.2.1, ⟨r - p.1.1, by
        constructor
        · dsimp [p]; linarith [hx.2.1]
        · change r - p.1.1 < r + gluingDepth C g
          linarith [p.1.2.1]⟩)).2
    have hb : b.1 = (Quotient.mk'' (f x) : (X i).Carrier) := rfl
    have hpb : F x = P.gluedMk ⟨i, b⟩ := hp
    have hmem := P.retained_mem_interior_of_chart_source i z ρ hρ hq he b
      (hpb ▸ hx.2.2)
    rw [hb] at hmem
    refine ⟨hmem, hp.trans ?_⟩
    apply congrArg P.gluedMk
    change (⟨i, b⟩ : P.ChainPieces) =
      P.componentInteriorPoint i ⟨Quotient.mk'' (f x), hmem⟩
    exact congrArg (fun q : P.ChainComponent i => (⟨i, q⟩ : P.ChainPieces))
      (Subtype.ext hb)
  obtain ⟨γ, hγ⟩ := P.gluedInteriorComplexChart_eventually_eq_deck i z ρ hρ hq he
    f F a hf.continuousAt hi hF
  have hEq : (fun x => P.gluedInteriorComplexChart i z ρ hρ hq he (F x)) =ᶠ[𝓝 a]
      gluingDeckComplex (γ : SL(2, ℝ)) ∘ gluingOutgoingPolarLift o r := by
    filter_upwards [hγ] with x hx
    exact hx.trans (gluingDeckComplex_coe (γ : SL(2, ℝ)) (f x)).symm
  exact ⟨γ, hEq⟩

private theorem outgoingSeamInteriorTransition_regular
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (z : ℍ) (ρ : ℝ) (hρ : 0 < ρ)
    (hq : ∀ w : ball z ρ,
      (Quotient.mk'' w.1 : (X (gluingChainEdgeLeft k)).Carrier) ∈
        P.componentInteriorSet (gluingChainEdgeLeft k))
    (he : Topology.IsOpenEmbedding (fun w : ball z ρ =>
      P.gluedMk (P.componentInteriorPoint (gluingChainEdgeLeft k)
        ⟨Quotient.mk'' w.1, hq w⟩)))
    (a : ℂ) (ha : a ∈ (P.seamAngularComplexChart k θ).target) (ht : a.re < 0)
    (hi : (P.seamAngularComplexChart k θ).symm a ∈
      (P.gluedInteriorComplexChart (gluingChainEdgeLeft k) z ρ hρ hq he).source) :
    ∃ D : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt
        (fun x => P.gluedInteriorComplexChart (gluingChainEdgeLeft k) z ρ hρ hq he
          ((P.seamAngularComplexChart k θ).symm x)) (D : ℂ →L[ℝ] ℂ) a ∧
      ContDiffAt ℝ ⊤
        (fun x => P.gluedInteriorComplexChart (gluingChainEdgeLeft k) z ρ hρ hq he
          ((P.seamAngularComplexChart k θ).symm x)) a := by
  let i := gluingChainEdgeLeft k
  let o := (P.centers i).2
  let r := gluingRadius C g
  let f : ℂ → ℍ := fun x => gluingPolarPoint o (Circle.exp x.im) (r - x.re)
  let F : ℂ → P.GluedCarrier := (P.seamAngularComplexChart k θ).symm
  obtain ⟨γ, hEq⟩ := P.outgoingSeamInteriorTransition_eventually_eq_deck
    k θ z ρ hρ hq he a ha ht hi
  have hrad : 0 < r - a.re := by
    dsimp [r]
    linarith [P.radius_pos]
  refine ⟨(gluingOutgoingPolarLiftDerivEquiv o r a hrad).trans
    (gluingDeckComplexDerivEquiv γ.1 (f a) (f a).im_pos), ?_, ?_⟩
  · change HasFDerivAt _
      ((gluingDeckComplexDerivEquiv γ.1 (f a) (f a).im_pos : ℂ →L[ℝ] ℂ).comp
        (gluingOutgoingPolarLiftDerivEquiv o r a hrad : ℂ →L[ℝ] ℂ)) a
    exact ((gluingDeckComplex_hasFDerivAt_equiv γ.1 (f a).im_pos).comp a
      (gluingOutgoingPolarLift_hasFDerivAt_equiv o r a hrad)).congr_of_eventuallyEq hEq
  · exact ((gluingDeckComplex_contDiffAt γ.1 (f a).im_pos).comp a
      (gluingOutgoingPolarLift_contDiff o r).contDiffAt).congr_of_eventuallyEq hEq

theorem incomingSeamInteriorTransition_eventually_eq_deck
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (z : ℍ) (ρ : ℝ) (hρ : 0 < ρ)
    (hq : ∀ w : ball z ρ,
      (Quotient.mk'' w.1 : (X (gluingChainEdgeRight k)).Carrier) ∈
        P.componentInteriorSet (gluingChainEdgeRight k))
    (he : Topology.IsOpenEmbedding (fun w : ball z ρ =>
      P.gluedMk (P.componentInteriorPoint (gluingChainEdgeRight k)
        ⟨Quotient.mk'' w.1, hq w⟩)))
    (a : ℂ) (ha : a ∈ (P.seamAngularComplexChart k θ).target) (ht : 0 < a.re)
    (hi : (P.seamAngularComplexChart k θ).symm a ∈
      (P.gluedInteriorComplexChart (gluingChainEdgeRight k) z ρ hρ hq he).source) :
    ∃ γ : (X (gluingChainEdgeRight k)).deckGroup,
      (fun x => P.gluedInteriorComplexChart (gluingChainEdgeRight k) z ρ hρ hq he
        ((P.seamAngularComplexChart k θ).symm x)) =ᶠ[𝓝 a]
          gluingDeckComplex γ.1 ∘ gluingIncomingPolarLift
            (P.centers (gluingChainEdgeRight k)).1 (gluingRadius C g) := by
  let i := gluingChainEdgeRight k
  let o := (P.centers i).1
  let r := gluingRadius C g
  let f : ℂ → ℍ := fun x => gluingPolarPoint o (Circle.exp (-x.im)) (r + x.re)
  let F : ℂ → P.GluedCarrier := (P.seamAngularComplexChart k θ).symm
  have hf : Continuous f := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    exact (gluingIncomingPolarLift_contDiff o r).continuous
  have hs : ∀ᶠ x in 𝓝 a, x ∈ (P.seamAngularComplexChart k θ).target ∧ 0 < x.re ∧
      F x ∈ (P.gluedInteriorComplexChart i z ρ hρ hq he).source := by
    filter_upwards [(P.seamAngularComplexChart k θ).open_target.mem_nhds ha,
      Complex.continuous_re.continuousAt.eventually (Ioi_mem_nhds ht),
      ((P.seamAngularComplexChart k θ).continuousAt_symm ha).eventually
        ((P.gluedInteriorComplexChart i z ρ hρ hq he).open_source.mem_nhds hi)] with x hx hxt hxi
    exact ⟨hx, hxt, hxi⟩
  have hF : ∀ᶠ x in 𝓝 a, ∃ hfx : (Quotient.mk'' (f x) : (X i).Carrier) ∈
      P.componentInteriorSet i,
      F x = P.gluedMk (P.componentInteriorPoint i ⟨Quotient.mk'' (f x), hfx⟩) := by
    filter_upwards [hs] with x hx
    obtain ⟨hxt, hxθ⟩ := (P.mem_seamAngularComplexChart_target k θ x).mp hx.1
    let p : GluingSeamAngularDomain C g θ := (⟨x.re, hxt⟩, ⟨x.im, hxθ⟩)
    have hm : gluingSeamAngularModel C g θ p = x := Complex.ext rfl rfl
    have hp : F x = P.gluedMk (P.seamIncomingPolarPoint k
        ((Circle.exp p.2.1)⁻¹, ⟨r + p.1.1, by
          constructor
          · dsimp [p]; linarith [hx.2.1]
          · change r + p.1.1 < r + gluingDepth C g
            linarith [p.1.2.2]⟩)) := by
      exact (congrArg F hm.symm).trans
        ((P.seamAngularComplexChart_symm_apply k θ p).trans
          (P.seamAngularPoint_of_nonneg k θ p hx.2.1.le))
    let b : P.ChainComponent i := (P.seamIncomingPolarPoint k
      ((Circle.exp p.2.1)⁻¹, ⟨r + p.1.1, by
        constructor
        · dsimp [p]; linarith [hx.2.1]
        · change r + p.1.1 < r + gluingDepth C g
          linarith [p.1.2.2]⟩)).2
    have hb : b.1 = (Quotient.mk'' (f x) : (X i).Carrier) := by
      dsimp [f]
      rw [Circle.exp_neg]
      rfl
    have hpb : F x = P.gluedMk ⟨i, b⟩ := hp
    have hmem := P.retained_mem_interior_of_chart_source i z ρ hρ hq he b
      (hpb ▸ hx.2.2)
    rw [hb] at hmem
    refine ⟨hmem, hp.trans ?_⟩
    apply congrArg P.gluedMk
    change (⟨i, b⟩ : P.ChainPieces) =
      P.componentInteriorPoint i ⟨Quotient.mk'' (f x), hmem⟩
    exact congrArg (fun q : P.ChainComponent i => (⟨i, q⟩ : P.ChainPieces))
      (Subtype.ext hb)
  obtain ⟨γ, hγ⟩ := P.gluedInteriorComplexChart_eventually_eq_deck i z ρ hρ hq he
    f F a hf.continuousAt hi hF
  have hEq : (fun x => P.gluedInteriorComplexChart i z ρ hρ hq he (F x)) =ᶠ[𝓝 a]
      gluingDeckComplex (γ : SL(2, ℝ)) ∘ gluingIncomingPolarLift o r := by
    filter_upwards [hγ] with x hx
    exact hx.trans (gluingDeckComplex_coe (γ : SL(2, ℝ)) (f x)).symm
  exact ⟨γ, hEq⟩

private theorem incomingSeamInteriorTransition_regular
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (z : ℍ) (ρ : ℝ) (hρ : 0 < ρ)
    (hq : ∀ w : ball z ρ,
      (Quotient.mk'' w.1 : (X (gluingChainEdgeRight k)).Carrier) ∈
        P.componentInteriorSet (gluingChainEdgeRight k))
    (he : Topology.IsOpenEmbedding (fun w : ball z ρ =>
      P.gluedMk (P.componentInteriorPoint (gluingChainEdgeRight k)
        ⟨Quotient.mk'' w.1, hq w⟩)))
    (a : ℂ) (ha : a ∈ (P.seamAngularComplexChart k θ).target) (ht : 0 < a.re)
    (hi : (P.seamAngularComplexChart k θ).symm a ∈
      (P.gluedInteriorComplexChart (gluingChainEdgeRight k) z ρ hρ hq he).source) :
    ∃ D : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt
        (fun x => P.gluedInteriorComplexChart (gluingChainEdgeRight k) z ρ hρ hq he
          ((P.seamAngularComplexChart k θ).symm x)) (D : ℂ →L[ℝ] ℂ) a ∧
      ContDiffAt ℝ ⊤
        (fun x => P.gluedInteriorComplexChart (gluingChainEdgeRight k) z ρ hρ hq he
          ((P.seamAngularComplexChart k θ).symm x)) a := by
  let i := gluingChainEdgeRight k
  let o := (P.centers i).1
  let r := gluingRadius C g
  let f : ℂ → ℍ := fun x => gluingPolarPoint o (Circle.exp (-x.im)) (r + x.re)
  let F : ℂ → P.GluedCarrier := (P.seamAngularComplexChart k θ).symm
  obtain ⟨γ, hEq⟩ := P.incomingSeamInteriorTransition_eventually_eq_deck
    k θ z ρ hρ hq he a ha ht hi
  have hrad : 0 < r + a.re := by
    dsimp [r]
    linarith [P.radius_pos]
  refine ⟨(gluingIncomingPolarLiftDerivEquiv o r a hrad).trans
    (gluingDeckComplexDerivEquiv γ.1 (f a) (f a).im_pos), ?_, ?_⟩
  · change HasFDerivAt _
      ((gluingDeckComplexDerivEquiv γ.1 (f a) (f a).im_pos : ℂ →L[ℝ] ℂ).comp
        (gluingIncomingPolarLiftDerivEquiv o r a hrad : ℂ →L[ℝ] ℂ)) a
    exact ((gluingDeckComplex_hasFDerivAt_equiv γ.1 (f a).im_pos).comp a
      (gluingIncomingPolarLift_hasFDerivAt_equiv o r a hrad)).congr_of_eventuallyEq hEq
  · exact ((gluingDeckComplex_contDiffAt γ.1 (f a).im_pos).comp a
      (gluingIncomingPolarLift_contDiff o r).contDiffAt).congr_of_eventuallyEq hEq

/-- Every native mixed overlap is locally one actual deck map composed
with its signed polar branch. The source determines the sign and component. -/
theorem seamInterior_transition_eventually_eq_deck_polar
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {x : ℂ} (hx : x ∈ ((P.seamAngularComplexChart k θ).symm.trans e).source) :
    (∃ (o : ℍ) (γ : SL(2, ℝ)), x.re < 0 ∧
      ((P.seamAngularComplexChart k θ).symm.trans e) =ᶠ[𝓝 x]
        gluingDeckComplex γ ∘ gluingOutgoingPolarLift o (gluingRadius C g)) ∨
    (∃ (o : ℍ) (γ : SL(2, ℝ)), 0 < x.re ∧
      ((P.seamAngularComplexChart k θ).symm.trans e) =ᶠ[𝓝 x]
        gluingDeckComplex γ ∘ gluingIncomingPolarLift o (gluingRadius C g)) := by
  obtain ⟨i, z, ρ, hρ, _h4, hq, hf, rfl⟩ := he
  change x ∈ (P.seamAngularComplexChart k θ).target ∧
    (P.seamAngularComplexChart k θ).symm x ∈
      (P.gluedInteriorComplexChart i z ρ hρ hq hf).source at hx
  have htarget := hx.1
  rw [seamAngularComplexChart_target] at htarget
  obtain ⟨p, rfl⟩ := htarget
  have hsource := hx.2
  rw [seamAngularComplexChart_symm_apply, gluedInteriorComplexChart_source] at hsource
  obtain ⟨w, hw⟩ := hsource
  have hp : p.1.1 ≠ 0 := fun hp =>
    P.seamAngularPoint_ne_componentInteriorPoint_of_zero k θ p hp i
      ⟨Quotient.mk'' w.1, hq w⟩ hw.symm
  rcases lt_or_gt_of_ne hp with hp | hp
  · have hpieces := P.gluedMk_eq_of_not_mem_chainSeamSet
      (P.componentInteriorPoint_not_mem_chainSeamSet i ⟨Quotient.mk'' w.1, hq w⟩)
      (hw.trans (P.seamAngularPoint_of_nonpos k θ p hp.le))
    have hij : i = gluingChainEdgeLeft k :=
      congrArg (fun a : P.ChainPieces => a.1) hpieces
    subst i
    obtain ⟨γ, hγ⟩ := P.outgoingSeamInteriorTransition_eventually_eq_deck
      k θ z ρ hρ hq hf (gluingSeamAngularModel C g θ p) hx.1 hp hx.2
    exact Or.inl ⟨_, γ.1, hp, hγ⟩
  · have hpieces := P.gluedMk_eq_of_not_mem_chainSeamSet
      (P.componentInteriorPoint_not_mem_chainSeamSet i ⟨Quotient.mk'' w.1, hq w⟩)
      (hw.trans (P.seamAngularPoint_of_nonneg k θ p hp.le))
    have hij : i = gluingChainEdgeRight k :=
      congrArg (fun a : P.ChainPieces => a.1) hpieces
    subst i
    obtain ⟨γ, hγ⟩ := P.incomingSeamInteriorTransition_eventually_eq_deck
      k θ z ρ hρ hq hf (gluingSeamAngularModel C g θ p) hx.1 hp hx.2
    exact Or.inr ⟨_, γ.1, hp, hγ⟩

private theorem seamInterior_transition_regular
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {x : ℂ} (hx : x ∈ ((P.seamAngularComplexChart k θ).symm.trans e).source) :
    ∃ D : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt ((P.seamAngularComplexChart k θ).symm.trans e) (D : ℂ →L[ℝ] ℂ) x ∧
      ContDiffAt ℝ ⊤ ((P.seamAngularComplexChart k θ).symm.trans e) x := by
  obtain ⟨i, z, ρ, hρ, _h4, hq, hf, rfl⟩ := he
  change x ∈ (P.seamAngularComplexChart k θ).target ∧
    (P.seamAngularComplexChart k θ).symm x ∈
      (P.gluedInteriorComplexChart i z ρ hρ hq hf).source at hx
  have htarget := hx.1
  rw [seamAngularComplexChart_target] at htarget
  obtain ⟨p, rfl⟩ := htarget
  have hsource := hx.2
  rw [seamAngularComplexChart_symm_apply, gluedInteriorComplexChart_source] at hsource
  obtain ⟨w, hw⟩ := hsource
  have hp : p.1.1 ≠ 0 := fun hp =>
    P.seamAngularPoint_ne_componentInteriorPoint_of_zero k θ p hp i
      ⟨Quotient.mk'' w.1, hq w⟩ hw.symm
  rcases lt_or_gt_of_ne hp with hp | hp
  · have hpieces := P.gluedMk_eq_of_not_mem_chainSeamSet
      (P.componentInteriorPoint_not_mem_chainSeamSet i ⟨Quotient.mk'' w.1, hq w⟩)
      (hw.trans (P.seamAngularPoint_of_nonpos k θ p hp.le))
    have hij : i = gluingChainEdgeLeft k :=
      congrArg (fun a : P.ChainPieces => a.1) hpieces
    subst i
    exact P.outgoingSeamInteriorTransition_regular k θ z ρ hρ hq hf
      (gluingSeamAngularModel C g θ p) hx.1 hp hx.2
  · have hpieces := P.gluedMk_eq_of_not_mem_chainSeamSet
      (P.componentInteriorPoint_not_mem_chainSeamSet i ⟨Quotient.mk'' w.1, hq w⟩)
      (hw.trans (P.seamAngularPoint_of_nonneg k θ p hp.le))
    have hij : i = gluingChainEdgeRight k :=
      congrArg (fun a : P.ChainPieces => a.1) hpieces
    subst i
    exact P.incomingSeamInteriorTransition_regular k θ z ρ hρ hq hf
      (gluingSeamAngularModel C g θ p) hx.1 hp hx.2

/-- The actual seam-to-interior transition is smooth on every point of its
native overlap. The overlap itself determines the correct adjacent component
and excludes signed radius zero. -/
theorem seamInterior_transition_contDiffAt
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {x : ℂ} (hx : x ∈ ((P.seamAngularComplexChart k θ).symm.trans e).source) :
    ContDiffAt ℝ ⊤ ((P.seamAngularComplexChart k θ).symm.trans e) x :=
  (P.seamInterior_transition_regular k θ e he hx).choose_spec.2

/-- The native seam-to-interior differential is an actual continuous linear
equivalence, constructed from the signed polar differential and a deck map. -/
theorem seamInterior_transition_hasFDerivAt_equiv
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {x : ℂ} (hx : x ∈ ((P.seamAngularComplexChart k θ).symm.trans e).source) :
    ∃ D : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt ((P.seamAngularComplexChart k θ).symm.trans e) (D : ℂ →L[ℝ] ℂ) x := by
  obtain ⟨D, hD, _⟩ := P.seamInterior_transition_regular k θ e he hx
  exact ⟨D, hD⟩

theorem seamInterior_transition_contDiffOn
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e) :
    ContDiffOn ℝ ⊤ ((P.seamAngularComplexChart k θ).symm.trans e)
      ((P.seamAngularComplexChart k θ).symm.trans e).source :=
  fun _ hx => (P.seamInterior_transition_contDiffAt k θ e he hx).contDiffWithinAt

end ExerciseGluingPreparation

#print axioms gluingOutgoingPolarLift_contDiff
#print axioms gluingIncomingPolarLift_contDiff
#print axioms gluingOutgoingPolarLift_hasFDerivAt_equiv
#print axioms gluingIncomingPolarLift_hasFDerivAt_equiv
#print axioms gluingOutgoingPolarLocalHomeomorph_symm_contDiffAt
#print axioms gluingIncomingPolarLocalHomeomorph_symm_contDiffAt
#print axioms ExerciseGluingPreparation.seamInterior_transition_contDiffAt
#print axioms ExerciseGluingPreparation.seamInterior_transition_hasFDerivAt_equiv
#print axioms ExerciseGluingPreparation.seamInterior_transition_contDiffOn
#print axioms ExerciseGluingPreparation.outgoingSeamInteriorTransition_eventually_eq_deck
#print axioms ExerciseGluingPreparation.incomingSeamInteriorTransition_eventually_eq_deck
#print axioms ExerciseGluingPreparation.seamInterior_transition_eventually_eq_deck_polar

end SystolicGrowth

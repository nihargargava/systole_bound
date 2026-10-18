module

public import Geometry.GluingSpinCircleAction
public import Geometry.GluingPolarTransitions

@[expose] public section

/-!
# Full tangent identification for the actual Fermi clutching

The incoming and outgoing polar branches have genuine invertible real
differentials. Their full boundary transition, obtained through the actual
inverse chart, is complex multiplication. Its normalized action on every
vector is exactly the square of the literal spin seam transition.
-/

open UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false

theorem gluingFermiIncomingLift_fderiv_apply
    (o : ℍ) (r : ℝ) (p v : ℝ × ℝ) :
    fderiv ℝ (gluingFermiIncomingLift o r) p v =
      fderiv ℝ (gluingPolarLift o) (r + p.1, p.2) v := by
  have hparam := ((hasFDerivAt_const r p).add
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have h := (gluingPolarLift_hasFDerivAt o (r + p.1, p.2)).comp p hparam
  change HasFDerivAt (gluingFermiIncomingLift o r) _ p at h
  rw [h.fderiv, (gluingPolarLift_hasFDerivAt o (r + p.1, p.2)).fderiv]
  simp

theorem gluingFermiOutgoingLift_fderiv_apply
    (o : ℍ) (r : ℝ) (p v : ℝ × ℝ) :
    fderiv ℝ (gluingFermiOutgoingLift o r) p v =
      -fderiv ℝ (gluingPolarLift o) (r - p.1, -p.2) v := by
  have hparam := ((hasFDerivAt_const r p).sub
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).neg
  have h := (gluingPolarLift_hasFDerivAt o (r - p.1, -p.2)).comp p hparam
  change HasFDerivAt (gluingFermiOutgoingLift o r) _ p at h
  rw [h.fderiv, (gluingPolarLift_hasFDerivAt o (r - p.1, -p.2)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    neg_apply, zero_sub]
  change gluingPolarLiftFDeriv o (r - p.1, -p.2) (-v) =
    -gluingPolarLiftFDeriv o (r - p.1, -p.2) v
  exact map_neg _ v

private theorem polar_fderiv_apply_eq_radial (o : ℍ) (p v : ℝ × ℝ) :
    fderiv ℝ (gluingPolarLift o) p v =
      fderiv ℝ (gluingPolarLift o) p (1, 0) *
        ((v.1 : ℂ) + Complex.I * (Real.sinh p.1 : ℂ) * (v.2 : ℂ)) := by
  have hv : v = v.1 • ((1, 0) : ℝ × ℝ) + v.2 • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  calc
    fderiv ℝ (gluingPolarLift o) p v =
        v.1 • fderiv ℝ (gluingPolarLift o) p (1, 0) +
          v.2 • fderiv ℝ (gluingPolarLift o) p (0, 1) := by
      conv_lhs => rw [hv]
      rw [map_add, map_smul, map_smul]
    _ = _ := by
      rw [gluingPolarLift_angular_fderiv_eq_radial]
      simp only [Complex.real_smul]
      ring

/-- Both genuine Fermi derivatives have the same full anisotropic radial-
angular factor; their different radial directions are not the entire proof. -/
theorem gluingFermiIncomingLift_fderiv_eq_radial
    (o : ℍ) (r : ℝ) (p v : ℝ × ℝ) :
    fderiv ℝ (gluingFermiIncomingLift o r) p v =
      fderiv ℝ (gluingFermiIncomingLift o r) p (1, 0) *
        ((v.1 : ℂ) + Complex.I * (Real.sinh (r + p.1) : ℂ) * (v.2 : ℂ)) := by
  rw [gluingFermiIncomingLift_fderiv_apply, gluingFermiIncomingLift_radial_fderiv]
  exact polar_fderiv_apply_eq_radial o _ v

theorem gluingFermiOutgoingLift_fderiv_eq_radial
    (o : ℍ) (r : ℝ) (p v : ℝ × ℝ) :
    fderiv ℝ (gluingFermiOutgoingLift o r) p v =
      fderiv ℝ (gluingFermiOutgoingLift o r) p (1, 0) *
        ((v.1 : ℂ) + Complex.I * (Real.sinh (r - p.1) : ℂ) * (v.2 : ℂ)) := by
  rw [gluingFermiOutgoingLift_fderiv_apply, gluingFermiOutgoingLift_radial_fderiv,
    polar_fderiv_apply_eq_radial, neg_mul]

def gluingFermiIncomingDerivEquiv (o : ℍ) (r : ℝ) (p : ℝ × ℝ)
    (hp : 0 < r + p.1) : (ℝ × ℝ) ≃L[ℝ] ℂ :=
  gluingPolarLiftDerivEquiv o (r + p.1, p.2) hp

def gluingFermiOutgoingDerivEquiv (o : ℍ) (r : ℝ) (p : ℝ × ℝ)
    (hp : 0 < r - p.1) : (ℝ × ℝ) ≃L[ℝ] ℂ :=
  (ContinuousLinearEquiv.neg ℝ).trans
    (gluingPolarLiftDerivEquiv o (r - p.1, -p.2) hp)

theorem gluingFermiIncomingDerivEquiv_toCLM (o : ℍ) (r : ℝ) (p : ℝ × ℝ)
    (hp : 0 < r + p.1) :
    (gluingFermiIncomingDerivEquiv o r p hp : (ℝ × ℝ) →L[ℝ] ℂ) =
      fderiv ℝ (gluingFermiIncomingLift o r) p := by
  apply ContinuousLinearMap.ext
  intro v
  rw [gluingFermiIncomingLift_fderiv_apply, (gluingPolarLift_hasFDerivAt o _).fderiv]
  exact congrArg (fun D : (ℝ × ℝ) →L[ℝ] ℂ => D v)
    (gluingPolarLiftDerivEquiv_toCLM o _ hp)

theorem gluingFermiOutgoingDerivEquiv_toCLM (o : ℍ) (r : ℝ) (p : ℝ × ℝ)
    (hp : 0 < r - p.1) :
    (gluingFermiOutgoingDerivEquiv o r p hp : (ℝ × ℝ) →L[ℝ] ℂ) =
      fderiv ℝ (gluingFermiOutgoingLift o r) p := by
  apply ContinuousLinearMap.ext
  intro v
  change gluingPolarLiftDerivEquiv o (r - p.1, -p.2) hp (-v) = _
  rw [map_neg, gluingFermiOutgoingLift_fderiv_apply,
    (gluingPolarLift_hasFDerivAt o _).fderiv]
  exact congrArg (fun D : (ℝ × ℝ) →L[ℝ] ℂ => -D v)
    (gluingPolarLiftDerivEquiv_toCLM o _ hp)

theorem gluingFermiIncomingLift_hasFDerivAt_equiv
    (o : ℍ) (r : ℝ) (p : ℝ × ℝ) (hp : 0 < r + p.1) :
    HasFDerivAt (gluingFermiIncomingLift o r)
      (gluingFermiIncomingDerivEquiv o r p hp : (ℝ × ℝ) →L[ℝ] ℂ) p := by
  have hparam := ((hasFDerivAt_const r p).add
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have h := (gluingPolarLift_hasFDerivAt o (r + p.1, p.2)).comp p hparam
  change HasFDerivAt (gluingFermiIncomingLift o r) _ p at h
  exact h.congr_fderiv (h.fderiv.symm.trans
    (gluingFermiIncomingDerivEquiv_toCLM o r p hp).symm)

theorem gluingFermiOutgoingLift_hasFDerivAt_equiv
    (o : ℍ) (r : ℝ) (p : ℝ × ℝ) (hp : 0 < r - p.1) :
    HasFDerivAt (gluingFermiOutgoingLift o r)
      (gluingFermiOutgoingDerivEquiv o r p hp : (ℝ × ℝ) →L[ℝ] ℂ) p := by
  have hparam := ((hasFDerivAt_const r p).sub
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).neg
  have h := (gluingPolarLift_hasFDerivAt o (r - p.1, -p.2)).comp p hparam
  change HasFDerivAt (gluingFermiOutgoingLift o r) _ p at h
  exact h.congr_fderiv (h.fderiv.symm.trans
    (gluingFermiOutgoingDerivEquiv_toCLM o r p hp).symm)

/-- The genuine full tangent transition between the two actual boundary
charts is constructed from their actual inverse differentials. -/
def gluingFermiBoundaryTangentTransition (oIn oOut : ℍ) {r : ℝ}
    (hr : 0 < r) (θ : ℝ) : ℂ ≃L[ℝ] ℂ :=
  (gluingFermiOutgoingDerivEquiv oOut r (0, θ) (by simpa using hr)).symm.trans
    (gluingFermiIncomingDerivEquiv oIn r (0, θ) (by simpa using hr))

def gluingFermiBoundaryTangentScalar (oIn oOut : ℍ) (r θ : ℝ) : ℂ :=
  fderiv ℝ (gluingFermiIncomingLift oIn r) (0, θ) (1, 0) /
    fderiv ℝ (gluingFermiOutgoingLift oOut r) (0, θ) (1, 0)

private theorem outgoing_radial_ne_zero (o : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    fderiv ℝ (gluingFermiOutgoingLift o r) (0, θ) (1, 0) ≠ 0 := by
  intro h
  let D := gluingFermiOutgoingDerivEquiv o r (0, θ) (by simpa using hr)
  have he : D (1, 0) = D 0 := by
    rw [map_zero]
    change (D : (ℝ × ℝ) →L[ℝ] ℂ) (1, 0) = 0
    simpa only [D, gluingFermiOutgoingDerivEquiv_toCLM] using h
  have hp := D.injective he
  have := congrArg Prod.fst hp
  norm_num at this

theorem gluingFermiBoundaryTangentScalar_fderiv
    (oIn oOut : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) (v : ℝ × ℝ) :
    fderiv ℝ (gluingFermiIncomingLift oIn r) (0, θ) v =
      gluingFermiBoundaryTangentScalar oIn oOut r θ *
        fderiv ℝ (gluingFermiOutgoingLift oOut r) (0, θ) v := by
  rw [gluingFermiIncomingLift_fderiv_eq_radial,
    gluingFermiOutgoingLift_fderiv_eq_radial]
  simp only [add_zero, sub_zero, gluingFermiBoundaryTangentScalar]
  rw [← mul_assoc, div_mul_cancel₀ _ (outgoing_radial_ne_zero oOut hr θ)]

/-- The actual full real-linear transition is complex multiplication on
every vector, not merely on its radial basis vector. -/
theorem gluingFermiBoundaryTangentTransition_apply
    (oIn oOut : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) (v : ℂ) :
    gluingFermiBoundaryTangentTransition oIn oOut hr θ v =
      gluingFermiBoundaryTangentScalar oIn oOut r θ * v := by
  let DOut := gluingFermiOutgoingDerivEquiv oOut r (0, θ) (by simpa using hr)
  let DIn := gluingFermiIncomingDerivEquiv oIn r (0, θ) (by simpa using hr)
  have h := gluingFermiBoundaryTangentScalar_fderiv oIn oOut hr θ (DOut.symm v)
  rw [← gluingFermiIncomingDerivEquiv_toCLM oIn r (0, θ) (by simpa using hr),
    ← gluingFermiOutgoingDerivEquiv_toCLM oOut r (0, θ) (by simpa using hr)] at h
  change DIn (DOut.symm v) = gluingFermiBoundaryTangentScalar oIn oOut r θ *
    DOut (DOut.symm v) at h
  rw [DOut.apply_symm_apply] at h
  exact h

/-- The literal spin multiplier squares to the phase of the actual full
transition, constructed above from genuine real differentials. -/
theorem gluingFermiBoundarySpinCircle_sq_eq_tangent_phase
    (oIn oOut : ℍ) (r θ : ℝ) :
    (gluingFermiBoundarySpinCircle r (Circle.exp θ) : ℂ) ^ 2 =
      gluingFermiBoundaryTangentScalar oIn oOut r θ /
        (‖gluingFermiBoundaryTangentScalar oIn oOut r θ‖ : ℂ) := by
  rw [gluingFermiBoundarySpinCircle_sq_eq_radial_phase_ratio oIn oOut]
  simp only [gluingFermiBoundaryTangentScalar, norm_div, Complex.ofReal_div]
  exact (div_div_div_comm _ _ _ _).symm

/-- This is exactly the normalized action on all actual tangent vectors;
the zero vector is included because both normalizations then vanish. -/
theorem gluingFermiBoundaryTangentTransition_normalized
    (oIn oOut : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) (v : ℂ) :
    gluingFermiBoundaryTangentTransition oIn oOut hr θ v /
      (‖gluingFermiBoundaryTangentTransition oIn oOut hr θ v‖ : ℂ) =
        (gluingFermiBoundarySpinCircle r (Circle.exp θ) : ℂ) ^ 2 *
          (v / (‖v‖ : ℂ)) := by
  rw [gluingFermiBoundaryTangentTransition_apply,
    gluingFermiBoundarySpinCircle_sq_eq_tangent_phase oIn oOut]
  simp only [norm_mul, Complex.ofReal_mul]
  rw [div_mul_div_comm]

theorem gluingFermiIncomingLift_contDiff (o : ℍ) (r : ℝ) :
    ContDiff ℝ ⊤ (gluingFermiIncomingLift o r) :=
  (gluingPolarLift_contDiff o).comp
    ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)

theorem gluingFermiOutgoingLift_contDiff (o : ℍ) (r : ℝ) :
    ContDiff ℝ ⊤ (gluingFermiOutgoingLift o r) :=
  (gluingPolarLift_contDiff o).comp
    ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd.neg)

def gluingFermiParameterHomeomorph : (ℝ × ℝ) ≃ₜ ℂ :=
  Complex.equivRealProdCLM.symm.toHomeomorph.trans Complex.conjCLE.toHomeomorph

theorem gluingFermiIncomingLift_eq_native (o : ℍ) (r : ℝ) (p : ℝ × ℝ) :
    gluingFermiIncomingLift o r p =
      gluingIncomingPolarLift o r (gluingFermiParameterHomeomorph p) := by
  simp [gluingFermiIncomingLift, gluingIncomingPolarLift, gluingIncomingPolarCoordinates,
    gluingFermiParameterHomeomorph, Complex.equivRealProdCLM_symm_apply]

theorem gluingFermiOutgoingLift_eq_native (o : ℍ) (r : ℝ) (p : ℝ × ℝ) :
    gluingFermiOutgoingLift o r p =
      gluingOutgoingPolarLift o r (gluingFermiParameterHomeomorph p) := by
  simp [gluingFermiOutgoingLift, gluingOutgoingPolarLift, gluingOutgoingPolarCoordinates,
    gluingFermiParameterHomeomorph, Complex.equivRealProdCLM_symm_apply]

/-- The existing native outgoing local chart, in the genuine corrected
orientation, rather than a separately supplied inverse chart. -/
def gluingFermiOutgoingLocalChart (o : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    OpenPartialHomeomorph (ℝ × ℝ) ℂ :=
  gluingFermiParameterHomeomorph.toOpenPartialHomeomorph.trans
    (gluingOutgoingPolarLocalHomeomorph o r (gluingFermiParameterHomeomorph (0, θ))
      (by simpa [gluingFermiParameterHomeomorph, Complex.equivRealProdCLM_symm_apply] using hr))

/-- The corresponding actual incoming signed Fermi chart. -/
def gluingFermiIncomingLocalChart (o : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    OpenPartialHomeomorph (ℝ × ℝ) ℂ :=
  gluingFermiParameterHomeomorph.toOpenPartialHomeomorph.trans
    (gluingIncomingPolarLocalHomeomorph o r (gluingFermiParameterHomeomorph (0, θ))
      (by simpa [gluingFermiParameterHomeomorph, Complex.equivRealProdCLM_symm_apply] using hr))

@[simp] theorem gluingFermiOutgoingLocalChart_apply
    (o : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) (p : ℝ × ℝ) :
    gluingFermiOutgoingLocalChart o hr θ p = gluingFermiOutgoingLift o r p :=
  (gluingFermiOutgoingLift_eq_native o r p).symm

@[simp] theorem gluingFermiIncomingLocalChart_apply
    (o : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) (p : ℝ × ℝ) :
    gluingFermiIncomingLocalChart o hr θ p = gluingFermiIncomingLift o r p :=
  (gluingFermiIncomingLift_eq_native o r p).symm

theorem gluingFermiOutgoingLocalChart_coe
    (o : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (gluingFermiOutgoingLocalChart o hr θ : (ℝ × ℝ) → ℂ) =
      gluingFermiOutgoingLift o r := funext (gluingFermiOutgoingLocalChart_apply o hr θ)

theorem gluingFermiIncomingLocalChart_coe
    (o : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (gluingFermiIncomingLocalChart o hr θ : (ℝ × ℝ) → ℂ) =
      gluingFermiIncomingLift o r := funext (gluingFermiIncomingLocalChart_apply o hr θ)

theorem gluingFermiOutgoingLocalChart_mem_source
    (o : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (0, θ) ∈ (gluingFermiOutgoingLocalChart o hr θ).source := by
  exact ⟨Set.mem_univ _, gluingOutgoingPolarLocalHomeomorph_mem_source o r _ _⟩

theorem gluingFermiIncomingLocalChart_mem_source
    (o : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (0, θ) ∈ (gluingFermiIncomingLocalChart o hr θ).source := by
  exact ⟨Set.mem_univ _, gluingIncomingPolarLocalHomeomorph_mem_source o r _ _⟩

set_option backward.isDefEq.respectTransparency true

/-- The inverse in the actual chart, rather than a supplied inverse
differential, has the constructed outgoing inverse derivative. -/
theorem gluingFermiOutgoingLocalChart_symm_hasFDerivAt
    (o : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    HasFDerivAt (gluingFermiOutgoingLocalChart o hr θ).symm
      ((gluingFermiOutgoingDerivEquiv o r (0, θ) (by simpa using hr)).symm :
        ℂ →L[ℝ] (ℝ × ℝ)) (gluingFermiOutgoingLift o r (0, θ)) := by
  let e := gluingFermiOutgoingLocalChart o hr θ
  have hs := gluingFermiOutgoingLocalChart_mem_source o hr θ
  have ht : gluingFermiOutgoingLift o r (0, θ) ∈ e.target := by
    simpa only [e, gluingFermiOutgoingLocalChart_apply] using e.map_source hs
  apply e.hasFDerivAt_symm ht
  have he : e.symm (gluingFermiOutgoingLift o r (0, θ)) = (0, θ) := by
    simpa only [e, gluingFermiOutgoingLocalChart_apply] using e.left_inv hs
  rw [he]
  rw [show (e : (ℝ × ℝ) → ℂ) = gluingFermiOutgoingLift o r from
    gluingFermiOutgoingLocalChart_coe o hr θ]
  exact gluingFermiOutgoingLift_hasFDerivAt_equiv o r (0, θ) (by simpa using hr)

/-- The full transition is the derivative of the genuine incoming chart
composed with the genuine outgoing inverse chart at the original boundary. -/
theorem gluingFermiBoundaryLocalTransition_hasFDerivAt
    (oIn oOut : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    HasFDerivAt ((gluingFermiOutgoingLocalChart oOut hr θ).symm.trans
      (gluingFermiIncomingLocalChart oIn hr θ))
        (gluingFermiBoundaryTangentTransition oIn oOut hr θ : ℂ →L[ℝ] ℂ)
          (gluingFermiOutgoingLift oOut r (0, θ)) := by
  let e := gluingFermiOutgoingLocalChart oOut hr θ
  have hs := gluingFermiOutgoingLocalChart_mem_source oOut hr θ
  have he : e.symm (gluingFermiOutgoingLift oOut r (0, θ)) = (0, θ) := by
    simpa only [e, gluingFermiOutgoingLocalChart_apply] using e.left_inv hs
  have hIn : HasFDerivAt (gluingFermiIncomingLift oIn r)
      (gluingFermiIncomingDerivEquiv oIn r (0, θ) (by simpa using hr) :
        (ℝ × ℝ) →L[ℝ] ℂ) (e.symm (gluingFermiOutgoingLift oOut r (0, θ))) := by
    rw [he]
    exact gluingFermiIncomingLift_hasFDerivAt_equiv oIn r (0, θ) (by simpa using hr)
  have hcomp := hIn.comp (gluingFermiOutgoingLift oOut r (0, θ))
    (gluingFermiOutgoingLocalChart_symm_hasFDerivAt oOut hr θ)
  have hf : (((gluingFermiOutgoingLocalChart oOut hr θ).symm.trans
      (gluingFermiIncomingLocalChart oIn hr θ)) : ℂ → ℂ) =
        gluingFermiIncomingLift oIn r ∘ (e.symm : ℂ → ℝ × ℝ) := by
    funext z
    exact gluingFermiIncomingLocalChart_apply oIn hr θ (e.symm z)
  rw [hf]
  exact hcomp

/-- Literal normalized tangent vectors under the actual local coordinate
transition agree with the squared seam clutching in every direction. -/
theorem gluingFermiBoundaryLocalTransition_normalized
    (oIn oOut : ℍ) {r : ℝ} (hr : 0 < r) (θ : ℝ) (v : ℂ) :
    (fderiv ℝ ((gluingFermiOutgoingLocalChart oOut hr θ).symm.trans
      (gluingFermiIncomingLocalChart oIn hr θ))
        (gluingFermiOutgoingLift oOut r (0, θ)) v) /
      (‖fderiv ℝ ((gluingFermiOutgoingLocalChart oOut hr θ).symm.trans
        (gluingFermiIncomingLocalChart oIn hr θ))
          (gluingFermiOutgoingLift oOut r (0, θ)) v‖ : ℂ) =
            (gluingFermiBoundarySpinCircle r (Circle.exp θ) : ℂ) ^ 2 *
              (v / (‖v‖ : ℂ)) := by
  rw [(gluingFermiBoundaryLocalTransition_hasFDerivAt oIn oOut hr θ).fderiv]
  exact gluingFermiBoundaryTangentTransition_normalized oIn oOut hr θ v

#print axioms gluingFermiIncomingDerivEquiv_toCLM
#print axioms gluingFermiOutgoingLift_hasFDerivAt_equiv
#print axioms gluingFermiBoundaryTangentTransition_apply
#print axioms gluingFermiBoundarySpinCircle_sq_eq_tangent_phase
#print axioms gluingFermiBoundaryTangentTransition_normalized
#print axioms gluingFermiBoundaryLocalTransition_hasFDerivAt
#print axioms gluingFermiBoundaryLocalTransition_normalized

end

end SystolicGrowth

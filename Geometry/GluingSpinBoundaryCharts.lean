module

public import Geometry.GluingFermiSpinClutching
public import Geometry.HyperbolicArea

@[expose] public section

open UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The literal positive-radius polar circle has distinct angular points. -/
theorem gluingPolarPoint_injective (o : ℍ) {ρ : ℝ} (hρ : 0 < ρ) :
    Function.Injective (fun u : Circle => gluingPolarPoint o u ρ) := by
  intro u v h
  have hc := congrArg (Vendored.RiemannDynamics.discChart o) h
  rw [discChart_gluingPolarPoint, discChart_gluingPolarPoint] at hc
  have ht : 0 < Real.tanh (ρ / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  have ht' : (Real.tanh (ρ / 2) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  exact Subtype.ext (mul_left_cancel₀ ht' hc)

namespace ClosedHyperbolicSurface

/-- The actual embedded boundary in the unchanged component surface. -/
def polarBoundary {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (ρ : ℝ) :
    Set X.Carrier := Set.range (fun u : Circle => X.orbitProjection (gluingPolarPoint o u ρ))

/-- Restrict the genuine component spin quotient to its actual boundary. -/
abbrev SpinBoundaryCarrier {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (ρ : ℝ) :=
  {q : X.SpinCarrier // X.spinBase q ∈ X.polarBoundary o ρ}

/-- Restrict the genuine component tangent quotient to the same boundary. -/
abbrev TangentBoundaryCarrier {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) :=
  {q : X.TangentFrameCarrier // X.tangentFrameBase q ∈ X.polarBoundary o ρ}

/-- The actual preferred-lift spin boundary parameterization. -/
def spinBoundaryParam {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (ρ : ℝ)
    (p : Circle × Circle) : X.SpinBoundaryCarrier o ρ :=
  ⟨Quotient.mk _ (⟨gluingPolarPoint o p.1 ρ, p.2⟩ : HalfPlaneSpinFrame), p.1, rfl⟩

/-- The analogous parameterization of actual unit tangent directions. -/
def tangentBoundaryParam {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (ρ : ℝ)
    (p : Circle × Circle) : X.TangentBoundaryCarrier o ρ :=
  ⟨Quotient.mk _ (⟨gluingPolarPoint o p.1 ρ, p.2⟩ : HalfPlaneTangentFrame), p.1, rfl⟩

theorem continuous_spinBoundaryParam {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) : Continuous (X.spinBoundaryParam o ρ) := by
  apply Continuous.subtype_mk
  apply continuous_quotient_mk'.comp
  change Continuous (halfPlaneSpinFrameHomeomorph.symm ∘
    fun p : Circle × Circle => (gluingPolarPoint o p.1 ρ, p.2))
  apply halfPlaneSpinFrameHomeomorph.symm.continuous.comp
  exact ((gluingPolarPoint_continuous o).comp
    (continuous_fst.prodMk continuous_const)).prodMk continuous_snd

theorem continuous_tangentBoundaryParam {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) : Continuous (X.tangentBoundaryParam o ρ) := by
  apply Continuous.subtype_mk
  apply continuous_quotient_mk'.comp
  change Continuous (halfPlaneTangentFrameHomeomorph.symm ∘
    fun p : Circle × Circle => (gluingPolarPoint o p.1 ρ, p.2))
  apply halfPlaneTangentFrameHomeomorph.symm.continuous.comp
  exact ((gluingPolarPoint_continuous o).comp
    (continuous_fst.prodMk continuous_const)).prodMk continuous_snd

/-- Genuine outer-ball injectivity identifies the actual boundary angle. -/
theorem orbitProjection_polarPoint_injective {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hR : 2 * R < X.systole) :
    Function.Injective (fun u : Circle => X.orbitProjection (gluingPolarPoint o u ρ)) := by
  intro u v h
  apply gluingPolarPoint_injective o hρ
  apply quotientMk_injOn_ball X o R hR
  · simpa [Metric.mem_ball, dist_comm, dist_gluingPolarPoint o u hρ.le] using hρR
  · simpa [Metric.mem_ball, dist_comm, dist_gluingPolarPoint o v hρ.le] using hρR
  · exact h

theorem spinBoundaryParam_injective {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hR : 2 * R < X.systole) :
    Function.Injective (X.spinBoundaryParam o ρ) := by
  intro p q h
  have hq := congrArg Subtype.val h
  have hp : p.1 = q.1 := X.orbitProjection_polarPoint_injective o hρ hρR hR
    (congrArg X.spinBase hq)
  obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.exact hq))
  have ha : A • gluingPolarPoint o q.1 ρ = gluingPolarPoint o q.1 ρ := by
    have ht := congrArg HalfPlaneSpinFrame.point hA
    change (A : SL(2, ℝ)) • gluingPolarPoint o q.1 ρ = gluingPolarPoint o p.1 ρ at ht
    change (A : SL(2, ℝ)) • gluingPolarPoint o q.1 ρ = gluingPolarPoint o q.1 ρ
    simpa only [hp] using ht
  have hAone := X.free A (gluingPolarPoint o q.1 ρ) ha
  subst A
  rw [one_smul] at hA
  exact Prod.ext hp (congrArg HalfPlaneSpinFrame.phase hA).symm

theorem tangentBoundaryParam_injective {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hR : 2 * R < X.systole) :
    Function.Injective (X.tangentBoundaryParam o ρ) := by
  intro p q h
  have hq := congrArg Subtype.val h
  have hp : p.1 = q.1 := X.orbitProjection_polarPoint_injective o hρ hρR hR
    (congrArg X.tangentFrameBase hq)
  obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.exact hq))
  have ha : A • gluingPolarPoint o q.1 ρ = gluingPolarPoint o q.1 ρ := by
    have ht := congrArg HalfPlaneTangentFrame.point hA
    change (A : SL(2, ℝ)) • gluingPolarPoint o q.1 ρ = gluingPolarPoint o p.1 ρ at ht
    change (A : SL(2, ℝ)) • gluingPolarPoint o q.1 ρ = gluingPolarPoint o q.1 ρ
    simpa only [hp] using ht
  have hAone := X.free A (gluingPolarPoint o q.1 ρ) ha
  subst A
  rw [one_smul] at hA
  exact Prod.ext hp (congrArg HalfPlaneTangentFrame.phase hA).symm

/-- Every actual spin direction over the boundary has a preferred polar lift. -/
theorem spinBoundaryParam_surjective {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) : Function.Surjective (X.spinBoundaryParam o ρ) := by
  rintro ⟨q, hq⟩
  induction q using Quotient.inductionOn with
  | h q =>
    obtain ⟨u, hu⟩ := hq
    obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact hu))
    let v : HalfPlaneSpinFrame := A • q
    refine ⟨(u, v.phase), ?_⟩
    apply Subtype.ext
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨A, ?_⟩
    apply HalfPlaneSpinFrame.ext
    · exact hA
    · rfl

theorem tangentBoundaryParam_surjective {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) : Function.Surjective (X.tangentBoundaryParam o ρ) := by
  rintro ⟨q, hq⟩
  induction q using Quotient.inductionOn with
  | h q =>
    obtain ⟨u, hu⟩ := hq
    obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp
      (MulAction.orbitRel_apply.mp (Quotient.exact hu))
    let v : HalfPlaneTangentFrame := A • q
    refine ⟨(u, v.phase), ?_⟩
    apply Subtype.ext
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨A, ?_⟩
    apply HalfPlaneTangentFrame.ext
    · exact hA
    · rfl

/-- A genuine product trivialization of the original component spin boundary. -/
def spinBoundaryChart {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hR : 2 * R < X.systole) :
    Circle × Circle ≃ₜ X.SpinBoundaryCarrier o ρ :=
  IsHomeomorph.homeomorph (X.spinBoundaryParam o ρ)
    (isHomeomorph_iff_continuous_bijective.mpr
      ⟨X.continuous_spinBoundaryParam o ρ,
        X.spinBoundaryParam_injective o hρ hρR hR,
        X.spinBoundaryParam_surjective o ρ⟩)

/-- A genuine product trivialization of the actual unit tangent boundary. -/
def tangentBoundaryChart {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hR : 2 * R < X.systole) :
    Circle × Circle ≃ₜ X.TangentBoundaryCarrier o ρ :=
  IsHomeomorph.homeomorph (X.tangentBoundaryParam o ρ)
    (isHomeomorph_iff_continuous_bijective.mpr
      ⟨X.continuous_tangentBoundaryParam o ρ,
        X.tangentBoundaryParam_injective o hρ hρR hR,
        X.tangentBoundaryParam_surjective o ρ⟩)

/-- The actual component squaring map restricted over the same boundary. -/
def spinBoundarySquare {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (ρ : ℝ)
    (q : X.SpinBoundaryCarrier o ρ) : X.TangentBoundaryCarrier o ρ :=
  ⟨X.spinSquare q.1, by simpa using q.2⟩

theorem continuous_spinBoundarySquare {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) : Continuous (X.spinBoundarySquare o ρ) :=
  (X.continuous_spinSquare.comp continuous_subtype_val).subtype_mk _

@[simp] theorem spinBoundarySquare_param {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) (p : Circle × Circle) :
    X.spinBoundarySquare o ρ (X.spinBoundaryParam o ρ p) =
      X.tangentBoundaryParam o ρ (p.1, p.2 ^ 2) := rfl

/-- Both genuine boundary charts preserve the actual spin double map. -/
@[simp] theorem spinBoundaryChart_square {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hR : 2 * R < X.systole)
    (p : Circle × Circle) :
    X.spinBoundarySquare o ρ (X.spinBoundaryChart o hρ hρR hR p) =
      X.tangentBoundaryChart o hρ hρR hR (p.1, p.2 ^ 2) := rfl

/-- Restriction preserves the genuine covering sheets; no boundary spin
cover is supplied as additional data. -/
theorem spinBoundarySquare_isCoveringMap {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (ρ : ℝ) : IsCoveringMap (X.spinBoundarySquare o ρ) := by
  let s : Set X.TangentFrameCarrier := X.tangentFrameBase ⁻¹' X.polarBoundary o ρ
  have he : X.spinBase ⁻¹' X.polarBoundary o ρ = X.spinSquare ⁻¹' s := by
    ext q
    simp [s]
  have h := (X.spinSquare_isCoveringMap.restrictPreimage s).comp_homeomorph
    (Homeomorph.setCongr he)
  exact h

/-- The literal Fermi square root transported to the two actual component
spin boundaries. Different component genera are allowed. -/
def fermiSpinBoundaryHomeomorph {gIn gOut : ℕ}
    (XIn : ClosedHyperbolicSurface gIn) (XOut : ClosedHyperbolicSurface gOut)
    (oIn oOut : ℍ) {ρ RIn ROut : ℝ} (hρ : 0 < ρ)
    (hIn : ρ < RIn) (hOut : ρ < ROut)
    (hsIn : 2 * RIn < XIn.systole) (hsOut : 2 * ROut < XOut.systole) :
    XOut.SpinBoundaryCarrier oOut ρ ≃ₜ XIn.SpinBoundaryCarrier oIn ρ :=
  ((XOut.spinBoundaryChart oOut hρ hOut hsOut).symm.trans
    (gluingFermiBoundarySpinHomeomorph ρ)).trans
      (XIn.spinBoundaryChart oIn hρ hIn hsIn)

/-- The corresponding genuine component tangent-boundary identification. -/
def fermiTangentBoundaryHomeomorph {gIn gOut : ℕ}
    (XIn : ClosedHyperbolicSurface gIn) (XOut : ClosedHyperbolicSurface gOut)
    (oIn oOut : ℍ) {ρ RIn ROut : ℝ} (hρ : 0 < ρ)
    (hIn : ρ < RIn) (hOut : ρ < ROut)
    (hsIn : 2 * RIn < XIn.systole) (hsOut : 2 * ROut < XOut.systole) :
    XOut.TangentBoundaryCarrier oOut ρ ≃ₜ XIn.TangentBoundaryCarrier oIn ρ :=
  ((XOut.tangentBoundaryChart oOut hρ hOut hsOut).symm.trans
    (gluingFermiBoundaryTangentHomeomorph ρ)).trans
      (XIn.tangentBoundaryChart oIn hρ hIn hsIn)

@[simp] theorem fermiSpinBoundaryHomeomorph_param {gIn gOut : ℕ}
    (XIn : ClosedHyperbolicSurface gIn) (XOut : ClosedHyperbolicSurface gOut)
    (oIn oOut : ℍ) {ρ RIn ROut : ℝ} (hρ : 0 < ρ)
    (hIn : ρ < RIn) (hOut : ρ < ROut)
    (hsIn : 2 * RIn < XIn.systole) (hsOut : 2 * ROut < XOut.systole)
    (p : Circle × Circle) :
    fermiSpinBoundaryHomeomorph XIn XOut oIn oOut hρ hIn hOut hsIn hsOut
      (XOut.spinBoundaryParam oOut ρ p) =
        XIn.spinBoundaryParam oIn ρ (gluingFermiBoundarySpinHomeomorph ρ p) := by
  change (XIn.spinBoundaryChart oIn hρ hIn hsIn)
    (gluingFermiBoundarySpinHomeomorph ρ
      ((XOut.spinBoundaryChart oOut hρ hOut hsOut).symm
        (XOut.spinBoundaryChart oOut hρ hOut hsOut p))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

@[simp] theorem fermiTangentBoundaryHomeomorph_param {gIn gOut : ℕ}
    (XIn : ClosedHyperbolicSurface gIn) (XOut : ClosedHyperbolicSurface gOut)
    (oIn oOut : ℍ) {ρ RIn ROut : ℝ} (hρ : 0 < ρ)
    (hIn : ρ < RIn) (hOut : ρ < ROut)
    (hsIn : 2 * RIn < XIn.systole) (hsOut : 2 * ROut < XOut.systole)
    (p : Circle × Circle) :
    fermiTangentBoundaryHomeomorph XIn XOut oIn oOut hρ hIn hOut hsIn hsOut
      (XOut.tangentBoundaryParam oOut ρ p) =
        XIn.tangentBoundaryParam oIn ρ (gluingFermiBoundaryTangentHomeomorph ρ p) := by
  change (XIn.tangentBoundaryChart oIn hρ hIn hsIn)
    (gluingFermiBoundaryTangentHomeomorph ρ
      ((XOut.tangentBoundaryChart oOut hρ hOut hsOut).symm
        (XOut.tangentBoundaryChart oOut hρ hOut hsOut p))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- Actual seam clutching commutes with the actual component spin covers. -/
theorem fermiSpinBoundaryHomeomorph_square {gIn gOut : ℕ}
    (XIn : ClosedHyperbolicSurface gIn) (XOut : ClosedHyperbolicSurface gOut)
    (oIn oOut : ℍ) {ρ RIn ROut : ℝ} (hρ : 0 < ρ)
    (hIn : ρ < RIn) (hOut : ρ < ROut)
    (hsIn : 2 * RIn < XIn.systole) (hsOut : 2 * ROut < XOut.systole)
    (q : XOut.SpinBoundaryCarrier oOut ρ) :
    XIn.spinBoundarySquare oIn ρ
      (fermiSpinBoundaryHomeomorph XIn XOut oIn oOut hρ hIn hOut hsIn hsOut q) =
        fermiTangentBoundaryHomeomorph XIn XOut oIn oOut hρ hIn hOut hsIn hsOut
          (XOut.spinBoundarySquare oOut ρ q) := by
  obtain ⟨p, rfl⟩ := XOut.spinBoundaryParam_surjective oOut ρ q
  rw [fermiSpinBoundaryHomeomorph_param, spinBoundarySquare_param,
    spinBoundarySquare_param, fermiTangentBoundaryHomeomorph_param]
  exact congrArg (XIn.tangentBoundaryParam oIn ρ)
    (gluingFermiBoundarySpinHomeomorph_square ρ p)

/-- The transported clutching identifies the two concrete square roots of
the literal incoming and outgoing radial differentials. -/
theorem fermiSpinBoundaryHomeomorph_radial_roots {gIn gOut : ℕ}
    (XIn : ClosedHyperbolicSurface gIn) (XOut : ClosedHyperbolicSurface gOut)
    (oIn oOut : ℍ) {ρ RIn ROut : ℝ} (hρ : 0 < ρ)
    (hIn : ρ < RIn) (hOut : ρ < ROut)
    (hsIn : 2 * RIn < XIn.systole) (hsOut : 2 * ROut < XOut.systole)
    (θ : ℝ) :
    fermiSpinBoundaryHomeomorph XIn XOut oIn oOut hρ hIn hOut hsIn hsOut
      (XOut.spinBoundaryParam oOut ρ
        (Circle.exp (-θ), gluingFermiOutgoingSpinCircle ρ (0, θ))) =
          XIn.spinBoundaryParam oIn ρ
            (Circle.exp θ, gluingFermiIncomingSpinCircle ρ (0, θ)) := by
  rw [fermiSpinBoundaryHomeomorph_param,
    gluingFermiBoundarySpinHomeomorph_radial_roots]

/-- The transported spin clutching covers the prescribed reflected
half-plane boundary identification, not merely an abstract circle map. -/
theorem fermiSpinBoundaryHomeomorph_base {gIn gOut : ℕ}
    (XIn : ClosedHyperbolicSurface gIn) (XOut : ClosedHyperbolicSurface gOut)
    (oIn oOut : ℍ) {ρ RIn ROut : ℝ} (hρ : 0 < ρ)
    (hIn : ρ < RIn) (hOut : ρ < ROut)
    (hsIn : 2 * RIn < XIn.systole) (hsOut : 2 * ROut < XOut.systole)
    (p : Circle × Circle) :
    XIn.spinBase
      (fermiSpinBoundaryHomeomorph XIn XOut oIn oOut hρ hIn hOut hsIn hsOut
        (XOut.spinBoundaryParam oOut ρ p)).1 =
          XIn.orbitProjection
            (gluingCircleMap oOut oIn (gluingPolarPoint oOut p.1 ρ)) := by
  rw [fermiSpinBoundaryHomeomorph_param, gluingCircleMap_gluingPolarPoint]
  rfl

end ClosedHyperbolicSurface

#print axioms gluingPolarPoint_injective
#print axioms ClosedHyperbolicSurface.orbitProjection_polarPoint_injective
#print axioms ClosedHyperbolicSurface.spinBoundaryParam_surjective
#print axioms ClosedHyperbolicSurface.spinBoundaryChart
#print axioms ClosedHyperbolicSurface.tangentBoundaryChart
#print axioms ClosedHyperbolicSurface.spinBoundaryChart_square
#print axioms ClosedHyperbolicSurface.spinBoundarySquare_isCoveringMap
#print axioms ClosedHyperbolicSurface.fermiSpinBoundaryHomeomorph_square
#print axioms ClosedHyperbolicSurface.fermiSpinBoundaryHomeomorph_radial_roots
#print axioms ClosedHyperbolicSurface.fermiSpinBoundaryHomeomorph_base

end
end SystolicGrowth

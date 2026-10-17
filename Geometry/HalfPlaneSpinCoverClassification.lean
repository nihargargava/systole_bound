module

public import Geometry.HalfPlaneSpinLift
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

/-!
# Classification of the actual odd two-sheet half-plane spin cover

The simply connected real-angle plane lifts through the genuine covering.
Odd monodromy of its actual fiber turn forces a half-turn to act by the
given antipode, and full-turn periodicity descends the lift to spin frames.
Exact two-point fibers and local covering maps supply the homeomorphism.
-/

open UpperHalfPlane Topology Set
open scoped UpperHalfPlane unitInterval

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SystolicGrowth

/-- **Math.** The literal base frame at the standard half-plane point. -/
def halfPlaneStandardTangentFrame : HalfPlaneTangentFrame := ⟨UpperHalfPlane.I, 1⟩

/-- **Math.** Real spin angles project by the actual doubled angle to
oriented tangent frames. -/
def halfPlaneRealSpinProjection (q : ℍ × ℝ) : HalfPlaneTangentFrame :=
  ⟨q.1, Circle.exp (2 * q.2)⟩

theorem continuous_halfPlaneRealSpinProjection : Continuous halfPlaneRealSpinProjection := by
  apply continuous_induced_rng.mpr
  exact continuous_fst.prodMk (Circle.exp.continuous.comp (continuous_const.mul continuous_snd))

@[simp]
theorem halfPlaneRealSpinProjection_standard_zero :
    halfPlaneRealSpinProjection (UpperHalfPlane.I, 0) = halfPlaneStandardTangentFrame := by
  apply HalfPlaneTangentFrame.ext <;> simp [halfPlaneRealSpinProjection, halfPlaneStandardTangentFrame]

theorem halfPlaneRealSpinProjection_add_pi (z : ℍ) (t : ℝ) :
    halfPlaneRealSpinProjection (z, t + Real.pi) = halfPlaneRealSpinProjection (z, t) := by
  apply HalfPlaneTangentFrame.ext
  · rfl
  · change Circle.exp (2 * (t + Real.pi)) = Circle.exp (2 * t)
    rw [show 2 * (t + Real.pi) = 2 * t + 2 * Real.pi by ring, Circle.exp_add_two_pi]

/-- **Math.** The actual standard one-turn tangent-fiber loop. Its real
spin-angle path runs from `0` to `π`, not from `0` to `2π`. -/
def halfPlaneStandardFrameOneTurn :
    Path halfPlaneStandardTangentFrame halfPlaneStandardTangentFrame where
  toFun t := halfPlaneRealSpinProjection (UpperHalfPlane.I, Real.pi * (t : ℝ))
  continuous_toFun := continuous_halfPlaneRealSpinProjection.comp
    (continuous_const.prodMk (continuous_const.mul continuous_subtype_val))
  source' := by simp
  target' := by
    change halfPlaneRealSpinProjection (UpperHalfPlane.I, Real.pi * 1) = _
    rw [mul_one, show Real.pi = 0 + Real.pi by simp,
      halfPlaneRealSpinProjection_add_pi, halfPlaneRealSpinProjection_standard_zero]

/-- **Math.** The real-angle plane genuinely lifts through the covering.
The prescribed odd standard-turn monodromy forces a `π` spin-angle shift
to equal the actual antipode everywhere, by connected lifting uniqueness. -/
theorem exists_halfPlaneRealSpinLift_antipodal
    {E : Type*} [TopologicalSpace E]
    (p : E → HalfPlaneTangentFrame) (hp : IsCoveringMap p)
    (A : E → E) (hA : Continuous A) (hpA : ∀ e, p (A e) = p e)
    (e₀ : E) (he₀ : p e₀ = halfPlaneStandardTangentFrame)
    (hodd : hp.liftPath halfPlaneStandardFrameOneTurn e₀
      (halfPlaneStandardFrameOneTurn.source.trans he₀.symm) 1 = A e₀) :
    ∃ F : C(ℍ × ℝ, E), F (UpperHalfPlane.I, 0) = e₀ ∧
      p ∘ F = halfPlaneRealSpinProjection ∧
      ∀ z t, F (z, t + Real.pi) = A (F (z, t)) := by
  letI : LocallyPathConnectedSpace (ℍ × ℝ) :=
    (UpperHalfPlane.isOpenEmbedding_coe.prodMap IsOpenEmbedding.id).locallyPathConnectedSpace
  obtain ⟨F, ⟨hF₀, hFp⟩, _⟩ := hp.existsUnique_continuousMap_lifts
    ⟨halfPlaneRealSpinProjection, continuous_halfPlaneRealSpinProjection⟩
    (UpperHalfPlane.I, 0) e₀ (he₀.trans halfPlaneRealSpinProjection_standard_zero.symm)
  let Γ : C(unitInterval, E) :=
    { toFun := fun t => F (UpperHalfPlane.I, Real.pi * (t : ℝ))
      continuous_toFun := F.continuous.comp
        (continuous_const.prodMk (continuous_const.mul continuous_subtype_val)) }
  have hΓ : Γ = hp.liftPath halfPlaneStandardFrameOneTurn e₀
      (halfPlaneStandardFrameOneTurn.source.trans he₀.symm) := by
    apply (hp.eq_liftPath_iff' _).mpr
    refine ⟨?_, ?_⟩
    · funext t
      exact congrFun hFp (UpperHalfPlane.I, Real.pi * (t : ℝ))
    · change F (UpperHalfPlane.I, Real.pi * 0) = e₀
      simpa only [mul_zero] using hF₀
  have hFπ : F (UpperHalfPlane.I, Real.pi) = A e₀ := by
    have h := congrArg (fun f : C(unitInterval, E) => f 1) hΓ
    change F (UpperHalfPlane.I, Real.pi * 1) = _ at h
    simpa only [mul_one] using h.trans hodd
  have hcontShift : Continuous (fun q : ℍ × ℝ => F (q.1, q.2 + Real.pi)) :=
    F.continuous.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
  have hcontA : Continuous (fun q : ℍ × ℝ => A (F q)) := hA.comp F.continuous
  have hcomp : p ∘ (fun q : ℍ × ℝ => F (q.1, q.2 + Real.pi)) =
      p ∘ (fun q : ℍ × ℝ => A (F q)) := by
    funext q
    calc
      p (F (q.1, q.2 + Real.pi)) = halfPlaneRealSpinProjection (q.1, q.2 + Real.pi) :=
        congrFun hFp _
      _ = halfPlaneRealSpinProjection q := halfPlaneRealSpinProjection_add_pi q.1 q.2
      _ = p (F q) := (congrFun hFp q).symm
      _ = p (A (F q)) := (hpA (F q)).symm
  have heq := hp.eq_of_comp_eq hcontShift hcontA hcomp (UpperHalfPlane.I, 0) (by
    simpa only [zero_add, hF₀] using hFπ)
  exact ⟨F, hF₀, hFp, fun z t => congrFun heq (z, t)⟩

/-- **Math.** A genuine two-sheet covering of the actual oriented-frame
space, with antipodal fibers and odd monodromy on the actual standard
fiber turn, is homeomorphic over frames to the canonical spin model. The
homeomorphism and its antipode compatibility are constructed, not supplied
as hypotheses. -/
theorem exists_halfPlaneSpinCoverHomeomorph
    {E : Type*} [TopologicalSpace E]
    (p : E → HalfPlaneTangentFrame) (hp : IsCoveringMap p)
    (A : E → E) (hA : Continuous A)
    (hAA : ∀ e, A (A e) = e) (hAne : ∀ e, A e ≠ e)
    (hfiber : ∀ e f, p e = p f ↔ e = f ∨ e = A f)
    (e₀ : E) (he₀ : p e₀ = halfPlaneStandardTangentFrame)
    (hodd : hp.liftPath halfPlaneStandardFrameOneTurn e₀
      (halfPlaneStandardFrameOneTurn.source.trans he₀.symm) 1 = A e₀) :
    ∃ H : HalfPlaneSpinFrame ≃ₜ E,
      (∀ q, p (H q) = halfPlaneSpinSquare q) ∧
      (∀ q, H (halfPlaneSpinAntipode q) = A (H q)) ∧
      H ⟨UpperHalfPlane.I, 1⟩ = e₀ := by
  have hpA : ∀ e, p (A e) = p e := fun e => (hfiber (A e) e).mpr (Or.inr rfl)
  obtain ⟨F, hF₀, hFp, hFπ⟩ :=
    exists_halfPlaneRealSpinLift_antipodal p hp A hA hpA e₀ he₀ hodd
  have hperiod (z : ℍ) : Function.Periodic (fun t => F (z, t)) (2 * Real.pi) := by
    intro t
    calc
      F (z, t + 2 * Real.pi) = F (z, (t + Real.pi) + Real.pi) := by
        rw [show t + 2 * Real.pi = (t + Real.pi) + Real.pi by ring]
      _ = A (F (z, t + Real.pi)) := hFπ z (t + Real.pi)
      _ = A (A (F (z, t))) := congrArg A (hFπ z t)
      _ = F (z, t) := hAA _
  let H : HalfPlaneSpinFrame → E := fun q => F (q.point, q.phase.val.arg)
  have hHexp (z : ℍ) (t : ℝ) : H ⟨z, Circle.exp t⟩ = F (z, t) := by
    change F (z, (Circle.exp t : ℂ).arg) = F (z, t)
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp (Circle.exp_arg (Circle.exp t))
    rw [hk]
    exact (hperiod z).int_mul k t
  let spinExp : ℍ × ℝ → HalfPlaneSpinFrame := fun q => ⟨q.1, Circle.exp q.2⟩
  have hspinExp : Continuous spinExp := by
    apply continuous_induced_rng.mpr
    exact continuous_fst.prodMk (Circle.exp.continuous.comp continuous_snd)
  have hopenSpinExp : IsOpenMap spinExp :=
    halfPlaneSpinFrameHomeomorph.symm.isOpenMap.comp
      (IsOpenMap.id.prodMap Circle.isCoveringMap_exp.isOpenMap)
  have hsurjSpinExp : Function.Surjective spinExp := by
    intro q
    obtain ⟨t, ht⟩ := Circle.exp_surjective q.phase
    exact ⟨(q.point, t), HalfPlaneSpinFrame.ext rfl ht⟩
  have hH : Continuous H := by
    apply (hopenSpinExp.isQuotientMap hspinExp hsurjSpinExp).continuous_iff.mpr
    have heq : H ∘ spinExp = F := funext fun q => hHexp q.1 q.2
    rw [heq]
    exact F.continuous
  have hsquare : ∀ q, p (H q) = halfPlaneSpinSquare q := by
    intro q
    change p (F (q.point, q.phase.val.arg)) = _
    rw [show p (F (q.point, q.phase.val.arg)) =
      halfPlaneRealSpinProjection (q.point, q.phase.val.arg) from congrFun hFp _]
    apply HalfPlaneTangentFrame.ext
    · rfl
    · change Circle.exp (2 * q.phase.val.arg) = q.phase ^ 2
      rw [show 2 * q.phase.val.arg = q.phase.val.arg + q.phase.val.arg by ring,
        Circle.exp_add, Circle.exp_arg, pow_two]
  have hanti : ∀ q, H (halfPlaneSpinAntipode q) = A (H q) := by
    intro q
    have hrep : (⟨q.point, Circle.exp q.phase.val.arg⟩ : HalfPlaneSpinFrame) = q := by
      apply HalfPlaneSpinFrame.ext
      · rfl
      · exact Circle.exp_arg q.phase
    have hrepAnti :
        (⟨q.point, Circle.exp (q.phase.val.arg + Real.pi)⟩ : HalfPlaneSpinFrame) =
          halfPlaneSpinAntipode q := by
      apply HalfPlaneSpinFrame.ext
      · rfl
      · apply Circle.ext
        change (Circle.exp (q.phase.val.arg + Real.pi) : ℂ) = ((-q.phase : Circle) : ℂ)
        rw [Circle.coe_exp, Circle.coe_neg, Complex.ofReal_add, add_mul,
          Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one,
          show Complex.exp (q.phase.val.arg * Complex.I) = (q.phase : ℂ) from
            congrArg Subtype.val (Circle.exp_arg q.phase)]
    calc
      H (halfPlaneSpinAntipode q) = H ⟨q.point, Circle.exp (q.phase.val.arg + Real.pi)⟩ :=
        congrArg H hrepAnti.symm
      _ = F (q.point, q.phase.val.arg + Real.pi) := hHexp _ _
      _ = A (F (q.point, q.phase.val.arg)) := hFπ _ _
      _ = A (H q) := by rw [← hHexp, hrep]
  have hinj : Function.Injective H := by
    intro q r hqr
    have hs : halfPlaneSpinSquare q = halfPlaneSpinSquare r := by
      rw [← hsquare, ← hsquare, hqr]
    rcases (halfPlaneSpinSquare_eq_iff q r).mp hs with h | h
    · exact h
    · have ha : A (H r) = H r := by rw [← hanti, ← h, hqr]
      exact False.elim (hAne (H r) ha)
  have hsurj : Function.Surjective H := by
    intro e
    obtain ⟨q, hq⟩ := halfPlaneSpinSquare_surjective (p e)
    have hpe : p (H q) = p e := (hsquare q).trans hq
    rcases (hfiber (H q) e).mp hpe with h | h
    · exact ⟨q, h⟩
    · refine ⟨halfPlaneSpinAntipode q, ?_⟩
      rw [hanti, h, hAA]
  have hlocal : IsLocalHomeomorph H := by
    have hcomp : p ∘ H = halfPlaneSpinSquare := funext hsquare
    have h := halfPlaneSpinSquare_isLocalHomeomorph
    rw [← hcomp] at h
    exact h.of_comp hp.isLocalHomeomorph hH
  let e := Equiv.ofBijective H ⟨hinj, hsurj⟩
  let model : HalfPlaneSpinFrame ≃ₜ E := e.toHomeomorphOfContinuousOpen hH hlocal.isOpenMap
  refine ⟨model, hsquare, hanti, ?_⟩
  change H ⟨UpperHalfPlane.I, 1⟩ = e₀
  have hexp : (⟨UpperHalfPlane.I, Circle.exp 0⟩ : HalfPlaneSpinFrame) =
      ⟨UpperHalfPlane.I, 1⟩ := by simp
  rw [← hexp, hHexp, hF₀]

#print axioms exists_halfPlaneRealSpinLift_antipodal
#print axioms exists_halfPlaneSpinCoverHomeomorph

end SystolicGrowth

module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSeamFundamentalGroup

@[expose] public section

/-!
# Positive circle winding is unchanged by based path transport

The positively oriented one-turn loop represents the same positive winding
class at every point of the circle, under Mathlib's path-induced based
fundamental-group equivalence.
-/

open Set
open scoped ContinuousMap unitInterval

namespace SystolicGrowth

noncomputable section

theorem circleFundamentalGroupMulEquivOfPath_apply
    {θ φ : Circle} (p : Path θ φ) (γ : Path θ θ) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath p ⟦γ⟧ =
      ⟦p.symm.trans (γ.trans p)⟧ := by
  rfl

/-- The positive one-turn class is unchanged by transport along the standard
counterclockwise arc between two points of the circle. -/
theorem circleOneTurnLoop_rebase_circlePath (θ φ : Circle) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (Circle.path θ φ)
        ⟦circleOneTurnLoop θ⟧ = ⟦circleOneTurnLoop φ⟧ := by
  rw [circleFundamentalGroupMulEquivOfPath_apply]
  let a : ℝ := (θ : ℂ).arg
  let b : ℝ := Circle.angleDiff θ φ + a
  let c : ℝ := (φ : ℂ).arg
  let period : ℝ := 2 * Real.pi
  let r : Path a b := Path.segment a b
  let oneθ : Path a (a + period) := Path.segment a (a + period)
  let shift : C(ℝ, ℝ) := ⟨fun x => x + period, continuous_id.add continuous_const⟩
  let rshift : Path (a + period) (b + period) := r.map shift.continuous
  let lifted : Path b (b + period) := r.symm.trans (oneθ.trans rshift)
  let straight : Path b (b + period) := Path.segment b (b + period)
  have hb : b = c ∨ b = c + period := by
    by_cases h : (θ : ℂ).arg ≤ (φ : ℂ).arg
    · left
      simp only [b, a, c, Circle.angleDiff, if_pos h]
      ring
    · right
      simp only [b, a, c, period, Circle.angleDiff, if_neg h]
      ring
  have hφ : Circle.exp b = φ := by
    rcases hb with h | h
    · rw [h]
      exact Circle.exp_arg φ
    · rw [h, Circle.exp_add_two_pi]
      exact Circle.exp_arg φ
  have hφshift : Circle.exp (b + period) = φ := by
    dsimp [period]
    rw [Circle.exp_add_two_pi, hφ]
  have hp : Circle.path θ φ =
      (r.map Circle.exp.continuous).cast (by simp [a])
        (by simp [b, a, hφ]) := by
    apply Path.ext
    funext t
    simp [Circle.path, r, a, b, Path.cast_coe, Path.map_coe]
  have honeθ : circleOneTurnLoop θ =
      (oneθ.map Circle.exp.continuous).cast (by simp [a])
        (by simp [a, period]) := by
    apply Path.ext
    funext t
    simp [circleOneTurnLoop, oneθ, a, period, Path.cast_coe, Path.map_coe]
  have hleft :
      ((lifted.map Circle.exp.continuous).cast hφ.symm hφshift.symm) =
        (Circle.path θ φ).symm.trans
          ((circleOneTurnLoop θ).trans (Circle.path θ φ)) := by
    apply Path.ext
    funext t
    simp [lifted, rshift, shift, r, oneθ, period, hp, honeθ, Path.cast_coe,
      Path.map_coe, Path.map_trans, Path.trans_apply, Circle.exp_two_pi]
  have hright :
      ((straight.map Circle.exp.continuous).cast hφ.symm hφshift.symm) =
        circleOneTurnLoop φ := by
    apply Path.ext
    funext t
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, straight,
      Path.segment_apply, circleOneTurnLoop_apply]
    change Circle.exp (AffineMap.lineMap b (b + period) (t : ℝ)) =
      Circle.exp (c + period * (t : ℝ))
    rcases hb with h | h
    · have hline : AffineMap.lineMap b (b + period) (t : ℝ) =
          c + period * (t : ℝ) := by
        rw [h, AffineMap.lineMap_apply]
        simp only [smul_eq_mul, vsub_eq_sub, vadd_eq_add]
        dsimp [period]
        ring
      rw [hline]
    · have hline : AffineMap.lineMap b (b + period) (t : ℝ) =
          c + period * (t : ℝ) + period := by
        rw [h, AffineMap.lineMap_apply]
        simp only [smul_eq_mul, vsub_eq_sub, vadd_eq_add]
        dsimp [period]
        ring
      rw [hline]
      dsimp [period]
      rw [Circle.exp_add_two_pi]
  have hhom : Path.Homotopic
      ((lifted.map Circle.exp.continuous).cast hφ.symm hφshift.symm)
      ((straight.map Circle.exp.continuous).cast hφ.symm hφshift.symm) := by
    have hmap : (lifted.map Circle.exp.continuous).Homotopic
        (straight.map Circle.exp.continuous) :=
      Path.Homotopic.map (SimplyConnectedSpace.paths_homotopic lifted straight) Circle.exp
    exact hmap.pathCast hφ.symm hφshift.symm
  rw [← hleft, ← hright]
  exact Path.Homotopic.Quotient.eq.mpr hhom

#print axioms circleOneTurnLoop_rebase_circlePath

/-- Paths avoiding the same rotated branch cut are homotopic relative to
their endpoints. The actual principal-argument lifts are continuous real
paths, whose homotopy projects back to the original circle paths. -/
theorem circle_paths_homotopic_of_mem_rotatedSlitPlane
    {θ φ : Circle} (p q : Path θ φ) (u : Circle)
    (hp : ∀ t : I, ((u * p t : Circle) : ℂ) ∈ Complex.slitPlane)
    (hq : ∀ t : I, ((u * q t : Circle) : ℂ) ∈ Complex.slitPlane) :
    p.Homotopic q := by
  let a : ℝ := ((u * θ : Circle) : ℂ).arg
  let b : ℝ := ((u * φ : Circle) : ℂ).arg
  let lift (r : Path θ φ)
      (hr : ∀ t : I, ((u * r t : Circle) : ℂ) ∈ Complex.slitPlane) : Path a b :=
    { toFun := fun t => ((u * r t : Circle) : ℂ).arg
      continuous_toFun := Complex.continuousOn_arg.comp_continuous
        (continuous_subtype_val.comp (continuous_const.mul r.continuous)) hr
      source' := by simp [a]
      target' := by simp [b] }
  let F : C(ℝ, Circle) :=
    ⟨fun x => u⁻¹ * Circle.exp x, continuous_const.mul Circle.exp.continuous⟩
  have ha : θ = F a := by
    change θ = u⁻¹ * Circle.exp (((u * θ : Circle) : ℂ).arg)
    rw [Circle.exp_arg]
    simp
  have hb : φ = F b := by
    change φ = u⁻¹ * Circle.exp (((u * φ : Circle) : ℂ).arg)
    rw [Circle.exp_arg]
    simp
  have hmap (r : Path θ φ)
      (hr : ∀ t : I, ((u * r t : Circle) : ℂ) ∈ Complex.slitPlane) :
      ((lift r hr).map F.continuous).cast ha hb = r := by
    apply Path.ext
    funext t
    change u⁻¹ * Circle.exp (((u * r t : Circle) : ℂ).arg) = r t
    rw [Circle.exp_arg]
    simp
  rw [← hmap p hp, ← hmap q hq]
  exact (Path.Homotopic.map
    (SimplyConnectedSpace.paths_homotopic (lift p hp) (lift q hq)) F).pathCast ha hb

#print axioms circle_paths_homotopic_of_mem_rotatedSlitPlane

/-- Two complementary positive circle arcs traverse exactly one positive
turn. The homotopy is obtained from real lifted paths with equal endpoints. -/
theorem circlePath_trans_circlePath_homotopic_oneTurn
    {θ φ : Circle} (hneq : θ ≠ φ) :
    ((Circle.path θ φ).trans (Circle.path φ θ)).Homotopic (circleOneTurnLoop θ) := by
  let a : ℝ := (θ : ℂ).arg
  let b : ℝ := Circle.angleDiff θ φ + a
  let c : ℝ := a + 2 * Real.pi
  let d : ℝ := (φ : ℂ).arg
  let r₁ : Path a b := Path.segment a b
  let r₂ : Path b c := Path.segment b c
  let lifted : Path a c := r₁.trans r₂
  let straight : Path a c := Path.segment a c
  have hb : b = d ∨ b = d + 2 * Real.pi := by
    by_cases h : (θ : ℂ).arg ≤ (φ : ℂ).arg
    · left
      simp only [b, a, d, Circle.angleDiff, if_pos h]
      ring
    · right
      simp only [b, a, d, Circle.angleDiff, if_neg h]
      ring
  have hc : c = Circle.angleDiff φ θ + b := by
    have h := Circle.angleDiff_add_angleDiff hneq
    dsimp [c, b]
    linarith
  have hθ : θ = Circle.exp a := (Circle.exp_arg θ).symm
  have hφ : φ = Circle.exp b := by
    rcases hb with h | h
    · rw [h]
      exact (Circle.exp_arg φ).symm
    · rw [h, Circle.exp_add_two_pi]
      exact (Circle.exp_arg φ).symm
  have hθc : θ = Circle.exp c := by
    dsimp [c]
    rw [Circle.exp_add_two_pi]
    exact hθ
  have hfirst : (r₁.map Circle.exp.continuous).cast hθ hφ = Circle.path θ φ := by
    apply Path.ext
    funext t
    simp [Circle.path, r₁, a, b, Path.cast_coe, Path.map_coe]
  have hsecond : (r₂.map Circle.exp.continuous).cast hφ hθc = Circle.path φ θ := by
    apply Path.ext
    funext t
    simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, r₂, Circle.path_apply,
      Path.segment_apply]
    change Circle.exp (AffineMap.lineMap b c (t : ℝ)) =
      Circle.exp (AffineMap.lineMap d (Circle.angleDiff φ θ + d) (t : ℝ))
    rcases hb with h | h
    · rw [hc, h]
    · have hline : AffineMap.lineMap b c (t : ℝ) =
          AffineMap.lineMap d (Circle.angleDiff φ θ + d) (t : ℝ) + 2 * Real.pi := by
        rw [hc, h, AffineMap.lineMap_apply, AffineMap.lineMap_apply]
        simp only [smul_eq_mul, vsub_eq_sub, vadd_eq_add]
        ring
      rw [hline, Circle.exp_add_two_pi]
  have hleft : (lifted.map Circle.exp.continuous).cast hθ hθc =
      (Circle.path θ φ).trans (Circle.path φ θ) := by
    apply Path.ext
    funext t
    simp [lifted, Path.map_trans, ← hfirst, ← hsecond, Path.cast_coe,
      Path.map_coe, Path.trans_apply]
  have hright : (straight.map Circle.exp.continuous).cast hθ hθc =
      circleOneTurnLoop θ := by
    apply Path.ext
    funext t
    simp [straight, a, c, circleOneTurnLoop, Path.cast_coe, Path.map_coe]
  rw [← hleft, ← hright]
  exact (Path.Homotopic.map (SimplyConnectedSpace.paths_homotopic lifted straight)
    Circle.exp).pathCast hθ hθc

/-- The complementary positive arcs have the literal positive one-turn
fundamental-group class, with no winding or endpoint hypothesis beyond being distinct. -/
theorem circlePath_trans_circlePath_oneTurn {θ φ : Circle} (hneq : θ ≠ φ) :
    (⟦(Circle.path θ φ).trans (Circle.path φ θ)⟧ : FundamentalGroup Circle θ) =
      ⟦circleOneTurnLoop θ⟧ :=
  Path.Homotopic.Quotient.eq.mpr (circlePath_trans_circlePath_homotopic_oneTurn hneq)

#print axioms circlePath_trans_circlePath_homotopic_oneTurn
#print axioms circlePath_trans_circlePath_oneTurn

end
end SystolicGrowth

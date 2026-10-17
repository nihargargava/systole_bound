module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Convex.PathConnected

@[expose] public section

/-!
# Height bounds for reflected circle arcs

The positive-real circle point and its reflection across the imaginary axis
are joined by an upper arc and a complementary lower arc. These lemmas give
their actual pointwise height bounds from sine monotonicity.
-/

open Set
open scoped Topology unitInterval

namespace SystolicGrowth

private theorem realSegment_mem_Icc {a b : ℝ} (hab : a ≤ b) (t : unitInterval) :
    Path.segment a b t ∈ Set.Icc a b := by
  have hmem : Path.segment a b t ∈ Set.range (Path.segment a b) := ⟨t, rfl⟩
  rw [Path.range_segment, segment_eq_Icc hab] at hmem
  exact hmem

/-- Sine is at least its initial value along the upper circle window from
`u` to its reflection `π - u`. -/
theorem real_sin_le_sin_of_upperArcWindow {u v : ℝ}
    (hu : u ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hv : v ∈ Set.Icc u (Real.pi - u)) :
    Real.sin u ≤ Real.sin v := by
  by_cases hv2 : v ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two hu.1 hv2 hv.1
  · have hreflect : Real.pi - v ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · linarith [hu.1, hv.2]
      · linarith [hu.1, hv.2]
    have horder : u ≤ Real.pi - v := by linarith [hv.2]
    rw [← Real.sin_pi_sub v]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two hu.1 hreflect.2 horder

/-- Sine is at most its initial value along the complementary circle window
from `π - u` to `2π + u`. -/
theorem real_sin_le_start_of_lowerArcWindow {u v : ℝ}
    (hu : u ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hv : v ∈ Set.Icc (Real.pi - u) (2 * Real.pi + u)) :
    Real.sin v ≤ Real.sin u := by
  by_cases hv3 : v ≤ 3 * Real.pi / 2
  · have hreflect : Real.pi - v ∈ Set.Icc (-(Real.pi / 2)) u := by
      constructor
      · linarith [hv3, Real.pi_pos]
      · linarith [hv.1]
    rw [← Real.sin_pi_sub v]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two hreflect.1 hu.2
      (by linarith [hreflect.2])
  · have hperiodic : v - 2 * Real.pi ∈ Set.Icc (-(Real.pi / 2)) u := by
      constructor
      · linarith [hv3]
      · linarith [hu.2, hv.2]
    rw [← Real.sin_sub_two_pi v]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two hperiodic.1 hu.2 hperiodic.2

private theorem circle_exp_im (x : ℝ) : (Circle.exp x : ℂ).im = Real.sin x := by
  rw [Circle.coe_exp, Complex.exp_mul_I]
  have hsin : (Complex.sin (x : ℂ)).re = Real.sin x := Complex.sin_ofReal_re x
  simpa using hsin

private theorem circle_reflected_exp {θ φ : Circle} (hθ : (θ : ℂ).re > 0)
    (hφ : (φ : ℂ) = -star (θ : ℂ)) :
    Circle.exp (Real.pi - (θ : ℂ).arg) = φ := by
  let u := (θ : ℂ).arg
  have huAbs : |u| < Real.pi / 2 := by
    apply Complex.abs_arg_lt_pi_div_two_iff.mpr
    exact Or.inl hθ
  have hπ : Circle.exp Real.pi = -1 := by
    apply Circle.ext
    rw [Circle.coe_exp, Complex.exp_pi_mul_I]
    norm_num
  have hθexp : Circle.exp u = θ := Circle.exp_arg θ
  calc
    Circle.exp (Real.pi - u) = Circle.exp Real.pi / Circle.exp u := by
      rw [Circle.exp_sub]
    _ = -1 / θ := by rw [hπ, hθexp]
    _ = -(θ⁻¹) := by simp [div_eq_mul_inv]
    _ = φ := by
      apply Circle.ext
      rw [Circle.coe_neg, Circle.coe_inv_eq_conj]
      exact hφ.symm

private theorem circle_reflected_angleDiff {θ φ : Circle}
    (hθ : (θ : ℂ).re > 0) (hφ : (φ : ℂ) = -star (θ : ℂ)) :
    Circle.angleDiff θ φ = Real.pi - 2 * (θ : ℂ).arg := by
  let u := (θ : ℂ).arg
  have huAbs : |u| < Real.pi / 2 := by
    apply Complex.abs_arg_lt_pi_div_two_iff.mpr
    exact Or.inl hθ
  have htheta : Circle.exp u = θ := Circle.exp_arg θ
  have hphi : Circle.exp (Real.pi - u) = φ := circle_reflected_exp hθ hφ
  have hexp : Circle.exp (Circle.angleDiff θ φ) = Circle.exp (Real.pi - 2 * u) := by
    calc
      Circle.exp (Circle.angleDiff θ φ) =
          Circle.exp (Circle.angleDiff θ φ) * θ * θ⁻¹ := by group
      _ = φ * θ⁻¹ := by rw [Circle.exp_angleDiff_mul]
      _ = Circle.exp (Real.pi - 2 * u) := by
        calc
          φ * θ⁻¹ = Circle.exp (Real.pi - u) * Circle.exp (-u) := by
            rw [← hphi, ← htheta, ← Circle.exp_neg]
          _ = Circle.exp ((Real.pi - u) + (-u)) := by rw [← Circle.exp_add]
          _ = Circle.exp (Real.pi - 2 * u) := by congr 1; ring
  have hinj : Set.InjOn Circle.exp (Set.Ico 0 (2 * Real.pi)) :=
    Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by nlinarith [Real.pi_pos])
  have hd : Real.pi - 2 * u ∈ Set.Ico 0 (2 * Real.pi) := by
    constructor
    · change 0 ≤ Real.pi - 2 * u
      nlinarith [abs_lt.mp huAbs]
    · change Real.pi - 2 * u < 2 * Real.pi
      nlinarith [abs_lt.mp huAbs]
  exact hinj ⟨Circle.angleDiff_nonneg θ φ, Circle.angleDiff_lt_two_pi θ φ⟩ hd hexp

/-- Every point of the positive (upper) arc from `θ` to its reflection has
imaginary part at least that of `θ`. -/
theorem circle_path_im_ge_source_of_re_pos_reflection {θ φ : Circle}
    (hθ : 0 < (θ : ℂ).re) (hφ : (φ : ℂ) = -star (θ : ℂ)) (t : unitInterval) :
    (θ : ℂ).im ≤ ((Circle.path θ φ t : Circle) : ℂ).im := by
  let u := (θ : ℂ).arg
  have huAbs : |u| < Real.pi / 2 := by
    apply Complex.abs_arg_lt_pi_div_two_iff.mpr
    exact Or.inl hθ
  have hu : u ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨le_of_lt (abs_lt.mp huAbs).1, le_of_lt (abs_lt.mp huAbs).2⟩
  have htheta : Circle.exp u = θ := Circle.exp_arg θ
  have harg : (θ : ℂ).arg = u := rfl
  have hangle : Circle.angleDiff θ φ = Real.pi - 2 * u :=
    circle_reflected_angleDiff hθ hφ
  have hval : Circle.path θ φ t = Circle.exp (Path.segment u (Real.pi - u) t) := by
    rw [Circle.path_apply, harg, hangle]
    rw [show Real.pi - 2 * u + u = Real.pi - u by ring]
  have hv : Path.segment u (Real.pi - u) t ∈ Set.Icc u (Real.pi - u) :=
    realSegment_mem_Icc (by linarith [hu.2]) t
  have hsin := real_sin_le_sin_of_upperArcWindow hu hv
  have hθim : (θ : ℂ).im = Real.sin u := by
    rw [← htheta]
    exact circle_exp_im u
  rw [hval, circle_exp_im, hθim]
  exact hsin

private theorem circle_reflected_angleDiff_reverse {θ φ : Circle}
    (hθ : (θ : ℂ).re > 0) (hφ : (φ : ℂ) = -star (θ : ℂ)) :
    Circle.angleDiff φ θ = Real.pi + 2 * (θ : ℂ).arg := by
  have hne : θ ≠ φ := by
    intro heq
    have hre := congrArg (fun z : Circle => (z : ℂ).re) heq
    have hφre : (φ : ℂ).re = -(θ : ℂ).re := by rw [hφ]; simp
    rw [hφre] at hre
    linarith
  have hsum := Circle.angleDiff_add_angleDiff hne
  rw [circle_reflected_angleDiff hθ hφ] at hsum
  linarith

private theorem circle_reflected_arg_cases {θ φ : Circle}
    (hθ : (θ : ℂ).re > 0) (hφ : (φ : ℂ) = -star (θ : ℂ)) :
    if 0 ≤ (θ : ℂ).arg then (φ : ℂ).arg = Real.pi - (θ : ℂ).arg
    else (φ : ℂ).arg = -Real.pi - (θ : ℂ).arg := by
  let u := (θ : ℂ).arg
  have huAbs : |u| < Real.pi / 2 := by
    apply Complex.abs_arg_lt_pi_div_two_iff.mpr
    exact Or.inl hθ
  have huL : -(Real.pi / 2) < u := (abs_lt.mp huAbs).1
  have huU : u < Real.pi / 2 := (abs_lt.mp huAbs).2
  have hphi : Circle.exp (Real.pi - u) = φ := circle_reflected_exp hθ hφ
  change (if 0 ≤ u then (φ : ℂ).arg = Real.pi - u
    else (φ : ℂ).arg = -Real.pi - u)
  by_cases hu : 0 ≤ u
  · simp only [if_pos hu]
    rw [← hphi]
    exact Circle.arg_exp (by linarith [Real.pi_pos, huL, huU]) (by linarith)
  · simp only [if_neg hu]
    have hperiod : Circle.exp (2 * Real.pi) = 1 := by
      apply Circle.ext
      simp
    have hphi' : Circle.exp (-Real.pi - u) = φ := by
      calc
        Circle.exp (-Real.pi - u) = Circle.exp ((Real.pi - u) - 2 * Real.pi) := by
          congr 1; ring
        _ = Circle.exp (Real.pi - u) / Circle.exp (2 * Real.pi) := Circle.exp_sub _ _
        _ = φ := by rw [hperiod, div_one, hphi]
    rw [← hphi']
    exact Circle.arg_exp (by linarith [hu]) (by linarith [Real.pi_pos, huL, huU])

/-- Every point of the complementary (lower) arc from `φ` back to `θ` has
imaginary part at most that of `θ`. -/
theorem circle_path_im_le_source_of_re_pos_reflection {θ φ : Circle}
    (hθ : 0 < (θ : ℂ).re) (hφ : (φ : ℂ) = -star (θ : ℂ)) (t : unitInterval) :
    ((Circle.path φ θ t : Circle) : ℂ).im ≤ (θ : ℂ).im := by
  let u := (θ : ℂ).arg
  have huAbs : |u| < Real.pi / 2 := by
    apply Complex.abs_arg_lt_pi_div_two_iff.mpr
    exact Or.inl hθ
  have hu : u ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨le_of_lt (abs_lt.mp huAbs).1, le_of_lt (abs_lt.mp huAbs).2⟩
  have htheta : Circle.exp u = θ := Circle.exp_arg θ
  have hθim : (θ : ℂ).im = Real.sin u := by
    rw [← htheta]
    exact circle_exp_im u
  have hangle := circle_reflected_angleDiff_reverse hθ hφ
  by_cases hu0 : 0 ≤ u
  · have harg := circle_reflected_arg_cases hθ hφ
    change (if 0 ≤ u then (φ : ℂ).arg = Real.pi - u
      else (φ : ℂ).arg = -Real.pi - u) at harg
    simp only [if_pos hu0] at harg
    have hpath : Circle.path φ θ t =
        Circle.exp (Path.segment (Real.pi - u) (2 * Real.pi + u) t) := by
      rw [Circle.path_apply, harg, hangle]
      rw [show Real.pi + 2 * u + (Real.pi - u) = 2 * Real.pi + u by ring]
    have hv : Path.segment (Real.pi - u) (2 * Real.pi + u) t ∈
        Set.Icc (Real.pi - u) (2 * Real.pi + u) :=
      realSegment_mem_Icc (by linarith [hu.1]) t
    have hsin := real_sin_le_start_of_lowerArcWindow hu hv
    have hpathIm : ((Circle.path φ θ t : Circle) : ℂ).im =
        Real.sin (Path.segment (Real.pi - u) (2 * Real.pi + u) t) := by
      rw [hpath]
      exact circle_exp_im _
    rw [hpathIm, hθim]
    exact hsin
  · have huNeg : u < 0 := lt_of_not_ge hu0
    have harg := circle_reflected_arg_cases hθ hφ
    change (if 0 ≤ u then (φ : ℂ).arg = Real.pi - u
      else (φ : ℂ).arg = -Real.pi - u) at harg
    simp only [if_neg hu0] at harg
    have hpath : Circle.path φ θ t =
        Circle.exp (Path.segment (-Real.pi - u) u t) := by
      rw [Circle.path_apply, harg, hangle]
      rw [show Real.pi + 2 * u + (-Real.pi - u) = u by ring]
    have hv0 : Path.segment (-Real.pi - u) u t ∈
        Set.Icc (-Real.pi - u) u :=
      realSegment_mem_Icc (by linarith [hu.1]) t
    have hv : Path.segment (-Real.pi - u) u t + 2 * Real.pi ∈
        Set.Icc (Real.pi - u) (2 * Real.pi + u) := by
      constructor <;> linarith [hv0.1, hv0.2]
    have hsin := real_sin_le_start_of_lowerArcWindow hu hv
    have hpathIm : ((Circle.path φ θ t : Circle) : ℂ).im =
        Real.sin (Path.segment (-Real.pi - u) u t) := by
      rw [hpath]
      exact circle_exp_im _
    rw [hpathIm, hθim]
    rw [← Real.sin_add_two_pi (Path.segment (-Real.pi - u) u t)]
    exact hsin

#print axioms real_sin_le_sin_of_upperArcWindow
#print axioms real_sin_le_start_of_lowerArcWindow
#print axioms circle_path_im_ge_source_of_re_pos_reflection
#print axioms circle_path_im_le_source_of_re_pos_reflection

end SystolicGrowth

module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.HyperbolicMetricSegments
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-!
# Genuine hyperbolic midpoints and their comparison identity

Vertical normalization constructs a midpoint in the actual Poincare metric.
Its universal third-point cosh identity also proves uniqueness, so the same
identity holds for every metric midpoint, including coincident endpoints.
-/

open UpperHalfPlane
open Filter
open Set
open scoped UpperHalfPlane MatrixGroups Topology

namespace SystolicGrowth

private theorem exp_midpoint_cosh_identity (u v A b : ℝ) (hb : b ≠ 0) :
    2 * Real.cosh (|v - u| / 2) *
        ((A + Real.exp ((u + v) / 2) ^ 2) /
          (2 * b * Real.exp ((u + v) / 2))) =
      (A + Real.exp u ^ 2) / (2 * b * Real.exp u) +
        (A + Real.exp v ^ 2) / (2 * b * Real.exp v) := by
  have hhalf : |v - u| / 2 = |(v - u) / 2| := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hu : Real.exp u = Real.exp ((u + v) / 2) / Real.exp ((v - u) / 2) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hv : Real.exp v = Real.exp ((u + v) / 2) * Real.exp ((v - u) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hhalf, Real.cosh_abs, Real.cosh_eq, Real.exp_neg, hu, hv]
  field_simp [hb, Real.exp_ne_zero]
  ring

/-- The cosh-distance from any test point to an arbitrary point of the
exponential vertical geodesic, written directly in coordinates. -/
theorem hyperbolicVerticalSegmentPoint_cosh_dist (a u v t : ℝ) (x : ℍ) :
    Real.cosh (dist x (hyperbolicVerticalSegmentPoint a u v t)) =
      ((x.re - a) ^ 2 + x.im ^ 2 +
        Real.exp ((1 - t) * u + t * v) ^ 2) /
          (2 * x.im * Real.exp ((1 - t) * u + t * v)) := by
  rw [UpperHalfPlane.cosh_dist']
  simp only [hyperbolicVerticalSegmentPoint_re, hyperbolicVerticalSegmentPoint_im]

private theorem exp_sinh_interpolation_identity (u v t A b : ℝ) (hb : b ≠ 0) :
    Real.sinh (v - u) *
        ((A + Real.exp ((1 - t) * u + t * v) ^ 2) /
          (2 * b * Real.exp ((1 - t) * u + t * v))) =
      Real.sinh ((1 - t) * (v - u)) *
          ((A + Real.exp u ^ 2) / (2 * b * Real.exp u)) +
        Real.sinh (t * (v - u)) *
          ((A + Real.exp v ^ 2) / (2 * b * Real.exp v)) := by
  let D : ℝ := Real.exp (v - u)
  let T : ℝ := Real.exp (t * (v - u))
  let U : ℝ := Real.exp u
  have hD : D ≠ 0 := by simp [D]
  have hT : T ≠ 0 := by simp [T]
  have hU : U ≠ 0 := by simp [U]
  have hpath : Real.exp ((1 - t) * u + t * v) = U * T := by
    rw [show (1 - t) * u + t * v = u + t * (v - u) by ring,
      Real.exp_add]
  have hv : Real.exp v = U * D := by
    rw [show v = u + (v - u) by ring, Real.exp_add]
  have hleft : Real.exp ((1 - t) * (v - u)) = D / T := by
    rw [show (1 - t) * (v - u) = (v - u) - t * (v - u) by ring,
      Real.exp_sub]
  have hDpos : Real.exp (v - u) = D := rfl
  have hTpos : Real.exp (t * (v - u)) = T := rfl
  have hUpos : Real.exp u = U := rfl
  have hDneg : Real.exp (-(v - u)) = D⁻¹ := by
    rw [Real.exp_neg]
  have hTneg : Real.exp (-(t * (v - u))) = T⁻¹ := by
    rw [Real.exp_neg]
  have hleftneg : Real.exp (-((1 - t) * (v - u))) = (D / T)⁻¹ := by
    calc
      Real.exp (-((1 - t) * (v - u))) =
          (Real.exp ((1 - t) * (v - u)))⁻¹ := Real.exp_neg _
      _ = (D / T)⁻¹ := by rw [hleft]
  simp only [Real.sinh_eq]
  rw [hDpos, hDneg, hleft, hleftneg, hTpos, hTneg, hpath, hUpos, hv]
  field_simp [hb, hD, hT, hU]
  ring

/-- Along the explicit vertical hyperbolic geodesic, cosh-distance obeys the
exact one-dimensional hyperbolic interpolation identity for every test point.
The signed parameter handles either endpoint orientation and also the
degenerate constant segment. -/
theorem hyperbolicVerticalSegmentPoint_sinh_interpolation
    (a u v t : ℝ) (x : ℍ) :
    Real.sinh (v - u) *
        Real.cosh (dist x (hyperbolicVerticalSegmentPoint a u v t)) =
      Real.sinh ((1 - t) * (v - u)) *
          Real.cosh (dist x (hyperbolicVerticalSegmentPoint a u v 0)) +
        Real.sinh (t * (v - u)) *
          Real.cosh (dist x (hyperbolicVerticalSegmentPoint a u v 1)) := by
  rw [hyperbolicVerticalSegmentPoint_cosh_dist,
    hyperbolicVerticalSegmentPoint_cosh_dist,
    hyperbolicVerticalSegmentPoint_cosh_dist]
  simp only [sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add]
  exact exp_sinh_interpolation_identity u v t
    ((x.re - a) ^ 2 + x.im ^ 2) x.im x.im_pos.ne'

private theorem geodInterp_smul (γ : SL(2, ℝ)) (a b : ℍ) (t : ℝ) :
    γ • Vendored.RiemannDynamics.geodInterp a b t =
      Vendored.RiemannDynamics.geodInterp (γ • a) (γ • b) t := by
  by_cases hab : a = b
  · subst b
    simp only [Vendored.RiemannDynamics.geodInterp_self]
  · have hAB : (γ • a : ℍ) ≠ γ • b := by
      intro h
      exact hab (smul_left_cancel γ h)
    have hcolLeft :
        dist (γ • a) (γ • Vendored.RiemannDynamics.geodInterp a b t) +
          dist (γ • Vendored.RiemannDynamics.geodInterp a b t) (γ • b) =
            dist (γ • a) (γ • b) ∨
        dist (γ • a) (γ • b) +
          dist (γ • b) (γ • Vendored.RiemannDynamics.geodInterp a b t) =
            dist (γ • a) (γ • Vendored.RiemannDynamics.geodInterp a b t) ∨
        dist (γ • Vendored.RiemannDynamics.geodInterp a b t) (γ • a) +
          dist (γ • a) (γ • b) =
            dist (γ • Vendored.RiemannDynamics.geodInterp a b t) (γ • b) := by
      rcases Vendored.RiemannDynamics.collinear_geodInterp a b t with h | h | h
      · left
        simpa only [dist_smul] using h
      · right
        left
        simpa only [dist_smul] using h
      · right
        right
        simpa only [dist_smul] using h
    have hcolRight := Vendored.RiemannDynamics.collinear_geodInterp
      (γ • a) (γ • b) t
    have hleft :
        dist (γ • a) (γ • Vendored.RiemannDynamics.geodInterp a b t) =
          dist (γ • a)
            (Vendored.RiemannDynamics.geodInterp (γ • a) (γ • b) t) := by
      calc
        dist (γ • a) (γ • Vendored.RiemannDynamics.geodInterp a b t) =
            dist (a : ℍ) (Vendored.RiemannDynamics.geodInterp a b t) :=
              dist_smul γ a _
        _ = |t| * dist a b :=
          Vendored.RiemannDynamics.dist_geodInterp_left_abs a b t
        _ = |t| * dist (γ • a) (γ • b) := by rw [dist_smul]
        _ = dist (γ • a)
            (Vendored.RiemannDynamics.geodInterp (γ • a) (γ • b) t) :=
          (Vendored.RiemannDynamics.dist_geodInterp_left_abs
            (γ • a) (γ • b) t).symm
    have hright :
        dist (γ • b) (γ • Vendored.RiemannDynamics.geodInterp a b t) =
          dist (γ • b)
            (Vendored.RiemannDynamics.geodInterp (γ • a) (γ • b) t) := by
      calc
        dist (γ • b) (γ • Vendored.RiemannDynamics.geodInterp a b t) =
            dist (b : ℍ) (Vendored.RiemannDynamics.geodInterp a b t) :=
              dist_smul γ b _
        _ = dist (Vendored.RiemannDynamics.geodInterp a b t) b := dist_comm _ _
        _ = |1 - t| * dist a b :=
          Vendored.RiemannDynamics.dist_geodInterp_right_abs a b t
        _ = |1 - t| * dist (γ • a) (γ • b) := by rw [dist_smul]
        _ = dist
            (Vendored.RiemannDynamics.geodInterp (γ • a) (γ • b) t) (γ • b) :=
          (Vendored.RiemannDynamics.dist_geodInterp_right_abs
            (γ • a) (γ • b) t).symm
        _ = dist (γ • b)
            (Vendored.RiemannDynamics.geodInterp (γ • a) (γ • b) t) := dist_comm _ _
    exact Vendored.RiemannDynamics.collinear_unique hAB hcolLeft hcolRight
      hleft hright

/-- The exact hyperbolic cosh interpolation law holds on the vendored
geodesic interpolation between arbitrary endpoints, not just a vertical
normalization. -/
theorem geodInterp_sinh_cosh_interpolation (a b x : ℍ) (t : ℝ) :
    Real.sinh (dist a b) *
        Real.cosh (dist x (Vendored.RiemannDynamics.geodInterp a b t)) =
      Real.sinh ((1 - t) * dist a b) * Real.cosh (dist x a) +
        Real.sinh (t * dist a b) * Real.cosh (dist x b) := by
  obtain ⟨γ, hγ⟩ := exists_hyperbolic_vertical_normalization a b
  let a' : ℍ := γ • a
  let b' : ℍ := γ • b
  let x' : ℍ := γ • x
  let u : ℝ := Real.log a'.im
  let v : ℝ := Real.log b'.im
  let p := hyperbolicVerticalSegmentPoint a'.re u v
  have hscale : |v - u| = dist a b := by
    dsimp [u, v, a', b']
    rw [← dist_smul γ a b, UpperHalfPlane.dist_of_re_eq hγ, Real.dist_eq,
      abs_sub_comm]
  have hleft : p 0 = a' := by
    dsimp [p, u, v]
    exact hyperbolicVerticalSegmentPoint_zero a' b'
  have hright : p 1 = b' := by
    dsimp [p, u, v]
    exact hyperbolicVerticalSegmentPoint_one a' b' hγ
  have hpath : Vendored.RiemannDynamics.geodInterp a' b' t = p t := by
    rw [Vendored.RiemannDynamics.geodInterp_vertical
      (show a'.re = b'.re from hγ)]
    apply Vendored.RiemannDynamics.ext_re_im
    · simp [p]
    · simp [p, u, v]
  have hcore :
      Real.sinh (dist a b) * Real.cosh (dist x' (p t)) =
        Real.sinh ((1 - t) * dist a b) * Real.cosh (dist x' a') +
          Real.sinh (t * dist a b) * Real.cosh (dist x' b') := by
    by_cases hδ : 0 ≤ v - u
    · have hdist : v - u = dist a b := by
        simpa only [abs_of_nonneg hδ] using hscale
      have h := hyperbolicVerticalSegmentPoint_sinh_interpolation
        a'.re u v t x'
      simpa only [p, hleft, hright, hdist] using h
    · have hδ' : 0 ≤ u - v := by linarith
      have hdist : u - v = dist a b := by
        have := hscale
        rw [abs_of_neg (by linarith : v - u < 0)] at this
        linarith
      have hreverse :
          hyperbolicVerticalSegmentPoint a'.re v u (1 - t) = p t := by
        apply Vendored.RiemannDynamics.ext_re_im
        · simp [p, hyperbolicVerticalSegmentPoint_re]
        · simp only [hyperbolicVerticalSegmentPoint_im, p]
          congr 1
          dsimp [u, v]
          ring
      have hrev0 : hyperbolicVerticalSegmentPoint a'.re v u 0 = b' := by
        apply Vendored.RiemannDynamics.ext_re_im
        · simpa using hγ
        · simp [hyperbolicVerticalSegmentPoint_im, u, v,
            Real.exp_log b'.im_pos]
      have hrev1 : hyperbolicVerticalSegmentPoint a'.re v u 1 = a' := by
        apply Vendored.RiemannDynamics.ext_re_im
        · simp
        · simp [hyperbolicVerticalSegmentPoint_im, u, v,
            Real.exp_log a'.im_pos]
      have h := hyperbolicVerticalSegmentPoint_sinh_interpolation
        a'.re v u (1 - t) x'
      rw [hreverse, hrev0, hrev1, hdist] at h
      rw [show 1 - (1 - t) = t by ring] at h
      simpa only [add_comm] using h
  have hcore' := hcore
  rw [← hpath] at hcore'
  rw [← geodInterp_smul γ a b t] at hcore'
  simpa only [a', b', x', dist_smul] using hcore'

/-- The geodesic interpolation midpoint in the hyperbolic plane satisfies
the exact midpoint-cosh comparison, obtained from the all-parameter signed
interpolation identity. -/
theorem geodInterp_midpoint_cosh (a b x : ℍ) :
    2 * Real.cosh (dist a b / 2) *
        Real.cosh (dist x (Vendored.RiemannDynamics.geodInterp a b (1 / 2))) =
      Real.cosh (dist x a) + Real.cosh (dist x b) := by
  let d : ℝ := dist a b
  by_cases hd : d = 0
  · have hab : a = b := dist_eq_zero.mp (by simpa [d] using hd)
    subst b
    simp [Vendored.RiemannDynamics.geodInterp_self]
    ring
  · have hdpos : 0 < d := lt_of_le_of_ne (by positivity) (Ne.symm hd)
    have hinterp := geodInterp_sinh_cosh_interpolation a b x (1 / 2)
    have hinterp' :
        Real.sinh d *
            Real.cosh (dist x (Vendored.RiemannDynamics.geodInterp a b (1 / 2))) =
          Real.sinh (d / 2) * (Real.cosh (dist x a) + Real.cosh (dist x b)) := by
      have hleft : (1 - (1 / 2 : ℝ)) * dist a b = d / 2 := by
        dsimp [d]
        ring
      have hright : (1 / 2 : ℝ) * dist a b = d / 2 := by
        dsimp [d]
        ring
      calc
        _ = Real.sinh (d / 2) * Real.cosh (dist x a) +
              Real.sinh (d / 2) * Real.cosh (dist x b) := by
          simpa only [hleft, hright] using hinterp
        _ = Real.sinh (d / 2) *
              (Real.cosh (dist x a) + Real.cosh (dist x b)) := by ring
    have hdouble : Real.sinh d =
        2 * Real.sinh (d / 2) * Real.cosh (d / 2) := by
      calc
        Real.sinh d = Real.sinh (d / 2 + d / 2) := by congr 1; ring
        _ = Real.sinh (d / 2) * Real.cosh (d / 2) +
              Real.cosh (d / 2) * Real.sinh (d / 2) := Real.sinh_add _ _
        _ = 2 * Real.sinh (d / 2) * Real.cosh (d / 2) := by ring
    have hfactor : Real.sinh (d / 2) ≠ 0 :=
      (Real.sinh_pos_iff.mpr (by linarith : 0 < d / 2)).ne'
    apply (mul_left_cancel₀ hfactor)
    calc
      Real.sinh (d / 2) *
          (2 * Real.cosh (d / 2) *
            Real.cosh (dist x (Vendored.RiemannDynamics.geodInterp a b (1 / 2)))) =
        Real.sinh d *
          Real.cosh (dist x (Vendored.RiemannDynamics.geodInterp a b (1 / 2))) := by
            rw [hdouble]
            ring
      _ = Real.sinh (d / 2) *
          (Real.cosh (dist x a) + Real.cosh (dist x b)) := hinterp'

/-- First variation of distance from a fixed point along a hyperbolic
geodesic, at an endpoint distinct from that point. This is the differential
form of the exact cosh interpolation identity. -/
theorem geodInterp_dist_hasDerivAt_zero (a b x : ℍ) (hab : a ≠ b)
    (hxa : x ≠ a) :
    HasDerivAt (fun t : ℝ => dist x (Vendored.RiemannDynamics.geodInterp a b t))
      ((Real.sinh (dist x a))⁻¹ *
        ((-dist a b * Real.cosh (dist a b) * Real.cosh (dist x a) +
          dist a b * Real.cosh (dist x b)) / Real.sinh (dist a b))) 0 := by
  let l : ℝ := dist a b
  let r₀ : ℝ := dist x a
  let r₁ : ℝ := dist x b
  let g : ℝ → ℝ := fun t =>
    (Real.sinh ((1 - t) * l) * Real.cosh r₀ +
      Real.sinh (t * l) * Real.cosh r₁) / Real.sinh l
  have hl : 0 < l := by
    dsimp [l]
    exact dist_pos.mpr hab
  have hl_sinh : Real.sinh l ≠ 0 := (Real.sinh_pos_iff.mpr hl).ne'
  have hr₀ : 0 < r₀ := by
    dsimp [r₀]
    exact dist_pos.mpr hxa
  have hr₀_sinh : Real.sinh r₀ ≠ 0 := (Real.sinh_pos_iff.mpr hr₀).ne'
  have hcosh (t : ℝ) :
      Real.cosh (dist x (Vendored.RiemannDynamics.geodInterp a b t)) = g t := by
    have h := geodInterp_sinh_cosh_interpolation a b x t
    apply (mul_left_cancel₀ hl_sinh)
    calc
      Real.sinh l * Real.cosh
          (dist x (Vendored.RiemannDynamics.geodInterp a b t)) =
          Real.sinh (dist a b) *
            Real.cosh (dist x (Vendored.RiemannDynamics.geodInterp a b t)) := by
              simp [l]
      _ = Real.sinh ((1 - t) * dist a b) * Real.cosh (dist x a) +
            Real.sinh (t * dist a b) * Real.cosh (dist x b) := h
      _ = Real.sinh l * g t := by
        dsimp [g]
        simp only [l, r₀, r₁]
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hl_sinh]
  have hEq :
      (fun t : ℝ => dist x (Vendored.RiemannDynamics.geodInterp a b t)) =
        fun t => Real.arcosh (g t) := by
    funext t
    calc
      dist x (Vendored.RiemannDynamics.geodInterp a b t) =
          Real.arcosh (Real.cosh
            (dist x (Vendored.RiemannDynamics.geodInterp a b t))) :=
        (Real.arcosh_cosh dist_nonneg).symm
      _ = Real.arcosh (g t) := by rw [hcosh]
  have hG₁ : g 0 = Real.cosh r₀ := by
    dsimp [g]
    simp only [zero_mul, sub_zero, one_mul, Real.sinh_zero, zero_mul, add_zero]
    field_simp [hl_sinh]
  have hr₀_nonneg : 0 ≤ r₀ := le_of_lt hr₀
  have hGpos : 1 < g 0 := by
    rw [hG₁]
    exact (Real.one_lt_cosh).2 hr₀.ne'
  have hlin₁ : HasDerivAt (fun t : ℝ => (1 - t) * l) (-l) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_sub 1).mul_const l
  have hlin₂ : HasDerivAt (fun t : ℝ => t * l) l 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const l
  have hs₁ : HasDerivAt (fun t : ℝ => Real.sinh ((1 - t) * l))
      (-l * Real.cosh l) 0 := by
    simpa only [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sinh l).comp_of_eq 0 hlin₁ (by ring)
  have hs₂ : HasDerivAt (fun t : ℝ => Real.sinh (t * l)) l 0 := by
    simpa only [Function.comp_def, Real.cosh_zero, one_mul] using
      (Real.hasDerivAt_sinh 0).comp_of_eq 0 hlin₂ (by ring)
  have hG : HasDerivAt g
      (((-l * Real.cosh l) * Real.cosh r₀ + l * Real.cosh r₁) /
        Real.sinh l) 0 := by
    change HasDerivAt (fun t : ℝ =>
      (Real.sinh ((1 - t) * l) * Real.cosh r₀ +
        Real.sinh (t * l) * Real.cosh r₁) / Real.sinh l) _ 0
    exact ((hs₁.mul_const (Real.cosh r₀)).add
      (hs₂.mul_const (Real.cosh r₁))).div_const (Real.sinh l)
  have hroot : Real.sqrt ((g 0) ^ 2 - 1) = Real.sinh r₀ := by
    rw [← Real.sinh_arcosh (le_of_lt hGpos), hG₁,
      Real.arcosh_cosh hr₀_nonneg]
  have hArcosh := (Real.hasDerivAt_arcosh hGpos).comp 0 hG
  rw [hroot] at hArcosh
  rw [hEq]
  simpa only [Function.comp_def, l, r₀, r₁] using hArcosh

private theorem hasDerivAt_nonneg_of_minimumOn_Icc {F : ℝ → ℝ} {F' : ℝ}
    (hF : HasDerivAt F F' 0)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) 1, F 0 ≤ F t) : 0 ≤ F' := by
  let S : Set ℝ := Set.Icc (0 : ℝ) 1
  have hLocal : IsLocalMinOn F S 0 := by
    change ∀ᶠ t in 𝓝[S] (0 : ℝ), F 0 ≤ F t
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hmin t ht
  have hseg : segment ℝ (0 : ℝ) 1 ⊆ S := by
    rw [segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]
  have htan : (1 : ℝ) ∈ posTangentConeAt S 0 := by
    have h := sub_mem_posTangentConeAt_of_segment_subset hseg
    simpa using h
  have hnonneg := hLocal.fderivWithin_nonneg htan
  have hInterior : (interior S).Nonempty := by
    refine ⟨1 / 2, ?_⟩
    norm_num [S, interior_Icc]
  have hunique : UniqueDiffWithinAt ℝ S 0 :=
    uniqueDiffWithinAt_convex (convex_Icc 0 1) hInterior (by
      apply subset_closure
      simp)
  have hderiv : derivWithin F S 0 = F' := hF.hasDerivWithinAt.derivWithin hunique
  change 0 ≤ (fderivWithin ℝ F S 0 : ℝ →L[ℝ] ℝ) 1 at hnonneg
  rw [fderivWithin_derivWithin, hderiv] at hnonneg
  exact hnonneg

/-- A right-local minimum on a nontrivial interval forces a nonnegative
right derivative. The interval may be shorter than `[0,1]`; this is useful
when a constrained minimizer only permits a short initial part of a direction. -/
private theorem hasDerivAt_nonneg_of_minimumOn_short_Icc
    {F : ℝ → ℝ} {F' δ : ℝ} (hF : HasDerivAt F F' 0)
    (hδ : 0 < δ) (hmin : ∀ t ∈ Set.Icc (0 : ℝ) δ, F 0 ≤ F t) :
    0 ≤ F' := by
  let S : Set ℝ := Set.Icc (0 : ℝ) δ
  have hLocal : IsLocalMinOn F S 0 := by
    change ∀ᶠ t in 𝓝[S] (0 : ℝ), F 0 ≤ F t
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hmin t ht
  have hseg : segment ℝ (0 : ℝ) δ ⊆ S := by
    rw [segment_eq_Icc (le_of_lt hδ)]
  have htan : δ ∈ posTangentConeAt S 0 := by
    have h := sub_mem_posTangentConeAt_of_segment_subset hseg
    simpa using h
  have hInterior : (interior S).Nonempty := by
    refine ⟨δ / 2, ?_⟩
    have hδ2 : 0 < δ / 2 := by positivity
    have hδ2' : δ / 2 < δ := by linarith
    change δ / 2 ∈ interior (Set.Icc (0 : ℝ) δ)
    rw [interior_Icc]
    exact ⟨hδ2, hδ2'⟩
  have hzero : (0 : ℝ) ∈ S := ⟨le_rfl, le_of_lt hδ⟩
  have hunique : UniqueDiffWithinAt ℝ S 0 :=
    uniqueDiffWithinAt_convex (convex_Icc 0 δ) hInterior (subset_closure hzero)
  have hnonneg := hLocal.fderivWithin_nonneg htan
  have hderiv : derivWithin F S 0 = F' :=
    hF.hasDerivWithinAt.derivWithin hunique
  change 0 ≤ (fderivWithin ℝ F S 0 : ℝ →L[ℝ] ℝ) δ at hnonneg
  have hderivδ : (fderivWithin ℝ F S 0 : ℝ →L[ℝ] ℝ) δ = F' * δ := by
    calc
      (fderivWithin ℝ F S 0 : ℝ →L[ℝ] ℝ) δ =
          δ • (fderivWithin ℝ F S 0 : ℝ →L[ℝ] ℝ) 1 := by
            rw [show δ = δ • (1 : ℝ) by simp, map_smul]
            simp
      _ = F' * δ := by
        rw [fderivWithin_derivWithin, hderiv]
        simp [smul_eq_mul]
        ring
  rw [hderivδ] at hnonneg
  have hmul : 0 ≤ F' * δ := hnonneg
  nlinarith

/-- If a pair of hyperbolic distances is minimized at the initial endpoint
of a geodesic segment, their summed first variation in the forward direction
is nonnegative. -/
theorem geodInterp_distance_sum_deriv_nonneg_of_minimizing
    (q w x y : ℍ) (hqw : q ≠ w) (hxq : x ≠ q) (hyq : y ≠ q)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      dist x q + dist y q ≤
        dist x (Vendored.RiemannDynamics.geodInterp q w t) +
          dist y (Vendored.RiemannDynamics.geodInterp q w t)) :
    0 ≤
      ((Real.sinh (dist x q))⁻¹ *
        ((-dist q w * Real.cosh (dist q w) * Real.cosh (dist x q) +
          dist q w * Real.cosh (dist x w)) / Real.sinh (dist q w))) +
      ((Real.sinh (dist y q))⁻¹ *
        ((-dist q w * Real.cosh (dist q w) * Real.cosh (dist y q) +
          dist q w * Real.cosh (dist y w)) / Real.sinh (dist q w))) := by
  let F : ℝ → ℝ := fun t =>
    dist x (Vendored.RiemannDynamics.geodInterp q w t) +
      dist y (Vendored.RiemannDynamics.geodInterp q w t)
  have hx := geodInterp_dist_hasDerivAt_zero q w x hqw hxq
  have hy := geodInterp_dist_hasDerivAt_zero q w y hqw hyq
  have hF : HasDerivAt F
      (((Real.sinh (dist x q))⁻¹ *
          ((-dist q w * Real.cosh (dist q w) * Real.cosh (dist x q) +
            dist q w * Real.cosh (dist x w)) / Real.sinh (dist q w))) +
        ((Real.sinh (dist y q))⁻¹ *
          ((-dist q w * Real.cosh (dist q w) * Real.cosh (dist y q) +
            dist q w * Real.cosh (dist y w)) / Real.sinh (dist q w)))) 0 := by
    change HasDerivAt
      (fun t : ℝ => dist x (Vendored.RiemannDynamics.geodInterp q w t) +
        dist y (Vendored.RiemannDynamics.geodInterp q w t)) _ 0
    exact hx.add hy
  have hminF : ∀ t ∈ Set.Icc (0 : ℝ) 1, F 0 ≤ F t := by
    intro t ht
    simpa only [F, Vendored.RiemannDynamics.geodInterp_zero] using hmin t ht
  have hnonneg := hasDerivAt_nonneg_of_minimumOn_Icc hF hminF
  simpa only [F, Vendored.RiemannDynamics.geodInterp_zero] using hnonneg

/-- Forward directional derivative of distance at the initial point of a
hyperbolic interpolation. At the base point itself, use the right derivative
`dist q w`; away from it, use the ordinary derivative formula above. -/
noncomputable def geodInterpDistanceForwardDerivative (q w x : ℍ) : ℝ := by
  classical
  exact if x = q then dist q w else
    (Real.sinh (dist x q))⁻¹ *
      ((-dist q w * Real.cosh (dist q w) * Real.cosh (dist x q) +
        dist q w * Real.cosh (dist x w)) / Real.sinh (dist q w))

/-- If the sum of two distances is minimized at the initial point of a
geodesic interval, the sum of its forward directional derivatives is
nonnegative. This includes the coincident-endpoint cases, where distance has
only a right derivative. -/
theorem geodInterp_distance_forward_derivative_sum_nonneg_of_minimizing
    (q w x y : ℍ)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      dist x q + dist y q ≤
      dist x (Vendored.RiemannDynamics.geodInterp q w t) +
          dist y (Vendored.RiemannDynamics.geodInterp q w t)) :
    0 ≤ geodInterpDistanceForwardDerivative q w x +
      geodInterpDistanceForwardDerivative q w y := by
  classical
  by_cases hqw : q = w
  · subst w
    simp [geodInterpDistanceForwardDerivative]
  · by_cases hx : x = q
    · subst x
      by_cases hy : y = q
      · subst y
        simp [geodInterpDistanceForwardDerivative]
      · have hyderiv := geodInterp_dist_hasDerivAt_zero q w y hqw hy
        have hlinear : HasDerivAt (fun t : ℝ => t * dist q w) (dist q w) 0 := by
          simpa using (hasDerivAt_id 0).mul_const (dist q w)
        let F : ℝ → ℝ := fun t => t * dist q w +
          dist y (Vendored.RiemannDynamics.geodInterp q w t)
        have hF := hlinear.add hyderiv
        change HasDerivAt F _ 0 at hF
        have hminF : ∀ t ∈ Set.Icc (0 : ℝ) 1, F 0 ≤ F t := by
          intro t ht
          have hqt : dist q (Vendored.RiemannDynamics.geodInterp q w t) =
              t * dist q w := Vendored.RiemannDynamics.dist_geodInterp_left q w ht
          simpa [F, Vendored.RiemannDynamics.geodInterp_zero, hqt] using hmin t ht
        have hnonneg := hasDerivAt_nonneg_of_minimumOn_Icc hF hminF
        simpa [geodInterpDistanceForwardDerivative, hy] using hnonneg
    · by_cases hy : y = q
      · subst y
        have hxderiv := geodInterp_dist_hasDerivAt_zero q w x hqw hx
        have hlinear : HasDerivAt (fun t : ℝ => t * dist q w) (dist q w) 0 := by
          simpa using (hasDerivAt_id 0).mul_const (dist q w)
        let F : ℝ → ℝ := fun t =>
          dist x (Vendored.RiemannDynamics.geodInterp q w t) + t * dist q w
        have hF := hxderiv.add hlinear
        change HasDerivAt F _ 0 at hF
        have hminF : ∀ t ∈ Set.Icc (0 : ℝ) 1, F 0 ≤ F t := by
          intro t ht
          have hqt : dist q (Vendored.RiemannDynamics.geodInterp q w t) =
              t * dist q w := Vendored.RiemannDynamics.dist_geodInterp_left q w ht
          simpa [F, Vendored.RiemannDynamics.geodInterp_zero, hqt] using hmin t ht
        have hnonneg := hasDerivAt_nonneg_of_minimumOn_Icc hF hminF
        simpa [geodInterpDistanceForwardDerivative, hx] using hnonneg
      · simpa [geodInterpDistanceForwardDerivative, hx, hy] using
        geodInterp_distance_sum_deriv_nonneg_of_minimizing
            q w x y hqw hx hy hmin

/-- The same first-variation conclusion holds when the sum of distances is
known to be minimized only on a short initial subsegment. -/
theorem geodInterp_distance_forward_derivative_sum_nonneg_of_local_minimizing
    (q w x y : ℍ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) δ,
      dist x q + dist y q ≤
        dist x (Vendored.RiemannDynamics.geodInterp q w t) +
          dist y (Vendored.RiemannDynamics.geodInterp q w t)) :
    0 ≤ geodInterpDistanceForwardDerivative q w x +
      geodInterpDistanceForwardDerivative q w y := by
  classical
  by_cases hqw : q = w
  · subst w
    simp [geodInterpDistanceForwardDerivative]
  · by_cases hx : x = q
    · subst x
      by_cases hy : y = q
      · subst y
        simp [geodInterpDistanceForwardDerivative]
      · have hyderiv := geodInterp_dist_hasDerivAt_zero q w y hqw hy
        have hlinear : HasDerivAt (fun t : ℝ => t * dist q w) (dist q w) 0 := by
          simpa using (hasDerivAt_id 0).mul_const (dist q w)
        let F : ℝ → ℝ := fun t => t * dist q w +
          dist y (Vendored.RiemannDynamics.geodInterp q w t)
        have hF := hlinear.add hyderiv
        change HasDerivAt F _ 0 at hF
        have hminF : ∀ t ∈ Set.Icc (0 : ℝ) δ, F 0 ≤ F t := by
          intro t ht
          have ht1 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hδ1⟩
          have hqt := Vendored.RiemannDynamics.dist_geodInterp_left q w ht1
          simpa [F, Vendored.RiemannDynamics.geodInterp_zero, hqt] using hmin t ht
        have hnonneg := hasDerivAt_nonneg_of_minimumOn_short_Icc hF hδ hminF
        simpa [geodInterpDistanceForwardDerivative, hy] using hnonneg
    · by_cases hy : y = q
      · subst y
        have hxderiv := geodInterp_dist_hasDerivAt_zero q w x hqw hx
        have hlinear : HasDerivAt (fun t : ℝ => t * dist q w) (dist q w) 0 := by
          simpa using (hasDerivAt_id 0).mul_const (dist q w)
        let F : ℝ → ℝ := fun t =>
          dist x (Vendored.RiemannDynamics.geodInterp q w t) + t * dist q w
        have hF := hxderiv.add hlinear
        change HasDerivAt F _ 0 at hF
        have hminF : ∀ t ∈ Set.Icc (0 : ℝ) δ, F 0 ≤ F t := by
          intro t ht
          have ht1 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hδ1⟩
          have hqt := Vendored.RiemannDynamics.dist_geodInterp_left q w ht1
          simpa [F, Vendored.RiemannDynamics.geodInterp_zero, hqt] using hmin t ht
        have hnonneg := hasDerivAt_nonneg_of_minimumOn_short_Icc hF hδ hminF
        simpa [geodInterpDistanceForwardDerivative, hx] using hnonneg
      · let F : ℝ → ℝ := fun t =>
          dist x (Vendored.RiemannDynamics.geodInterp q w t) +
            dist y (Vendored.RiemannDynamics.geodInterp q w t)
        have hxderiv := geodInterp_dist_hasDerivAt_zero q w x hqw hx
        have hyderiv := geodInterp_dist_hasDerivAt_zero q w y hqw hy
        have hF : HasDerivAt F
            (((Real.sinh (dist x q))⁻¹ *
                ((-dist q w * Real.cosh (dist q w) * Real.cosh (dist x q) +
                  dist q w * Real.cosh (dist x w)) / Real.sinh (dist q w))) +
              ((Real.sinh (dist y q))⁻¹ *
                ((-dist q w * Real.cosh (dist q w) * Real.cosh (dist y q) +
                  dist q w * Real.cosh (dist y w)) / Real.sinh (dist q w)))) 0 := by
          change HasDerivAt
            (fun t : ℝ =>
              dist x (Vendored.RiemannDynamics.geodInterp q w t) +
                dist y (Vendored.RiemannDynamics.geodInterp q w t)) _ 0
          exact hxderiv.add hyderiv
        have hminF : ∀ t ∈ Set.Icc (0 : ℝ) δ, F 0 ≤ F t := by
          intro t ht
          simpa only [F, Vendored.RiemannDynamics.geodInterp_zero] using hmin t ht
        have hnonneg := hasDerivAt_nonneg_of_minimumOn_short_Icc hF hδ hminF
        simpa [F, Vendored.RiemannDynamics.geodInterp_zero,
          geodInterpDistanceForwardDerivative, hx, hy] using hnonneg

/-- The first-variation condition at the bend of a broken hyperbolic
geodesic implies the midpoint-cosh comparison against any third point. The
midpoint is taken on the longer leg. This is the analytic hinge estimate used
to prove the opposite-copy CAT midpoint inequality for the finite gluing. -/
theorem exists_hyperbolic_broken_geodesic_midpoint_cosh_le
    (q x y z : ℍ) (hqx : q ≠ x) (hqy : q ≠ y) (hqz : q ≠ z)
    (hba : dist q y ≤ dist q x)
    (hvariation : 0 ≤ geodInterpDistanceForwardDerivative q z x +
      geodInterpDistanceForwardDerivative q z y) :
    ∃ m : ℍ,
      m ∈ Vendored.RiemannDynamics.geodSeg x q ∧
        (dist x m = (dist q x + dist q y) / 2 ∧
          (dist m q = (dist q x - dist q y) / 2 ∧
            2 * Real.cosh ((dist q x + dist q y) / 2) *
                Real.cosh (dist z m) ≤
              Real.cosh (dist z x) + Real.cosh (dist z y))) := by
  let a : ℝ := dist q x
  let b : ℝ := dist q y
  let c : ℝ := dist q z
  let A : ℝ := Real.cosh (dist z x)
  let B : ℝ := Real.cosh (dist z y)
  have ha : 0 < a := by
    dsimp [a]
    exact dist_pos.mpr hqx
  have hb : 0 < b := by
    dsimp [b]
    exact dist_pos.mpr hqy
  have hc : 0 < c := by
    dsimp [c]
    exact dist_pos.mpr hqz
  have has : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  have hbs : 0 < Real.sinh b := Real.sinh_pos_iff.mpr hb
  have hcs : 0 < Real.sinh c := Real.sinh_pos_iff.mpr hc
  have hdx : geodInterpDistanceForwardDerivative q z x =
      (c / Real.sinh c) *
        ((A - Real.cosh c * Real.cosh a) / Real.sinh a) := by
    simp [geodInterpDistanceForwardDerivative, a, c, A,
      Ne.symm hqx, dist_comm]
    ring
  have hdy : geodInterpDistanceForwardDerivative q z y =
      (c / Real.sinh c) *
        ((B - Real.cosh c * Real.cosh b) / Real.sinh b) := by
    simp [geodInterpDistanceForwardDerivative, b, c, B,
      Ne.symm hqy, dist_comm]
    ring
  have hnormalized : 0 ≤
      (A - Real.cosh c * Real.cosh a) / Real.sinh a +
        (B - Real.cosh c * Real.cosh b) / Real.sinh b := by
    have hscaled : 0 ≤ (c / Real.sinh c) *
        ((A - Real.cosh c * Real.cosh a) / Real.sinh a +
          (B - Real.cosh c * Real.cosh b) / Real.sinh b) := by
      simpa [hdx, hdy, mul_add] using hvariation
    have hfactor : 0 < c / Real.sinh c := div_pos hc hcs
    by_contra hnot
    have hneg :
        (A - Real.cosh c * Real.cosh a) / Real.sinh a +
          (B - Real.cosh c * Real.cosh b) / Real.sinh b < 0 := lt_of_not_ge hnot
    have := mul_neg_of_pos_of_neg hfactor hneg
    linarith
  have hnum : 0 ≤ Real.sinh b * A + Real.sinh a * B -
      Real.sinh (a + b) * Real.cosh c := by
    have hmul : 0 ≤ Real.sinh a * Real.sinh b *
        ((A - Real.cosh c * Real.cosh a) / Real.sinh a +
          (B - Real.cosh c * Real.cosh b) / Real.sinh b) :=
      mul_nonneg (mul_nonneg has.le hbs.le) hnormalized
    have hidentity : Real.sinh b * A + Real.sinh a * B -
        Real.sinh (a + b) * Real.cosh c =
      Real.sinh a * Real.sinh b *
        ((A - Real.cosh c * Real.cosh a) / Real.sinh a +
          (B - Real.cosh c * Real.cosh b) / Real.sinh b) := by
      field_simp [ne_of_gt has, ne_of_gt hbs]
      rw [Real.sinh_add]
      ring
    rw [hidentity]
    exact hmul
  let t : ℝ := (a + b) / (2 * a)
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [t]
      positivity
    · dsimp [t]
      apply (div_le_one (by positivity)).2
      dsimp [a, b] at hba ⊢
      nlinarith
  let m : ℍ := Vendored.RiemannDynamics.geodInterp x q t
  have hxm : dist x m = (a + b) / 2 := by
    dsimp [m]
    rw [Vendored.RiemannDynamics.dist_geodInterp_left x q ht]
    rw [dist_comm x q]
    dsimp [t, a]
    field_simp [hqx]
  have hinterp := geodInterp_sinh_cosh_interpolation x q z t
  have hta : t * a = (a + b) / 2 := by
    dsimp [t]
    field_simp
  have hone_ta : (1 - t) * a = (a - b) / 2 := by
    dsimp [t]
    field_simp
    ring
  have hmq : dist m q = (a - b) / 2 := by
    dsimp [m]
    rw [Vendored.RiemannDynamics.dist_geodInterp_right_abs x q t,
      abs_of_nonneg (by linarith [ht.2])]
    rw [dist_comm x q]
    simpa [t, a] using hone_ta
  have hinterp' : Real.sinh a * Real.cosh (dist z m) =
      Real.sinh ((a - b) / 2) * A +
        Real.sinh ((a + b) / 2) * Real.cosh c := by
    change Real.sinh a *
        Real.cosh (dist z (Vendored.RiemannDynamics.geodInterp x q t)) = _
    have hxa : dist x q = a := by simp [a, dist_comm]
    have hqz' : dist z q = c := by simp [c, dist_comm]
    rw [hxa, hqz'] at hinterp
    rw [hone_ta, hta] at hinterp
    simpa [A] using hinterp
  have hsum_sinh : Real.sinh a - Real.sinh b =
      2 * Real.cosh ((a + b) / 2) * Real.sinh ((a - b) / 2) := by
    let p : ℝ := (a + b) / 2
    let r : ℝ := (a - b) / 2
    have ha' : a = p + r := by dsimp [p, r]; ring
    have hb' : b = p - r := by dsimp [p, r]; ring
    calc
      Real.sinh a - Real.sinh b = Real.sinh (p + r) - Real.sinh (p - r) := by
        rw [← ha', ← hb']
      _ = 2 * Real.cosh p * Real.sinh r := by
        rw [Real.sinh_add, show p - r = p + -r by ring,
          Real.sinh_add, Real.sinh_neg, Real.cosh_neg]
        ring
      _ = 2 * Real.cosh ((a + b) / 2) * Real.sinh ((a - b) / 2) := by
        simp [p, r]
  have hdouble_sinh : 2 * Real.cosh ((a + b) / 2) *
      Real.sinh ((a + b) / 2) = Real.sinh (a + b) := by
    rw [show a + b = (a + b) / 2 + (a + b) / 2 by ring,
      Real.sinh_add]
    ring_nf
  have htarget_scaled : 0 ≤ Real.sinh a *
      (A + B - 2 * Real.cosh ((a + b) / 2) * Real.cosh (dist z m)) := by
    calc
      _ = Real.sinh a * A + Real.sinh a * B -
          2 * Real.cosh ((a + b) / 2) *
            (Real.sinh a * Real.cosh (dist z m)) := by ring
      _ = Real.sinh a * A + Real.sinh a * B -
          2 * Real.cosh ((a + b) / 2) *
            (Real.sinh ((a - b) / 2) * A +
              Real.sinh ((a + b) / 2) * Real.cosh c) := by rw [hinterp']
      _ = Real.sinh b * A + Real.sinh a * B -
          Real.sinh (a + b) * Real.cosh c := by
        calc
          _ = (Real.sinh a -
                2 * Real.cosh ((a + b) / 2) *
                  Real.sinh ((a - b) / 2)) * A +
                Real.sinh a * B -
                  (2 * Real.cosh ((a + b) / 2) *
                    Real.sinh ((a + b) / 2)) * Real.cosh c := by ring
          _ = (Real.sinh a - (Real.sinh a - Real.sinh b)) * A +
                Real.sinh a * B - Real.sinh (a + b) * Real.cosh c := by
            rw [← hsum_sinh, hdouble_sinh]
          _ = _ := by ring
      _ ≥ 0 := hnum
  have htarget : 0 ≤ A + B -
      2 * Real.cosh ((a + b) / 2) * Real.cosh (dist z m) := by
    by_contra hnot
    have hneg : A + B -
        2 * Real.cosh ((a + b) / 2) * Real.cosh (dist z m) < 0 :=
      lt_of_not_ge hnot
    have := mul_neg_of_pos_of_neg has hneg
    linarith
  have hmseg := Vendored.RiemannDynamics.geodInterp_mem_geodSeg x q ht
  have hxm' : dist x m = (dist q x + dist q y) / 2 := by
    simpa [a, b] using hxm
  have hmq' : dist m q = (dist q x - dist q y) / 2 := by
    simpa [a, b] using hmq
  have hcompare' :
      2 * Real.cosh ((dist q x + dist q y) / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y) := by
    dsimp [A, B] at htarget ⊢
    linarith
  exact ⟨m, hmseg, ⟨hxm', ⟨hmq', hcompare'⟩⟩⟩

/-- The exponential-height vertical midpoint satisfies the hyperbolic
comparison identity for every actual upper-half-plane point. -/
theorem hyperbolicVerticalSegmentPoint_midpoint_cosh (a u v : ℝ) (x : ℍ) :
    2 * Real.cosh (|v - u| / 2) *
        Real.cosh (dist x (hyperbolicVerticalSegmentPoint a u v (1 / 2))) =
      Real.cosh (dist x (hyperbolicVerticalSegmentPoint a u v 0)) +
        Real.cosh (dist x (hyperbolicVerticalSegmentPoint a u v 1)) := by
  rw [hyperbolicVerticalSegmentPoint_cosh_dist,
    hyperbolicVerticalSegmentPoint_cosh_dist,
    hyperbolicVerticalSegmentPoint_cosh_dist]
  have hmid : (1 - (1 / 2 : ℝ)) * u + (1 / 2 : ℝ) * v = (u + v) / 2 := by ring
  rw [hmid]
  simp only [sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add]
  exact exp_midpoint_cosh_identity u v ((x.re - a) ^ 2 + x.im ^ 2) x.im x.im_pos.ne'

/-- A genuine hyperbolic midpoint exists and satisfies the universal cosh
identity. No noncoincidence or assumed comparison-curvature predicate is used. -/
theorem exists_hyperbolic_midpoint_cosh (y z : ℍ) :
    ∃ m : ℍ, dist y m = dist y z / 2 ∧ dist m z = dist y z / 2 ∧
      ∀ x : ℍ, 2 * Real.cosh (dist y z / 2) * Real.cosh (dist x m) =
        Real.cosh (dist x y) + Real.cosh (dist x z) := by
  obtain ⟨γ, hγ⟩ := exists_hyperbolic_vertical_normalization y z
  let y' : ℍ := γ • y
  let z' : ℍ := γ • z
  let p := hyperbolicVerticalSegmentPoint y'.re (Real.log y'.im) (Real.log z'.im)
  let m : ℍ := γ⁻¹ • p (1 / 2)
  have h0 : p 0 = y' := hyperbolicVerticalSegmentPoint_zero y' z'
  have h1 : p 1 = z' := hyperbolicVerticalSegmentPoint_one y' z' hγ
  have hscale : |Real.log z'.im - Real.log y'.im| = dist y z := by
    rw [← dist_smul γ y z, UpperHalfPlane.dist_of_re_eq hγ, Real.dist_eq,
      abs_sub_comm]
  have hm : (γ • m : ℍ) = p (1 / 2) := by simp only [m, smul_inv_smul]
  refine ⟨m, ?_, ?_, ?_⟩
  · rw [← dist_smul γ y m, hm]
    change dist y' (p (1 / 2)) = dist y z / 2
    rw [← h0, hyperbolicVerticalSegmentPoint_dist, hscale]
    norm_num
    ring
  · rw [← dist_smul γ m z, hm]
    change dist (p (1 / 2)) z' = dist y z / 2
    rw [← h1, hyperbolicVerticalSegmentPoint_dist, hscale]
    norm_num
    ring
  · intro x
    have h := hyperbolicVerticalSegmentPoint_midpoint_cosh y'.re
      (Real.log y'.im) (Real.log z'.im) (γ • x)
    change 2 * Real.cosh (|Real.log z'.im - Real.log y'.im| / 2) *
        Real.cosh (dist (γ • x) (p (1 / 2))) =
      Real.cosh (dist (γ • x) (p 0)) + Real.cosh (dist (γ • x) (p 1)) at h
    rw [hscale, h0, h1] at h
    rw [← hm, dist_smul] at h
    simpa only [y', z', dist_smul] using h

/-- The same exact identity holds for every genuine metric midpoint, not
merely for the midpoint selected by vertical normalization. -/
theorem hyperbolic_midpoint_cosh {y z m : ℍ}
    (hym : dist y m = dist y z / 2) (hmz : dist m z = dist y z / 2) (x : ℍ) :
    2 * Real.cosh (dist y z / 2) * Real.cosh (dist x m) =
      Real.cosh (dist x y) + Real.cosh (dist x z) := by
  obtain ⟨p, _, _, hp⟩ := exists_hyperbolic_midpoint_cosh y z
  have h := hp m
  rw [dist_comm m y, hym, hmz] at h
  have hc : Real.cosh (dist m p) = Real.cosh 0 := by
    rw [Real.cosh_zero]
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
      (Real.cosh_pos (dist y z / 2)).ne')
    calc
      (2 * Real.cosh (dist y z / 2)) * Real.cosh (dist m p) =
          Real.cosh (dist y z / 2) + Real.cosh (dist y z / 2) := h
      _ = (2 * Real.cosh (dist y z / 2)) * 1 := by ring
  have hmp : m = p := dist_eq_zero.mp
    (Real.cosh_injOn (show dist m p ∈ Set.Ici 0 from dist_nonneg)
      (by simp) hc)
  simpa only [hmp] using hp x

/-- Genuine hyperbolic metric midpoints are unique, including for zero-length
segments. -/
theorem hyperbolic_midpoint_unique {y z m n : ℍ}
    (hym : dist y m = dist y z / 2) (hmz : dist m z = dist y z / 2)
    (hyn : dist y n = dist y z / 2) (hnz : dist n z = dist y z / 2) : m = n := by
  have h := hyperbolic_midpoint_cosh hyn hnz m
  rw [dist_comm m y, hym, hmz] at h
  have hc : Real.cosh (dist m n) = Real.cosh 0 := by
    rw [Real.cosh_zero]
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
      (Real.cosh_pos (dist y z / 2)).ne')
    calc
      (2 * Real.cosh (dist y z / 2)) * Real.cosh (dist m n) =
          Real.cosh (dist y z / 2) + Real.cosh (dist y z / 2) := h
      _ = (2 * Real.cosh (dist y z / 2)) * 1 := by ring
  exact dist_eq_zero.mp
    (Real.cosh_injOn (show dist m n ∈ Set.Ici 0 from dist_nonneg)
      (by simp) hc)

/-- Any geodesically convex subset of the hyperbolic plane inherits the exact
midpoint-cosh comparison. The midpoint is the ambient constant-speed
interpolation at time `1/2`; convexity is used only to place it in the
subtype. -/
theorem exists_subtype_hyperbolic_midpoint_cosh {S : Set ℍ}
    (hS : ∀ a ∈ S, ∀ b ∈ S,
      Vendored.RiemannDynamics.geodSeg a b ⊆ S) (a b : S) :
    ∃ m : S, dist a m = dist a b / 2 ∧ dist m b = dist a b / 2 ∧
      ∀ x : S, 2 * Real.cosh (dist a b / 2) * Real.cosh (dist x m) =
        Real.cosh (dist x a) + Real.cosh (dist x b) := by
  let p : ℍ := Vendored.RiemannDynamics.geodInterp a.1 b.1 (1 / 2)
  have hhalf : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hp : p ∈ S := hS a.1 a.2 b.1 b.2
    (Vendored.RiemannDynamics.geodInterp_mem_geodSeg a.1 b.1 hhalf)
  refine ⟨⟨p, hp⟩, ?_, ?_, ?_⟩
  · change dist a.1 p = dist a.1 b.1 / 2
    rw [Vendored.RiemannDynamics.dist_geodInterp_left a.1 b.1 hhalf]
    ring
  · change dist p b.1 = dist a.1 b.1 / 2
    rw [Vendored.RiemannDynamics.dist_geodInterp_right_abs a.1 b.1 (1 / 2)]
    ring
  · intro x
    change 2 * Real.cosh (dist a.1 b.1 / 2) * Real.cosh (dist x.1 p) =
      Real.cosh (dist x.1 a.1) + Real.cosh (dist x.1 b.1)
    simpa [p] using geodInterp_midpoint_cosh a.1 b.1 x.1

/-- A continuous function obeying a positive-scale local cosh midpoint
inequality lies below the exact sinh interpolation of its endpoint values.
Only one symmetric comparison interval at each interior point is needed. -/
theorem sinh_interpolation_le_of_local_midpoint
    {D : ℝ} (hD : 0 < D) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Icc 0 1))
    (hlocal : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ h : ℝ, 0 < h ∧
      t - h ∈ Icc 0 1 ∧ t + h ∈ Icc 0 1 ∧
      2 * Real.cosh (D * h) * F t ≤ F (t - h) + F (t + h)) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      Real.sinh D * F t ≤
        Real.sinh ((1 - t) * D) * F 0 + Real.sinh (t * D) * F 1 := by
  have hden : 0 < Real.sinh D := Real.sinh_pos_iff.mpr hD
  let H : ℝ → ℝ := fun t =>
    (Real.sinh ((1 - t) * D) * F 0 + Real.sinh (t * D) * F 1) / Real.sinh D
  have hH : Continuous H := by
    dsimp [H]
    fun_prop
  have hH0 : H 0 = F 0 := by simp [H, hden.ne']
  have hH1 : H 1 = F 1 := by simp [H, hden.ne']
  have hHeq (t h : ℝ) :
      2 * Real.cosh (D * h) * H t = H (t - h) + H (t + h) := by
    have ha : (1 - (t - h)) * D = (1 - t) * D + D * h := by ring
    have hb : (1 - (t + h)) * D = (1 - t) * D - D * h := by ring
    have hc : (t - h) * D = t * D - D * h := by ring
    have hd : (t + h) * D = t * D + D * h := by ring
    dsimp [H]
    rw [ha, hb, hc, hd]
    simp only [Real.sinh_add, Real.sinh_sub]
    ring
  let G : ℝ → ℝ := fun t => F t - H t
  have hG : ContinuousOn G (Icc 0 1) := hF.sub hH.continuousOn
  have hG0 : G 0 = 0 := by simp [G, hH0]
  have hG1 : G 1 = 0 := by simp [G, hH1]
  have hGle : ∀ t ∈ Icc (0 : ℝ) 1, G t ≤ 0 := by
    by_contra! h
    obtain ⟨t, ht, htpos⟩ := h
    obtain ⟨u, hu, hmax⟩ :=
      isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num)) hG
    have hup : 0 < G u := lt_of_lt_of_le htpos (hmax ht)
    have hu0 : 0 < u := by
      by_contra h
      have : u = 0 := le_antisymm (le_of_not_gt h) hu.1
      simp [this, hG0] at hup
    have hu1 : u < 1 := by
      by_contra h
      have : u = 1 := le_antisymm hu.2 (le_of_not_gt h)
      simp [this, hG1] at hup
    obtain ⟨h, hh, hminus, hplus, hmid⟩ := hlocal u ⟨hu0, hu1⟩
    have hmidG : 2 * Real.cosh (D * h) * G u ≤ G (u - h) + G (u + h) := by
      dsimp [G]
      nlinarith only [hmid, hHeq u h]
    have hcosh : 1 < Real.cosh (D * h) :=
      Real.one_lt_cosh.mpr (mul_pos hD hh).ne'
    have hm : G (u - h) ≤ G u := hmax hminus
    have hp : G (u + h) ≤ G u := hmax hplus
    nlinarith only [hmidG, hcosh, hup, hm, hp]
  intro t ht
  have hle : F t ≤ H t := sub_nonpos.mp (hGle t ht)
  have := mul_le_mul_of_nonneg_left hle hden.le
  simpa [H, hden.ne', mul_div_cancel₀] using this

#print axioms sinh_interpolation_le_of_local_midpoint

/-- The local-to-global comparison specialized to the actual midpoint. -/
theorem cosh_midpoint_le_of_local_midpoint
    {D : ℝ} (hD : 0 < D) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Icc 0 1))
    (hlocal : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ h : ℝ, 0 < h ∧
      t - h ∈ Icc 0 1 ∧ t + h ∈ Icc 0 1 ∧
      2 * Real.cosh (D * h) * F t ≤ F (t - h) + F (t + h)) :
    2 * Real.cosh (D / 2) * F (1 / 2) ≤ F 0 + F 1 := by
  have h := sinh_interpolation_le_of_local_midpoint hD F hF hlocal
    (1 / 2) (by constructor <;> norm_num)
  have hden : 0 < Real.sinh (D / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have hdouble : Real.sinh D = 2 * Real.sinh (D / 2) * Real.cosh (D / 2) := by
    conv_lhs => rw [show D = D / 2 + D / 2 by ring]
    rw [Real.sinh_add]
    ring
  have hfirst : (1 - (1 / 2 : ℝ)) * D = D / 2 := by ring
  have hsecond : (1 / 2 : ℝ) * D = D / 2 := by ring
  rw [hdouble, hfirst, hsecond] at h
  apply le_of_mul_le_mul_left (a := Real.sinh (D / 2)) _ hden
  nlinarith only [h]

#print axioms cosh_midpoint_le_of_local_midpoint

#print axioms hyperbolicVerticalSegmentPoint_cosh_dist
#print axioms hyperbolicVerticalSegmentPoint_sinh_interpolation
#print axioms geodInterp_sinh_cosh_interpolation
#print axioms geodInterp_midpoint_cosh
#print axioms geodInterp_dist_hasDerivAt_zero
#print axioms geodInterp_distance_sum_deriv_nonneg_of_minimizing
#print axioms geodInterpDistanceForwardDerivative
#print axioms geodInterp_distance_forward_derivative_sum_nonneg_of_minimizing
#print axioms geodInterp_distance_forward_derivative_sum_nonneg_of_local_minimizing
#print axioms exists_hyperbolic_broken_geodesic_midpoint_cosh_le
#print axioms hyperbolicVerticalSegmentPoint_midpoint_cosh
#print axioms exists_hyperbolic_midpoint_cosh
#print axioms hyperbolic_midpoint_cosh
#print axioms hyperbolic_midpoint_unique
#print axioms exists_subtype_hyperbolic_midpoint_cosh

end SystolicGrowth

module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.HyperbolicConeArea

@[expose] public section

/-!
# Hyperbolic comparison for nonunit-speed scalar Jacobi fields

An exponential differential along the geodesic with initial velocity `rU`
uses the time interval `[0,1]`, radial speed `r`, and angular initial
velocity `rN`. Rescaling a scalar Jacobi solution with curvature at most
`-r²` and initial derivative `r` gives the angular comparison `sinh(r t)`.
All endpoint derivatives are derived within the original finite interval;
no extension or positivity premise is needed.
-/

open Set

namespace SystolicGrowth

noncomputable section

/-- **Math.** Hyperbolic comparison needs only continuous initial data and
the differential inequality on the open interval. In particular, the norm
of a Jacobi field may vanish at the initial point without having a second
derivative there. -/
theorem sinh_le_of_second_deriv_ge_mul_self_on_Icc
    {f v : ℝ → ℝ} {b speed : ℝ}
    (hfc : ContinuousOn f (Icc 0 b)) (hvc : ContinuousOn v (Icc 0 b))
    (hf : ∀ x ∈ Ioo 0 b, HasDerivAt f (v x) x)
    (hv : ∀ x ∈ Ioo 0 b, ∃ a, HasDerivAt v a x ∧ speed ^ 2 * f x ≤ a)
    (hf0 : f 0 = 0) (hv0 : v 0 = speed)
    {t : ℝ} (ht : t ∈ Icc 0 b) : Real.sinh (speed * t) ≤ f t := by
  let G : ℝ → ℝ := fun x => f x - Real.sinh (speed * x)
  let D : ℝ → ℝ := fun x => v x - speed * Real.cosh (speed * x)
  let H : ℝ → ℝ := fun x => Real.exp (-(speed * x)) * (D x + speed * G x)
  let K : ℝ → ℝ := fun x => Real.exp (speed * x) * G x
  have hlin (x : ℝ) : HasDerivAt (fun y => speed * y) speed x := by
    simpa using (hasDerivAt_id x).const_mul speed
  have hsinh (x : ℝ) : HasDerivAt (fun y => Real.sinh (speed * y))
      (speed * Real.cosh (speed * x)) x := by
    simpa only [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sinh (speed * x)).comp x (hlin x)
  have hcosh (x : ℝ) : HasDerivAt (fun y => speed * Real.cosh (speed * y))
      (speed ^ 2 * Real.sinh (speed * x)) x := by
    exact (((Real.hasDerivAt_cosh (speed * x)).comp x (hlin x)).const_mul speed).congr_deriv
      (by ring)
  have hG (x : ℝ) (hx : x ∈ Ioo 0 b) : HasDerivAt G (D x) x :=
    (hf x hx).sub (hsinh x)
  have hH (x : ℝ) (hx : x ∈ Ioo 0 b) :
      ∃ a, HasDerivAt H a x ∧ 0 ≤ a := by
    obtain ⟨a, ha, hbound⟩ := hv x hx
    have hexp : HasDerivAt (fun y => Real.exp (-(speed * y)))
        (-speed * Real.exp (-(speed * x))) x := by
      simpa only [Function.comp_def, Pi.neg_apply, mul_comm] using
        (Real.hasDerivAt_exp (-(speed * x))).comp x (hlin x).neg
    refine ⟨Real.exp (-(speed * x)) * (a - speed ^ 2 * f x), ?_,
      mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hbound)⟩
    exact (hexp.mul ((ha.sub (hcosh x)).add ((hG x hx).const_mul speed))).congr_deriv
      (by
        change (-speed * Real.exp (-(speed * x))) * (D x + speed * G x) +
          Real.exp (-(speed * x)) *
            ((a - speed ^ 2 * Real.sinh (speed * x)) + speed * D x) = _
        dsimp [D, G]
        ring)
  have hGc : ContinuousOn G (Icc 0 b) :=
    hfc.sub ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).continuousOn)
  have hDc : ContinuousOn D (Icc 0 b) :=
    hvc.sub ((continuous_const.mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).continuousOn)
  have hHc : ContinuousOn H (Icc 0 b) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn.mul
      (hDc.add (continuousOn_const.mul hGc))
  have hmono : MonotoneOn H (Icc 0 b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 b) hHc
    · intro x hx
      obtain ⟨a, ha, _⟩ := hH x (by simpa only [interior_Icc] using hx)
      exact ha.differentiableAt.differentiableWithinAt
    · intro x hx
      obtain ⟨a, ha, hnonneg⟩ := hH x (by simpa only [interior_Icc] using hx)
      rwa [ha.deriv]
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hH0 : H 0 = 0 := by simp [H, D, G, hf0, hv0]
  have hsum (x : ℝ) (hx : x ∈ Icc 0 b) : 0 ≤ D x + speed * G x := by
    have h := hmono h0 hx hx.1
    rw [hH0] at h
    exact (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp h
  have hK (x : ℝ) (hx : x ∈ Ioo 0 b) :
      HasDerivAt K (Real.exp (speed * x) * (D x + speed * G x)) x := by
    have hexp := (Real.hasDerivAt_exp (speed * x)).comp x (hlin x)
    exact (hexp.mul (hG x hx)).congr_deriv (by
      change (Real.exp (speed * x) * speed) * G x + Real.exp (speed * x) * D x = _
      ring)
  have hKc : ContinuousOn K (Icc 0 b) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hGc
  have hKmono : MonotoneOn K (Icc 0 b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 b) hKc
    · intro x hx
      exact (hK x (by simpa only [interior_Icc] using hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hK x (by simpa only [interior_Icc] using hx)).deriv]
      exact mul_nonneg (Real.exp_pos _).le (hsum x (interior_subset hx))
  have hK0 : K 0 = 0 := by simp [K, G, hf0]
  have hnonneg : 0 ≤ K t := by simpa only [hK0] using hKmono h0 ht ht.1
  have hdiff : 0 ≤ f t - Real.sinh (speed * t) :=
    (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp hnonneg
  exact sub_nonneg.mp hdiff

/-- **Math.** Rescaling a finite-interval scalar Jacobi pair with positive
initial velocity `λ` and curvature coefficient at most `-λ²` yields the
hyperbolic lower bound `sinh(λ t)`. -/
theorem sinh_le_scalarJacobi_of_curvature_le_neg_sq
    {k f v : ℝ → ℝ} {b speed : ℝ} (hspeed : 0 < speed)
    (hfv : Riemannian.Jacobi.IsJacobiPairOn
      (fun t => k t • ContinuousLinearMap.id ℝ ℝ) 0 b f v)
    (hk : ∀ t ∈ Icc 0 b, k t ≤ -(speed ^ 2))
    (hf0 : f 0 = 0) (hv0 : v 0 = speed)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    Real.sinh (speed * t) ≤ f t := by
  let F : ℝ → ℝ := fun s => f (s / speed)
  let V : ℝ → ℝ := fun s => v (s / speed) / speed
  let K : ℝ → ℝ := fun s => k (s / speed) / speed ^ 2
  have hmap : MapsTo (fun s : ℝ => s / speed) (Icc 0 (speed * b)) (Icc 0 b) := by
    intro s hs
    exact ⟨div_nonneg hs.1 hspeed.le,
      (div_le_iff₀ hspeed).mpr (by simpa [mul_comm] using hs.2)⟩
  have hscaled : Riemannian.Jacobi.IsJacobiPairOn
      (fun s => K s • ContinuousLinearMap.id ℝ ℝ) 0 (speed * b) F V := by
    refine ⟨?_, ?_⟩
    · intro s hs
      have h := (hfv.1 (s / speed) (hmap hs)).comp s
        ((hasDerivAt_id s).div_const speed).hasDerivWithinAt hmap
      simpa [F, V, Function.comp_def, div_eq_mul_inv] using h
    · intro s hs
      have h := ((hfv.2 (s / speed) (hmap hs)).comp s
        ((hasDerivAt_id s).div_const speed).hasDerivWithinAt hmap).div_const speed
      have hcoef : (-(k (s / speed) * f (s / speed)) * speed⁻¹) / speed =
          -(K s * F s) := by
        dsimp [K, F]
        field_simp
      simpa only [V, Function.comp_def, id_eq, one_div, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul, hcoef] using h
  have hK : ∀ s ∈ Icc 0 (speed * b), K s ≤ -1 := by
    intro s hs
    dsimp [K]
    apply (div_le_iff₀ (sq_pos_of_pos hspeed)).mpr
    calc
      k (s / speed) ≤ -(speed ^ 2) := hk (s / speed) (hmap hs)
      _ = -1 * speed ^ 2 := by ring
  have hF0 : F 0 = 0 := by simp [F, hf0]
  have hV0 : V 0 = 1 := by simp [V, hv0, hspeed.ne']
  have htime : speed * t ∈ Icc 0 (speed * b) :=
    ⟨mul_nonneg hspeed.le ht.1, mul_le_mul_of_nonneg_left ht.2 hspeed.le⟩
  have h := sinh_le_scalarJacobi_of_curvature_le_neg_one
    hscaled hK hF0 hV0 htime
  simpa [F, mul_comm, hspeed.ne'] using h

#print axioms sinh_le_scalarJacobi_of_curvature_le_neg_sq
#print axioms sinh_le_of_second_deriv_ge_mul_self_on_Icc

end
end SystolicGrowth

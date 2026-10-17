module

public import Geometry.HyperbolicArea
public import Core.Reduction

@[expose] public section

open Filter Set UpperHalfPlane
open scoped MatrixGroups Pointwise Topology UpperHalfPlane

namespace SystolicGrowth

/-! ## Parameters for geometric gluing

These estimates justify the radius choices in the chain-gluing construction.
-/

/-- For a nonnegative argument, `arsinh x` is at most `log (2x + 1)`.
This elementary estimate makes the `2 log log g` loss explicit. -/
theorem arsinh_le_log_two_mul_add_one {x : ℝ} (hx : 0 ≤ x) :
    Real.arsinh x ≤ Real.log (2 * x + 1) := by
  have hsqrt : Real.sqrt (1 + x ^ 2) ≤ x + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  rw [Real.arsinh]
  apply Real.log_le_log
  · have hsqrt_one : 1 ≤ Real.sqrt (1 + x ^ 2) := by
      exact (Real.le_sqrt (x := 1) (y := 1 + x ^ 2)
        (by norm_num) (by positivity)).2 (by nlinarith [sq_nonneg x])
    linarith
  · linarith

/-- Radius of the circles removed in the chain-gluing construction. -/
noncomputable def gluingRadius (C : ℝ) (g : ℕ) : ℝ :=
  Real.arsinh (targetSystole C g / (2 * Real.pi))

/-- Distance an essential same-seam excursion must travel into a component. -/
noncomputable def gluingDepth (C : ℝ) (g : ℕ) : ℝ :=
  targetSystole C g / 2

/-- Radius on which the disk used for gluing must embed. -/
noncomputable def gluingEmbeddedRadius (C : ℝ) (g : ℕ) : ℝ :=
  gluingRadius C g + gluingDepth C g

/-- The chosen seam circle has exactly the target length. -/
theorem two_pi_mul_sinh_gluingRadius (C : ℝ) (g : ℕ) :
    2 * Real.pi * Real.sinh (gluingRadius C g) = targetSystole C g := by
  rw [gluingRadius, Real.sinh_arsinh]
  field_simp [Real.pi_ne_zero]

/-- The `2 log log g` loss pays exactly for the two copies of the gluing
radius.  The hypotheses are the elementary large-`g` inequalities kept
separate from the geometric argument. -/
theorem twice_gluingEmbeddedRadius_lt_systole
    {C K : ℝ} {g : ℕ} {systoleBound : ℝ}
    (hC : K < C) (hL : 0 ≤ targetSystole C g)
    (hscale :
      2 * (targetSystole C g / (2 * Real.pi)) + 1 ≤ Real.log g)
    (hsystole :
      (4 / 3 : ℝ) * Real.log g - K ≤ systoleBound) :
    2 * gluingEmbeddedRadius C g < systoleBound := by
  have hx : 0 ≤ targetSystole C g / (2 * Real.pi) := by positivity
  have harsinh : gluingRadius C g ≤ Real.log (Real.log g) := by
    calc
      gluingRadius C g ≤
          Real.log (2 * (targetSystole C g / (2 * Real.pi)) + 1) := by
        exact arsinh_le_log_two_mul_add_one hx
      _ ≤ Real.log (Real.log g) := by
        apply Real.log_le_log
        · linarith
        · exact hscale
  have htarget :
      2 * gluingEmbeddedRadius C g ≤
        (4 / 3 : ℝ) * Real.log g - C := by
    dsimp [gluingEmbeddedRadius, gluingDepth, targetSystole]
    linarith
  exact htarget.trans_lt (by linarith)

/-- The quantitative target has the required leading asymptotic constant. -/
theorem tendsto_targetSystole_div_log (C : ℝ) :
    Tendsto (fun g : ℕ ↦ targetSystole C g / Real.log g)
      atTop (𝓝 (4 / 3 : ℝ)) := by
  have hlog : Tendsto (fun g : ℕ ↦ Real.log g) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog_div :
      Tendsto (fun g : ℕ ↦ Real.log (Real.log g) / Real.log g)
        atTop (𝓝 0) := by
    have h :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hlog
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using h
  have hC_div : Tendsto (fun g : ℕ ↦ C / Real.log g) atTop (𝓝 0) :=
    hlog.const_div_atTop C
  have hdecomposed : Tendsto
      (fun g : ℕ ↦
        (4 / 3 : ℝ) - 2 * (Real.log (Real.log g) / Real.log g) -
          C / Real.log g)
      atTop (𝓝 (4 / 3 : ℝ)) := by
    simpa using
      (tendsto_const_nhds.sub (hloglog_div.const_mul 2)).sub hC_div
  apply hdecomposed.congr'
  filter_upwards [hlog.eventually_gt_atTop 0] with g hg
  dsimp [targetSystole]
  field_simp

/-- Eventually the target length is nonnegative and small enough that its
chosen seam radius is at most `log (log g)`. -/
theorem eventually_targetSystole_nonneg_and_scale {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ g : ℕ in atTop,
      0 ≤ targetSystole C g ∧
        2 * (targetSystole C g / (2 * Real.pi)) + 1 ≤ Real.log g := by
  have hlog : Tendsto (fun g : ℕ ↦ Real.log g) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio :
      ∀ᶠ g : ℕ in atTop, 1 < targetSystole C g / Real.log g :=
    (tendsto_targetSystole_div_log C).eventually
      (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 4 / 3))
  filter_upwards [hratio, hlog.eventually_ge_atTop 2] with g hratio_g hlog_g
  have hlog_pos : 0 < Real.log g := by linarith
  have hL_pos : 0 < targetSystole C g := by
    have := (lt_div_iff₀ hlog_pos).mp hratio_g
    linarith
  refine ⟨hL_pos.le, ?_⟩
  have hloglog_nonneg : 0 ≤ Real.log (Real.log g) :=
    Real.log_nonneg (by linarith)
  have hL_upper :
      targetSystole C g ≤ (4 / 3 : ℝ) * Real.log g := by
    dsimp [targetSystole]
    linarith
  have hnumerator_nonneg :
      0 ≤ (4 / 3 : ℝ) * Real.log g := by positivity
  have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hdivide :
      ((4 / 3 : ℝ) * Real.log g) / Real.pi ≤
        ((4 / 3 : ℝ) * Real.log g) / 3 := by
    exact div_le_div_of_nonneg_left hnumerator_nonneg (by norm_num) hpi
  calc
    2 * (targetSystole C g / (2 * Real.pi)) + 1 =
        targetSystole C g / Real.pi + 1 := by
      field_simp [Real.pi_ne_zero]
    _ ≤ ((4 / 3 : ℝ) * Real.log g) / Real.pi + 1 := by
      gcongr
    _ ≤ ((4 / 3 : ℝ) * Real.log g) / 3 + 1 := by
      linarith
    _ ≤ Real.log g := by
      nlinarith

/-- Once `C` is larger than the component loss `K`, the target gluing disk
eventually embeds in every component satisfying the stated systole bound. -/
theorem eventually_twice_gluingEmbeddedRadius_lt
    {C K : ℝ} (hC : 0 ≤ C) (hKC : K < C) :
    ∀ᶠ g : ℕ in atTop, ∀ systoleBound : ℝ,
      (4 / 3 : ℝ) * Real.log g - K ≤ systoleBound →
        2 * gluingEmbeddedRadius C g < systoleBound := by
  filter_upwards [eventually_targetSystole_nonneg_and_scale hC] with g hg
  intro systoleBound hsystole
  exact twice_gluingEmbeddedRadius_lt_systole
    hKC hg.1 hg.2 hsystole

/-- A canonical positive gluing constant strictly larger than `K`. -/
def gluingConstant (K : ℝ) : ℝ := max 1 (K + 1)

theorem gluingConstant_pos (K : ℝ) : 0 < gluingConstant K :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem lt_gluingConstant (K : ℝ) : K < gluingConstant K :=
  (lt_add_one K).trans_le (le_max_right _ _)

/-- Canonical eventual embedded-radius estimate with no free choice of the
loss constant. -/
theorem eventually_twice_gluingEmbeddedRadius_gluingConstant_lt (K : ℝ) :
    ∀ᶠ g : ℕ in atTop, ∀ systoleBound : ℝ,
      (4 / 3 : ℝ) * Real.log g - K ≤ systoleBound →
        2 * gluingEmbeddedRadius (gluingConstant K) g < systoleBound :=
  eventually_twice_gluingEmbeddedRadius_lt
    (gluingConstant_pos K).le (lt_gluingConstant K)

/-- Components with the required systole bound eventually contain an
embedded disk at the full gluing radius. -/
theorem eventually_gluing_ball_embeds (K : ℝ) :
    ∀ᶠ g : ℕ in atTop, ∀ (h : ℕ) (X : ClosedHyperbolicSurface h) (o : ℍ),
      (4 / 3 : ℝ) * Real.log g - K ≤ X.systole →
        Set.InjOn
          (fun z : ℍ ↦ (Quotient.mk'' z : X.Carrier))
          (Metric.ball o (gluingEmbeddedRadius (gluingConstant K) g)) := by
  filter_upwards
    [eventually_twice_gluingEmbeddedRadius_gluingConstant_lt K] with g hg
  intro h X o hsystole
  exact quotientMk_injOn_ball X o _ (hg X.systole hsystole)

/-- Equivalently, every nonidentity deck translate of the selected gluing
disk is disjoint from it. -/
theorem eventually_gluing_ball_translates_disjoint (K : ℝ) :
    ∀ᶠ g : ℕ in atTop, ∀ (h : ℕ) (X : ClosedHyperbolicSurface h) (o : ℍ),
      (4 / 3 : ℝ) * Real.log g - K ≤ X.systole →
        ∀ γ : X.deckGroup, γ ≠ 1 →
          Disjoint
            (γ • Metric.ball o (gluingEmbeddedRadius (gluingConstant K) g))
            (Metric.ball o (gluingEmbeddedRadius (gluingConstant K) g)) := by
  filter_upwards
    [eventually_twice_gluingEmbeddedRadius_gluingConstant_lt K] with g hg
  intro h X o hsystole γ hγ
  exact disjoint_smul_ball X o _ (hg X.systole hsystole) γ hγ

end SystolicGrowth

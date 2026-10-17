module

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

/-
## Vendoring provenance

Extracted from
`RiemannDynamics/Uniformization/Fuchsian.lean`, lines 78–397, and the
`unitDiscOpens` definition in `RiemannDynamics/Uniformization/Trichotomy.lean`,
lines 44–45, at immutable upstream commit
`b3fa37cc0f18a23ea66b654ea3f73eb472129010` of
https://github.com/will1491/RiemannDynamics. Both upstream files are Apache-2.0 licensed.
The original header, theorem statements and proofs are retained; imports and
namespace are adapted. Existing vendored Cayley lemmas are reused. The uniformization,
path-cover, Fuchsian-subgroup and RMT4 dependency branches are not imported.
-/
public import Vendored.RiemannDynamics.Uniformization.MobiusDisk
public import Vendored.RiemannDynamics.Hyperbolic.DiskModel.DiskMetric
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

@[expose] public section

/-!
# Analytic disc automorphisms realized in SL(2, ℝ)

This extracted classification supplies actual determinant-one matrices for
analytic automorphisms of the disc after the original Cayley transform. It
does not identify a replacement metric's universal cover or provide a coherent
group-homomorphic choice of lifts.
-/

open Metric Topology Filter TopologicalSpace
open scoped Manifold ContDiff unitInterval

namespace SystolicGrowth.Vendored.RiemannDynamics

/-- The original open unit disc as a plane domain. -/
def unitDiscOpens : Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

/-- **Disc automorphisms are Möbius**: a biholomorphism of the unit disc is a
rotation composed with a disc Möbius map, by the Schwarz lemma applied to the
composition fixing the origin and to its inverse. -/
theorem exists_mobius_of_diffeomorph_unitDisc
    (e : ↥unitDiscOpens ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) :
    ∃ η w : ℂ, ‖η‖ = 1 ∧ w ∈ ball (0 : ℂ) 1 ∧
      ∀ z : ↥unitDiscOpens, (e z : ℂ) = η * mobiusDisk w (z : ℂ) := by
  classical
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  -- The point sent to the origin by `e`.
  set p0 : ↥unitDiscOpens := (⟨0, h0⟩ : ↥unitDiscOpens) with hp0def
  set w' : ℂ := ((e.symm p0 : ↥unitDiscOpens) : ℂ) with hw'def
  have hw' : w' ∈ ball (0 : ℂ) 1 := (e.symm p0).2
  have hnw' : -w' ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_neg]; exact mem_ball_zero_iff.mp hw'
  -- Plane reading of a disc diffeomorphism is holomorphic on the ball.
  have key : ∀ f : ↥unitDiscOpens ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens,
      DifferentiableOn ℂ
        (fun z : ℂ => if hz : z ∈ ball (0 : ℂ) 1 then (f ⟨z, hz⟩ : ℂ) else 0)
        (ball (0 : ℂ) 1) := by
    intro f z₀ hz₀
    have hval : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun q : ↥unitDiscOpens => (f q : ℂ)) :=
      contMDiff_subtype_val.comp f.contMDiff
    -- Local analytic section of the inclusion of the ball.
    set F : ℂ → ↥unitDiscOpens :=
      fun p => if hp : p ∈ ball (0 : ℂ) 1 then (⟨p, hp⟩ : ↥unitDiscOpens) else ⟨0, h0⟩
      with hFdef
    have hFval : ∀ p ∈ ball (0 : ℂ) 1, (F p : ℂ) = p := by
      intro p hp
      simp only [hFdef]
      rw [dif_pos hp]
    have h_analytic : AnalyticAt ℂ (fun p : ℂ => (F p : ℂ)) z₀ := by
      refine analyticAt_id.congr ?_
      filter_upwards [isOpen_ball.mem_nhds hz₀] with p hp
      exact (hFval p hp).symm
    have hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F z₀ := by
      rw [contMDiffAt_iff]
      constructor
      · exact IsInducing.subtypeVal.continuousAt_iff.mpr h_analytic.continuousAt
      · simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, PartialEquiv.refl_symm,
          Function.comp_id, modelWithCornersSelf_coe, Set.range_id, id_eq]
        rw [contDiffWithinAt_univ]
        exact h_analytic.contDiffAt
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        ((fun q : ↥unitDiscOpens => (f q : ℂ)) ∘ F) z₀ :=
      (hval.contMDiffAt).comp z₀ hF
    have h3 : ContDiffAt ℂ ω ((fun q : ↥unitDiscOpens => (f q : ℂ)) ∘ F) z₀ :=
      contMDiffAt_iff_contDiffAt.mp hcomp
    have hev : (fun z : ℂ => if hz : z ∈ ball (0 : ℂ) 1 then (f ⟨z, hz⟩ : ℂ) else 0)
        =ᶠ[𝓝 z₀] ((fun q : ↥unitDiscOpens => (f q : ℂ)) ∘ F) := by
      filter_upwards [isOpen_ball.mem_nhds hz₀] with p hp
      simp only [Function.comp_apply, hFdef]
      rw [dif_pos hp, dif_pos hp]
    exact (h3.analyticAt.differentiableAt.congr_of_eventuallyEq
      hev).differentiableWithinAt
  -- The plane readings of `e` and `e.symm`.
  set E : ℂ → ℂ :=
    fun z => if hz : z ∈ ball (0 : ℂ) 1 then (e ⟨z, hz⟩ : ℂ) else 0 with hEdef
  set E' : ℂ → ℂ :=
    fun z => if hz : z ∈ ball (0 : ℂ) 1 then (e.symm ⟨z, hz⟩ : ℂ) else 0 with hE'def
  have hEdiff : DifferentiableOn ℂ E (ball (0 : ℂ) 1) := key e
  have hE'diff : DifferentiableOn ℂ E' (ball (0 : ℂ) 1) := key e.symm
  have hEval : ∀ q : ↥unitDiscOpens, E (q : ℂ) = (e q : ℂ) := by
    intro q
    have hq : (q : ℂ) ∈ ball (0 : ℂ) 1 := q.2
    simp only [hEdef]
    rw [dif_pos hq]
  have hEmaps : Set.MapsTo E (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    simp only [hEdef]
    rw [dif_pos hz]
    exact (e ⟨z, hz⟩).2
  have hE'maps : Set.MapsTo E' (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    simp only [hE'def]
    rw [dif_pos hz]
    exact (e.symm ⟨z, hz⟩).2
  -- `E'` inverts `E` on the ball.
  have hE'E : ∀ u ∈ ball (0 : ℂ) 1, E' (E u) = u := by
    intro u hu
    have h1 : E u = (e ⟨u, hu⟩ : ℂ) := by simp only [hEdef]; rw [dif_pos hu]
    have h2 : E u ∈ ball (0 : ℂ) 1 := hEmaps hu
    simp only [hE'def]
    rw [dif_pos h2]
    have h3 : (⟨E u, h2⟩ : ↥unitDiscOpens) = e ⟨u, hu⟩ := Subtype.ext h1
    rw [h3, e.symm_apply_apply]
  -- Möbius self-maps of the ball.
  have hMmaps : Set.MapsTo (mobiusDisk (-w')) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    fun z hz => mobiusDisk_mapsTo hz hnw'
  have hM'maps : Set.MapsTo (mobiusDisk w') (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    fun z hz => mobiusDisk_mapsTo hz hw'
  -- Normalized composition and its inverse.
  set φ : ℂ → ℂ := fun z => E (mobiusDisk (-w') z) with hφdef
  set ψ : ℂ → ℂ := fun z => mobiusDisk w' (E' z) with hψdef
  have hφdiff : DifferentiableOn ℂ φ (ball (0 : ℂ) 1) := by
    rw [hφdef]
    exact hEdiff.comp (mobiusDisk_differentiableOn hnw') hMmaps
  have hψdiff : DifferentiableOn ℂ ψ (ball (0 : ℂ) 1) := by
    rw [hψdef]
    exact (mobiusDisk_differentiableOn hw').comp hE'diff hE'maps
  have hφmaps : Set.MapsTo φ (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    simp only [hφdef]
    exact hEmaps (hMmaps hz)
  have hψmaps : Set.MapsTo ψ (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    simp only [hψdef]
    exact hM'maps (hE'maps hz)
  have hφ0 : φ 0 = 0 := by
    simp only [hφdef, mobiusDisk_neg_apply_zero]
    have h1 : E w' = (e ⟨w', hw'⟩ : ℂ) := by simp only [hEdef]; rw [dif_pos hw']
    rw [h1]
    have h2 : (⟨w', hw'⟩ : ↥unitDiscOpens) = e.symm p0 := Subtype.ext hw'def
    rw [h2, e.apply_symm_apply, hp0def]
  have hψ0 : ψ 0 = 0 := by
    simp only [hψdef]
    have h1 : E' 0 = (e.symm ⟨0, h0⟩ : ℂ) := by simp only [hE'def]; rw [dif_pos h0]
    rw [h1, ← hp0def, ← hw'def, mobiusDisk_self]
  -- `ψ` inverts `φ` on the ball.
  have hψφ : ∀ z ∈ ball (0 : ℂ) 1, ψ (φ z) = z := by
    intro z hz
    have hu : mobiusDisk (-w') z ∈ ball (0 : ℂ) 1 := hMmaps hz
    simp only [hψdef, hφdef]
    rw [hE'E _ hu]
    have h1 := mobiusDisk_neg_mobiusDisk hz hnw'
    rwa [neg_neg] at h1
  -- Schwarz in both directions: `φ` is a norm isometry.
  have hφle : ∀ z ∈ ball (0 : ℂ) 1, ‖φ z‖ ≤ ‖z‖ := fun z hz =>
    Complex.norm_le_norm_of_mapsTo_ball hφdiff
      (fun u hu => ball_subset_closedBall (hφmaps hu)) hφ0 (mem_ball_zero_iff.mp hz)
  have hψle : ∀ z ∈ ball (0 : ℂ) 1, ‖ψ z‖ ≤ ‖z‖ := fun z hz =>
    Complex.norm_le_norm_of_mapsTo_ball hψdiff
      (fun u hu => ball_subset_closedBall (hψmaps hu)) hψ0 (mem_ball_zero_iff.mp hz)
  have hφnorm : ∀ z ∈ ball (0 : ℂ) 1, ‖φ z‖ = ‖z‖ := by
    intro z hz
    refine le_antisymm (hφle z hz) ?_
    have h1 := hψle (φ z) (hφmaps hz)
    rwa [hψφ z hz] at h1
  -- The slope at a fixed interior point has unit norm.
  have hz₀mem : (2⁻¹ : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_inv, Complex.norm_ofNat]
    norm_num
  have hz₀ne : (2⁻¹ : ℂ) ≠ 0 := by norm_num
  have hn2 : ‖(2⁻¹ : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hz₀ne
  have hnds : ‖dslope φ 0 (2⁻¹ : ℂ)‖ = 1 := by
    rw [dslope_of_ne φ hz₀ne, slope_def_module, hφ0, sub_zero, sub_zero, norm_smul,
      norm_inv, hφnorm _ hz₀mem]
    exact inv_mul_cancel₀ hn2
  -- Equality case of the Schwarz lemma: `φ` is a rotation.
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div (c := (0 : ℂ))
    (R₁ := 1) (R₂ := 1) hφdiff
    (by
      rw [hφ0]
      exact fun u hu => ball_subset_closedBall (hφmaps hu))
    hz₀mem (by rw [hnds]; norm_num)
  refine ⟨dslope φ 0 (2⁻¹ : ℂ), w', hnds, hw', ?_⟩
  intro z
  have hz : (z : ℂ) ∈ ball (0 : ℂ) 1 := z.2
  have hu : mobiusDisk w' (z : ℂ) ∈ ball (0 : ℂ) 1 := hM'maps hz
  have h1 := haff hu
  simp only [hφ0, zero_add, sub_zero, smul_eq_mul] at h1
  have h2 : mobiusDisk (-w') (mobiusDisk w' (z : ℂ)) = (z : ℂ) :=
    mobiusDisk_neg_mobiusDisk hz hw'
  have h3 : φ (mobiusDisk w' (z : ℂ)) = (e z : ℂ) := by
    simp only [hφdef]
    rw [h2]
    exact hEval z
  rw [h3] at h1
  rw [h1]
  exact mul_comm _ _

/-- **Disc automorphisms act as `SL(2, ℝ)` on the upper half plane**: the
Cayley conjugate of a rotation-Möbius automorphism of the disc is a real
fractional linear map of positive determinant, normalized to determinant
one. -/
theorem exists_sl2_of_diffeomorph_unitDisc
    (e : ↥unitDiscOpens ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ ↥unitDiscOpens) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ↥unitDiscOpens, ∃ τ τ' : UpperHalfPlane,
        (τ : ℂ) = cayleyToHalfPlane (z : ℂ) ∧
        (τ' : ℂ) = cayleyToHalfPlane ((e z : ℂ)) ∧ A • τ = τ' := by
  obtain ⟨η, w, hη, hw, he⟩ := exists_mobius_of_diffeomorph_unitDisc e
  -- A square root `u` of the rotation `η`, with `‖u‖ = 1`.
  set u : ℂ := Complex.exp ((η.arg / 2 : ℝ) * Complex.I) with hu_def
  have hu_norm : ‖u‖ = 1 := by rw [hu_def]; exact Complex.norm_exp_ofReal_mul_I _
  have hu_ne : u ≠ 0 := by rw [hu_def]; exact Complex.exp_ne_zero _
  have hu_sq : u ^ 2 = η := by
    rw [hu_def, ← Complex.exp_nat_mul,
      show ((2 : ℕ) : ℂ) * ((η.arg / 2 : ℝ) * Complex.I) = (η.arg : ℝ) * Complex.I by
        push_cast; ring]
    conv_rhs => rw [← Complex.norm_mul_exp_arg_mul_I η]
    rw [hη, Complex.ofReal_one, one_mul]
  have hcu_inv : (starRingEnd ℂ) u = u⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [mul_comm, Complex.mul_conj', hu_norm]
    norm_num
  -- The scaling factor `s = √(1 - ‖w‖²)`.
  have hw1 : ‖w‖ < 1 := by
    have h := hw
    rwa [mem_ball, dist_zero_right] at h
  have hs2pos : (0 : ℝ) < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  set s : ℝ := Real.sqrt (1 - ‖w‖ ^ 2) with hs_def
  have hs_pos : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.mpr hs2pos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hs_sq : s ^ 2 = 1 - ‖w‖ ^ 2 := by rw [hs_def]; exact Real.sq_sqrt hs2pos.le
  -- The two complex seeds of the matrix entries.
  set x : ℂ := u * (1 - w) with hx_def
  set y : ℂ := u * (1 + w) with hy_def
  set a : ℝ := x.re / s with ha_def
  set b : ℝ := y.im / s with hb_def
  set c : ℝ := (-x.im) / s with hc_def
  set d : ℝ := y.re / s with hd_def
  have haR : a * s = x.re := by rw [ha_def]; exact div_mul_cancel₀ x.re hs_ne
  have hbR : b * s = y.im := by rw [hb_def]; exact div_mul_cancel₀ y.im hs_ne
  have hcR : c * s = -x.im := by rw [hc_def]; exact div_mul_cancel₀ (-x.im) hs_ne
  have hdR : d * s = y.re := by rw [hd_def]; exact div_mul_cancel₀ y.re hs_ne
  have hcx : (starRingEnd ℂ) x = u⁻¹ * (1 - (starRingEnd ℂ) w) := by
    rw [hx_def, map_mul, map_sub, map_one, hcu_inv]
  have hcy : (starRingEnd ℂ) y = u⁻¹ * (1 + (starRingEnd ℂ) w) := by
    rw [hy_def, map_mul, map_add, map_one, hcu_inv]
  -- Complex bridges for the four real entries.
  have haxC : (a : ℂ) * (s : ℂ) * 2 = x + (starRingEnd ℂ) x := by
    rw [Complex.add_conj, ← haR]; push_cast; ring
  have hdxC : (d : ℂ) * (s : ℂ) * 2 = y + (starRingEnd ℂ) y := by
    rw [Complex.add_conj, ← hdR]; push_cast; ring
  have hbxC : (b : ℂ) * (s : ℂ) * 2 = -Complex.I * (y - (starRingEnd ℂ) y) := by
    rw [Complex.sub_conj, ← hbR]; push_cast
    linear_combination (2 * (b : ℂ) * (s : ℂ)) * Complex.I_sq
  have hcxC : (c : ℂ) * (s : ℂ) * 2 = Complex.I * (x - (starRingEnd ℂ) x) := by
    rw [Complex.sub_conj]
    have hxim : x.im = -(c * s) := by rw [hcR, neg_neg]
    rw [hxim]; push_cast
    linear_combination (2 * (c : ℂ) * (s : ℂ)) * Complex.I_sq
  -- Determinant one.
  have hu2 : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq u
    rw [hu_norm, Complex.normSq_apply] at h
    linear_combination h
  have hnw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hdet_aux : x.re * y.re + x.im * y.im = 1 - ‖w‖ ^ 2 := by
    rw [hnw, hx_def, hy_def]
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    linear_combination (1 - w.re ^ 2 - w.im ^ 2) * hu2
  have hdet1 : a * d - b * c = 1 := by
    have h1 : (a * d - b * c) * s ^ 2 = x.re * y.re + x.im * y.im := by
      linear_combination (a * s) * hdR + y.re * haR - (b * s) * hcR + x.im * hbR
    have h2 : (a * d - b * c) * s ^ 2 = 1 * s ^ 2 := by
      rw [h1, hdet_aux, hs_sq]; ring
    exact mul_right_cancel₀ (pow_ne_zero 2 hs_ne) h2
  have hdetM : Matrix.det !![a, b; c, d] = 1 := by
    rw [Matrix.det_fin_two_of]; exact hdet1
  -- The fractional linear action identity, for every point of the disc.
  have main : ∀ ζ : ℂ, ζ ∈ ball (0 : ℂ) 1 →
      ((a : ℂ) * cayleyToHalfPlane ζ + (b : ℂ)) /
        ((c : ℂ) * cayleyToHalfPlane ζ + (d : ℂ))
        = cayleyToHalfPlane (η * mobiusDisk w ζ) := by
    intro ζ hζ
    have h1ζ : (1 : ℂ) - ζ ≠ 0 := one_sub_ne_zero_of_mem_ball hζ
    have hdζ : (1 : ℂ) - (starRingEnd ℂ) w * ζ ≠ 0 := mobiusDisk_denom_ne_zero hζ hw
    have hFmem : η * mobiusDisk w ζ ∈ ball (0 : ℂ) 1 := by
      have hm := mobiusDisk_mapsTo hζ hw
      rw [mem_ball, dist_zero_right] at hm ⊢
      rw [norm_mul, hη, one_mul]; exact hm
    have h1F : (1 : ℂ) - η * mobiusDisk w ζ ≠ 0 := one_sub_ne_zero_of_mem_ball hFmem
    have hCim : 0 < (cayleyToHalfPlane ζ).im := cayleyToHalfPlane_im_pos hζ
    have hDen : (c : ℂ) * cayleyToHalfPlane ζ + (d : ℂ) ≠ 0 := by
      intro h0
      have him : c * (cayleyToHalfPlane ζ).im = 0 := by
        simpa using congrArg Complex.im h0
      have hc0 : c = 0 := by
        rcases mul_eq_zero.mp him with h | h
        · exact h
        · exact absurd h (ne_of_gt hCim)
      have hre : c * (cayleyToHalfPlane ζ).re + d = 0 := by
        simpa using congrArg Complex.re h0
      rw [hc0, zero_mul, zero_add] at hre
      rw [hc0, hre] at hdet1
      norm_num at hdet1
    have hCF : cayleyToHalfPlane (η * mobiusDisk w ζ)
        = Complex.I * (1 + η * mobiusDisk w ζ) / (1 - η * mobiusDisk w ζ) := rfl
    rw [hCF, div_eq_div_iff hDen h1F]
    set G : ℂ := (1 + ζ) / (1 - ζ) with hG_def
    have hC_eq : cayleyToHalfPlane ζ = Complex.I * G := by
      rw [hG_def]
      simp only [cayleyToHalfPlane]
      ring
    rw [hC_eq]
    have star : ((x + (starRingEnd ℂ) x) * G - (y - (starRingEnd ℂ) y))
          * (1 - η * mobiusDisk w ζ)
        = (1 + η * mobiusDisk w ζ)
          * ((y + (starRingEnd ℂ) y) - (x - (starRingEnd ℂ) x) * G) := by
      rw [hcx, hcy, hx_def, hy_def, hG_def, ← hu_sq]
      simp only [mobiusDisk]
      field_simp
      ring
    have h2s : ((s : ℂ) * 2) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hs_ne) two_ne_zero
    refine mul_right_cancel₀ h2s ?_
    linear_combination (Complex.I * G * (1 - η * mobiusDisk w ζ)) * haxC
      + (1 - η * mobiusDisk w ζ) * hbxC
      + (-(Complex.I ^ 2) * G * (1 + η * mobiusDisk w ζ)) * hcxC
      + (-Complex.I * (1 + η * mobiusDisk w ζ)) * hdxC
      + Complex.I * star
      + (-Complex.I * G * (1 + η * mobiusDisk w ζ) * (x - (starRingEnd ℂ) x))
        * Complex.I_sq
  -- Assemble the `SL(2, ℝ)` element and verify the action pointwise.
  set A : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨!![a, b; c, d], hdetM⟩
  refine ⟨A, fun z => ?_⟩
  have hz : (z : ℂ) ∈ ball (0 : ℂ) 1 := z.2
  have hez : ((e z : ℂ)) ∈ ball (0 : ℂ) 1 := (e z).2
  refine ⟨⟨cayleyToHalfPlane (z : ℂ), cayleyToHalfPlane_im_pos hz⟩,
    ⟨cayleyToHalfPlane ((e z : ℂ)), cayleyToHalfPlane_im_pos hez⟩, rfl, rfl, ?_⟩
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  change ((a : ℂ) * cayleyToHalfPlane (z : ℂ) + (b : ℂ)) /
      ((c : ℂ) * cayleyToHalfPlane (z : ℂ) + (d : ℂ)) = cayleyToHalfPlane ((e z : ℂ))
  rw [he z]
  exact main _ hz

#print axioms exists_mobius_of_diffeomorph_unitDisc
#print axioms exists_sl2_of_diffeomorph_unitDisc

end SystolicGrowth.Vendored.RiemannDynamics

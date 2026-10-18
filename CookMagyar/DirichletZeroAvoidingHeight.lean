module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.DirichletLocalZeros
public import CookMagyar.DirichletLocalFactorization
public import CookMagyar.DirichletLogDerivativePositivity

@[expose] public section

/-!
# Choosing a height away from the actual Dirichlet zeros

A finite grid supplies a point in an interval which avoids every member
of a finite set by an explicit inverse-cardinality distance. Jensen's
proved local count gives a logarithmic separation for the actual zeros.
This is the horizontal-height prerequisite for the shifted Perron contour,
not a quantitative zero-free region in the whole strip.
-/

open Metric Set

namespace SystolicGrowth.CookMagyarCircle

private theorem exists_height_away_from_finset (S : Finset ℂ) (a d : ℝ)
    (hd : 0 < d) :
    ∃ H ∈ Icc a (a + d), ∀ z ∈ S,
      d / (3 * ((S.card : ℝ) + 1)) ≤ |H - z.im| := by
  classical
  let N : ℕ := S.card + 1
  let h : ℝ := d / (N : ℝ)
  let x (i : Fin N) : ℝ := a + (i : ℝ) * h
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hh : 0 < h := div_pos hd hN
  have hhd : h * N = d := by dsimp [h]; exact div_mul_cancel₀ _ hN.ne'
  have hx (i : Fin N) : x i ∈ Icc a (a + d) := by
    have hi0 : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg _
    have hiN : (i : ℝ) ≤ N := by exact_mod_cast i.isLt.le
    dsimp [x]
    constructor
    · nlinarith [mul_nonneg hi0 hh.le]
    · nlinarith [mul_le_mul_of_nonneg_right hiN hh.le]
  by_contra hno
  have hbad (i : Fin N) : ∃ z : S, |x i - z.val.im| < h / 3 := by
    have hnot : ¬ ∀ z ∈ S, d / (3 * ((S.card : ℝ) + 1)) ≤ |x i - z.im| :=
      fun hgood => hno ⟨x i, hx i, hgood⟩
    push Not at hnot
    obtain ⟨z, hz, hclose⟩ := hnot
    refine ⟨⟨z, hz⟩, ?_⟩
    have hδ : d / (3 * ((S.card : ℝ) + 1)) = h / 3 := by
      dsimp [h, N]
      push_cast
      field_simp
    simpa only [hδ] using hclose
  choose f hf using hbad
  have hinj : Function.Injective f := by
    intro i j hij
    have hclosei := hf i
    have hclosej := hf j
    rw [hij] at hclosei
    have hdist : |x i - x j| < 2 * h / 3 := by
      have htriangle := abs_add_le (x i - (f j).val.im) ((f j).val.im - x j)
      rw [sub_add_sub_cancel, abs_sub_comm (f j).val.im (x j)] at htriangle
      linarith
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hgap : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
      have horder : x i ≤ x j := by dsimp [x]; nlinarith
      rw [abs_of_nonpos (sub_nonpos.mpr horder)] at hdist
      dsimp [x] at hdist
      nlinarith [mul_le_mul_of_nonneg_right hgap hh.le]
    · have hgap : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hji
      have horder : x j ≤ x i := by dsimp [x]; nlinarith
      rw [abs_of_nonneg (sub_nonneg.mpr horder)] at hdist
      dsimp [x] at hdist
      nlinarith [mul_le_mul_of_nonneg_right hgap hh.le]
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  dsimp [N] at hcard
  omega

variable {q : ℕ} [NeZero q]

/-- In a quarter-unit interval one can choose an actual height separated
from every actual local zero by a conductor-and-height logarithmic distance. -/
theorem exists_dirichlet_local_zero_avoiding_height
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ) :
    ∃ H ∈ Icc τ (τ + 1 / 4), ∀ z ∈ dirichletLocalZeros χ τ,
      1 / (24 * (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
        Real.log (6 / 5 : ℝ) + 1)) ≤ |H - z.im| := by
  let J : ℝ := Real.log (28 * (q : ℝ) * (|τ| + 2)) / Real.log (6 / 5 : ℝ)
  have hcard : ((dirichletLocalZeros χ τ).card : ℝ) ≤ J :=
    dirichletLocalZeros_card_le χ hχ τ
  have hJ : 0 ≤ J := (Nat.cast_nonneg _).trans hcard
  obtain ⟨H, hH, hsep⟩ := exists_height_away_from_finset
    (dirichletLocalZeros χ τ) τ (1 / 4) (by norm_num)
  refine ⟨H, hH, ?_⟩
  intro z hz
  have hcount : (0 : ℝ) < (dirichletLocalZeros χ τ).card + 1 := by positivity
  have hbound : 1 / (24 * (J + 1)) ≤
      (1 / 4) / (3 * (((dirichletLocalZeros χ τ).card : ℝ) + 1)) := by
    have hr : (1 / 4 : ℝ) /
        (3 * (((dirichletLocalZeros χ τ).card : ℝ) + 1)) =
        1 / (12 * (((dirichletLocalZeros χ τ).card : ℝ) + 1)) := by
      field_simp
      ring
    rw [hr]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  exact hbound.trans (hsep z hz)

/-- A selected horizontal line is separated from every zero of the actual
L-function throughout the fixed strip around `1`. Zeros outside the local
disk are handled geometrically, not omitted from the conclusion. -/
theorem exists_dirichlet_zero_avoiding_horizontal_strip
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ) :
    ∃ H ∈ Icc τ (τ + 1 / 4), ∀ σ ∈ Icc (9 / 10 : ℝ) (11 / 10),
      ∀ z : ℂ, DirichletCharacter.LFunction χ z = 0 →
        1 / (24 * (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
          Real.log (6 / 5 : ℝ) + 1)) ≤ ‖((σ : ℂ) + (H : ℂ) * Complex.I) - z‖ := by
  let J : ℝ := Real.log (28 * (q : ℝ) * (|τ| + 2)) / Real.log (6 / 5 : ℝ)
  have hcard : ((dirichletLocalZeros χ τ).card : ℝ) ≤ J :=
    dirichletLocalZeros_card_le χ hχ τ
  have hJ : 0 ≤ J := (Nat.cast_nonneg _).trans hcard
  have hsmall : 1 / (24 * (J + 1)) ≤ (1 / 20 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 24 * (J + 1))).mpr
    nlinarith
  obtain ⟨H, hH, hsep⟩ := exists_dirichlet_local_zero_avoiding_height χ hχ τ
  refine ⟨H, hH, ?_⟩
  intro σ hσ z hz
  let s : ℂ := (σ : ℂ) + (H : ℂ) * Complex.I
  let c : ℂ := 2 + (τ : ℂ) * Complex.I
  by_cases hlocal : z ∈ closedBall c (5 / 4 : ℝ)
  · have hmem : z ∈ dirichletLocalZeros χ τ :=
      (mem_dirichletLocalZeros_iff χ hχ τ z).mpr ⟨hlocal, hz⟩
    have him : (s - z).im = H - z.im := by simp [s]
    exact (hsep z hmem).trans (by simpa only [him] using Complex.abs_im_le_norm (s - z))
  · have hnorm : ‖s - c‖ ≤ (6 / 5 : ℝ) := by
      have hre : (s - c).re = σ - 2 := by simp [s, c]
      have him : (s - c).im = H - τ := by simp [s, c]
      have hresq : (σ - 2) ^ 2 ≤ (121 / 100 : ℝ) := by
        nlinarith [hσ.1, hσ.2]
      have himsq : (H - τ) ^ 2 ≤ (1 / 16 : ℝ) := by
        nlinarith [hH.1, hH.2]
      have hsq : ‖s - c‖ ^ 2 ≤ (6 / 5 : ℝ) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
        nlinarith
      nlinarith [norm_nonneg (s - c)]
    have hfar : (5 / 4 : ℝ) < ‖z - c‖ := by
      simpa only [mem_closedBall, dist_eq_norm, not_le] using hlocal
    have htriangle : ‖z - c‖ ≤ ‖s - z‖ + ‖s - c‖ := by
      have h := norm_add_le (z - s) (s - c)
      simpa only [sub_add_sub_cancel, norm_sub_rev z s] using h
    exact hsmall.trans (by linarith : (1 / 20 : ℝ) ≤ ‖s - z‖)

/-- A single height avoids zeros on both horizontal edges. The finite forbidden
set combines the local zero set at `τ` with the conjugate image of the local
zero set at `-τ`; Jensen's count therefore loses at most a factor of two. -/
theorem exists_dirichlet_zero_avoiding_horizontal_edges
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ) :
    ∃ H ∈ Icc τ (τ + 1 / 4), ∀ σ ∈ Icc (9 / 10 : ℝ) (11 / 10),
      ∀ z : ℂ, DirichletCharacter.LFunction χ z = 0 →
        1 / (48 * (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
          Real.log (6 / 5 : ℝ) + 1)) ≤
            ‖((σ : ℂ) + (H : ℂ) * Complex.I) - z‖ ∧
        1 / (48 * (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
          Real.log (6 / 5 : ℝ) + 1)) ≤
            ‖((σ : ℂ) - (H : ℂ) * Complex.I) - z‖ := by
  let J : ℝ := Real.log (28 * (q : ℝ) * (|τ| + 2)) /
    Real.log (6 / 5 : ℝ)
  let Zpos := dirichletLocalZeros χ τ
  let Zneg := dirichletLocalZeros χ (-τ)
  let S := Zpos ∪ Zneg.image (fun z : ℂ => star z)
  have hcardPos : (Zpos.card : ℝ) ≤ J := by
    dsimp [Zpos, J]
    exact dirichletLocalZeros_card_le χ hχ τ
  have hcardNeg : (Zneg.card : ℝ) ≤ J := by
    dsimp [Zneg, J]
    simpa [abs_neg] using dirichletLocalZeros_card_le χ hχ (-τ)
  have hJ : 0 ≤ J := (Nat.cast_nonneg _).trans hcardPos
  have hcard : (S.card : ℝ) ≤ 2 * J := by
    have hnat : S.card ≤ Zpos.card + Zneg.card := by
      dsimp [S]
      calc
        _ ≤ Zpos.card + (Zneg.image (fun z : ℂ => star z)).card :=
          Finset.card_union_le Zpos (Zneg.image (fun z : ℂ => star z))
        _ ≤ Zpos.card + Zneg.card := Nat.add_le_add_left Finset.card_image_le _
    have hreal : (S.card : ℝ) ≤ (Zpos.card : ℝ) + (Zneg.card : ℝ) := by
      exact_mod_cast hnat
    nlinarith
  obtain ⟨H, hH, hsep⟩ := exists_height_away_from_finset S τ (1 / 4)
    (by norm_num)
  have hsepBound : 1 / (48 * (J + 1)) ≤
      (1 / 4 : ℝ) / (3 * ((S.card : ℝ) + 1)) := by
    have hrewrite : (1 / 4 : ℝ) / (3 * ((S.card : ℝ) + 1)) =
        1 / (12 * ((S.card : ℝ) + 1)) := by field_simp; ring
    rw [hrewrite]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hsmall : 1 / (48 * (J + 1)) ≤ (1 / 20 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 48 * (J + 1))).mpr
    nlinarith
  have hlocalPos (z : ℂ) (hz : z ∈ Zpos) :
      1 / (48 * (J + 1)) ≤ |H - z.im| := by
    apply hsepBound.trans
    exact hsep z (Finset.mem_union_left _ hz)
  have hlocalNeg (z : ℂ) (hz : z ∈ Zneg) :
      1 / (48 * (J + 1)) ≤ |H + z.im| := by
    have hconj : star z ∈ S :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
    have h := hsep (star z) hconj
    simpa [Complex.star_def, Complex.conj_im] using hsepBound.trans h
  refine ⟨H, hH, ?_⟩
  intro σ hσ z hz
  let sPlus : ℂ := (σ : ℂ) + (H : ℂ) * Complex.I
  let sMinus : ℂ := (σ : ℂ) - (H : ℂ) * Complex.I
  let cPlus : ℂ := 2 + (τ : ℂ) * Complex.I
  let cMinus : ℂ := 2 + ((-τ : ℝ) : ℂ) * Complex.I
  have hlinePlus : (sPlus - z).im = H - z.im := by simp [sPlus]
  have hlineMinus : (sMinus - z).im = -H - z.im := by simp [sMinus]
  have hposPlus (hlocal : z ∈ closedBall cPlus (5 / 4 : ℝ)) :
      1 / (48 * (J + 1)) ≤ ‖sPlus - z‖ := by
    have hmem : z ∈ Zpos :=
      (mem_dirichletLocalZeros_iff χ hχ τ z).mpr ⟨by simpa [cPlus] using hlocal, hz⟩
    exact (hlocalPos z hmem).trans (by
      simpa [hlinePlus] using Complex.abs_im_le_norm (sPlus - z))
  have hposMinus (hlocal : z ∈ closedBall cMinus (5 / 4 : ℝ)) :
      1 / (48 * (J + 1)) ≤ ‖sMinus - z‖ := by
    have hmem : z ∈ Zneg :=
      (mem_dirichletLocalZeros_iff χ hχ (-τ) z).mpr ⟨by simpa [cMinus] using hlocal, hz⟩
    have him : |H + z.im| = |(sMinus - z).im| := by
      rw [hlineMinus]
      rw [show -H - z.im = -(H + z.im) by ring, abs_neg]
    exact (hlocalNeg z hmem).trans (by simpa [him] using Complex.abs_im_le_norm (sMinus - z))
  have hnormPlus : ‖sPlus - cPlus‖ ≤ (6 / 5 : ℝ) := by
    have hre : (sPlus - cPlus).re = σ - 2 := by simp [sPlus, cPlus]
    have him : (sPlus - cPlus).im = H - τ := by simp [sPlus, cPlus]
    have hresq : (σ - 2) ^ 2 ≤ (121 / 100 : ℝ) := by nlinarith [hσ.1, hσ.2]
    have himsq : (H - τ) ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith [hH.1, hH.2]
    have hsq : ‖sPlus - cPlus‖ ^ 2 ≤ (6 / 5 : ℝ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
      nlinarith
    nlinarith [norm_nonneg (sPlus - cPlus)]
  have hnormMinus : ‖sMinus - cMinus‖ ≤ (6 / 5 : ℝ) := by
    have hre : (sMinus - cMinus).re = σ - 2 := by simp [sMinus, cMinus]
    have him : (sMinus - cMinus).im = τ - H := by simp [sMinus, cMinus]; ring
    have hresq : (σ - 2) ^ 2 ≤ (121 / 100 : ℝ) := by nlinarith [hσ.1, hσ.2]
    have himsq : (τ - H) ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith [hH.1, hH.2]
    have hsq : ‖sMinus - cMinus‖ ^ 2 ≤ (6 / 5 : ℝ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
      nlinarith
    nlinarith [norm_nonneg (sMinus - cMinus)]
  have hfarPlus (hlocal : z ∉ closedBall cPlus (5 / 4 : ℝ)) :
      (5 / 4 : ℝ) < ‖z - cPlus‖ := by
    simpa only [mem_closedBall, dist_eq_norm, not_le] using hlocal
  have hfarMinus (hlocal : z ∉ closedBall cMinus (5 / 4 : ℝ)) :
      (5 / 4 : ℝ) < ‖z - cMinus‖ := by
    simpa only [mem_closedBall, dist_eq_norm, not_le] using hlocal
  have htrianglePlus : ‖z - cPlus‖ ≤ ‖sPlus - z‖ + ‖sPlus - cPlus‖ := by
    have h := norm_add_le (z - sPlus) (sPlus - cPlus)
    simpa only [sub_add_sub_cancel, norm_sub_rev z sPlus] using h
  have htriangleMinus : ‖z - cMinus‖ ≤ ‖sMinus - z‖ + ‖sMinus - cMinus‖ := by
    have h := norm_add_le (z - sMinus) (sMinus - cMinus)
    simpa only [sub_add_sub_cancel, norm_sub_rev z sMinus] using h
  constructor
  · by_cases hlocal : z ∈ closedBall cPlus (5 / 4 : ℝ)
    · exact hposPlus hlocal
    · exact hsmall.trans (by linarith [hfarPlus hlocal, hnormPlus, htrianglePlus])
  · by_cases hlocal : z ∈ closedBall cMinus (5 / 4 : ℝ)
    · exact hposMinus hlocal
    · exact hsmall.trans (by linarith [hfarMinus hlocal, hnormMinus, htriangleMinus])

/-- The selected horizontal strip contains no zero of the actual function.
Its nonvanishing is a consequence of the quantitative distance theorem. -/
theorem exists_dirichlet_nonvanishing_horizontal_strip
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ) :
    ∃ H ∈ Icc τ (τ + 1 / 4), ∀ σ ∈ Icc (9 / 10 : ℝ) (11 / 10),
      DirichletCharacter.LFunction χ ((σ : ℂ) + (H : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨H, hH, hsep⟩ := exists_dirichlet_zero_avoiding_horizontal_strip χ hχ τ
  refine ⟨H, hH, ?_⟩
  intro σ hσ hzero
  have h := hsep σ hσ _ hzero
  simp only [sub_self, norm_zero] at h
  have hcard := dirichletLocalZeros_card_le χ hχ τ
  have hJ := (Nat.cast_nonneg (dirichletLocalZeros χ τ).card).trans hcard
  have hpos : 0 < 1 / (24 * (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
      Real.log (6 / 5 : ℝ) + 1)) := by positivity
  exact (not_lt_of_ge h) hpos

/-- The open-ball divisor contribution to the local logarithmic derivative
is bounded at every point separated from the actual zeros. Its mass is proved
to be at most the closed-ball Jensen mass; it is not assumed as an input. -/
theorem norm_dirichlet_LFunction_open_local_zero_logDeriv_sum_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ σ H δ : ℝ)
    (hδ : 0 < δ)
    (hsep : ∀ z : ℂ, DirichletCharacter.LFunction χ z = 0 →
      δ ≤ ‖((σ : ℂ) + (H : ℂ) * Complex.I) - z‖) :
    ‖∑ᶠ u : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
            (((σ : ℂ) + (H : ℂ) * Complex.I) - u)‖ ≤
      (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
        Real.log (6 / 5 : ℝ)) / δ := by
  classical
  let c : ℂ := 2 + (τ : ℂ) * Complex.I
  let U : Set ℂ := ball c (5 / 4 : ℝ)
  let C : Set ℂ := closedBall c (5 / 4 : ℝ)
  let f : ℂ → ℂ := DirichletCharacter.LFunction χ
  let D : ℂ → ℤ := MeromorphicOn.divisor f U
  let Dc : ℂ → ℤ := MeromorphicOn.divisor f C
  let Z : Finset ℂ := dirichletLocalZeros χ τ
  let s : ℂ := (σ : ℂ) + (H : ℂ) * Complex.I
  let J : ℝ := Real.log (28 * (q : ℝ) * (|τ| + 2)) /
    Real.log (6 / 5 : ℝ)
  obtain ⟨hfinite, _, _, _, _, _⟩ :=
    exists_dirichlet_LFunction_local_factorization χ hχ τ
  have hJ : 0 ≤ J := by
    have hcard := dirichletLocalZeros_card_le χ hχ τ
    exact (Nat.cast_nonneg _).trans (by simpa [J] using hcard)
  have hfU : AnalyticOnNhd ℂ f U := by
    intro z hz
    exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hfC : AnalyticOnNhd ℂ f C := by
    intro z hz
    exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hnonneg : ∀ u, 0 ≤ D u := fun u =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfU u
  have hCnonneg : ∀ u, 0 ≤ Dc u := fun u =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfC u
  have hsumDc : (∑ u ∈ Z, (Dc u : ℝ)) ≤ J := by
    have hsumD : (∑ u ∈ Z, Dc u : ℤ) ≤ J := by
      have hfiniteSum : (∑ᶠ u : ℂ, Dc u) = ∑ u ∈ Z, Dc u := by
        apply finsum_eq_sum_of_support_subset
        intro u hu
        change u ∈ Z
        have hu' : u ∈ Function.support Dc := hu
        simpa only [Z, dirichletLocalZeros, Set.Finite.mem_toFinset] using hu'
      rw [← hfiniteSum]
      simpa only [Dc, c, f, J] using dirichlet_LFunction_local_sum_divisor_le χ hχ τ
    have hcast : ((∑ u ∈ Z, Dc u : ℤ) : ℝ) = ∑ u ∈ Z, (Dc u : ℝ) := by
      simp only [Int.cast_sum]
    rw [← hcast]
    exact_mod_cast hsumD
  have hmass : (∑ u ∈ hfinite.toFinset, (D u : ℝ)) ≤ J := by
    calc
      _ = ∑ u ∈ hfinite.toFinset, (Dc u : ℝ) := by
        apply Finset.sum_congr rfl
        intro u hu
        have huSupp : u ∈ Function.support D :=
          (Set.Finite.mem_toFinset hfinite).mp hu
        have huD : D u ≠ 0 := Function.mem_support.mp huSupp
        have huU : u ∈ U := by
          by_contra hnot
          have : D u = 0 := by simp [D, hnot]
          exact huD this
        have huC : u ∈ C := Metric.mem_closedBall.mpr (Metric.mem_ball.mp huU).le
        have hsame : D u = Dc u := by
          change MeromorphicOn.divisor f U u = MeromorphicOn.divisor f C u
          rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfU huU,
            MeromorphicOn.AnalyticOnNhd.divisor_apply hfC huC]
        rw [hsame]
      _ ≤ ∑ u ∈ Z, (Dc u : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro u hu
          have huSupp : u ∈ Function.support D :=
            (Set.Finite.mem_toFinset hfinite).mp hu
          have huD : D u ≠ 0 := Function.mem_support.mp huSupp
          have huU : u ∈ U := by
            by_contra hnot
            have : D u = 0 := by simp [D, hnot]
            exact huD this
          have huC : u ∈ C := Metric.mem_closedBall.mpr (Metric.mem_ball.mp huU).le
          have hsame : D u = Dc u := by
            change MeromorphicOn.divisor f U u = MeromorphicOn.divisor f C u
            rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfU huU,
              MeromorphicOn.AnalyticOnNhd.divisor_apply hfC huC]
          have huDc : Dc u ≠ 0 := hsame ▸ huD
          change u ∈ Z
          have huSupportC : u ∈ Function.support Dc := Function.mem_support.mpr huDc
          simpa only [Z, dirichletLocalZeros, Set.Finite.mem_toFinset] using huSupportC
        · intro u huZ hnot
          have huZ' : u ∈ dirichletLocalZeros χ τ := by simpa [Z] using huZ
          have huC : u ∈ C := (mem_dirichletLocalZeros_iff χ hχ τ u).mp huZ' |>.1
          exact_mod_cast hCnonneg u
      _ ≤ J := hsumDc
  have hsumEq : (∑ᶠ u : ℂ, (D u : ℂ) / (s - u)) =
      ∑ u ∈ hfinite.toFinset, (D u : ℂ) / (s - u) := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    have hDu : D u ≠ 0 := by
      intro hzero
      apply hu
      simp [hzero]
    exact (Set.Finite.mem_toFinset hfinite).mpr hDu
  have hterm (u : ℂ) (hu : u ∈ hfinite.toFinset) :
      ‖(D u : ℂ) / (s - u)‖ ≤ (D u : ℝ) / δ := by
    have huSupport : u ∈ Function.support D := (Set.Finite.mem_toFinset hfinite).mp hu
    have hfAnalytic : AnalyticOnNhd ℂ f U := hfU
    have horder : ∀ v : U, meromorphicOrderAt f v ≠ ⊤ := by
      intro v
      rw [(hfU v.1 v.2).meromorphicOrderAt_eq]
      exact fun h => dirichlet_LFunction_analyticOrderAt_ne_top χ hχ v.1
        (ENat.map_eq_top_iff.mp h)
    have hzeroSet := hfU.meromorphicNFOn.zero_set_eq_divisor_support horder
    have huZero : f u = 0 := by
      change u ∈ Function.support (MeromorphicOn.divisor f U) at huSupport
      rw [← hzeroSet] at huSupport
      exact huSupport.2
    have hden : δ ≤ ‖s - u‖ := by
      apply hsep u
      simpa [f] using huZero
    have hDreal : ‖(D u : ℂ)‖ = (D u : ℝ) := by
      rw [Complex.norm_intCast]
      have hDnonneg : (0 : ℝ) ≤ (D u : ℝ) := by exact_mod_cast hnonneg u
      exact abs_of_nonneg hDnonneg
    have hDnonneg : (0 : ℝ) ≤ (D u : ℝ) := by exact_mod_cast hnonneg u
    rw [norm_div, hDreal]
    have hinv : (‖s - u‖)⁻¹ ≤ δ⁻¹ :=
      by simpa only [one_div] using one_div_le_one_div_of_le hδ hden
    calc
      (D u : ℝ) / ‖s - u‖ = (D u : ℝ) * (‖s - u‖)⁻¹ := by ring
      _ ≤ (D u : ℝ) * δ⁻¹ := mul_le_mul_of_nonneg_left hinv hDnonneg
      _ = (D u : ℝ) / δ := by ring
  have hsumNorm : ‖∑ u ∈ hfinite.toFinset, (D u : ℂ) / (s - u)‖ ≤
      ∑ u ∈ hfinite.toFinset, ‖(D u : ℂ) / (s - u)‖ := norm_sum_le _ _
  have hsumTerm : (∑ u ∈ hfinite.toFinset, ‖(D u : ℂ) / (s - u)‖) ≤
      ∑ u ∈ hfinite.toFinset, (D u : ℝ) / δ :=
    Finset.sum_le_sum fun u hu => hterm u hu
  have hsumDiv : (∑ u ∈ hfinite.toFinset, (D u : ℝ) / δ) =
      (∑ u ∈ hfinite.toFinset, (D u : ℝ)) / δ := by rw [Finset.sum_div]
  calc
    ‖∑ᶠ u : ℂ, (D u : ℂ) / (s - u)‖ =
        ‖∑ u ∈ hfinite.toFinset, (D u : ℂ) / (s - u)‖ := by rw [hsumEq]
    _ ≤ ∑ u ∈ hfinite.toFinset, ‖(D u : ℂ) / (s - u)‖ := hsumNorm
    _ ≤ ∑ u ∈ hfinite.toFinset, (D u : ℝ) / δ := hsumTerm
    _ = (∑ u ∈ hfinite.toFinset, (D u : ℝ)) / δ := hsumDiv
    _ ≤ J / δ := div_le_div_of_nonneg_right hmass hδ.le

/-- A single common height gives the open-divisor bound on both horizontal
edges. The upper contour uses the factorization centered at `+τ`, and the lower
contour the one centered at `-τ`. -/
theorem exists_dirichlet_open_divisor_edge_height_bound
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ) :
    ∃ H ∈ Icc τ (τ + 1 / 4),
      (∀ σ ∈ Icc (9 / 10 : ℝ) (11 / 10),
        ‖∑ᶠ u : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
            (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
              (((σ : ℂ) + (H : ℂ) * Complex.I) - u)‖ ≤
          48 * (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
            Real.log (6 / 5 : ℝ)) *
              (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
                Real.log (6 / 5 : ℝ) + 1) ∧
        ‖∑ᶠ u : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
            (ball (2 + ((-τ : ℝ) : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
              (((σ : ℂ) + ((-H : ℝ) : ℂ) * Complex.I) - u)‖ ≤
          48 * (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
            Real.log (6 / 5 : ℝ)) *
              (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
                Real.log (6 / 5 : ℝ) + 1)) ∧
      (∀ σ' ∈ Icc (9 / 10 : ℝ) (11 / 10),
        ∀ z : ℂ, DirichletCharacter.LFunction χ z = 0 →
          1 / (48 * (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
            Real.log (6 / 5 : ℝ) + 1)) ≤
              ‖((σ' : ℂ) + (H : ℂ) * Complex.I) - z‖ ∧
          1 / (48 * (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
            Real.log (6 / 5 : ℝ) + 1)) ≤
              ‖((σ' : ℂ) - (H : ℂ) * Complex.I) - z‖) := by
  let J : ℝ := Real.log (28 * (q : ℝ) * (|τ| + 2)) /
    Real.log (6 / 5 : ℝ)
  let δ : ℝ := 1 / (48 * (J + 1))
  have hJ : 0 ≤ J := by
    have hcard := dirichletLocalZeros_card_le χ hχ τ
    exact (Nat.cast_nonneg _).trans (by simpa [J] using hcard)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨H, hH, havoid⟩ := exists_dirichlet_zero_avoiding_horizontal_edges χ hχ τ
  refine ⟨H, hH, ?_⟩
  constructor
  · intro σ hσ
    constructor
    · have hsep (z : ℂ) (hz : DirichletCharacter.LFunction χ z = 0) :
          δ ≤ ‖((σ : ℂ) + (H : ℂ) * Complex.I) - z‖ := by
        simpa [δ, J] using (havoid σ hσ z hz).1
      have hb := norm_dirichlet_LFunction_open_local_zero_logDeriv_sum_le
        χ hχ τ σ H δ hδ hsep
      have hconvert : J / δ = 48 * J * (J + 1) := by
        dsimp [δ]
        field_simp
      calc
        ‖∑ᶠ u : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
              (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
                (((σ : ℂ) + (H : ℂ) * Complex.I) - u)‖ ≤ J / δ := hb
        _ = 48 * J * (J + 1) := hconvert
    · have hsep (z : ℂ) (hz : DirichletCharacter.LFunction χ z = 0) :
        δ ≤ ‖((σ : ℂ) + ((-H : ℝ) : ℂ) * Complex.I) - z‖ := by
        have hpoint : ((σ : ℂ) + ((-H : ℝ) : ℂ) * Complex.I) - z =
            ((σ : ℂ) - (H : ℂ) * Complex.I) - z := by
          simp only [Complex.ofReal_neg]
          ring
        rw [hpoint]
        simpa [δ, J, abs_neg] using (havoid σ hσ z hz).2
      have hb := norm_dirichlet_LFunction_open_local_zero_logDeriv_sum_le
        χ hχ (-τ) σ (-H) δ hδ hsep
      have hconvert :
          (Real.log (28 * (q : ℝ) * (|(-τ : ℝ)| + 2)) /
            Real.log (6 / 5 : ℝ)) / δ = 48 * J * (J + 1) := by
        simpa [J, abs_neg] using (show J / δ = 48 * J * (J + 1) by
          dsimp [δ]
          field_simp)
      simpa only [hconvert] using hb
  · simpa [J, δ] using havoid

#print axioms exists_dirichlet_local_zero_avoiding_height
#print axioms exists_dirichlet_zero_avoiding_horizontal_strip
#print axioms exists_dirichlet_zero_avoiding_horizontal_edges
#print axioms exists_dirichlet_nonvanishing_horizontal_strip
#print axioms norm_dirichlet_LFunction_open_local_zero_logDeriv_sum_le
#print axioms exists_dirichlet_open_divisor_edge_height_bound

end SystolicGrowth.CookMagyarCircle


namespace SystolicGrowth.CookMagyarMajorArc

private theorem character_real_of_square_eq_one
    {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) :
    ∀ r : ZMod q, (χ r).im = 0 := by
  intro r
  have heval : χ r * χ r = (1 : DirichletCharacter ℂ q) r := by
    have h := congrArg (fun ψ : DirichletCharacter ℂ q => ψ r) hχ
    simpa only [pow_two, MulChar.mul_apply] using h
  by_cases hr : IsUnit r
  · have heval' : χ r * χ r = 1 := by simpa [MulChar.one_apply hr] using heval
    have hfactor : (χ r - 1) * (χ r + 1) = 0 := by
      calc
        (χ r - 1) * (χ r + 1) = χ r * χ r - 1 := by ring
        _ = 0 := by rw [heval']; ring
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · have hval : χ r = 1 := sub_eq_zero.mp hminus
      simp [hval]
    · have hval : χ r = -1 := by linear_combination hplus
      have him := congrArg Complex.im hval
      simpa using him
  · have hzero : χ r = 0 := χ.map_nonunit hr
    simp [hzero]

/-- The full uniform zero-free alternative: every zero in this region is
the same simple real exceptional zero, and its character is real-valued. -/
theorem exists_dirichlet_LFunction_single_near_one_exception :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 100 ∧
      ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∀ z : ℂ, DirichletCharacter.LFunction χ z = 0 →
          1 - c / (Real.log (28 * (q : ℝ) * (|z.im| + 2)) + 1) < z.re →
            (∀ r : ZMod q, (χ r).im = 0) ∧ z.im = 0 ∧ z.re < 1 ∧
              deriv (DirichletCharacter.LFunction χ) z ≠ 0 ∧
              ∀ w : ℂ, DirichletCharacter.LFunction χ w = 0 →
                1 - c / (Real.log (28 * (q : ℝ) * (|w.im| + 2)) + 1) < w.re →
                  w = z := by
  obtain ⟨cN, hcN, hnonreal⟩ := dirichlet_LFunction_zero_free_nonreal_character
  obtain ⟨cR, hcR, hrealNonreal⟩ :=
    dirichlet_LFunction_zero_free_real_character_nonreal_zero
  obtain ⟨cU, hcU, hunique⟩ := exists_dirichlet_LFunction_real_zero_unique_near_one
  obtain ⟨cS, hcS, hsimple⟩ := exists_dirichlet_LFunction_real_zero_simple_near_one
  let c : ℝ := min cN (min cR (min cU (min cS (1 / 100))))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hcNle : c ≤ cN := by dsimp [c]; exact min_le_left _ _
  have hcRle : c ≤ cR := by
    dsimp [c]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hcUle : c ≤ cU := by
    dsimp [c]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hcSle : c ≤ cS := by
    dsimp [c]
    exact le_trans (min_le_right _ _) <| le_trans (min_le_right _ _) <|
      le_trans (min_le_right _ _) (min_le_left _ _)
  have hcSmall : c ≤ 1 / 100 := by
    dsimp [c]
    exact le_trans (min_le_right _ _) <| le_trans (min_le_right _ _) <|
      le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨c, hc, hcSmall, ?_⟩
  intro q hq χ hχ z hz hregion
  letI : NeZero q := hq
  have hqge : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (NeZero.pos q))
  have hBge (x : ℂ) : 1 ≤ 28 * (q : ℝ) * (|x.im| + 2) := by
    have him : 0 ≤ |x.im| := abs_nonneg x.im
    nlinarith [hqge]
  have hellpos (x : ℂ) :
      0 < Real.log (28 * (q : ℝ) * (|x.im| + 2)) + 1 := by
    have hlog := Real.log_nonneg (hBge x)
    linarith
  have hscale (d : ℝ) (hd : c ≤ d) (x : ℂ) :
      1 - d / (Real.log (28 * (q : ℝ) * (|x.im| + 2)) + 1) ≤
        1 - c / (Real.log (28 * (q : ℝ) * (|x.im| + 2)) + 1) := by
    have hdiv := div_le_div_of_nonneg_right hd (hellpos x).le
    linarith
  by_cases hχsq : χ ^ 2 = 1
  · have hχreal := character_real_of_square_eq_one χ hχsq
    have hzIm : z.im = 0 := by
      by_contra hzim
      have hR := hrealNonreal χ hχ hχreal z hz hzim
      exact (not_lt_of_ge (hR.trans (hscale cR hcRle z))) hregion
    have hzrele : z.re ≤ 1 := dirichlet_LFunction_zero_re_le_one χ hz
    have hzreltn : z.re < 1 := by
      by_contra hnot
      have hzre : z.re = 1 := le_antisymm hzrele (le_of_not_gt hnot)
      have hnonzero : DirichletCharacter.LFunction χ z ≠ 0 :=
        DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl hχ)
          (by rw [hzre])
      exact hnonzero hz
    have hzeq : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [hzIm]
    have hfixedPos : 0 < Real.log (56 * (q : ℝ)) + 1 := by
      have harg : 1 ≤ 56 * (q : ℝ) := by nlinarith [hqge]
      have := Real.log_nonneg harg
      linarith
    have hlogeq (x : ℂ) (hxim : x.im = 0) :
        Real.log (28 * (q : ℝ) * (|x.im| + 2)) + 1 =
          Real.log (56 * (q : ℝ)) + 1 := by
      simp [hxim]
      congr 1
      ring
    have hregionFixed (d : ℝ) (hd : c ≤ d) (x : ℂ) (hxim : x.im = 0)
        (hxreg : 1 - c / (Real.log (28 * (q : ℝ) * (|x.im| + 2)) + 1) < x.re) :
        1 - d / (Real.log (56 * (q : ℝ)) + 1) < x.re := by
      rw [hlogeq x hxim] at hxreg
      have hdiv := div_le_div_of_nonneg_right hd hfixedPos.le
      linarith
    have hzsimpleRegion := hregionFixed cS hcSle z hzIm hregion
    have hzReal : DirichletCharacter.LFunction χ (z.re : ℂ) = 0 := by
      rw [← hzeq]
      exact hz
    have hderivReal := hsimple q hq χ hχ z.re hzsimpleRegion hzReal
    have hderiv : deriv (DirichletCharacter.LFunction χ) z ≠ 0 := by
      rwa [hzeq]
    have hother (w : ℂ) (hw : DirichletCharacter.LFunction χ w = 0)
        (hwreg : 1 - c / (Real.log (28 * (q : ℝ) * (|w.im| + 2)) + 1) < w.re) :
        w = z := by
      have hwIm : w.im = 0 := by
        by_contra hwim
        have hR := hrealNonreal χ hχ hχreal w hw hwim
        exact (not_lt_of_ge (hR.trans (hscale cR hcRle w))) hwreg
      have hwRele : w.re ≤ 1 := dirichlet_LFunction_zero_re_le_one χ hw
      have hwregionFixed := hregionFixed cU hcUle w hwIm hwreg
      have hweq : w = (w.re : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hwIm]
      have hwReal : DirichletCharacter.LFunction χ (w.re : ℂ) = 0 := by
        rw [← hweq]
        exact hw
      have hbetaeq := hunique q hq χ hχ z.re w.re
        (hregionFixed cU hcUle z hzIm hregion)
        hwregionFixed hzReal hwReal
      rw [hweq, hzeq, hbetaeq]
    exact ⟨hχreal, hzIm, hzreltn, hderiv, hother⟩
  · have hN := hnonreal (χ := χ) hχsq z hz
    exact False.elim ((not_lt_of_ge (hN.trans (hscale cN hcNle z))) hregion)

#print axioms exists_dirichlet_LFunction_single_near_one_exception

end SystolicGrowth.CookMagyarMajorArc

namespace SystolicGrowth.CookMagyarCircle

open SystolicGrowth.CookMagyarMajorArc

private theorem exists_left_edge_endpoint_far_from
    (d β : ℝ) (hd : 0 < d) :
    ∃ σ : ℝ, σ ∈ Icc (1 - d) (1 - d / 2) ∧
      d / 4 ≤ |σ - β| := by
  by_cases hβ : β ≤ 1 - 3 * d / 4
  · refine ⟨1 - d / 2, ⟨by linarith, le_rfl⟩, ?_⟩
    exact (show d / 4 ≤ (1 - d / 2) - β by linarith).trans (le_abs_self _)
  · refine ⟨1 - d, ⟨le_rfl, by linarith⟩, ?_⟩
    exact (show d / 4 ≤ -((1 - d) - β) by linarith).trans (neg_le_abs _)

private theorem left_edge_real_separation
    (c k ell ellz σ β : ℝ) (hc : 0 < c) (hell : 0 < ell)
    (hellz : 0 < ellz) (hcomp : ellz ≤ ell) (hck : 4 * c ≤ k)
    (hσ : 1 - c / ell ≤ σ) (hβ : β ≤ 1 - k / ellz) :
    c / (4 * ell) ≤ σ - β := by
  have hk : 0 < k := by linarith
  have hratio : 4 * c / ell ≤ k / ellz :=
    (div_le_div_of_nonneg_right hck hell.le).trans
      (div_le_div_of_nonneg_left hk.le hellz hcomp)
  have hcRatio : 0 < c / ell := div_pos hc hell
  have hquarter : c / (4 * ell) = (1 / 4) * (c / ell) := by ring
  have hfour : 4 * c / ell = 4 * (c / ell) := by ring
  rw [hfour] at hratio
  rw [hquarter]
  linarith

private theorem left_edge_high_imaginary_separation
    (H τ t δ : ℝ) (hτ : |τ| ≤ H) (ht : H + 2 < |t|) (hδ : δ ≤ 2) :
    δ ≤ |τ - t| := by
  have h := abs_sub_abs_le_abs_sub t τ
  rw [abs_sub_comm t τ] at h
  linarith

private theorem left_edge_log_mass_budget
    (c ell L d : ℝ) (hc : 0 < c) (hell : 0 < ell) (hd : 0 < d) (hL : L ≤ ell) :
    (L / d) / (c / (4 * ell)) ≤ (4 / (c * d)) * ell ^ 2 := by
  calc
    (L / d) / (c / (4 * ell)) = (4 / (c * d)) * ell * L := by
      field_simp [hc.ne', hell.ne', hd.ne']
    _ ≤ (4 / (c * d)) * ell * ell :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    _ = (4 / (c * d)) * ell ^ 2 := by ring

set_option maxHeartbeats 0 in
/-- Choose one left edge with a uniform logarithmic-derivative bound; every
zero to its right in the same height window is the unique simple real exception. -/
theorem exists_dirichlet_LFunction_bounded_left_vertical_edge :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 / 100 ∧ 0 < C ∧
      ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∀ H : ℝ, 2 ≤ H →
        let ellH : ℝ := Real.log (28 * (q : ℝ) * (H + 4)) + 1
        ∃ σ ∈ Icc (1 - c / ellH) (1 - c / (2 * ellH)),
          (∀ τ : ℝ, |τ| ≤ H →
            DirichletCharacter.LFunction χ ((σ : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 ∧
            ‖logDeriv (DirichletCharacter.LFunction χ)
              ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C * ellH ^ 2) ∧
          ∀ z : ℂ, DirichletCharacter.LFunction χ z = 0 →
            |z.im| ≤ H → σ ≤ z.re →
            (∀ r : ZMod q, (χ r).im = 0) ∧ z.im = 0 ∧ z.re < 1 ∧
              deriv (DirichletCharacter.LFunction χ) z ≠ 0 ∧
              ∀ w : ℂ, DirichletCharacter.LFunction χ w = 0 →
                |w.im| ≤ H → σ ≤ w.re → w = z := by
  obtain ⟨k, hk, hkSmall, hactualRegion⟩ :=
    exists_dirichlet_LFunction_single_near_one_exception
  let c : ℝ := k / 4
  let K : ℝ := 8760 * (1 + Real.log 5 / Real.log (6 / 5 : ℝ))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcSmall : c ≤ 1 / 100 := by dsimp [c]; linarith
  have h65 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  have hK : 0 < K := by
    dsimp [K]
    have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
    positivity
  refine ⟨c, 4 / (c * Real.log (6 / 5 : ℝ)) + K, hc, hcSmall, by positivity, ?_⟩
  intro q hq χ hχ H hH
  let ell : ℝ := Real.log (28 * (q : ℝ) * (H + 4)) + 1
  let δ : ℝ := c / (4 * ell)
  have hqge : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hB : 1 ≤ 28 * (q : ℝ) * (H + 4) := by
    have hprod := mul_le_mul hqge (show (6 : ℝ) ≤ H + 4 by linarith)
      (by norm_num : (0 : ℝ) ≤ 6) hqpos.le
    nlinarith
  have hell : 1 ≤ ell := by dsimp [ell]; linarith [Real.log_nonneg hB]
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : δ ≤ 2 := by
    have hden : 0 < 4 * ell := by positivity
    change c / (4 * ell) ≤ 2
    rw [div_le_iff₀ hden]
    linarith
  let Near (z : ℂ) : Prop :=
    1 - k / (Real.log (28 * (q : ℝ) * (|z.im| + 2)) + 1) < z.re
  have hcommon : ∃ β : ℝ, ∀ z : ℂ,
      DirichletCharacter.LFunction χ z = 0 → Near z → z.re = β := by
    classical
    by_cases hex : ∃ z : ℂ, DirichletCharacter.LFunction χ z = 0 ∧ Near z
    · obtain ⟨z, hz, hzNear⟩ := hex
      refine ⟨z.re, ?_⟩
      intro w hw hwNear
      exact congrArg Complex.re ((hactualRegion χ hχ z hz hzNear).2.2.2.2 w hw hwNear)
    · refine ⟨0, ?_⟩
      intro z hz hzNear
      exact False.elim (hex ⟨z, hz, hzNear⟩)
  obtain ⟨β, hβ⟩ := hcommon
  obtain ⟨σ, hσInterval, hσFar⟩ :=
    exists_left_edge_endpoint_far_from (c / ell) β (div_pos hc hellpos)
  have hσHalf : (c / ell) / 2 = c / (2 * ell) := by field_simp [hellpos.ne']
  rw [hσHalf] at hσInterval
  have hσFar' : δ ≤ |σ - β| := by
    have heq : (c / ell) / 4 = δ := by dsimp [δ]; field_simp [hellpos.ne']
    rwa [heq] at hσFar
  refine ⟨σ, hσInterval, ?_, ?_⟩
  · intro τ hτ
    have hsep : ∀ z : ℂ, DirichletCharacter.LFunction χ z = 0 →
        δ ≤ ‖((σ : ℂ) + (τ : ℂ) * Complex.I) - z‖ := by
      intro z hz
      by_cases hhigh : H + 2 < |z.im|
      · have hfar := left_edge_high_imaginary_separation H τ z.im δ hτ hhigh hδsmall
        exact hfar.trans (by
          simpa using Complex.abs_im_le_norm (((σ : ℂ) + (τ : ℂ) * Complex.I) - z))
      · by_cases hzNear : Near z
        · have hzβ : z.re = β := hβ z hz hzNear
          have hfar : δ ≤ |σ - z.re| := by rw [hzβ]; exact hσFar'
          exact hfar.trans (by
            simpa using Complex.abs_re_le_norm (((σ : ℂ) + (τ : ℂ) * Complex.I) - z))
        · let ellz : ℝ := Real.log (28 * (q : ℝ) * (|z.im| + 2)) + 1
          have hargz : 1 ≤ 28 * (q : ℝ) * (|z.im| + 2) := by
            nlinarith [abs_nonneg z.im]
          have hellz : 0 < ellz := by
            dsimp [ellz]
            linarith [Real.log_nonneg hargz]
          have hcomp : ellz ≤ ell := by
            have hargle : 28 * (q : ℝ) * (|z.im| + 2) ≤ 28 * (q : ℝ) * (H + 4) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have hzHeight : |z.im| ≤ H + 2 := le_of_not_gt hhigh
              linarith
            exact add_le_add (Real.log_le_log (by positivity) hargle) le_rfl
          have hzOrd : z.re ≤ 1 - k / ellz := le_of_not_gt hzNear
          have hfar := left_edge_real_separation c k ell ellz σ z.re hc hellpos hellz hcomp
            (by dsimp [c]; linarith) hσInterval.1 hzOrd
          exact hfar.trans (by
            simpa using Complex.re_le_norm (((σ : ℂ) + (τ : ℂ) * Complex.I) - z))
    have hsne : DirichletCharacter.LFunction χ ((σ : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
      intro hz
      have hbad := hsep ((σ : ℂ) + (τ : ℂ) * Complex.I) hz
      simp only [sub_self, norm_zero] at hbad
      exact (not_le_of_gt hδ) hbad
    have hσBounds : 9 / 10 ≤ σ ∧ σ ≤ 11 / 10 := by
      have hratio := div_le_self hc.le hell
      have hratio2 : 0 ≤ c / (2 * ell) := by positivity
      constructor <;> linarith [hσInterval.1, hσInterval.2]
    have hdisc : (σ : ℂ) + (τ : ℂ) * Complex.I ∈
        closedBall (2 + (τ : ℂ) * Complex.I) (6 / 5 : ℝ) := by
      have hdiff : ((σ : ℂ) + (τ : ℂ) * Complex.I) -
          (2 + (τ : ℂ) * Complex.I) = ((σ - 2 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [mem_closedBall, dist_eq_norm, hdiff, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith [hσBounds.2] : σ - 2 ≤ 0)]
      linarith [hσBounds.1]
    have hlogBound : Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1 ≤ ell := by
      have hargle : 28 * (q : ℝ) * (|τ| + 2) ≤ 28 * (q : ℝ) * (H + 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      exact add_le_add (Real.log_le_log (by positivity) hargle) le_rfl
    have hlogOnly : Real.log (28 * (q : ℝ) * (|τ| + 2)) ≤ ell := by linarith
    have hsum := norm_dirichlet_LFunction_open_local_zero_logDeriv_sum_le
      χ hχ τ σ τ δ hδ hsep
    let S : ℂ := ∑ᶠ u : ℂ,
      ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
          (((σ : ℂ) + (τ : ℂ) * Complex.I) - u)
    have hsumBudget : ‖S‖ ≤ (4 / (c * Real.log (6 / 5 : ℝ))) * ell ^ 2 := by
      exact hsum.trans (left_edge_log_mass_budget c ell
        (Real.log (28 * (q : ℝ) * (|τ| + 2))) (Real.log (6 / 5 : ℝ))
          hc hellpos h65 hlogOnly)
    have hrem := norm_dirichlet_LFunction_local_logDeriv_sub_divisor_sum_le
      χ hχ τ hdisc hsne
    have hremBudget : ‖logDeriv (DirichletCharacter.LFunction χ)
        ((σ : ℂ) + (τ : ℂ) * Complex.I) - S‖ ≤ K * ell ^ 2 := by
      have hellSquare : ell ≤ ell ^ 2 := by nlinarith
      exact hrem.trans ((mul_le_mul_of_nonneg_left hlogBound hK.le).trans
        (mul_le_mul_of_nonneg_left hellSquare hK.le))
    refine ⟨hsne, ?_⟩
    have hnorm := norm_add_le (logDeriv (DirichletCharacter.LFunction χ)
      ((σ : ℂ) + (τ : ℂ) * Complex.I) - S) S
    rw [sub_add_cancel] at hnorm
    change ‖logDeriv (DirichletCharacter.LFunction χ)
      ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      (4 / (c * Real.log (6 / 5 : ℝ)) + K) * ell ^ 2
    nlinarith
  · have hinside (z : ℂ) (hzHeight : |z.im| ≤ H) (hσz : σ ≤ z.re) : Near z := by
      by_contra hzNotNear
      let ellz : ℝ := Real.log (28 * (q : ℝ) * (|z.im| + 2)) + 1
      have hargz : 1 ≤ 28 * (q : ℝ) * (|z.im| + 2) := by
        nlinarith [abs_nonneg z.im]
      have hellz : 0 < ellz := by
        dsimp [ellz]
        linarith [Real.log_nonneg hargz]
      have hcomp : ellz ≤ ell := by
        have hargle : 28 * (q : ℝ) * (|z.im| + 2) ≤ 28 * (q : ℝ) * (H + 4) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
        exact add_le_add (Real.log_le_log (by positivity) hargle) le_rfl
      have hzOrd : z.re ≤ 1 - k / ellz := le_of_not_gt hzNotNear
      have hfar := left_edge_real_separation c k ell ellz σ z.re hc hellpos hellz hcomp
        (by dsimp [c]; linarith) hσInterval.1 hzOrd
      change δ ≤ σ - z.re at hfar
      linarith
    intro z hz hzHeight hσz
    obtain ⟨hreal, hzIm, hzRe, hzDeriv, hother⟩ :=
      hactualRegion χ hχ z hz (hinside z hzHeight hσz)
    refine ⟨hreal, hzIm, hzRe, hzDeriv, ?_⟩
    intro w hw hwHeight hσw
    exact hother w hw (hinside w hwHeight hσw)

#print axioms exists_dirichlet_LFunction_bounded_left_vertical_edge

end SystolicGrowth.CookMagyarCircle

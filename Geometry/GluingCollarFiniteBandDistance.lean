module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFinWarp
public import Geometry.GluingCollarSourceMetric
public import Geometry.GluingCollarClampGeodesics
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# Intrinsic distances on one finite collar band and its Fermi strip

These path infima retain both the radial-window and band/strip constraints.
The forward band map gives a quantitative comparison before different bands
are identified in the finite approximation.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace SystolicGrowth

/-- Boundary compatibility for adjacent strip copies: the upper edge of one
band is glued to the lower edge of the next by angular reflection. -/
def gluingCollarFiniteStripAdjacentBoundaryRelation (z w : ℂ) : Prop :=
  z.re = w.re ∧ z.im = -w.im

/-- The oriented seam relation between consecutive copies of the finite
Fermi strip. The lower copy's upper edge is identified with the next copy's
lower edge at the same radial coordinate. -/
def gluingCollarFiniteBandTargetSeam (r ε : ℝ)
    (p q : ℤ × ℂ) : Prop :=
  p.1 + 1 = q.1 ∧ ∃ t : ℝ,
    p.2 = (t : ℂ) + Complex.I *
      ((ε * gluingCollarWarp r t : ℝ) : ℂ) ∧
    q.2 = (t : ℂ) + Complex.I *
      ((-ε * gluingCollarWarp r t : ℝ) : ℂ)

/-- Ambient seam quotient for the countable chain of strip copies. The
admissible radial-window strip classes are specified below. -/
abbrev gluingCollarFiniteBandTarget (r ε : ℝ) : Type :=
  Quotient (Relation.EqvGen.setoid (gluingCollarFiniteBandTargetSeam r ε))

/-- The width-`ε` bands centered at `c + 2nε`, `n : ℤ`, cover the entire
angular line. This is the coverage fact needed to assemble all finite pieces. -/
theorem exists_gluingCollarFiniteBand_center {c ε v : ℝ} (hε : 0 < ε) :
    ∃ n : ℤ, |v - (c + 2 * (n : ℝ) * ε)| ≤ ε := by
  let q : ℝ := (v - c + ε) / (2 * ε)
  let n : ℤ := ⌊q⌋
  have hden : 0 < 2 * ε := by positivity
  have hfloorLower : (n : ℝ) ≤ q := by
    exact Int.floor_le q
  have hfloorUpper : q < (n : ℝ) + 1 := by
    exact Int.lt_floor_add_one q
  have hleft : (n : ℝ) * (2 * ε) ≤ v - c + ε := by
    exact (le_div_iff₀ hden).mp hfloorLower
  have hright : v - c + ε < ((n : ℝ) + 1) * (2 * ε) := by
    exact (div_lt_iff₀ hden).mp hfloorUpper
  refine ⟨n, abs_le.mpr ?_⟩
  constructor <;> nlinarith [hleft, hright]

/-- A bounded angular interval meets only finitely many of the lattice bands.
The bound on the index is chosen uniformly for the whole interval, not
separately for each point. -/
theorem exists_gluingCollarFiniteBand_range_bound
    {c ε B : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ v : ℝ, |v| ≤ B →
      ∃ n : ℤ, n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) ∧
        |v - (c + 2 * (n : ℝ) * ε)| ≤ ε := by
  have hden : 0 < 2 * ε := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt ((B + |c| + ε) / (2 * ε))
  refine ⟨N, fun v hv => ?_⟩
  obtain ⟨n, hnBand⟩ := exists_gluingCollarFiniteBand_center hε
  have hv' : -B ≤ v ∧ v ≤ B := abs_le.mp hv
  have hc₁ : -|c| ≤ c := neg_abs_le c
  have hc₂ : c ≤ |c| := le_abs_self c
  have hnBand' : -ε ≤ v - (c + 2 * (n : ℝ) * ε) ∧
      v - (c + 2 * (n : ℝ) * ε) ≤ ε := abs_le.mp hnBand
  have hnMul : |2 * (n : ℝ) * ε| ≤ B + |c| + ε := by
    rw [abs_le]
    constructor <;> nlinarith
  have habsMul : |2 * (n : ℝ) * ε| = (2 * ε) * |(n : ℝ)| := by
    calc
      |2 * (n : ℝ) * ε| = |(2 : ℝ)| * |(n : ℝ)| * |ε| := by
        rw [abs_mul, abs_mul]
      _ = (2 * ε) * |(n : ℝ)| := by
        rw [abs_of_nonneg (by norm_num), abs_of_pos hε]
        ring
  have hnReal : |(n : ℝ)| ≤ (B + |c| + ε) / (2 * ε) := by
    apply (le_div_iff₀ hden).2
    calc
      |(n : ℝ)| * (2 * ε) = |2 * (n : ℝ) * ε| := by rw [habsMul]; ring
      _ ≤ B + |c| + ε := hnMul
  have hnAbsLt : |(n : ℝ)| < (N : ℝ) :=
    lt_of_le_of_lt hnReal hN
  have hnRealIcc : -(N : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (N : ℝ) :=
    abs_lt.mp hnAbsLt |>.imp le_of_lt le_of_lt
  have hnIcc : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    rw [Finset.mem_Icc]
    constructor
    · exact_mod_cast hnRealIcc.1
    · exact_mod_cast hnRealIcc.2
  exact ⟨n, hnIcc, hnBand⟩

/-- A Lipschitz path on the unit interval visits only a uniformly bounded
finite set of angular band indices. The bound depends on the path's
Euclidean Lipschitz constant and its initial angular coordinate. -/
theorem exists_gluingCollarFiniteBand_path_range_bound
    {c ε : ℝ} (hε : 0 < ε) (α : ℝ → ℂ)
    (hLip : ∃ K : ℝ≥0, LipschitzOnWith K α (Icc (0 : ℝ) 1)) :
    ∃ N : ℕ, ∀ t ∈ Icc (0 : ℝ) 1,
      ∃ n : ℤ, n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) ∧
        |(α t).im - (c + 2 * (n : ℝ) * ε)| ≤ ε := by
  obtain ⟨K, hα⟩ := hLip
  let B : ℝ := |(α 0).im| + K
  have himBound : ∀ t ∈ Icc (0 : ℝ) 1, |(α t).im| ≤ B := by
    intro t ht
    have hd := hα.dist_le_mul t ht 0 (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    have hn : ‖α t - α 0‖ ≤ (K : ℝ) * t := by
      simpa only [Complex.dist_eq, Real.dist_eq, sub_zero,
        abs_of_nonneg ht.1] using hd
    have himNorm : |(α t).im - (α 0).im| ≤ ‖α t - α 0‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (α t - α 0)
    have htK : (K : ℝ) * t ≤ K := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg
    calc
      |(α t).im| = |((α t).im - (α 0).im) + (α 0).im| := by congr 1; ring
      _ ≤ |(α t).im - (α 0).im| + |(α 0).im| := abs_add_le _ _
      _ ≤ B := by dsimp [B]; linarith
  obtain ⟨N, hN⟩ := exists_gluingCollarFiniteBand_range_bound
    (c := c) (ε := ε) (B := B) hε
  refine ⟨N, fun t ht => ?_⟩
  obtain ⟨n, hnIcc, hnBand⟩ := hN (α t).im (himBound t ht)
  exact ⟨n, hnIcc, hnBand⟩

/-- Distinct overlapping source bands are adjacent, and their intersection is
exactly their common boundary point. This is the uniqueness fact needed when
defining a map into the target pieces modulo boundary identifications. -/
theorem gluingCollarFiniteBand_overlap_eq_upper_boundary
    {c ε v : ℝ} {n m : ℤ} (hε : 0 < ε)
    (hn : |v - (c + 2 * (n : ℝ) * ε)| ≤ ε)
    (hm : |v - (c + 2 * (m : ℝ) * ε)| ≤ ε) (hnm : n < m) :
    m = n + 1 ∧ v = c + 2 * (n : ℝ) * ε + ε := by
  have hnUpper : v - (c + 2 * (n : ℝ) * ε) ≤ ε := (abs_le.mp hn).2
  have hmLower : -ε ≤ v - (c + 2 * (m : ℝ) * ε) := (abs_le.mp hm).1
  have hgap : (m : ℝ) - (n : ℝ) ≤ 1 := by nlinarith
  have hnle : n + 1 ≤ m := by omega
  have hnleReal : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hnle
  have hmeqReal : (m : ℝ) = (n : ℝ) + 1 := by nlinarith
  have hmeq : m = n + 1 := by exact_mod_cast hmeqReal
  refine ⟨hmeq, ?_⟩
  have hcenter : c + 2 * (m : ℝ) * ε =
      c + 2 * (n : ℝ) * ε + 2 * ε := by rw [hmeqReal]; ring
  rw [hcenter] at hmLower
  linarith

/-- The same overlap classification with the two band indices reversed. -/
theorem gluingCollarFiniteBand_overlap_eq_lower_boundary
    {c ε v : ℝ} {n m : ℤ} (hε : 0 < ε)
    (hn : |v - (c + 2 * (n : ℝ) * ε)| ≤ ε)
    (hm : |v - (c + 2 * (m : ℝ) * ε)| ≤ ε) (hmn : m < n) :
    n = m + 1 ∧ v = c + 2 * (m : ℝ) * ε + ε := by
  exact gluingCollarFiniteBand_overlap_eq_upper_boundary hε hm hn hmn

/-- The complex norm used in the band infimum is the ordinary warped
coordinate speed of the collar. -/
theorem gluingCollarFinBandSourceSpeed_eq_sqrt (r : ℝ) (u v : ℝ → ℝ) (t : ℝ) :
    gluingCollarFinBandSourceSpeed r u v t =
      Real.sqrt (deriv u t ^ 2 +
        gluingCollarWarp r (u t) ^ 2 * deriv v t ^ 2) := by
  unfold gluingCollarFinBandSourceSpeed
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im]
  congr 1
  ring

/-- Fermi-coordinate speed for a target path in the finite strip. -/
noncomputable def gluingCollarFiniteStripSpeed (lam : ℝ) (β : ℝ → ℂ) (t : ℝ) : ℝ :=
  ‖((Real.cosh (lam * (β t).im) * deriv (fun s => (β s).re) t : ℝ) : ℂ) +
    Complex.I * ((deriv (fun s => (β s).im) t : ℝ) : ℂ)‖

/-- The source path infimum inside one closed band and bounded radial window. -/
noncomputable def gluingCollarFiniteBandEDist
    (r R c ε : ℝ) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ (α : ℝ → ℂ) (_h0 : α 0 = z) (_h1 : α 1 = w)
    (_hLip : ∃ K : ℝ≥0, LipschitzOnWith K α (Icc (0 : ℝ) 1))
    (_hWindow : ∀ t ∈ Icc (0 : ℝ) 1, (α t).re ∈ Icc (-R) R)
    (_hBand : ∀ t ∈ Icc (0 : ℝ) 1, |(α t).im - c| ≤ ε),
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
      (gluingCollarFinBandSourceSpeed r
        (fun s => (α s).re) (fun s => (α s).im) t)

/-- The target path infimum inside the variable-width finite Fermi strip. -/
noncomputable def gluingCollarFiniteStripEDist
    (r R lam ε : ℝ) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ (β : ℝ → ℂ) (_h0 : β 0 = z) (_h1 : β 1 = w)
    (_hLip : ∃ K : ℝ≥0, LipschitzOnWith K β (Icc (0 : ℝ) 1))
    (_hWindow : ∀ t ∈ Icc (0 : ℝ) 1, (β t).re ∈ Icc (-R) R)
    (_hStrip : ∀ t ∈ Icc (0 : ℝ) 1,
      |(β t).im| ≤ ε * gluingCollarWarp r (β t).re),
    ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
      (gluingCollarFiniteStripSpeed lam β t)

/-- Restricting to a closed band can only increase the native collar
distance. The speed under this infimum is exactly the native warped speed. -/
theorem gluingCollarModelEDist_le_finiteBandEDist
    {r : ℝ} (hr : 0 < r) (R c ε : ℝ) (z w : ℂ) :
    gluingCollarModelEDist hr z w ≤
      gluingCollarFiniteBandEDist r R c ε z w := by
  unfold gluingCollarFiniteBandEDist
  refine le_iInf fun α => le_iInf fun h0 => le_iInf fun h1 =>
    le_iInf fun hLip => le_iInf fun _ => le_iInf fun _ => ?_
  obtain ⟨K, hK⟩ := hLip
  have hu : LipschitzOnWith K (fun t => (α t).re) (Icc (0 : ℝ) 1) := by
    simpa [Function.comp_def] using
      (RCLike.lipschitzWith_re (K := ℂ)).comp_lipschitzOnWith hK
  have hv : LipschitzOnWith K (fun t => (α t).im) (Icc (0 : ℝ) 1) := by
    simpa [Function.comp_def] using
      (RCLike.lipschitzWith_im (K := ℂ)).comp_lipschitzOnWith hK
  have hsource := gluingCollarModelEDist_le_sourceLength hr zero_le_one hu hv
  have hsource' : gluingCollarModelEDist hr z w ≤
      gluingCollarSourceLength r 0 1
        (fun t => (α t).re) (fun t => (α t).im) := by
    simpa only [Complex.re_add_im, h0, h1] using hsource
  rw [gluingCollarSourceLength_eq_deriv_integral zero_le_one r hu hv] at hsource'
  simpa only [gluingCollarFinBandSourceSpeed_eq_sqrt] using hsource'

/-- Clamp only the angular coordinate to the closed band centered at `c`. -/
noncomputable def gluingCollarAngularClamp (c ε : ℝ) (z : ℂ) : ℂ :=
  ⟨z.re, c + gluingCollarClampReal ε (z.im - c)⟩

@[simp] theorem gluingCollarAngularClamp_re (c ε : ℝ) (z : ℂ) :
    (gluingCollarAngularClamp c ε z).re = z.re := rfl

@[simp] theorem gluingCollarAngularClamp_im (c ε : ℝ) (z : ℂ) :
    (gluingCollarAngularClamp c ε z).im =
      c + gluingCollarClampReal ε (z.im - c) := rfl

/-- Angular clamping fixes every point already in the closed band. -/
theorem gluingCollarAngularClamp_eq_self {c ε : ℝ} {z : ℂ}
    (hz : |z.im - c| ≤ ε) : gluingCollarAngularClamp c ε z = z := by
  apply Complex.ext
  · rfl
  · simp only [gluingCollarAngularClamp_im,
      gluingCollarClampReal_eq_of_mem (abs_le.mp hz)]
    ring

/-- Angular clamping always lands in the closed band. -/
theorem gluingCollarAngularClamp_mem_band {c ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    |(gluingCollarAngularClamp c ε z).im - c| ≤ ε := by
  rw [gluingCollarAngularClamp_im, add_sub_cancel_left]
  apply abs_le.mpr
  simp only [gluingCollarClampReal]
  constructor
  · exact le_max_left _ _
  · apply max_le
    · linarith
    · exact min_le_left _ _

/-- Angular clamping is nonexpanding in ordinary complex coordinates. -/
theorem gluingCollarAngularClamp_lipschitz (c ε : ℝ) :
    LipschitzWith 1 (gluingCollarAngularClamp c ε) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro z w
  have hclamp := (gluingCollarClampReal_lipschitz (R := ε)).dist_le_mul
    (z.im - c) (w.im - c)
  have habs : |gluingCollarClampReal ε (z.im - c) -
      gluingCollarClampReal ε (w.im - c)| ≤ |z.im - w.im| := by
    have h := hclamp
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at h
    have hsub : (z.im - c) - (w.im - c) = z.im - w.im := by ring
    simpa only [hsub] using h
  have hsq : (gluingCollarClampReal ε (z.im - c) -
      gluingCollarClampReal ε (w.im - c)) ^ 2 ≤ (z.im - w.im) ^ 2 := by
    have h := (sq_le_sq₀
      (abs_nonneg (gluingCollarClampReal ε (z.im - c) -
        gluingCollarClampReal ε (w.im - c)))
      (abs_nonneg (z.im - w.im))).mpr habs
    simpa only [sq_abs] using h
  change dist (gluingCollarAngularClamp c ε z)
    (gluingCollarAngularClamp c ε w) ≤ (1 : ℝ≥0) * dist z w
  rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im]
  simp only [gluingCollarAngularClamp_re, gluingCollarAngularClamp_im,
    NNReal.coe_one, one_mul]
  have him : (c + gluingCollarClampReal ε (z.im - c) -
      (c + gluingCollarClampReal ε (w.im - c))) ^ 2 =
      (gluingCollarClampReal ε (z.im - c) -
        gluingCollarClampReal ε (w.im - c)) ^ 2 := by ring
  rw [him]
  exact Real.sqrt_le_sqrt (add_le_add le_rfl hsq)

/-- Angular clamping contracts the actual warped source speed almost
everywhere, including paths that spend positive time at a band boundary. -/
theorem gluingCollarAngularClamp_sourceSpeed_le_ae
    {r c ε : ℝ} {α : ℝ → ℂ} {K : ℝ≥0}
    (hα : LipschitzOnWith K α (Icc (0 : ℝ) 1)) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      gluingCollarFinBandSourceSpeed r
        (fun s => (gluingCollarAngularClamp c ε (α s)).re)
        (fun s => (gluingCollarAngularClamp c ε (α s)).im) t ≤
      gluingCollarFinBandSourceSpeed r
        (fun s => (α s).re) (fun s => (α s).im) t := by
  have hv : LipschitzOnWith K (fun s => (α s).im) (Icc (0 : ℝ) 1) := by
    simpa [Function.comp_def] using
      (RCLike.lipschitzWith_im (K := ℂ)).comp_lipschitzOnWith hα
  have hshift : LipschitzOnWith K
      (fun s => (α s).im - c) (Icc (0 : ℝ) 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := hv.dist_le_mul x hx y hy
    simpa [Real.dist_eq] using h
  have hderiv := gluingCollarClamp_deriv_abs_le_ae (R := ε) hshift
  filter_upwards [hderiv] with t hdt
  have hvim : (fun s => (gluingCollarAngularClamp c ε (α s)).im) =
      fun s => c + gluingCollarClampReal ε ((α s).im - c) := by funext s; rfl
  have hvderiv : |deriv (fun s => (gluingCollarAngularClamp c ε (α s)).im) t| ≤
      |deriv (fun s => (α s).im) t| := by
    rw [hvim, deriv_const_add]
    simpa only [deriv_sub_const] using hdt
  have hsq : (deriv (fun s => (gluingCollarAngularClamp c ε (α s)).im) t) ^ 2 ≤
      (deriv (fun s => (α s).im) t) ^ 2 := by
    have h := (sq_le_sq₀
      (abs_nonneg (deriv (fun s => (gluingCollarAngularClamp c ε (α s)).im) t))
      (abs_nonneg (deriv (fun s => (α s).im) t))).mpr hvderiv
    simpa only [sq_abs] using h
  rw [gluingCollarFinBandSourceSpeed_eq_sqrt,
    gluingCollarFinBandSourceSpeed_eq_sqrt]
  simp only [gluingCollarAngularClamp_re]
  apply Real.sqrt_le_sqrt
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hsq (sq_nonneg _))

/-- The source-speed integral used by the finite-band infimum is exactly
the previously constructed admissible collar length on a Lipschitz path. -/
theorem gluingCollarFinBand_source_integral_eq_curve_integral
    (r : ℝ) {α : ℝ → ℂ} {K : ℝ≥0}
    (hα : LipschitzOnWith K α (Icc (0 : ℝ) 1)) :
    (∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
      (gluingCollarFinBandSourceSpeed r
        (fun s => (α s).re) (fun s => (α s).im) t)) =
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
        (Real.sqrt (gluingComplexCollarTangentForm r
          (α t) (deriv α t) (deriv α t))) := by
  have hu : LipschitzOnWith K (fun t => (α t).re) (Icc (0 : ℝ) 1) := by
    simpa [Function.comp_def] using
      (RCLike.lipschitzWith_re (K := ℂ)).comp_lipschitzOnWith hα
  have hv : LipschitzOnWith K (fun t => (α t).im) (Icc (0 : ℝ) 1) := by
    simpa [Function.comp_def] using
      (RCLike.lipschitzWith_im (K := ℂ)).comp_lipschitzOnWith hα
  calc
    _ = ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
        (Real.sqrt (deriv (fun s => (α s).re) t ^ 2 +
          gluingCollarWarp r (α t).re ^ 2 *
            deriv (fun s => (α s).im) t ^ 2)) := by
              congr 1
              funext t
              exact congrArg ENNReal.ofReal
                (gluingCollarFinBandSourceSpeed_eq_sqrt r
                  (fun s => (α s).re) (fun s => (α s).im) t)
    _ = gluingCollarSourceLength r 0 1
          (fun s => (α s).re) (fun s => (α s).im) :=
            (gluingCollarSourceLength_eq_deriv_integral zero_le_one r hu hv).symm
    _ = _ := gluingCollarSourceLength_eq_curve_integral zero_le_one r hα

/-- Angular clamping sends every window-admissible path into a closed band
without increasing its weighted length. -/
theorem gluingCollarFiniteBandEDist_le_windowEDist
    {r R c ε : ℝ} (hε : 0 ≤ ε) {z w : ℂ}
    (hz : |z.im - c| ≤ ε) (hw : |w.im - c| ≤ ε) :
    gluingCollarFiniteBandEDist r R c ε z w ≤
      gluingCollarWindowAdmissibleEDist r R z w := by
  unfold gluingCollarWindowAdmissibleEDist
  refine le_iInf fun α => le_iInf fun h0 => le_iInf fun h1 =>
    le_iInf fun hLip => le_iInf fun hWindow => ?_
  obtain ⟨K, hK⟩ := hLip
  let β : ℝ → ℂ := fun t => gluingCollarAngularClamp c ε (α t)
  have hβ : LipschitzOnWith K β (Icc (0 : ℝ) 1) := by
    simpa only [β, Function.comp_def, one_mul] using
      (gluingCollarAngularClamp_lipschitz c ε).comp_lipschitzOnWith hK
  have hβ0 : β 0 = z := by
    dsimp [β]
    rw [h0]
    exact gluingCollarAngularClamp_eq_self hz
  have hβ1 : β 1 = w := by
    dsimp [β]
    rw [h1]
    exact gluingCollarAngularClamp_eq_self hw
  have hβWindow : ∀ t ∈ Icc (0 : ℝ) 1, (β t).re ∈ Icc (-R) R := by
    intro t ht
    simpa [β] using hWindow t ht
  have hβBand : ∀ t ∈ Icc (0 : ℝ) 1, |(β t).im - c| ≤ ε := by
    intro t _
    exact gluingCollarAngularClamp_mem_band hε (α t)
  have hlen : (∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
      (gluingCollarFinBandSourceSpeed r
        (fun s => (β s).re) (fun s => (β s).im) t)) ≤
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
        (gluingCollarFinBandSourceSpeed r
          (fun s => (α s).re) (fun s => (α s).im) t) := by
    apply lintegral_mono_ae
    filter_upwards [gluingCollarAngularClamp_sourceSpeed_le_ae
      (r := r) (c := c) (ε := ε) hK] with t ht
    exact ENNReal.ofReal_le_ofReal (by simpa only [β] using ht)
  calc
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
        (gluingCollarFinBandSourceSpeed r
          (fun s => (β s).re) (fun s => (β s).im) t) := by
            unfold gluingCollarFiniteBandEDist
            exact iInf_le_of_le β (iInf_le_of_le hβ0 (iInf_le_of_le hβ1
              (iInf_le_of_le (show ∃ K' : ℝ≥0,
                LipschitzOnWith K' β (Icc (0 : ℝ) 1) from ⟨K, hβ⟩)
                (iInf_le_of_le hβWindow (iInf_le_of_le hβBand le_rfl)))))
    _ ≤ _ := hlen
    _ = _ := gluingCollarFinBand_source_integral_eq_curve_integral r hK

/-- On endpoints of the closed band and radial window, restricting paths to
that band preserves the actual native collar distance. -/
theorem gluingCollarFiniteBandEDist_eq_native
    {r R c ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    {z w : ℂ} (hzWindow : z.re ∈ Icc (-R) R)
    (hwWindow : w.re ∈ Icc (-R) R)
    (hzBand : |z.im - c| ≤ ε) (hwBand : |w.im - c| ≤ ε) :
    gluingCollarFiniteBandEDist r R c ε z w =
      gluingCollarModelEDist hr z w := by
  apply le_antisymm
  · exact (gluingCollarFiniteBandEDist_le_windowEDist hε hzBand hwBand).trans
      (gluingCollarWindowAdmissibleEDist_eq_native hr hR hzWindow hwWindow).le
  · exact gluingCollarModelEDist_le_finiteBandEDist hr R c ε z w

/-- The generic target speed of the actual forward image is the speed used
in the fixed-band length estimate. -/
theorem gluingCollarFiniteStripSpeed_forward (r c lam : ℝ) (α : ℝ → ℂ) (t : ℝ) :
    gluingCollarFiniteStripSpeed lam
      (fun s => gluingCollarFinBandForward r c (α s)) t =
    gluingCollarFinBandTargetSpeed r lam c
      (fun s => (α s).re) (fun s => (α s).im) t := by
  simp [gluingCollarFiniteStripSpeed, gluingCollarFinBandTargetSpeed,
    gluingCollarFinBandForward_re, gluingCollarFinBandForward_im]

/-- Forward comparison of the actual constrained path infima on one band.
The multiplicative factor depends only on the radial window and band width. -/
theorem gluingCollarFiniteStripEDist_forward_le
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hlam : 0 ≤ lam) (hε : 0 ≤ ε) (c : ℝ) (z w : ℂ) :
    gluingCollarFiniteStripEDist r R lam ε
      (gluingCollarFinBandForward r c z)
      (gluingCollarFinBandForward r c w) ≤
    ENNReal.ofReal (1 + (Real.cosh (lam * (ε * Real.sinh (r + R))) - 1 +
      ε * Real.cosh (|r| + R))) *
      gluingCollarFiniteBandEDist r R c ε z w := by
  let D : ℝ := 1 + (Real.cosh (lam * (ε * Real.sinh (r + R))) - 1 +
    ε * Real.cosh (|r| + R))
  have hDpos : 0 < D := by
    dsimp [D]
    nlinarith [Real.one_le_cosh (lam * (ε * Real.sinh (r + R))),
      mul_nonneg hε (Real.cosh_pos (|r| + R)).le]
  have hD0 : ENNReal.ofReal D ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hDpos
  have hDtop : ENNReal.ofReal D ≠ ⊤ := by simp
  have hcurve : gluingCollarFiniteStripEDist r R lam ε
      (gluingCollarFinBandForward r c z)
      (gluingCollarFinBandForward r c w) ≤
      ⨅ (α : ℝ → ℂ) (_h0 : α 0 = z) (_h1 : α 1 = w)
        (_hLip : ∃ K : ℝ≥0, LipschitzOnWith K α (Icc (0 : ℝ) 1))
        (_hWindow : ∀ t ∈ Icc (0 : ℝ) 1, (α t).re ∈ Icc (-R) R)
        (_hBand : ∀ t ∈ Icc (0 : ℝ) 1, |(α t).im - c| ≤ ε),
        ENNReal.ofReal D *
          ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
            (gluingCollarFinBandSourceSpeed r
              (fun s => (α s).re) (fun s => (α s).im) t) := by
    refine le_iInf fun α => le_iInf fun h0 => le_iInf fun h1 =>
      le_iInf fun hLip => le_iInf fun hWindow => le_iInf fun hBand => ?_
    obtain ⟨K, hK⟩ := hLip
    let β : ℝ → ℂ := fun t => gluingCollarFinBandForward r c (α t)
    obtain ⟨K', hβ⟩ := gluingCollarFinBandForward_path_lipschitz
      hr hR hK hWindow hε hBand
    have hβ0 : β 0 = gluingCollarFinBandForward r c z := by simp [β, h0]
    have hβ1 : β 1 = gluingCollarFinBandForward r c w := by simp [β, h1]
    have hβWindow : ∀ t ∈ Icc (0 : ℝ) 1, (β t).re ∈ Icc (-R) R := by
      intro t ht
      simpa [β] using hWindow t ht
    have hβStrip : ∀ t ∈ Icc (0 : ℝ) 1,
        |(β t).im| ≤ ε * gluingCollarWarp r (β t).re := by
      intro t ht
      simpa [β] using gluingCollarFinBandForward_mem_strip hr c (α t) (hBand t ht)
    have hu : LipschitzOnWith K (fun t => (α t).re) (Icc (0 : ℝ) 1) := by
      simpa [Function.comp_def] using
        (RCLike.lipschitzWith_re (K := ℂ)).comp_lipschitzOnWith hK
    have hv : LipschitzOnWith K (fun t => (α t).im) (Icc (0 : ℝ) 1) := by
      simpa [Function.comp_def] using
        (RCLike.lipschitzWith_im (K := ℂ)).comp_lipschitzOnWith hK
    have hlen := gluingCollarFinBand_forward_length_le_mul
      hr zero_le_one hR hu hv hWindow hlam hε hBand
    have htarget : gluingCollarFiniteStripEDist r R lam ε
        (gluingCollarFinBandForward r c z)
        (gluingCollarFinBandForward r c w) ≤
        ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
          (gluingCollarFiniteStripSpeed lam β t) := by
      unfold gluingCollarFiniteStripEDist
      exact iInf_le_of_le β (iInf_le_of_le hβ0 (iInf_le_of_le hβ1
        (iInf_le_of_le (show ∃ K' : ℝ≥0,
          LipschitzOnWith K' β (Icc (0 : ℝ) 1) from ⟨K', hβ⟩)
          (iInf_le_of_le hβWindow (iInf_le_of_le hβStrip le_rfl)))))
    calc
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
          (gluingCollarFiniteStripSpeed lam β t) := htarget
      _ = ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
          (gluingCollarFinBandTargetSpeed r lam c
            (fun s => (α s).re) (fun s => (α s).im) t) := by
              congr 1
              funext t
              simpa only [β] using congrArg ENNReal.ofReal
                (gluingCollarFiniteStripSpeed_forward r c lam α t)
      _ ≤ _ := hlen
  calc
    _ ≤ _ := hcurve
    _ = ENNReal.ofReal D * gluingCollarFiniteBandEDist r R c ε z w := by
      unfold gluingCollarFiniteBandEDist
      simp only [ENNReal.mul_iInf_of_ne hD0 hDtop]

/-- The inverse map gives the reverse comparison on the same fixed piece.
This does not yet compare paths that cross between adjacent bands. -/
theorem gluingCollarFiniteBandEDist_inverse_le
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hε : 0 ≤ ε) (c : ℝ) (z w : ℂ) :
    gluingCollarFiniteBandEDist r R c ε
      (gluingCollarFinBandInverse r c z)
      (gluingCollarFinBandInverse r c w) ≤
    ENNReal.ofReal (1 + ε * Real.cosh (|r| + R)) *
      gluingCollarFiniteStripEDist r R lam ε z w := by
  let D : ℝ := 1 + ε * Real.cosh (|r| + R)
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hD0 : ENNReal.ofReal D ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hDpos
  have hDtop : ENNReal.ofReal D ≠ ⊤ := by simp
  have hcurve : gluingCollarFiniteBandEDist r R c ε
      (gluingCollarFinBandInverse r c z)
      (gluingCollarFinBandInverse r c w) ≤
      ⨅ (β : ℝ → ℂ) (_h0 : β 0 = z) (_h1 : β 1 = w)
        (_hLip : ∃ K : ℝ≥0, LipschitzOnWith K β (Icc (0 : ℝ) 1))
        (_hWindow : ∀ t ∈ Icc (0 : ℝ) 1, (β t).re ∈ Icc (-R) R)
        (_hStrip : ∀ t ∈ Icc (0 : ℝ) 1,
          |(β t).im| ≤ ε * gluingCollarWarp r (β t).re),
        ENNReal.ofReal D *
          ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
            (gluingCollarFiniteStripSpeed lam β t) := by
    refine le_iInf fun β => le_iInf fun h0 => le_iInf fun h1 =>
      le_iInf fun hLip => le_iInf fun hWindow => le_iInf fun hStrip => ?_
    obtain ⟨K, hK⟩ := hLip
    let α : ℝ → ℂ := fun t => gluingCollarFinBandInverse r c (β t)
    obtain ⟨K', hα⟩ := gluingCollarFinBandInverse_path_lipschitz
      hr hR hK hWindow hε hStrip (c := c)
    have hα0 : α 0 = gluingCollarFinBandInverse r c z := by simp [α, h0]
    have hα1 : α 1 = gluingCollarFinBandInverse r c w := by simp [α, h1]
    have hαWindow : ∀ t ∈ Icc (0 : ℝ) 1, (α t).re ∈ Icc (-R) R := by
      intro t ht
      simpa [α] using hWindow t ht
    have hαBand : ∀ t ∈ Icc (0 : ℝ) 1, |(α t).im - c| ≤ ε := by
      intro t ht
      simpa [α] using gluingCollarFinBandInverse_mem_band hr c (β t) (hStrip t ht)
    have hu : LipschitzOnWith K' (fun t => (α t).re) (Icc (0 : ℝ) 1) := by
      simpa [Function.comp_def, α] using
        (RCLike.lipschitzWith_re (K := ℂ)).comp_lipschitzOnWith hα
    have hv : LipschitzOnWith K' (fun t => (α t).im) (Icc (0 : ℝ) 1) := by
      simpa [Function.comp_def, α] using
        (RCLike.lipschitzWith_im (K := ℂ)).comp_lipschitzOnWith hα
    have hlen := gluingCollarFinBand_inverse_length_le_mul
      (r := r) (c := c) (lam := lam)
      zero_le_one hR hu hv hαWindow hε hαBand
    have hspeed (t : ℝ) :
        gluingCollarFinBandTargetSpeed r lam c
          (fun s => (α s).re) (fun s => (α s).im) t =
        gluingCollarFiniteStripSpeed lam β t := by
      calc
        _ = gluingCollarFiniteStripSpeed lam
              (fun s => gluingCollarFinBandForward r c (α s)) t :=
                (gluingCollarFiniteStripSpeed_forward r c lam α t).symm
        _ = _ := by
          congr 1
          funext s
          exact gluingCollarFinBandForward_inverse hr c (β s)
    have hsource : gluingCollarFiniteBandEDist r R c ε
        (gluingCollarFinBandInverse r c z)
        (gluingCollarFinBandInverse r c w) ≤
        ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
          (gluingCollarFinBandSourceSpeed r
            (fun s => (α s).re) (fun s => (α s).im) t) := by
      unfold gluingCollarFiniteBandEDist
      exact iInf_le_of_le α (iInf_le_of_le hα0 (iInf_le_of_le hα1
        (iInf_le_of_le (show ∃ K' : ℝ≥0,
          LipschitzOnWith K' α (Icc (0 : ℝ) 1) from ⟨K', hα⟩)
          (iInf_le_of_le hαWindow (iInf_le_of_le hαBand le_rfl)))))
    calc
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
          (gluingCollarFinBandSourceSpeed r
            (fun s => (α s).re) (fun s => (α s).im) t) := hsource
      _ ≤ ENNReal.ofReal D *
          ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
            (gluingCollarFinBandTargetSpeed r lam c
              (fun s => (α s).re) (fun s => (α s).im) t) := hlen
      _ = _ := by
        congr 1
        congr 1
        funext t
        exact congrArg ENNReal.ofReal (hspeed t)
  calc
    _ ≤ _ := hcurve
    _ = ENNReal.ofReal D * gluingCollarFiniteStripEDist r R lam ε z w := by
      unfold gluingCollarFiniteStripEDist
      simp only [ENNReal.mul_iInf_of_ne hD0 hDtop]

/-- The finite strip distance of two points in one source band is bounded
by the actual native collar distance times the explicit distortion. -/
theorem gluingCollarFiniteStripEDist_forward_le_native
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hlam : 0 ≤ lam) (hε : 0 ≤ ε) (c : ℝ) {z w : ℂ}
    (hzWindow : z.re ∈ Icc (-R) R) (hwWindow : w.re ∈ Icc (-R) R)
    (hzBand : |z.im - c| ≤ ε) (hwBand : |w.im - c| ≤ ε) :
    gluingCollarFiniteStripEDist r R lam ε
      (gluingCollarFinBandForward r c z)
      (gluingCollarFinBandForward r c w) ≤
    ENNReal.ofReal (1 + (Real.cosh (lam * (ε * Real.sinh (r + R))) - 1 +
      ε * Real.cosh (|r| + R))) *
      gluingCollarModelEDist hr z w := by
  simpa only [gluingCollarFiniteBandEDist_eq_native
    hr hR hε hzWindow hwWindow hzBand hwBand] using
      gluingCollarFiniteStripEDist_forward_le hr hR hlam hε c z w

/-- Conversely, the native collar distance of inverse images of strip
points is controlled by their finite strip distance. -/
theorem gluingCollarModelEDist_inverse_le_strip
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hε : 0 ≤ ε) (c : ℝ) {z w : ℂ}
    (hzWindow : z.re ∈ Icc (-R) R) (hwWindow : w.re ∈ Icc (-R) R)
    (hzStrip : |z.im| ≤ ε * gluingCollarWarp r z.re)
    (hwStrip : |w.im| ≤ ε * gluingCollarWarp r w.re) :
    gluingCollarModelEDist hr
      (gluingCollarFinBandInverse r c z)
      (gluingCollarFinBandInverse r c w) ≤
    ENNReal.ofReal (1 + ε * Real.cosh (|r| + R)) *
      gluingCollarFiniteStripEDist r R lam ε z w := by
  have hband := gluingCollarFiniteBandEDist_inverse_le
    hr hR hε c z w (lam := lam)
  rw [gluingCollarFiniteBandEDist_eq_native hr hR hε
    (by simpa using hzWindow) (by simpa using hwWindow)
    (gluingCollarFinBandInverse_mem_band hr c z hzStrip)
    (gluingCollarFinBandInverse_mem_band hr c w hwStrip)] at hband
  exact hband

/-- Capping a point of a finite Fermi strip vertically to its midline costs
at most its transverse coordinate. The straight cap remains inside the strip,
and its target Fermi speed is exactly constant. -/
theorem gluingCollarFiniteStripEDist_le_vertical_cap
    {r R lam ε : ℝ} {z : ℂ}
    (hzWindow : z.re ∈ Icc (-R) R)
    (hzStrip : |z.im| ≤ ε * gluingCollarWarp r z.re) :
    gluingCollarFiniteStripEDist r R lam ε z (z.re : ℂ) ≤
      ENNReal.ofReal |z.im| := by
  let β : ℝ → ℂ := fun s => ⟨z.re, z.im - s * z.im⟩
  have hβ0 : β 0 = z := by
    apply Complex.ext <;> simp [β]
  have hβ1 : β 1 = (z.re : ℂ) := by
    apply Complex.ext <;> simp [β]
  have hu : LipschitzOnWith 0 (fun _ : ℝ => z.re) (Icc (0 : ℝ) 1) := by
    exact LipschitzOnWith.of_dist_le_mul fun x _ y _ => by simp
  have hβlip : LipschitzOnWith (Real.toNNReal |z.im|)
      β (Icc (0 : ℝ) 1) := by
    apply LipschitzOnWith.of_dist_le'
    intro x hx y hy
    have hdiff : β x - β y = Complex.ofReal ((y - x) * z.im) * Complex.I := by
      apply Complex.ext
      · simp [β]
      · simp [β]
        ring
    have hnorm : ‖β x - β y‖ = |(y - x) * z.im| := by
      rw [hdiff]
      simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      rw [abs_mul]
    have hdist : dist (β x) (β y) = |z.im| * dist x y := by
      rw [dist_eq_norm, hnorm, abs_mul, Real.dist_eq, abs_sub_comm]
      ring
    exact hdist.le
  have hβwindow : ∀ s ∈ Icc (0 : ℝ) 1, (β s).re ∈ Icc (-R) R := by
    intro s hs
    simpa [β] using hzWindow
  have hβstrip : ∀ s ∈ Icc (0 : ℝ) 1,
      |(β s).im| ≤ ε * gluingCollarWarp r (β s).re := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have hfac0 : 0 ≤ 1 - s := by linarith
    have hfac1 : 1 - s ≤ 1 := by linarith
    rw [show (β s).im = (1 - s) * z.im by simp [β]; ring,
      abs_mul, abs_of_nonneg hfac0]
    calc
      (1 - s) * |z.im| ≤ 1 * |z.im| :=
        mul_le_mul_of_nonneg_right hfac1 (abs_nonneg _)
      _ = |z.im| := by ring
      _ ≤ ε * gluingCollarWarp r z.re := hzStrip
  have hβre_deriv (t : ℝ) : deriv (fun s => (β s).re) t = 0 := by
    simp [β]
  have hβim_deriv (t : ℝ) : deriv (fun s => (β s).im) t = -z.im := by
    have hfun : (fun s : ℝ => (β s).im) = fun s => z.im - s * z.im := rfl
    rw [hfun, deriv_const_sub, deriv_mul_const_field]
    simp
  have hspeed (t : ℝ) : gluingCollarFiniteStripSpeed lam β t = |z.im| := by
    simp [gluingCollarFiniteStripSpeed, hβre_deriv, hβim_deriv]
  unfold gluingCollarFiniteStripEDist
  refine iInf_le_of_le β (iInf_le_of_le hβ0 (iInf_le_of_le hβ1
    (iInf_le_of_le ⟨Real.toNNReal |z.im|, hβlip⟩
      (iInf_le_of_le hβwindow (iInf_le_of_le hβstrip ?_)))))
  calc
    (∫⁻ t in Icc (0 : ℝ) 1,
        ENNReal.ofReal (gluingCollarFiniteStripSpeed lam β t)) =
        ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal |z.im| := by
          congr 1
          funext t
          exact congrArg ENNReal.ofReal (hspeed t)
    _ = ENNReal.ofReal |z.im| := by
      simp only [MeasureTheory.setLIntegral_const, Real.volume_Icc,
        sub_zero, ENNReal.ofReal_one, mul_one]
  exact le_rfl

/-- If a target point lies in the finite strip, its vertical cap costs at
most the local strip half-width `ε * f(t)`. -/
theorem gluingCollarFiniteStripEDist_le_strip_width
    {r R lam ε : ℝ} {z : ℂ}
    (hzWindow : z.re ∈ Icc (-R) R)
    (hzStrip : |z.im| ≤ ε * gluingCollarWarp r z.re) :
    gluingCollarFiniteStripEDist r R lam ε z (z.re : ℂ) ≤
      ENNReal.ofReal (ε * gluingCollarWarp r z.re) := by
  calc
    gluingCollarFiniteStripEDist r R lam ε z (z.re : ℂ) ≤
        ENNReal.ofReal |z.im| :=
      gluingCollarFiniteStripEDist_le_vertical_cap hzWindow hzStrip
    _ ≤ ENNReal.ofReal (ε * gluingCollarWarp r z.re) :=
      ENNReal.ofReal_le_ofReal hzStrip

/-- The source collar has the matching vertical cap estimate: in the
warped metric, moving the angular coordinate to the band center costs at
most `ε * f(t)`. -/
theorem gluingCollarModelEDist_le_vertical_cap
    {r ε c : ℝ} (hr : 0 < r) {z : ℂ}
    (hzBand : |z.im - c| ≤ ε) :
    gluingCollarModelEDist hr z ⟨z.re, c⟩ ≤
      ENNReal.ofReal (ε * gluingCollarWarp r z.re) := by
  let u : ℝ → ℝ := fun _ => z.re
  let d : ℝ := z.im - c
  let v : ℝ → ℝ := fun s => c + (1 - s) * d
  have hu : LipschitzOnWith 0 u (Icc (0 : ℝ) 1) := by
    exact LipschitzOnWith.of_dist_le_mul fun x _ y _ => by simp [u]
  have hv : LipschitzOnWith (Real.toNNReal |d|) v (Icc (0 : ℝ) 1) := by
    apply LipschitzOnWith.of_dist_le'
    intro x hx y hy
    have hdiff : v x - v y = (y - x) * d := by
      simp [v]
      ring
    have hdist : dist (v x) (v y) = |d| * dist x y := by
      rw [Real.dist_eq, Real.dist_eq, hdiff, abs_mul, abs_sub_comm]
      ring
    exact hdist.le
  have hpath := gluingCollarModelEDist_le_sourceLength hr zero_le_one hu hv
  have hlength : gluingCollarSourceLength r 0 1 u v =
      ENNReal.ofReal (gluingCollarWarp r z.re * |d|) := by
    rw [gluingCollarSourceLength_eq_deriv_integral zero_le_one r hu hv]
    have hspeed (t : ℝ) : Real.sqrt
        (deriv u t ^ 2 + gluingCollarWarp r (u t) ^ 2 * deriv v t ^ 2) =
        gluingCollarWarp r z.re * |d| := by
      have hdu : deriv u t = 0 := by simp [u]
      have hdv : deriv v t = -d := by
        have hvfun : v = fun s => (c + d) - s * d := by
          funext s
          simp [v, d]
          ring
        rw [hvfun, deriv_const_sub, deriv_mul_const_field]
        simp
      have hwp := gluingCollarWarp_pos hr z.re
      have hrad : deriv u t ^ 2 + gluingCollarWarp r (u t) ^ 2 *
          deriv v t ^ 2 = (gluingCollarWarp r z.re * d) ^ 2 := by
        rw [hdu, hdv]
        simp [u]
        ring
      rw [hrad, Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos hwp]
    calc
      _ = ∫⁻ t in Icc (0 : ℝ) 1,
          ENNReal.ofReal (gluingCollarWarp r z.re * |d|) := by
            apply lintegral_congr_ae
            filter_upwards with t
            exact congrArg ENNReal.ofReal (hspeed t)
      _ = ENNReal.ofReal (gluingCollarWarp r z.re * |d|) := by
        simp only [MeasureTheory.setLIntegral_const, Real.volume_Icc,
          sub_zero, ENNReal.ofReal_one, mul_one]
  have hstart : (u 0 : ℂ) + (v 0 : ℂ) * Complex.I = z := by
    simp [u, v, d, Complex.re_add_im]
  have hend : (u 1 : ℂ) + (v 1 : ℂ) * Complex.I = ⟨z.re, c⟩ := by
    apply Complex.ext <;> simp [u, v]
  have hsource : gluingCollarModelEDist hr z ⟨z.re, c⟩ ≤
      gluingCollarSourceLength r 0 1 u v := by
    simpa only [hstart, hend] using hpath
  calc
    gluingCollarModelEDist hr z ⟨z.re, c⟩ ≤
        gluingCollarSourceLength r 0 1 u v := hsource
    _ = ENNReal.ofReal (gluingCollarWarp r z.re * |d|) := hlength
    _ ≤ ENNReal.ofReal (ε * gluingCollarWarp r z.re) := by
      apply ENNReal.ofReal_le_ofReal
      rw [mul_comm ε]
      exact mul_le_mul_of_nonneg_left hzBand
        (gluingCollarWarp_pos hr z.re).le

/-- In the finite approximation, the image of a point in one source band
can be capped to the image of its band center at cost at most `ε*f(t)`. -/
theorem gluingCollarFiniteStripEDist_forward_to_band_center_le
    {r R lam c ε : ℝ} (hr : 0 < r) {z : ℂ}
    (hzWindow : z.re ∈ Icc (-R) R)
    (hzBand : |z.im - c| ≤ ε) :
    gluingCollarFiniteStripEDist r R lam ε
      (gluingCollarFinBandForward r c z)
      (gluingCollarFinBandForward r c ⟨z.re, c⟩) ≤
      ENNReal.ofReal (ε * gluingCollarWarp r z.re) := by
  have hstrip := gluingCollarFinBandForward_mem_strip hr c z hzBand
  have hwindow :
      (gluingCollarFinBandForward r c z).re ∈ Icc (-R) R := by
    simpa using hzWindow
  have hstrip' : |(gluingCollarFinBandForward r c z).im| ≤
      ε * gluingCollarWarp r (gluingCollarFinBandForward r c z).re := by
    simpa using hstrip
  have hcap : gluingCollarFiniteStripEDist r R lam ε
      (gluingCollarFinBandForward r c z)
      ((gluingCollarFinBandForward r c z).re : ℂ) ≤
      ENNReal.ofReal (ε * gluingCollarWarp r z.re) := by
    simpa [gluingCollarFinBandForward_re] using
      gluingCollarFiniteStripEDist_le_strip_width (lam := lam) hwindow hstrip'
  have hmid : gluingCollarFinBandForward r c ⟨z.re, c⟩ = (z.re : ℂ) := by
    apply Complex.ext <;> simp [gluingCollarFinBandForward]
  rw [hmid]
  simpa only [gluingCollarFinBandForward_re] using hcap

/-- On a fixed radial window, the forward cap cost has one uniform bound
that tends to zero with the finite-band width. -/
theorem gluingCollarFiniteStripEDist_forward_to_band_center_le_window
    {r R lam c ε : ℝ} (hr : 0 < r) {z : ℂ}
    (hzWindow : z.re ∈ Icc (-R) R)
    (hzBand : |z.im - c| ≤ ε) :
    gluingCollarFiniteStripEDist r R lam ε
      (gluingCollarFinBandForward r c z)
      (gluingCollarFinBandForward r c ⟨z.re, c⟩) ≤
      ENNReal.ofReal (ε * Real.sinh (r + R)) := by
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) hzBand
  have hwarp := gluingCollarWarp_abs_le_window hr hzWindow
  rw [abs_of_pos (gluingCollarWarp_pos hr z.re)] at hwarp
  calc
    _ ≤ ENNReal.ofReal (ε * gluingCollarWarp r z.re) :=
      gluingCollarFiniteStripEDist_forward_to_band_center_le hr hzWindow hzBand
    _ ≤ ENNReal.ofReal (ε * Real.sinh (r + R)) :=
      ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hwarp hε)

/-- The matching source cap is uniform on every fixed radial window. -/
theorem gluingCollarModelEDist_le_vertical_cap_on_window
    {r R ε c : ℝ} (hr : 0 < r) {z : ℂ}
    (hzWindow : z.re ∈ Icc (-R) R)
    (hzBand : |z.im - c| ≤ ε) :
    gluingCollarModelEDist hr z ⟨z.re, c⟩ ≤
      ENNReal.ofReal (ε * Real.sinh (r + R)) := by
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) hzBand
  have hwarp := gluingCollarWarp_abs_le_window hr hzWindow
  rw [abs_of_pos (gluingCollarWarp_pos hr z.re)] at hwarp
  calc
    _ ≤ ENNReal.ofReal (ε * gluingCollarWarp r z.re) :=
      gluingCollarModelEDist_le_vertical_cap hr hzBand
    _ ≤ ENNReal.ofReal (ε * Real.sinh (r + R)) :=
      ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hwarp hε)

/-- The two adjacent band maps send their shared source boundary to the
reflected strip-boundary points used by the finite-piece identification. -/
theorem gluingCollarFinBand_adjacent_boundary_compatible
    (r c ε t : ℝ) :
    gluingCollarFiniteStripAdjacentBoundaryRelation
      (gluingCollarFinBandForward r c
        ((t : ℂ) + Complex.I * ((c + ε : ℝ) : ℂ)))
      (gluingCollarFinBandForward r (c + 2 * ε)
        ((t : ℂ) + Complex.I * ((c + ε : ℝ) : ℂ))) := by
  constructor
  · simp
  · simp only [gluingCollarFinBandForward_im, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero, Complex.add_im, Complex.mul_im]
    ring

/-- The reflected target boundary points identified across adjacent strips
have exactly the same source point under their respective inverse maps. -/
theorem gluingCollarFinBand_adjacent_inverse_boundary_agree
    {r : ℝ} (hr : 0 < r) (c ε t : ℝ) :
    gluingCollarFinBandInverse r c
      (gluingCollarFinBandForward r c
        ((t : ℂ) + Complex.I * ((c + ε : ℝ) : ℂ))) =
    gluingCollarFinBandInverse r (c + 2 * ε)
      (gluingCollarFinBandForward r (c + 2 * ε)
        ((t : ℂ) + Complex.I * ((c + ε : ℝ) : ℂ))) := by
  rw [gluingCollarFinBandInverse_forward hr,
    gluingCollarFinBandInverse_forward hr]

/-- The forward maps of any two band presentations of one source point agree
or are precisely the reflected adjacent target-boundary pair. -/
theorem gluingCollarFiniteBand_forward_overlap_compatible
    {r c ε : ℝ} (hε : 0 < ε) (z : ℂ) {n m : ℤ}
    (hn : |z.im - (c + 2 * (n : ℝ) * ε)| ≤ ε)
    (hm : |z.im - (c + 2 * (m : ℝ) * ε)| ≤ ε) :
    n = m ∧ gluingCollarFinBandForward r (c + 2 * (n : ℝ) * ε) z =
        gluingCollarFinBandForward r (c + 2 * (m : ℝ) * ε) z ∨
      gluingCollarFiniteStripAdjacentBoundaryRelation
        (gluingCollarFinBandForward r (c + 2 * (n : ℝ) * ε) z)
        (gluingCollarFinBandForward r (c + 2 * (m : ℝ) * ε) z) := by
  by_cases hnm : n = m
  · subst m
    exact Or.inl ⟨rfl, rfl⟩
  · rcases lt_or_gt_of_ne hnm with hlt | hgt
    · obtain ⟨hmeq, hboundary⟩ :=
        gluingCollarFiniteBand_overlap_eq_upper_boundary hε hn hm hlt
      subst m
      have hz : z = (z.re : ℂ) +
          Complex.I * ((c + 2 * (n : ℝ) * ε + ε : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hboundary]
      have hnext : c + 2 * ((n + 1 : ℤ) : ℝ) * ε =
          (c + 2 * (n : ℝ) * ε) + 2 * ε := by
        push_cast
        ring
      right
      rw [hz, hnext]
      exact gluingCollarFinBand_adjacent_boundary_compatible
        r (c + 2 * (n : ℝ) * ε) ε z.re
    · obtain ⟨hne, hboundary⟩ :=
        gluingCollarFiniteBand_overlap_eq_lower_boundary hε hn hm hgt
      have hz : z = (z.re : ℂ) +
          Complex.I * ((c + 2 * (m : ℝ) * ε + ε : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hboundary]
      have hnext : c + 2 * ((m + 1 : ℤ) : ℝ) * ε =
          (c + 2 * (m : ℝ) * ε) + 2 * ε := by
        push_cast
        ring
      have hrel := gluingCollarFinBand_adjacent_boundary_compatible
        r (c + 2 * (m : ℝ) * ε) ε z.re
      have hrel' :
          gluingCollarFiniteStripAdjacentBoundaryRelation
            (gluingCollarFinBandForward r (c + 2 * ((m + 1 : ℤ) : ℝ) * ε) z)
            (gluingCollarFinBandForward r (c + 2 * (m : ℝ) * ε) z) := by
        rw [hz, hnext]
        rcases hrel with ⟨hre, him⟩
        exact ⟨hre.symm, by rw [him]; ring⟩
      right
      simpa [hne] using hrel'

/-- The quotient identifies the two forward images of one adjacent source
band boundary. -/
private theorem gluingCollarFiniteBandTarget_mk_adjacent_boundary
    (r c ε t : ℝ) (n : ℤ) :
    Quotient.mk (Relation.EqvGen.setoid (gluingCollarFiniteBandTargetSeam r ε))
      (n, gluingCollarFinBandForward r (c + 2 * (n : ℝ) * ε)
        ((t : ℂ) + Complex.I *
          ((c + 2 * (n : ℝ) * ε + ε : ℝ) : ℂ))) =
    Quotient.mk (Relation.EqvGen.setoid (gluingCollarFiniteBandTargetSeam r ε))
      (n + 1, gluingCollarFinBandForward r
        (c + 2 * ((n + 1 : ℤ) : ℝ) * ε)
        ((t : ℂ) + Complex.I *
          ((c + 2 * (n : ℝ) * ε + ε : ℝ) : ℂ))) := by
  let z : ℂ := (t : ℂ) +
    Complex.I * ((c + 2 * (n : ℝ) * ε + ε : ℝ) : ℂ)
  have hcenter : c + 2 * ((n + 1 : ℤ) : ℝ) * ε =
      (c + 2 * (n : ℝ) * ε) + 2 * ε := by
    push_cast
    ring
  have hupper : gluingCollarFinBandForward r (c + 2 * (n : ℝ) * ε) z =
      (t : ℂ) + Complex.I * ((ε * gluingCollarWarp r t : ℝ) : ℂ) := by
    dsimp [z]
    apply Complex.ext
    · simp [gluingCollarFinBandForward]
    · simp only [gluingCollarFinBandForward_im, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, add_zero, Complex.add_im, Complex.mul_im]
      ring
  have hlower : gluingCollarFinBandForward r
      (c + 2 * ((n + 1 : ℤ) : ℝ) * ε) z =
      (t : ℂ) + Complex.I * (((-ε * gluingCollarWarp r t : ℝ) : ℂ)) := by
    rw [hcenter]
    dsimp [z]
    apply Complex.ext
    · simp [gluingCollarFinBandForward]
    · simp only [gluingCollarFinBandForward_im, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, add_zero, Complex.add_im, Complex.mul_im]
      ring
  change Quotient.mk _ (n, gluingCollarFinBandForward
      r (c + 2 * (n : ℝ) * ε) z) =
    Quotient.mk _ (n + 1, gluingCollarFinBandForward
      r (c + 2 * ((n + 1 : ℤ) : ℝ) * ε) z)
  apply Quotient.sound
  apply Relation.EqvGen.rel
  exact ⟨rfl, t, hupper, hlower⟩

/-- Any two band representations of one source point define the same point
of the quotient chain target. This makes the global bandwise map independent
of the chosen covering band. -/
theorem gluingCollarFiniteBandTarget_mk_eq_of_overlap
    {r c ε : ℝ} (hε : 0 < ε) (z : ℂ) {n m : ℤ}
    (hn : |z.im - (c + 2 * (n : ℝ) * ε)| ≤ ε)
    (hm : |z.im - (c + 2 * (m : ℝ) * ε)| ≤ ε) :
    Quotient.mk (Relation.EqvGen.setoid (gluingCollarFiniteBandTargetSeam r ε))
        (n, gluingCollarFinBandForward r (c + 2 * (n : ℝ) * ε) z) =
      Quotient.mk (Relation.EqvGen.setoid (gluingCollarFiniteBandTargetSeam r ε))
        (m, gluingCollarFinBandForward r (c + 2 * (m : ℝ) * ε) z) := by
  by_cases hnm : n = m
  · subst m
    rfl
  · rcases lt_or_gt_of_ne hnm with hlt | hgt
    · obtain ⟨hmeq, hboundary⟩ :=
        gluingCollarFiniteBand_overlap_eq_upper_boundary hε hn hm hlt
      subst m
      have hz : z = (z.re : ℂ) +
          Complex.I * ((c + 2 * (n : ℝ) * ε + ε : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hboundary]
      rw [hz]
      exact gluingCollarFiniteBandTarget_mk_adjacent_boundary
        r c ε z.re n
    · obtain ⟨hne, hboundary⟩ :=
        gluingCollarFiniteBand_overlap_eq_lower_boundary hε hn hm hgt
      have hz : z = (z.re : ℂ) +
          Complex.I * ((c + 2 * (m : ℝ) * ε + ε : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hboundary]
      rw [hz, hne]
      exact (gluingCollarFiniteBandTarget_mk_adjacent_boundary
        r c ε z.re m).symm

/-- A fixed choice of lattice band containing each angular coordinate. -/
noncomputable def gluingCollarFiniteBandChoiceIndex
    (c ε : ℝ) (hε : 0 < ε) (v : ℝ) : ℤ :=
  Classical.choose (exists_gluingCollarFiniteBand_center
    (c := c) (ε := ε) (v := v) hε)

theorem gluingCollarFiniteBandChoiceIndex_mem
    {c ε : ℝ} (hε : 0 < ε) (v : ℝ) :
    |v - (c + 2 * (gluingCollarFiniteBandChoiceIndex c ε hε v : ℝ) * ε)| ≤ ε :=
  Classical.choose_spec (exists_gluingCollarFiniteBand_center
    (c := c) (ε := ε) (v := v) hε)

/-- The global source-to-chain map chooses any covering band; overlap
compatibility makes the resulting quotient point independent of the choice. -/
noncomputable def gluingCollarFiniteBandTargetMap
    (r c ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    gluingCollarFiniteBandTarget r ε :=
  Quotient.mk _ (gluingCollarFiniteBandChoiceIndex c ε hε z.im,
    gluingCollarFinBandForward r
      (c + 2 * (gluingCollarFiniteBandChoiceIndex c ε hε z.im : ℝ) * ε) z)

/-- Any band containing the source point gives the same quotient target map
value as the chosen representative. -/
theorem gluingCollarFiniteBandTargetMap_eq_band_rep
    {r c ε : ℝ} (hε : 0 < ε) (z : ℂ) (n : ℤ)
    (hn : |z.im - (c + 2 * (n : ℝ) * ε)| ≤ ε) :
    gluingCollarFiniteBandTargetMap r c ε hε z =
      Quotient.mk _ (n, gluingCollarFinBandForward r
        (c + 2 * (n : ℝ) * ε) z) := by
  exact gluingCollarFiniteBandTarget_mk_eq_of_overlap hε z
    (gluingCollarFiniteBandChoiceIndex_mem hε z.im) hn

/-- Every chosen representative of the global band map lies in its actual
variable-width Fermi strip. -/
theorem gluingCollarFiniteBandTargetMap_rep_mem_strip
    {r c ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (z : ℂ) :
    |(gluingCollarFinBandForward r
      (c + 2 * (gluingCollarFiniteBandChoiceIndex c ε hε z.im : ℝ) * ε) z).im| ≤
      ε * gluingCollarWarp r z.re := by
  exact gluingCollarFinBandForward_mem_strip hr
    (c + 2 * (gluingCollarFiniteBandChoiceIndex c ε hε z.im : ℝ) * ε)
    z (gluingCollarFiniteBandChoiceIndex_mem hε z.im)

/-- The inverse coordinates agree on an actual adjacent seam pair. -/
theorem gluingCollarFiniteBandTargetSeam_inverse_eq
    {r ε : ℝ} (hr : 0 < r) (c : ℝ) {p q : ℤ × ℂ}
    (hpq : gluingCollarFiniteBandTargetSeam r ε p q) :
    gluingCollarFinBandInverse r (c + 2 * (p.1 : ℝ) * ε) p.2 =
      gluingCollarFinBandInverse r (c + 2 * (q.1 : ℝ) * ε) q.2 := by
  obtain ⟨hindex, t, hp, hq⟩ := hpq
  have hindex' : (q.1 : ℝ) = (p.1 : ℝ) + 1 := by
    exact_mod_cast hindex.symm
  have hf := (gluingCollarWarp_pos hr t).ne'
  rw [hp, hq]
  apply Complex.ext
  · simp
  · simp only [gluingCollarFinBandInverse_im, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, zero_add]
    rw [hindex']
    field_simp
    ring

/-- The inverse band coordinates descend through the generated seam relation.
Thus the source point is recovered without selecting a target representative. -/
noncomputable def gluingCollarFiniteBandTargetInverse
    {r : ℝ} (hr : 0 < r) (c ε : ℝ) :
    gluingCollarFiniteBandTarget r ε → ℂ :=
  Quotient.lift
    (fun p : ℤ × ℂ => gluingCollarFinBandInverse r (c + 2 * (p.1 : ℝ) * ε) p.2)
    (by
      intro p q hpq
      induction hpq with
      | rel p q hpq => exact gluingCollarFiniteBandTargetSeam_inverse_eq hr c hpq
      | refl => rfl
      | symm p q _ ih => exact ih.symm
      | trans p q s _ _ ihpq ihqs => exact ihpq.trans ihqs)

@[simp] theorem gluingCollarFiniteBandTargetInverse_mk
    {r : ℝ} (hr : 0 < r) (c ε : ℝ) (p : ℤ × ℂ) :
    gluingCollarFiniteBandTargetInverse hr c ε (Quotient.mk _ p) =
      gluingCollarFinBandInverse r (c + 2 * (p.1 : ℝ) * ε) p.2 := rfl

/-- The quotient-valued band map retains the exact source coordinates. -/
@[simp] theorem gluingCollarFiniteBandTargetInverse_map
    {r c ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (z : ℂ) :
    gluingCollarFiniteBandTargetInverse hr c ε
      (gluingCollarFiniteBandTargetMap r c ε hε z) = z := by
  exact gluingCollarFinBandInverse_forward hr _ z

theorem gluingCollarFiniteBandTargetMap_injective
    {r c ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    Function.Injective (gluingCollarFiniteBandTargetMap r c ε hε) := by
  intro z w hzw
  simpa only [gluingCollarFiniteBandTargetInverse_map hr hε] using
    congrArg (gluingCollarFiniteBandTargetInverse hr c ε) hzw

/-- Every genuine strip representative is recovered by the global band map
after inverse transport, including points of either reflected boundary. -/
theorem gluingCollarFiniteBandTargetMap_inverse_mk
    {r c ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (p : ℤ × ℂ)
    (hp : |p.2.im| ≤ ε * gluingCollarWarp r p.2.re) :
    gluingCollarFiniteBandTargetMap r c ε hε
        (gluingCollarFiniteBandTargetInverse hr c ε (Quotient.mk _ p)) =
      Quotient.mk _ p := by
  rw [gluingCollarFiniteBandTargetInverse_mk,
    gluingCollarFiniteBandTargetMap_eq_band_rep hε _ p.1
      (gluingCollarFinBandInverse_mem_band hr _ p.2 hp),
    gluingCollarFinBandForward_inverse hr]

/-- A genuine target point has a strip representative in the prescribed
radial window. This excludes the extra ambient points outside the strips. -/
def gluingCollarFiniteBandTargetAdmissible (r R ε : ℝ)
    (p : gluingCollarFiniteBandTarget r ε) : Prop :=
  ∃ n : ℤ, ∃ z : ℂ, z.re ∈ Icc (-R) R ∧
    |z.im| ≤ ε * gluingCollarWarp r z.re ∧ Quotient.mk _ (n, z) = p

/-- The actual bounded-window strip chain carrier. -/
abbrev gluingCollarFiniteBandChain (r R ε : ℝ) : Type :=
  {p : gluingCollarFiniteBandTarget r ε //
    gluingCollarFiniteBandTargetAdmissible r R ε p}

theorem gluingCollarFiniteBandTargetMap_admissible
    {r R c ε : ℝ} (hr : 0 < r) (hε : 0 < ε) {z : ℂ}
    (hz : z.re ∈ Icc (-R) R) :
    gluingCollarFiniteBandTargetAdmissible r R ε
      (gluingCollarFiniteBandTargetMap r c ε hε z) :=
  ⟨_, _, by simpa using hz,
    by simpa using gluingCollarFiniteBandTargetMap_rep_mem_strip hr hε z, rfl⟩

theorem gluingCollarFiniteBandTargetInverse_mem_window
    {r R ε : ℝ} (hr : 0 < r) (c : ℝ)
    {p : gluingCollarFiniteBandTarget r ε}
    (hp : gluingCollarFiniteBandTargetAdmissible r R ε p) :
    (gluingCollarFiniteBandTargetInverse hr c ε p).re ∈ Icc (-R) R := by
  obtain ⟨n, z, hz, _, rfl⟩ := hp
  simpa using hz

/-- Inverse transport and the global band map are exact inverses on every
admissible target point, rather than only on a chosen representative. -/
theorem gluingCollarFiniteBandTargetMap_inverse
    {r R c ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    {p : gluingCollarFiniteBandTarget r ε}
    (hp : gluingCollarFiniteBandTargetAdmissible r R ε p) :
    gluingCollarFiniteBandTargetMap r c ε hε
      (gluingCollarFiniteBandTargetInverse hr c ε p) = p := by
  obtain ⟨n, z, _, hzStrip, rfl⟩ := hp
  exact gluingCollarFiniteBandTargetMap_inverse_mk hr hε (n, z) hzStrip

/-- The strip chain and the original radial window have exactly the same
points; the distance comparison is a separate obligation. -/
noncomputable def gluingCollarFiniteBandChainEquiv
    {r R c ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    {z : ℂ // z.re ∈ Icc (-R) R} ≃ gluingCollarFiniteBandChain r R ε where
  toFun z := ⟨gluingCollarFiniteBandTargetMap r c ε hε z.1,
    gluingCollarFiniteBandTargetMap_admissible hr hε z.2⟩
  invFun p := ⟨gluingCollarFiniteBandTargetInverse hr c ε p.1,
    gluingCollarFiniteBandTargetInverse_mem_window hr c p.2⟩
  left_inv z := Subtype.ext (gluingCollarFiniteBandTargetInverse_map hr hε z.1)
  right_inv p := Subtype.ext (gluingCollarFiniteBandTargetMap_inverse hr hε p.2)

/-- A genuine minimizing window geodesic crosses every intermediate angular
level. Splitting at that point preserves its exact total native distance.
This permits induction across bands without subdividing an oscillatory curve. -/
theorem gluingCollarModelEDist_exists_angular_split
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) {x y : ℂ}
    (hx : x.re ∈ Icc (-R) R) (hy : y.re ∈ Icc (-R) R)
    {a : ℝ} (ha : a ∈ Icc x.im y.im) :
    ∃ z : ℂ, z.re ∈ Icc (-R) R ∧ z.im = a ∧
      gluingCollarModelEDist hr x y =
        gluingCollarModelEDist hr x z + gluingCollarModelEDist hr z y := by
  letI := gluingCollarModelMetricSpace hr
  letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
  letI := (gluingCollarModelMetricSpace hr).toUniformSpace
  obtain ⟨γ, hγ, hwindow⟩ :=
    gluingCollarModelMetric_exists_window_geodesic hr hR hx hy
  have hcont : Continuous (fun s : unitInterval => (γ s).im) :=
    Complex.continuous_im.comp γ.continuous
  have ha' : a ∈ Icc ((γ 0).im) ((γ 1).im) := by
    simpa only [γ.source, γ.target] using ha
  obtain ⟨s, hs⟩ := intermediate_value_univ (a := (0 : unitInterval))
    (b := (1 : unitInterval)) hcont ha'
  have hleft := hγ 0 s
  have hright := hγ s 1
  have hzero : ((0 : unitInterval) : ℝ) = 0 := rfl
  have hone : ((1 : unitInterval) : ℝ) = 1 := rfl
  simp only [γ.source, hzero,
    zero_sub, abs_neg, abs_of_nonneg s.property.1] at hleft
  simp only [γ.target, hone] at hright
  rw [abs_of_nonpos (sub_nonpos.mpr s.property.2)] at hright
  have hsum : dist x y = dist x (γ s) + dist (γ s) y := by
    rw [hleft, hright]
    ring
  have hed (v w : ℂ) :
      gluingCollarModelEDist hr v w = ENNReal.ofReal (dist v w) := by
    rw [← gluingCollarModelMetricSpace_edist hr v w, edist_dist]
  refine ⟨γ s, hwindow s, hs, ?_⟩
  rw [hed, hed, hed, hsum, ENNReal.ofReal_add dist_nonneg dist_nonneg]

/-- A symmetric triangular distance bound proved on every closed lattice
band extends to the whole radial window. Exact geodesic cuts pay for each
crossed band only once, so the distortion does not depend on their number. -/
theorem gluingCollarModelEDist_bandwise_bound
    {r R c ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hε : 0 < ε)
    (δ : ℂ → ℂ → ℝ≥0∞) (A : ℝ≥0∞)
    (htriangle : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (hcomm : ∀ x y, δ x y = δ y x)
    (hband : ∀ (n : ℤ) (x y : ℂ),
      x.re ∈ Icc (-R) R → y.re ∈ Icc (-R) R →
      |x.im - (c + 2 * (n : ℝ) * ε)| ≤ ε →
      |y.im - (c + 2 * (n : ℝ) * ε)| ≤ ε →
      δ x y ≤ A * gluingCollarModelEDist hr x y)
    {x y : ℂ} (hx : x.re ∈ Icc (-R) R) (hy : y.re ∈ Icc (-R) R) :
    δ x y ≤ A * gluingCollarModelEDist hr x y := by
  have hincreasing (k : ℕ) : ∀ (n : ℤ) (x y : ℂ),
      x.re ∈ Icc (-R) R → y.re ∈ Icc (-R) R →
      |x.im - (c + 2 * (n : ℝ) * ε)| ≤ ε →
      |y.im - (c + 2 * ((n + (k : ℤ) : ℤ) : ℝ) * ε)| ≤ ε →
      δ x y ≤ A * gluingCollarModelEDist hr x y := by
    induction k with
    | zero =>
        intro n x y hx hy hxn hyn
        exact hband n x y hx hy hxn (by simpa using hyn)
    | succ k ih =>
        intro n x y hx hy hxn hyn
        let a : ℝ := c + 2 * ((n + (k : ℤ) : ℤ) : ℝ) * ε + ε
        have hcast : ((n + (k : ℤ) : ℤ) : ℝ) = (n : ℝ) + (k : ℝ) := by
          push_cast
          rfl
        have hcast' : ((n + ((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) =
            (n : ℝ) + (k : ℝ) + 1 := by
          push_cast
          ring
        have ha : a ∈ Icc x.im y.im := by
          have hx' := (abs_le.mp hxn).2
          have hy' := (abs_le.mp hyn).1
          rw [hcast'] at hy'
          dsimp [a]
          rw [hcast]
          constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) k]
        obtain ⟨z, hz, hza, hsplit⟩ :=
          gluingCollarModelEDist_exists_angular_split hr hR hx hy ha
        have hzn : |z.im - (c + 2 * ((n + (k : ℤ) : ℤ) : ℝ) * ε)| ≤ ε := by
          rw [hza]
          dsimp [a]
          rw [add_sub_cancel_left, abs_of_pos hε]
        have hzn' :
            |z.im - (c + 2 * ((n + ((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) * ε)| ≤ ε := by
          have heq : a - (c + 2 * ((n + ((k + 1 : ℕ) : ℤ) : ℤ) : ℝ) * ε) =
              -ε := by
            dsimp [a]
            push_cast
            ring
          rw [hza, heq, abs_neg, abs_of_pos hε]
        calc
          δ x y ≤ δ x z + δ z y := htriangle x z y
          _ ≤ A * gluingCollarModelEDist hr x z +
              A * gluingCollarModelEDist hr z y :=
            add_le_add (ih n x z hx hz hxn hzn)
              (hband (n + ((k + 1 : ℕ) : ℤ)) z y hz hy hzn' hyn)
          _ = A * gluingCollarModelEDist hr x y := by rw [hsplit, mul_add]
  obtain ⟨n, hn⟩ := exists_gluingCollarFiniteBand_center (c := c) (v := x.im) hε
  obtain ⟨m, hm⟩ := exists_gluingCollarFiniteBand_center (c := c) (v := y.im) hε
  by_cases hnm : n ≤ m
  · let k : ℕ := (m - n).toNat
    have hmk : n + (k : ℤ) = m := by
      dsimp [k]
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hnm)]
      omega
    have h := hincreasing k n x y hx hy hn
    rw [hmk] at h
    exact h hm
  · have hmn : m ≤ n := le_of_lt (lt_of_not_ge hnm)
    let k : ℕ := (n - m).toNat
    have hnk : m + (k : ℤ) = n := by
      dsimp [k]
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hmn)]
      omega
    have h := hincreasing k m y x hy hx hm
    rw [hnk] at h
    have hxy := h hn
    rw [hcomm y x] at hxy
    have hnative : gluingCollarModelEDist hr y x = gluingCollarModelEDist hr x y := by
      letI := gluingCollarModelMetricSpace hr
      letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
      letI := (gluingCollarModelMetricSpace hr).toUniformSpace
      rw [← gluingCollarModelMetricSpace_edist hr y x,
        ← gluingCollarModelMetricSpace_edist hr x y, edist_comm]
    simpa only [hnative] using hxy

/-- Costs of finite walks through genuine strip copies, with their boundary
points identified by the target quotient. A strip step retains its constrained
path-infimum cost; concatenation adds costs and reversal preserves them. -/
inductive GluingCollarFiniteChainPath (r R lam ε : ℝ) :
    gluingCollarFiniteBandTarget r ε → gluingCollarFiniteBandTarget r ε →
      ℝ≥0∞ → Prop
  | refl (p) : GluingCollarFiniteChainPath r R lam ε p p 0
  | strip (n : ℤ) (z w : ℂ)
      (hzWindow : z.re ∈ Icc (-R) R) (hwWindow : w.re ∈ Icc (-R) R)
      (hzStrip : |z.im| ≤ ε * gluingCollarWarp r z.re)
      (hwStrip : |w.im| ≤ ε * gluingCollarWarp r w.re) :
      GluingCollarFiniteChainPath r R lam ε
        (Quotient.mk _ (n, z)) (Quotient.mk _ (n, w))
        (gluingCollarFiniteStripEDist r R lam ε z w)
  | symm {p q A} : GluingCollarFiniteChainPath r R lam ε p q A →
      GluingCollarFiniteChainPath r R lam ε q p A
  | trans {p q s A B} : GluingCollarFiniteChainPath r R lam ε p q A →
      GluingCollarFiniteChainPath r R lam ε q s B →
      GluingCollarFiniteChainPath r R lam ε p s (A + B)

/-- The intrinsic distance of the strip chain is the infimum of all finite
concatenation costs. The admissible carrier excludes ambient outside points. -/
noncomputable def gluingCollarFiniteChainEDist (r R lam ε : ℝ)
    (p q : gluingCollarFiniteBandTarget r ε) : ℝ≥0∞ :=
  ⨅ A : ℝ≥0∞, ⨅ _h : GluingCollarFiniteChainPath r R lam ε p q A, A

theorem gluingCollarFiniteChainEDist_le_cost
    {r R lam ε : ℝ} {p q : gluingCollarFiniteBandTarget r ε} {A : ℝ≥0∞}
    (h : GluingCollarFiniteChainPath r R lam ε p q A) :
    gluingCollarFiniteChainEDist r R lam ε p q ≤ A := by
  exact iInf_le_of_le A (iInf_le_of_le h le_rfl)

@[simp] theorem gluingCollarFiniteChainEDist_self (r R lam ε : ℝ)
    (p : gluingCollarFiniteBandTarget r ε) :
    gluingCollarFiniteChainEDist r R lam ε p p = 0 := by
  exact le_antisymm
    (gluingCollarFiniteChainEDist_le_cost (GluingCollarFiniteChainPath.refl p)) bot_le

theorem gluingCollarFiniteChainEDist_comm (r R lam ε : ℝ)
    (p q : gluingCollarFiniteBandTarget r ε) :
    gluingCollarFiniteChainEDist r R lam ε p q =
      gluingCollarFiniteChainEDist r R lam ε q p := by
  have h (p q : gluingCollarFiniteBandTarget r ε) :
      gluingCollarFiniteChainEDist r R lam ε p q ≤
        gluingCollarFiniteChainEDist r R lam ε q p := by
    refine le_iInf fun A => le_iInf fun hqp => ?_
    exact gluingCollarFiniteChainEDist_le_cost hqp.symm
  exact (h p q).antisymm (h q p)

theorem gluingCollarFiniteChainEDist_triangle (r R lam ε : ℝ)
    (p q s : gluingCollarFiniteBandTarget r ε) :
    gluingCollarFiniteChainEDist r R lam ε p s ≤
      gluingCollarFiniteChainEDist r R lam ε p q +
        gluingCollarFiniteChainEDist r R lam ε q s := by
  exact ENNReal.le_iInf₂_add_iInf₂ fun A hpq B hqs =>
    gluingCollarFiniteChainEDist_le_cost (hpq.trans hqs)

/-- Every local strip path contributes a genuine same-copy walk in the
quotient chain, including endpoints on either boundary. -/
theorem gluingCollarFiniteChainEDist_le_strip
    {r R lam ε : ℝ} (n : ℤ) {z w : ℂ}
    (hzWindow : z.re ∈ Icc (-R) R) (hwWindow : w.re ∈ Icc (-R) R)
    (hzStrip : |z.im| ≤ ε * gluingCollarWarp r z.re)
    (hwStrip : |w.im| ≤ ε * gluingCollarWarp r w.re) :
    gluingCollarFiniteChainEDist r R lam ε
        (Quotient.mk _ (n, z)) (Quotient.mk _ (n, w)) ≤
      gluingCollarFiniteStripEDist r R lam ε z w :=
  gluingCollarFiniteChainEDist_le_cost
    (GluingCollarFiniteChainPath.strip n z w hzWindow hwWindow hzStrip hwStrip)

/-- The local forward comparisons assemble across every crossed band with
one uniform distortion factor. There is no angular-distance restriction. -/
theorem gluingCollarFiniteChainEDist_forward_le_native
    {r R c lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hlam : 0 ≤ lam) (hε : 0 < ε) {x y : ℂ}
    (hx : x.re ∈ Icc (-R) R) (hy : y.re ∈ Icc (-R) R) :
    gluingCollarFiniteChainEDist r R lam ε
        (gluingCollarFiniteBandTargetMap r c ε hε x)
        (gluingCollarFiniteBandTargetMap r c ε hε y) ≤
      ENNReal.ofReal (1 + (Real.cosh (lam * (ε * Real.sinh (r + R))) - 1 +
        ε * Real.cosh (|r| + R))) * gluingCollarModelEDist hr x y := by
  apply gluingCollarModelEDist_bandwise_bound (c := c) hr hR hε
    (fun z w => gluingCollarFiniteChainEDist r R lam ε
      (gluingCollarFiniteBandTargetMap r c ε hε z)
      (gluingCollarFiniteBandTargetMap r c ε hε w)) _
    (fun z w s => gluingCollarFiniteChainEDist_triangle r R lam ε _ _ _)
    (fun z w => gluingCollarFiniteChainEDist_comm r R lam ε _ _) ?_ hx hy
  intro n z w hz hw hzn hwn
  rw [gluingCollarFiniteBandTargetMap_eq_band_rep hε z n hzn,
    gluingCollarFiniteBandTargetMap_eq_band_rep hε w n hwn]
  calc
    _ ≤ gluingCollarFiniteStripEDist r R lam ε
        (gluingCollarFinBandForward r (c + 2 * (n : ℝ) * ε) z)
        (gluingCollarFinBandForward r (c + 2 * (n : ℝ) * ε) w) :=
      gluingCollarFiniteChainEDist_le_strip n (by simpa using hz) (by simpa using hw)
        (by simpa only [gluingCollarFinBandForward_re] using
          gluingCollarFinBandForward_mem_strip hr _ z hzn)
        (by simpa only [gluingCollarFinBandForward_re] using
          gluingCollarFinBandForward_mem_strip hr _ w hwn)
    _ ≤ _ := gluingCollarFiniteStripEDist_forward_le_native
      hr hR hlam hε.le _ hz hw hzn hwn

/-- Every pair of genuine bounded-window target points has finite chain
distance, as follows from the global source-to-chain comparison. -/
theorem gluingCollarFiniteChainEDist_lt_top
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hlam : 0 ≤ lam) (hε : 0 < ε)
    {p q : gluingCollarFiniteBandTarget r ε}
    (hp : gluingCollarFiniteBandTargetAdmissible r R ε p)
    (hq : gluingCollarFiniteBandTargetAdmissible r R ε q) :
    gluingCollarFiniteChainEDist r R lam ε p q < ⊤ := by
  have h := gluingCollarFiniteChainEDist_forward_le_native
    (c := 0) hr hR hlam hε
    (gluingCollarFiniteBandTargetInverse_mem_window hr 0 hp)
    (gluingCollarFiniteBandTargetInverse_mem_window hr 0 hq)
  rw [gluingCollarFiniteBandTargetMap_inverse hr hε hp,
    gluingCollarFiniteBandTargetMap_inverse hr hε hq] at h
  exact h.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (gluingCollarModelEDist_lt_top hr _ _))

/-- Every finite target walk pulls back to a source distance bound. The
proof uses the actual inverse on seam classes and adds the costs of all steps. -/
theorem gluingCollarFiniteChain_inverse_le_cost
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hε : 0 ≤ ε) (c : ℝ)
    {p q : gluingCollarFiniteBandTarget r ε} {A : ℝ≥0∞}
    (h : GluingCollarFiniteChainPath r R lam ε p q A) :
    gluingCollarModelEDist hr
        (gluingCollarFiniteBandTargetInverse hr c ε p)
        (gluingCollarFiniteBandTargetInverse hr c ε q) ≤
      ENNReal.ofReal (1 + ε * Real.cosh (|r| + R)) * A := by
  letI := gluingCollarModelMetricSpace hr
  letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
  letI := (gluingCollarModelMetricSpace hr).toUniformSpace
  have hed (x y : ℂ) : gluingCollarModelEDist hr x y = edist x y :=
    (gluingCollarModelMetricSpace_edist hr x y).symm
  induction h with
  | refl p => simp only [hed, edist_self, mul_zero, le_refl]
  | strip n z w hz hw hzs hws =>
      simpa only [gluingCollarFiniteBandTargetInverse_mk] using
        gluingCollarModelEDist_inverse_le_strip hr hR hε
          (c + 2 * (n : ℝ) * ε) hz hw hzs hws
  | symm h ih => simpa only [hed, edist_comm] using ih
  | trans hpq hqs ihpq ihqs =>
      calc
        _ ≤ gluingCollarModelEDist hr _ _ + gluingCollarModelEDist hr _ _ := by
          simp only [hed]
          exact edist_triangle _ _ _
        _ ≤ _ := add_le_add ihpq ihqs
        _ = _ := (mul_add _ _ _).symm

/-- The reverse comparison holds for the whole quotient chain, including
paths crossing arbitrarily many adjacent strips. -/
theorem gluingCollarModelEDist_inverse_le_chain
    {r R lam ε : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hε : 0 ≤ ε) (c : ℝ)
    (p q : gluingCollarFiniteBandTarget r ε) :
    gluingCollarModelEDist hr
        (gluingCollarFiniteBandTargetInverse hr c ε p)
        (gluingCollarFiniteBandTargetInverse hr c ε q) ≤
      ENNReal.ofReal (1 + ε * Real.cosh (|r| + R)) *
        gluingCollarFiniteChainEDist r R lam ε p q := by
  have hDpos : 0 < 1 + ε * Real.cosh (|r| + R) := by positivity
  have hD0 := ENNReal.ofReal_ne_zero_iff.mpr hDpos
  unfold gluingCollarFiniteChainEDist
  simp only [ENNReal.mul_iInf_of_ne hD0 ENNReal.ofReal_ne_top]
  exact le_iInf fun A => le_iInf fun h =>
    gluingCollarFiniteChain_inverse_le_cost hr hR hε c h

#print axioms gluingCollarFinBandSourceSpeed_eq_sqrt
#print axioms gluingCollarModelEDist_le_finiteBandEDist
#print axioms gluingCollarAngularClamp_sourceSpeed_le_ae
#print axioms gluingCollarFiniteBandEDist_eq_native
#print axioms gluingCollarFiniteStripSpeed_forward
#print axioms gluingCollarFiniteStripEDist_forward_le
#print axioms gluingCollarFiniteBandEDist_inverse_le
#print axioms gluingCollarFiniteStripEDist_forward_le_native
#print axioms gluingCollarModelEDist_inverse_le_strip
#print axioms gluingCollarFiniteStripEDist_le_vertical_cap
#print axioms gluingCollarFiniteStripEDist_le_strip_width
#print axioms gluingCollarModelEDist_le_vertical_cap
#print axioms gluingCollarFiniteStripEDist_forward_to_band_center_le
#print axioms gluingCollarFiniteStripEDist_forward_to_band_center_le_window
#print axioms gluingCollarModelEDist_le_vertical_cap_on_window
#print axioms gluingCollarFinBand_adjacent_boundary_compatible
#print axioms gluingCollarFinBand_adjacent_inverse_boundary_agree
#print axioms exists_gluingCollarFiniteBand_center
#print axioms exists_gluingCollarFiniteBand_range_bound
#print axioms exists_gluingCollarFiniteBand_path_range_bound
#print axioms gluingCollarFiniteBand_overlap_eq_upper_boundary
#print axioms gluingCollarFiniteBand_overlap_eq_lower_boundary
#print axioms gluingCollarFiniteBand_forward_overlap_compatible
#print axioms gluingCollarFiniteBandTarget_mk_eq_of_overlap
#print axioms gluingCollarFiniteBandTargetMap_eq_band_rep
#print axioms gluingCollarFiniteBandTargetMap_rep_mem_strip
#print axioms gluingCollarFiniteBandTargetSeam_inverse_eq
#print axioms gluingCollarFiniteBandTargetInverse_map
#print axioms gluingCollarFiniteBandTargetMap_injective
#print axioms gluingCollarFiniteBandTargetMap_inverse_mk
#print axioms gluingCollarFiniteBandTargetMap_admissible
#print axioms gluingCollarFiniteBandTargetMap_inverse
#print axioms gluingCollarFiniteBandChainEquiv
#print axioms gluingCollarModelEDist_exists_angular_split
#print axioms gluingCollarModelEDist_bandwise_bound
#print axioms gluingCollarFiniteChainEDist_self
#print axioms gluingCollarFiniteChainEDist_triangle
#print axioms gluingCollarFiniteChainEDist_comm
#print axioms gluingCollarFiniteChainEDist_le_strip
#print axioms gluingCollarFiniteChainEDist_forward_le_native
#print axioms gluingCollarFiniteChainEDist_lt_top
#print axioms gluingCollarFiniteChain_inverse_le_cost
#print axioms gluingCollarModelEDist_inverse_le_chain

end SystolicGrowth

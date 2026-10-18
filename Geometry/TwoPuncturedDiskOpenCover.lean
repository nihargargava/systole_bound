module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

@[expose] public section

/-!
# Convex two-open-cover of a twice-punctured disk

Split the unit disk across an open horizontal band separating two punctures
on the imaginary axis. Each side before its one puncture is removed is convex;
the overlap is a nonempty convex strip and hence contractible.
-/

open Set

namespace SystolicGrowth

noncomputable section

/-- The lower retained center on the imaginary axis. -/
def twoPuncturedDiskLeftCenter (α : ℝ) : ℂ := (α : ℂ) * Complex.I

/-- The upper retained center on the imaginary axis. -/
def twoPuncturedDiskRightCenter (β : ℝ) : ℂ := (β : ℂ) * Complex.I

/-- Lower edge of the overlap band, one quarter of the gap above `α`. -/
def twoPuncturedDiskOverlapLower (α β : ℝ) : ℝ :=
  (α + β) / 2 - (β - α) / 4

/-- Upper edge of the overlap band, one quarter of the gap below `β`. -/
def twoPuncturedDiskOverlapUpper (α β : ℝ) : ℝ :=
  (α + β) / 2 + (β - α) / 4

/-- The original disk with both centers removed. -/
def twoPuncturedUnitDisk (α β : ℝ) : Set ℂ :=
  {z | z ∈ Metric.ball (0 : ℂ) 1 ∧ z ≠ twoPuncturedDiskLeftCenter α ∧
    z ≠ twoPuncturedDiskRightCenter β}

/-- The unpunctured lower side domain. -/
def twoPuncturedDiskLowerBase (α β : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) 1 ∩ {z | z.im < twoPuncturedDiskOverlapUpper α β}

/-- The unpunctured upper side domain. -/
def twoPuncturedDiskUpperBase (α β : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) 1 ∩ {z | twoPuncturedDiskOverlapLower α β < z.im}

/-- The lower member of the cover, with only its retained center deleted. -/
def twoPuncturedDiskLowerSide (α β : ℝ) : Set ℂ :=
  {z | z ∈ twoPuncturedDiskLowerBase α β ∧
    z ≠ twoPuncturedDiskLeftCenter α}

/-- The upper member of the cover, with only its retained center deleted. -/
def twoPuncturedDiskUpperSide (α β : ℝ) : Set ℂ :=
  {z | z ∈ twoPuncturedDiskUpperBase α β ∧
    z ≠ twoPuncturedDiskRightCenter β}

/-- The explicit open strip which is the overlap. -/
def twoPuncturedDiskOverlap (α β : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) 1 ∩ {z | twoPuncturedDiskOverlapLower α β < z.im ∧
    z.im < twoPuncturedDiskOverlapUpper α β}

theorem twoPuncturedDiskOverlap_bounds {α β : ℝ} (hαβ : α < β) :
    α < twoPuncturedDiskOverlapLower α β ∧
    twoPuncturedDiskOverlapLower α β < twoPuncturedDiskOverlapUpper α β ∧
    twoPuncturedDiskOverlapUpper α β < β := by
  dsimp [twoPuncturedDiskOverlapLower, twoPuncturedDiskOverlapUpper]
  constructor <;> [linarith; constructor <;> linarith]

theorem twoPuncturedDiskLeftCenter_im (α : ℝ) :
    (twoPuncturedDiskLeftCenter α).im = α := by
  simp [twoPuncturedDiskLeftCenter]

theorem twoPuncturedDiskRightCenter_im (β : ℝ) :
    (twoPuncturedDiskRightCenter β).im = β := by
  simp [twoPuncturedDiskRightCenter]

theorem twoPuncturedDiskLeftCenter_norm (α : ℝ) :
    ‖twoPuncturedDiskLeftCenter α‖ = |α| := by
  simp [twoPuncturedDiskLeftCenter]

theorem twoPuncturedDiskRightCenter_norm (β : ℝ) :
    ‖twoPuncturedDiskRightCenter β‖ = |β| := by
  simp [twoPuncturedDiskRightCenter]

theorem twoPuncturedDiskLowerBase_convex (α β : ℝ) :
    Convex ℝ (twoPuncturedDiskLowerBase α β) := by
  have him : Convex ℝ {z : ℂ | z.im < twoPuncturedDiskOverlapUpper α β} := by
    change Convex ℝ (Complex.im ⁻¹' Set.Iio (twoPuncturedDiskOverlapUpper α β))
    exact (convex_Iio _).linear_preimage Complex.imLm
  simpa [twoPuncturedDiskLowerBase] using
    (convex_ball (0 : ℂ) 1).inter him

theorem twoPuncturedDiskUpperBase_convex (α β : ℝ) :
    Convex ℝ (twoPuncturedDiskUpperBase α β) := by
  have him : Convex ℝ {z : ℂ | twoPuncturedDiskOverlapLower α β < z.im} := by
    change Convex ℝ (Complex.im ⁻¹' Set.Ioi (twoPuncturedDiskOverlapLower α β))
    exact (convex_Ioi _).linear_preimage Complex.imLm
  simpa [twoPuncturedDiskUpperBase] using
    (convex_ball (0 : ℂ) 1).inter him

theorem twoPuncturedDiskLeftCenter_mem_lowerBase {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β) :
    twoPuncturedDiskLeftCenter α ∈ twoPuncturedDiskLowerBase α β := by
  refine ⟨?_, ?_⟩
  · change dist (twoPuncturedDiskLeftCenter α) 0 < 1
    rw [dist_zero_right, twoPuncturedDiskLeftCenter_norm]
    exact (abs_lt.mpr ⟨hα, hα1⟩)
  · change (twoPuncturedDiskLeftCenter α).im < twoPuncturedDiskOverlapUpper α β
    rw [twoPuncturedDiskLeftCenter_im]
    exact (twoPuncturedDiskOverlap_bounds hαβ).1.trans
      (twoPuncturedDiskOverlap_bounds hαβ).2.1

theorem twoPuncturedDiskRightCenter_mem_upperBase {α β : ℝ}
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β) :
    twoPuncturedDiskRightCenter β ∈ twoPuncturedDiskUpperBase α β := by
  refine ⟨?_, ?_⟩
  · change dist (twoPuncturedDiskRightCenter β) 0 < 1
    rw [dist_zero_right, twoPuncturedDiskRightCenter_norm]
    exact (abs_lt.mpr ⟨hβ, hβ1⟩)
  · change twoPuncturedDiskOverlapLower α β < (twoPuncturedDiskRightCenter β).im
    rw [twoPuncturedDiskRightCenter_im]
    exact (twoPuncturedDiskOverlap_bounds hαβ).2.1.trans
      (twoPuncturedDiskOverlap_bounds hαβ).2.2

theorem twoPuncturedDiskRightCenter_not_lowerBase {α β : ℝ}
    (hαβ : α < β) :
    twoPuncturedDiskRightCenter β ∉ twoPuncturedDiskLowerBase α β := by
  intro hz
  change twoPuncturedDiskRightCenter β ∈ Metric.ball (0 : ℂ) 1 ∧
    (twoPuncturedDiskRightCenter β).im < twoPuncturedDiskOverlapUpper α β at hz
  have hcut := hz.2
  rw [twoPuncturedDiskRightCenter_im] at hcut
  exact (not_lt_of_ge (twoPuncturedDiskOverlap_bounds hαβ).2.2.le) hcut

theorem twoPuncturedDiskLeftCenter_not_upperBase {α β : ℝ}
    (hαβ : α < β) :
    twoPuncturedDiskLeftCenter α ∉ twoPuncturedDiskUpperBase α β := by
  intro hz
  change twoPuncturedDiskLeftCenter α ∈ Metric.ball (0 : ℂ) 1 ∧
    twoPuncturedDiskOverlapLower α β < (twoPuncturedDiskLeftCenter α).im at hz
  have hcut := hz.2
  rw [twoPuncturedDiskLeftCenter_im] at hcut
  exact (not_lt_of_ge (twoPuncturedDiskOverlap_bounds hαβ).1.le) hcut

theorem twoPuncturedDiskLowerBase_isOpen (α β : ℝ) :
    IsOpen (twoPuncturedDiskLowerBase α β) := by
  have him : IsOpen {z : ℂ | z.im < twoPuncturedDiskOverlapUpper α β} :=
    isOpen_Iio.preimage Complex.continuous_im
  simpa [twoPuncturedDiskLowerBase] using
    Metric.isOpen_ball.inter him

theorem twoPuncturedDiskUpperBase_isOpen (α β : ℝ) :
    IsOpen (twoPuncturedDiskUpperBase α β) := by
  have him : IsOpen {z : ℂ | twoPuncturedDiskOverlapLower α β < z.im} :=
    isOpen_Ioi.preimage Complex.continuous_im
  simpa [twoPuncturedDiskUpperBase] using
    Metric.isOpen_ball.inter him

theorem twoPuncturedDiskLowerSide_isOpen (α β : ℝ) :
    IsOpen (twoPuncturedDiskLowerSide α β) := by
  change IsOpen (twoPuncturedDiskLowerBase α β ∩
    ({twoPuncturedDiskLeftCenter α} : Set ℂ)ᶜ)
  exact (twoPuncturedDiskLowerBase_isOpen α β).inter isClosed_singleton.isOpen_compl

theorem twoPuncturedDiskUpperSide_isOpen (α β : ℝ) :
    IsOpen (twoPuncturedDiskUpperSide α β) := by
  change IsOpen (twoPuncturedDiskUpperBase α β ∩
    ({twoPuncturedDiskRightCenter β} : Set ℂ)ᶜ)
  exact (twoPuncturedDiskUpperBase_isOpen α β).inter isClosed_singleton.isOpen_compl

theorem twoPuncturedDiskLowerSide_subset_domain {α β : ℝ}
    (hαβ : α < β) :
    twoPuncturedDiskLowerSide α β ⊆ twoPuncturedUnitDisk α β := by
  intro z hz
  refine ⟨hz.1.1, hz.2, ?_⟩
  intro hq
  have hlow := hz.1.2
  change z.im < twoPuncturedDiskOverlapUpper α β at hlow
  rw [hq, twoPuncturedDiskRightCenter_im] at hlow
  exact (not_lt_of_ge (twoPuncturedDiskOverlap_bounds hαβ).2.2.le) hlow

theorem twoPuncturedDiskUpperSide_subset_domain {α β : ℝ}
    (hαβ : α < β) :
    twoPuncturedDiskUpperSide α β ⊆ twoPuncturedUnitDisk α β := by
  intro z hz
  refine ⟨hz.1.1, ?_, hz.2⟩
  intro hp
  have hhigh := hz.1.2
  change twoPuncturedDiskOverlapLower α β < z.im at hhigh
  rw [hp, twoPuncturedDiskLeftCenter_im] at hhigh
  exact (not_lt_of_ge (twoPuncturedDiskOverlap_bounds hαβ).1.le) hhigh

theorem twoPuncturedDisk_lower_upper_cover {α β : ℝ}
    (hαβ : α < β) :
    twoPuncturedUnitDisk α β =
      twoPuncturedDiskLowerSide α β ∪ twoPuncturedDiskUpperSide α β := by
  ext z
  constructor
  · rintro ⟨hz, hp, hq⟩
    by_cases hcut : z.im < twoPuncturedDiskOverlapUpper α β
    · left
      exact ⟨⟨hz, hcut⟩, hp⟩
    · right
      refine ⟨⟨hz, ?_⟩, hq⟩
      exact lt_of_lt_of_le (twoPuncturedDiskOverlap_bounds hαβ).2.1
        (le_of_not_gt hcut)
  · rintro (hz | hz)
    · exact twoPuncturedDiskLowerSide_subset_domain hαβ hz
    · exact twoPuncturedDiskUpperSide_subset_domain hαβ hz

theorem twoPuncturedDisk_overlap_eq_strip {α β : ℝ}
    (hαβ : α < β) :
    twoPuncturedDiskLowerSide α β ∩ twoPuncturedDiskUpperSide α β =
      twoPuncturedDiskOverlap α β := by
  ext z
  constructor
  · rintro ⟨hzL, hzU⟩
    exact ⟨hzL.1.1, hzU.1.2, hzL.1.2⟩
  · rintro ⟨hz, hlow, hhigh⟩
    refine ⟨⟨⟨hz, hhigh⟩, ?_⟩, ⟨⟨hz, hlow⟩, ?_⟩⟩
    · intro hp
      rw [hp, twoPuncturedDiskLeftCenter_im] at hlow
      exact (not_lt_of_ge (twoPuncturedDiskOverlap_bounds hαβ).1.le) hlow
    · intro hq
      rw [hq, twoPuncturedDiskRightCenter_im] at hhigh
      exact (not_lt_of_ge (twoPuncturedDiskOverlap_bounds hαβ).2.2.le) hhigh

theorem twoPuncturedDiskOverlap_convex (α β : ℝ) :
    Convex ℝ (twoPuncturedDiskOverlap α β) := by
  have hstrip : Convex ℝ {z : ℂ |
      twoPuncturedDiskOverlapLower α β < z.im ∧
      z.im < twoPuncturedDiskOverlapUpper α β} := by
    change Convex ℝ (Complex.im ⁻¹' Set.Ioo
      (twoPuncturedDiskOverlapLower α β) (twoPuncturedDiskOverlapUpper α β))
    exact (convex_Ioo _ _).linear_preimage Complex.imLm
  simpa [twoPuncturedDiskOverlap] using
    (convex_ball (0 : ℂ) 1).inter hstrip

private theorem twoPuncturedDiskOverlap_center_mem {α β : ℝ}
    (hα : -1 < α) (_hα1 : α < 1) (_hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β) :
    (((α + β) / 2 : ℝ) : ℂ) * Complex.I ∈ twoPuncturedDiskOverlap α β := by
  let c := (α + β) / 2
  have hc : -1 < c ∧ c < 1 := by dsimp [c]; constructor <;> linarith
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · change dist ((((α + β) / 2 : ℝ) : ℂ) * Complex.I) 0 < 1
    rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one]
    exact (abs_lt.mpr hc)
  · have hb := twoPuncturedDiskOverlap_bounds hαβ
    dsimp [c, twoPuncturedDiskOverlapLower]
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, add_zero, mul_one]
    linarith
  · have hb := twoPuncturedDiskOverlap_bounds hαβ
    dsimp [c, twoPuncturedDiskOverlapUpper]
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, add_zero, mul_one]
    linarith

theorem twoPuncturedDiskOverlap_nonempty {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β) : (twoPuncturedDiskOverlap α β).Nonempty :=
  ⟨((α + β) / 2 : ℝ) * Complex.I,
    twoPuncturedDiskOverlap_center_mem hα hα1 hβ hβ1 hαβ⟩

theorem twoPuncturedDiskOverlap_contractible {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β) : ContractibleSpace (twoPuncturedDiskOverlap α β) :=
  (twoPuncturedDiskOverlap_convex α β).contractibleSpace
    (twoPuncturedDiskOverlap_nonempty hα hα1 hβ hβ1 hαβ)

theorem twoPuncturedDiskOverlap_simplyConnected {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β) : SimplyConnectedSpace (twoPuncturedDiskOverlap α β) := by
  letI := twoPuncturedDiskOverlap_contractible hα hα1 hβ hβ1 hαβ
  infer_instance

theorem twoPuncturedDiskOverlap_pathConnected {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β) : PathConnectedSpace (twoPuncturedDiskOverlap α β) := by
  letI := twoPuncturedDiskOverlap_contractible hα hα1 hβ hβ1 hαβ
  infer_instance

theorem twoPuncturedDiskOverlap_fundamentalGroup_subsingleton {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β) (x : twoPuncturedDiskOverlap α β) :
    Subsingleton (FundamentalGroup (twoPuncturedDiskOverlap α β) x) := by
  letI := twoPuncturedDiskOverlap_simplyConnected hα hα1 hβ hβ1 hαβ
  infer_instance

#print axioms twoPuncturedDiskLowerBase_convex
#print axioms twoPuncturedDiskUpperBase_convex
#print axioms twoPuncturedDiskLowerSide_isOpen
#print axioms twoPuncturedDiskUpperSide_isOpen
#print axioms twoPuncturedDisk_lower_upper_cover
#print axioms twoPuncturedDisk_overlap_eq_strip
#print axioms twoPuncturedDiskOverlap_fundamentalGroup_subsingleton

end

end SystolicGrowth

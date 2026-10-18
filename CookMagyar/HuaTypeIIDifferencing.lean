module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaTypeIIFrequency
public import CookMagyar.GeneralCubicWeyl

@[expose] public section

/-!
# First differencing on Hua's Type-II common outer interval

After the ordered-pair reindexing in `MinorArcExerciseGaps`, one pair
`w < v` contributes a cubic phase summed over the intersection of three
outer-index intervals. This file keeps that variable common interval exact
while applying the first finite positive-shift identity. The shifted phase
is quadratic and retains both arbitrary lower coefficients. No cancellation
estimate is asserted here.
-/

open ComplexConjugate
open scoped BigOperators

namespace SystolicGrowth.CookMagyarCircle

/-- The source's common outer interval for one fixed inner pair `v,w`.
It is the intersection of `D<u≤D'`, `P'/v<u≤(P/l)/v`, and
`P'/w<u≤(P/l)/w`. Positivity of `v,w` is supplied by its later caller. -/
noncomputable def huaTypeIICommonOuterWindow
    (P l D D' v w : ℕ) (P' : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc (D + 1) D').filter (fun u =>
    P' / (v : ℝ) < (u : ℝ) ∧ (u : ℝ) ≤ ((P : ℝ) / l) / v ∧
    P' / (w : ℝ) < (u : ℝ) ∧ (u : ℝ) ≤ ((P : ℝ) / l) / w)

/-- Membership exposes every strict lower and weak upper endpoint, with
no relaxation of the original common interval. -/
theorem mem_huaTypeIICommonOuterWindow_iff
    (P l D D' v w u : ℕ) (P' : ℝ) :
    u ∈ huaTypeIICommonOuterWindow P l D D' v w P' ↔
      D < u ∧ u ≤ D' ∧
      P' / (v : ℝ) < (u : ℝ) ∧ (u : ℝ) ≤ ((P : ℝ) / l) / v ∧
      P' / (w : ℝ) < (u : ℝ) ∧ (u : ℝ) ≤ ((P : ℝ) / l) / w := by
  simp only [huaTypeIICommonOuterWindow, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hvlo, hvhi, hwlo, hwhi⟩
    exact ⟨by omega, hhi, hvlo, hvhi, hwlo, hwhi⟩
  · rintro ⟨hlo, hhi, hvlo, hvhi, hwlo, hwhi⟩
    exact ⟨⟨by omega, hhi⟩, hvlo, hvhi, hwlo, hwhi⟩

/-- Membership of all eight vertices of a nonnegative three-shift cube in
the Type-II common outer window is equivalent to membership of its two
extreme vertices. The strict lower and weak upper source endpoints remain
unchanged; this is only interval convexity, not an analytic estimate. -/
theorem hua_typeII_commonWindow_eightShift_iff_endpoints
    (P l D D' v w u h k r : ℕ) (P' : ℝ) :
    let U := huaTypeIICommonOuterWindow P l D D' v w P'
    (u ∈ U ∧ u + h ∈ U ∧ u + k ∈ U ∧ u + k + h ∈ U ∧
      u + r ∈ U ∧ u + r + h ∈ U ∧ u + r + k ∈ U ∧
      u + r + k + h ∈ U) ↔
      u ∈ U ∧ u + r + k + h ∈ U := by
  dsimp only
  constructor
  · rintro ⟨hu, _, _, _, _, _, _, htop⟩
    exact ⟨hu, htop⟩
  · rintro ⟨hu, htop⟩
    obtain ⟨hDlo, _, hvlo, _, hwlo, _⟩ :=
      (mem_huaTypeIICommonOuterWindow_iff P l D D' v w u P').1 hu
    obtain ⟨_, hDhi, _, hvhi, _, hwhi⟩ :=
      (mem_huaTypeIICommonOuterWindow_iff
        P l D D' v w (u + r + k + h) P').1 htop
    have hbetween (x : ℕ) (hux : u ≤ x) (hxt : x ≤ u + r + k + h) :
        x ∈ huaTypeIICommonOuterWindow P l D D' v w P' := by
      apply (mem_huaTypeIICommonOuterWindow_iff P l D D' v w x P').2
      have huxR : (u : ℝ) ≤ (x : ℝ) := by exact_mod_cast hux
      have hxtR : (x : ℝ) ≤ ((u + r + k + h : ℕ) : ℝ) := by
        exact_mod_cast hxt
      exact ⟨by omega, by omega,
        lt_of_lt_of_le hvlo huxR, le_trans hxtR hvhi,
        lt_of_lt_of_le hwlo huxR, le_trans hxtR hwhi⟩
    exact ⟨hu,
      hbetween (u + h) (by omega) (by omega),
      hbetween (u + k) (by omega) (by omega),
      hbetween (u + k + h) (by omega) (by omega),
      hbetween (u + r) (by omega) (by omega),
      hbetween (u + r + h) (by omega) (by omega),
      hbetween (u + r + k) (by omega) (by omega),
      htop⟩

/-- One positive shift of a real cubic phase is an exact quadratic phase.
The original quadratic and linear coefficients remain in the displayed
lower coefficients; only the constant term of the original phase cancels. -/
theorem generalCubicPhase_firstDifference_eq_quadratic
    (A B C E : ℝ) (h u : ℕ) :
    generalCubicPhase A B C E (u + h) *
      conj (generalCubicPhase A B C E u) =
    generalCubicPhase 0
      (3 * A * h)
      (3 * A * (h : ℝ) ^ 2 + 2 * B * h)
      (A * (h : ℝ) ^ 3 + B * (h : ℝ) ^ 2 + C * h) u := by
  unfold generalCubicPhase generalCubicPolynomial
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul]
  simp
  simp only [map_ofNat]
  ring

/-- The exact first positive-shift identity for a cubic phase restricted
to a finite support inside `0≤u≤N`. Both endpoints of each autocorrelation
remain as membership in the *same* support, with no interval enlargement.
The source-shaped specialization below uses the common outer window. -/
private theorem norm_generalCubicPhase_sum_sq_eq_firstDifference_on_support
    (U : Finset ℕ) (N : ℕ) (hU : U ⊆ Finset.range (N + 1))
    (A B C E : ℝ) :
    ‖∑ u ∈ U, generalCubicPhase A B C E u‖ ^ 2 =
      (U.card : ℝ) +
        2 * (∑ h ∈ Finset.Icc 1 N,
          ∑ u ∈ (Finset.range (N + 1 - h)).filter
            (fun u => u ∈ U ∧ u + h ∈ U),
              generalCubicPhase 0
                (3 * A * h)
                (3 * A * (h : ℝ) ^ 2 + 2 * B * h)
                (A * (h : ℝ) ^ 3 + B * (h : ℝ) ^ 2 + C * h) u).re := by
  classical
  let f : ℕ → ℂ := fun u => if u ∈ U then generalCubicPhase A B C E u else 0
  have hfilter : (Finset.range (N + 1)).filter (fun u => u ∈ U) = U := by
    ext u
    constructor
    · intro hu
      exact (Finset.mem_filter.mp hu).2
    · intro hu
      exact Finset.mem_filter.mpr ⟨hU hu, hu⟩
  have hsum : (∑ u ∈ Finset.range (N + 1), f u) =
      ∑ u ∈ U, generalCubicPhase A B C E u := by
    change (∑ u ∈ Finset.range (N + 1),
      if u ∈ U then generalCubicPhase A B C E u else 0) = _
    rw [← Finset.sum_filter, hfilter]
  have hdiag : (∑ u ∈ Finset.range (N + 1), ‖f u‖ ^ 2) =
      (U.card : ℝ) := by
    have hpoint (u : ℕ) : ‖f u‖ ^ 2 = if u ∈ U then (1 : ℝ) else 0 := by
      by_cases hu : u ∈ U <;> simp [f, hu]
    simp_rw [hpoint]
    rw [← Finset.sum_filter, hfilter]
    simp
  have hpair :
      (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range i,
        f i * conj (f j)) =
      ∑ h ∈ Finset.Icc 1 N,
        ∑ u ∈ Finset.range (N + 1 - h), f (u + h) * conj (f u) := by
    calc
      _ = ∑ hu ∈ positiveCubicShiftPairs N,
            f (hu.2 + hu.1) * conj (f hu.2) := by
        rw [sum_triangle_eq_strictCubicIndexPairs]
        exact sum_strictCubicIndexPairs_eq_positiveShiftPairs N
          (fun i j => f i * conj (f j))
      _ = _ := sum_positiveCubicShiftPairs_eq_sum_by_shift N
        (fun h u => f (u + h) * conj (f u))
  have hshift (h u : ℕ) : f (u + h) * conj (f u) =
      if u ∈ U ∧ u + h ∈ U then
        generalCubicPhase 0
          (3 * A * h)
          (3 * A * (h : ℝ) ^ 2 + 2 * B * h)
          (A * (h : ℝ) ^ 3 + B * (h : ℝ) ^ 2 + C * h) u else 0 := by
    by_cases hu : u ∈ U <;> by_cases huh : u + h ∈ U
    · simp [f, hu, huh, generalCubicPhase_firstDifference_eq_quadratic]
    · simp [f, hu, huh]
    · simp [f, hu, huh]
    · simp [f, hu, huh]
  have hpair' :
      (∑ h ∈ Finset.Icc 1 N,
        ∑ u ∈ Finset.range (N + 1 - h), f (u + h) * conj (f u)) =
      ∑ h ∈ Finset.Icc 1 N,
        ∑ u ∈ (Finset.range (N + 1 - h)).filter
          (fun u => u ∈ U ∧ u + h ∈ U),
            generalCubicPhase 0
              (3 * A * h)
              (3 * A * (h : ℝ) ^ 2 + 2 * B * h)
              (A * (h : ℝ) ^ 3 + B * (h : ℝ) ^ 2 + C * h) u := by
    apply Finset.sum_congr rfl
    intro h hh
    simp_rw [hshift h]
    rw [← Finset.sum_filter]
  have hnorm := norm_sum_range_sq_eq_diagonal_add_pairs f (N + 1)
  rw [hsum, hdiag, hpair, hpair'] at hnorm
  exact hnorm

/-- First differencing of the *actual ordered-pair common outer window*.
The left side is the cubic summand in MIN-01's proved ordered off-diagonal
identity. For every positive shift the right side includes precisely the
indices `u` and `u+h` satisfying all three source intervals. The quadratic
phase retains arbitrary original coefficients `b,c`; the leading cubic
frequency can be rewritten using `hua_typeII_real_leading_frequency_eq_natCast`
when `w<v`. -/
theorem hua_typeII_ordered_pair_commonWindow_firstDifference
    (P l D D' v w a q : ℕ) (P' b c : ℝ) :
    let U := huaTypeIICommonOuterWindow P l D D' v w P'
    let A : ℝ := ((a : ℝ) / q) * (l : ℝ) ^ 3 *
      ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
    let B : ℝ := b * (l : ℝ) ^ 2 *
      ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
    let C : ℝ := c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
    ‖∑ u ∈ U, generalCubicPhase A B C 0 u‖ ^ 2 =
      (U.card : ℝ) +
        2 * (∑ h ∈ Finset.Icc 1 D',
          ∑ u ∈ (Finset.range (D' + 1 - h)).filter
            (fun u => u ∈ U ∧ u + h ∈ U),
              generalCubicPhase 0
                (3 * A * h)
                (3 * A * (h : ℝ) ^ 2 + 2 * B * h)
                (A * (h : ℝ) ^ 3 + B * (h : ℝ) ^ 2 + C * h) u).re := by
  dsimp only
  apply norm_generalCubicPhase_sum_sq_eq_firstDifference_on_support
  intro u hu
  have hu' := (mem_huaTypeIICommonOuterWindow_iff P l D D' v w u P').1 hu
  exact Finset.mem_range.mpr (by omega)

/-- Apply the finite positive-shift identity once more to the quadratic
autocorrelation at a fixed first shift. The second shifted support has the
four exact membership tests `u,u+h,u+k,u+k+h` in the original finite set.
The resulting phase is linear with leading frequency `6*A*h*k`. -/
private theorem norm_quadratic_shift_sum_sq_eq_secondDifference_on_support
    (U : Finset ℕ) (N h : ℕ) (hh : h ≤ N) (A B C : ℝ) :
    let W := (Finset.range (N + 1 - h)).filter
      (fun u => u ∈ U ∧ u + h ∈ U)
    ‖∑ u ∈ W,
      generalCubicPhase 0
        (3 * A * h)
        (3 * A * (h : ℝ) ^ 2 + 2 * B * h)
        (A * (h : ℝ) ^ 3 + B * (h : ℝ) ^ 2 + C * h) u‖ ^ 2 =
      (W.card : ℝ) +
        2 * (∑ k ∈ Finset.Icc 1 (N - h),
          ∑ u ∈ (Finset.range ((N - h) + 1 - k)).filter
            (fun u => u ∈ U ∧ u + h ∈ U ∧
              u + k ∈ U ∧ u + k + h ∈ U),
              generalCubicPhase 0 0
                (6 * A * h * k)
                (3 * A * h * (k : ℝ) ^ 2 +
                  (3 * A * (h : ℝ) ^ 2 + 2 * B * h) * k) u).re := by
  classical
  dsimp only
  let W := (Finset.range (N + 1 - h)).filter
    (fun u => u ∈ U ∧ u + h ∈ U)
  have hW : W ⊆ Finset.range ((N - h) + 1) := by
    intro u hu
    have hu' := (Finset.mem_filter.mp hu).1
    exact Finset.mem_range.mpr (by
      have := Finset.mem_range.mp hu'
      omega)
  have hsupport (k : ℕ) :
      (Finset.range ((N - h) + 1 - k)).filter
          (fun u => u ∈ W ∧ u + k ∈ W) =
      (Finset.range ((N - h) + 1 - k)).filter
          (fun u => u ∈ U ∧ u + h ∈ U ∧
            u + k ∈ U ∧ u + k + h ∈ U) := by
    ext u
    simp only [Finset.mem_filter, W]
    constructor
    · rintro ⟨hur, ⟨_, huU, huhU⟩, ⟨_, hukU, hukhU⟩⟩
      exact ⟨hur, huU, huhU, hukU, hukhU⟩
    · rintro ⟨hur, huU, huhU, hukU, hukhU⟩
      have hur' : u ∈ Finset.range (N + 1 - h) := by
        apply Finset.mem_range.mpr
        have := Finset.mem_range.mp hur
        omega
      have hukr' : u + k ∈ Finset.range (N + 1 - h) := by
        apply Finset.mem_range.mpr
        have := Finset.mem_range.mp hur
        omega
      exact ⟨hur, ⟨hur', huU, huhU⟩, ⟨hukr', hukU, hukhU⟩⟩
  have hbase := norm_generalCubicPhase_sum_sq_eq_firstDifference_on_support
    W (N - h) hW (0 : ℝ) (3 * A * h)
      (3 * A * (h : ℝ) ^ 2 + 2 * B * h)
      (A * (h : ℝ) ^ 3 + B * (h : ℝ) ^ 2 + C * h)
  simp only [mul_zero, zero_mul, zero_add] at hbase
  simp_rw [hsupport] at hbase
  have hcoef (k : ℕ) :
      2 * (3 * A * h) * (k : ℝ) = 6 * A * h * k := by ring
  simp_rw [hcoef] at hbase
  exact hbase

/-- The source-shaped second difference of one ordered-pair contribution.
The quadratic autocorrelation from the first shift becomes a linear phase
on precisely the fourfold intersection of the common outer window; this
identity makes no analytic cancellation claim. -/
theorem hua_typeII_ordered_pair_commonWindow_secondDifference
    (P l D D' v w a q h : ℕ) (P' b c : ℝ) (hh : h ≤ D') :
    let U := huaTypeIICommonOuterWindow P l D D' v w P'
    let W := (Finset.range (D' + 1 - h)).filter
      (fun u => u ∈ U ∧ u + h ∈ U)
    let A : ℝ := ((a : ℝ) / q) * (l : ℝ) ^ 3 *
      ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
    let B : ℝ := b * (l : ℝ) ^ 2 *
      ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
    let C : ℝ := c * (l : ℝ) * ((v : ℝ) - (w : ℝ))
    ‖∑ u ∈ W,
      generalCubicPhase 0
        (3 * A * h)
        (3 * A * (h : ℝ) ^ 2 + 2 * B * h)
        (A * (h : ℝ) ^ 3 + B * (h : ℝ) ^ 2 + C * h) u‖ ^ 2 =
      (W.card : ℝ) +
        2 * (∑ k ∈ Finset.Icc 1 (D' - h),
          ∑ u ∈ (Finset.range ((D' - h) + 1 - k)).filter
            (fun u => u ∈ U ∧ u + h ∈ U ∧
              u + k ∈ U ∧ u + k + h ∈ U),
              generalCubicPhase 0 0
                (6 * A * h * k)
                (3 * A * h * (k : ℝ) ^ 2 +
                  (3 * A * (h : ℝ) ^ 2 + 2 * B * h) * k) u).re := by
  dsimp only
  exact norm_quadratic_shift_sum_sq_eq_secondDifference_on_support
    (huaTypeIICommonOuterWindow P l D D' v w P') D' h hh
      (((a : ℝ) / q) * (l : ℝ) ^ 3 *
        ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
      (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
      (c * (l : ℝ) * ((v : ℝ) - (w : ℝ)))

/-- A third exact positive shift of the linear phase from the second
difference. Every vertex of the three-dimensional shift cube retains
membership in the original finite support. The phase is now constant in
`u`, with the original cubic frequency multiplied by `6*h*k*r`. -/
private theorem norm_linear_shift_sum_sq_eq_thirdDifference_on_support
    (U : Finset ℕ) (N h k : ℕ) (hh : h ≤ N) (hk : k ≤ N - h)
    (A B : ℝ) :
    let T := (Finset.range ((N - h) + 1 - k)).filter
      (fun u => u ∈ U ∧ u + h ∈ U ∧
        u + k ∈ U ∧ u + k + h ∈ U)
    ‖∑ u ∈ T,
      generalCubicPhase 0 0
        (6 * A * h * k)
        (3 * A * h * (k : ℝ) ^ 2 +
          (3 * A * (h : ℝ) ^ 2 + 2 * B * h) * k) u‖ ^ 2 =
      (T.card : ℝ) +
        2 * (∑ r ∈ Finset.Icc 1 (N - h - k),
          ∑ u ∈ (Finset.range ((N - h - k) + 1 - r)).filter
            (fun u => u ∈ U ∧ u + h ∈ U ∧
              u + k ∈ U ∧ u + k + h ∈ U ∧
              u + r ∈ U ∧ u + r + h ∈ U ∧
              u + r + k ∈ U ∧ u + r + k + h ∈ U),
              generalCubicPhase 0 0 0
                (6 * A * h * k * r) u).re := by
  classical
  dsimp only
  let T := (Finset.range ((N - h) + 1 - k)).filter
    (fun u => u ∈ U ∧ u + h ∈ U ∧
      u + k ∈ U ∧ u + k + h ∈ U)
  have hT : T ⊆ Finset.range ((N - h - k) + 1) := by
    intro u hu
    have hu' := (Finset.mem_filter.mp hu).1
    exact Finset.mem_range.mpr (by
      have := Finset.mem_range.mp hu'
      omega)
  have hsupport (r : ℕ) :
      (Finset.range ((N - h - k) + 1 - r)).filter
          (fun u => u ∈ T ∧ u + r ∈ T) =
      (Finset.range ((N - h - k) + 1 - r)).filter
          (fun u => u ∈ U ∧ u + h ∈ U ∧
            u + k ∈ U ∧ u + k + h ∈ U ∧
            u + r ∈ U ∧ u + r + h ∈ U ∧
            u + r + k ∈ U ∧ u + r + k + h ∈ U) := by
    ext u
    simp only [Finset.mem_filter, T]
    constructor
    · rintro ⟨hur, ⟨_, huU, huhU, hukU, hukhU⟩,
        ⟨_, hurU, hurhU, hurkU, hurkhU⟩⟩
      exact ⟨hur, huU, huhU, hukU, hukhU,
        hurU, hurhU, hurkU, hurkhU⟩
    · rintro ⟨hur, huU, huhU, hukU, hukhU,
        hurU, hurhU, hurkU, hurkhU⟩
      have hur' : u ∈ Finset.range ((N - h) + 1 - k) := by
        apply Finset.mem_range.mpr
        have := Finset.mem_range.mp hur
        omega
      have hurr' : u + r ∈ Finset.range ((N - h) + 1 - k) := by
        apply Finset.mem_range.mpr
        have := Finset.mem_range.mp hur
        omega
      exact ⟨hur, ⟨hur', huU, huhU, hukU, hukhU⟩,
        ⟨hurr', hurU, hurhU, hurkU, hurkhU⟩⟩
  have hbase := norm_generalCubicPhase_sum_sq_eq_firstDifference_on_support
    T (N - h - k) hT (0 : ℝ) 0 (6 * A * h * k)
      (3 * A * h * (k : ℝ) ^ 2 +
        (3 * A * (h : ℝ) ^ 2 + 2 * B * h) * k)
  simp only [mul_zero, zero_mul, zero_add] at hbase
  simp_rw [hsupport] at hbase
  exact hbase

/-- The third exact differencing stage for one Type-II ordered pair on
its common outer window. The right-hand constant phase has coefficient
`6*A*h*k*r`, with all eight unrelaxed endpoint memberships explicit.
This identity precedes, but does not supply, the analytic summation bound. -/
theorem hua_typeII_ordered_pair_commonWindow_thirdDifference
    (P l D D' v w a q h k : ℕ) (P' b : ℝ)
    (hh : h ≤ D') (hk : k ≤ D' - h) :
    let U := huaTypeIICommonOuterWindow P l D D' v w P'
    let T := (Finset.range ((D' - h) + 1 - k)).filter
      (fun u => u ∈ U ∧ u + h ∈ U ∧
        u + k ∈ U ∧ u + k + h ∈ U)
    let A : ℝ := ((a : ℝ) / q) * (l : ℝ) ^ 3 *
      ((v : ℝ) ^ 3 - (w : ℝ) ^ 3)
    let B : ℝ := b * (l : ℝ) ^ 2 *
      ((v : ℝ) ^ 2 - (w : ℝ) ^ 2)
    ‖∑ u ∈ T,
      generalCubicPhase 0 0
        (6 * A * h * k)
        (3 * A * h * (k : ℝ) ^ 2 +
          (3 * A * (h : ℝ) ^ 2 + 2 * B * h) * k) u‖ ^ 2 =
      (T.card : ℝ) +
        2 * (∑ r ∈ Finset.Icc 1 (D' - h - k),
          ∑ u ∈ (Finset.range ((D' - h - k) + 1 - r)).filter
            (fun u => u ∈ U ∧ u + h ∈ U ∧
              u + k ∈ U ∧ u + k + h ∈ U ∧
              u + r ∈ U ∧ u + r + h ∈ U ∧
              u + r + k ∈ U ∧ u + r + k + h ∈ U),
              generalCubicPhase 0 0 0
                (6 * A * h * k * r) u).re := by
  dsimp only
  exact norm_linear_shift_sum_sq_eq_thirdDifference_on_support
    (huaTypeIICommonOuterWindow P l D D' v w P') D' h k hh hk
      (((a : ℝ) / q) * (l : ℝ) ^ 3 *
        ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
      (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))

#print axioms mem_huaTypeIICommonOuterWindow_iff
#print axioms hua_typeII_commonWindow_eightShift_iff_endpoints
#print axioms generalCubicPhase_firstDifference_eq_quadratic
#print axioms hua_typeII_ordered_pair_commonWindow_firstDifference
#print axioms hua_typeII_ordered_pair_commonWindow_secondDifference
#print axioms hua_typeII_ordered_pair_commonWindow_thirdDifference

end SystolicGrowth.CookMagyarCircle

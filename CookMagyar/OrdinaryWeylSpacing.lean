module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.OrdinaryWeylLinear

@[expose] public section

namespace SystolicGrowth
namespace CookMagyarCircle

open CookMagyarArcs

/-! # Rational-grid spacing for ordinary cubic Weyl -/

/-- Zero-safe majorant from the linear character-sum bound, expressed in
the circle metric so that the spacing lemmas can be applied directly. -/
noncomputable def linearDistanceEnvelope (Y theta : ℝ) : ℝ :=
  if periodicDistance theta 0 = 0 then Y
  else min Y (1 / (2 * periodicDistance theta 0))

theorem linearDistanceEnvelope_le (Y theta : ℝ) :
    linearDistanceEnvelope Y theta ≤ Y := by
  by_cases hz : periodicDistance theta 0 = 0
  · simp [linearDistanceEnvelope, hz]
  · simp only [linearDistanceEnvelope, hz, if_false]
    exact min_le_left _ _

theorem linearDistanceEnvelope_nonneg {Y theta : ℝ} (hY : 0 ≤ Y) :
    0 ≤ linearDistanceEnvelope Y theta := by
  by_cases hz : periodicDistance theta 0 = 0
  · simp [linearDistanceEnvelope, hz, hY]
  · simp only [linearDistanceEnvelope, hz, if_false]
    have hdpos : 0 < periodicDistance theta 0 :=
      lt_of_le_of_ne dist_nonneg (Ne.symm hz)
    apply le_min
    · exact hY
    · positivity

/-- On a nonzero distance shell, the zero-safe character-sum envelope is
bounded by the reciprocal of that shell's lower endpoint. -/
theorem linearDistanceEnvelope_le_reciprocal_of_shell
    {Y q : ℝ} {k : ℕ} {theta : ℝ}
    (hq : 0 < q) (hk : 0 < k)
    (hshell : (k : ℝ) / q ≤ periodicDistance theta 0) :
    linearDistanceEnvelope Y theta ≤ q / k := by
  have hratio : 0 < (k : ℝ) / q := div_pos (by exact_mod_cast hk) hq
  have hdpos : 0 < periodicDistance theta 0 :=
    lt_of_lt_of_le hratio hshell
  have hinv : 1 / periodicDistance theta 0 ≤ q / k := by
    calc
      1 / periodicDistance theta 0 ≤ 1 / ((k : ℝ) / q) :=
        one_div_le_one_div_of_le hratio hshell
      _ = q / k := by field_simp
  have hhalf : 1 / (2 * periodicDistance theta 0) ≤
      1 / periodicDistance theta 0 := by
    have htwo : 0 < 2 * periodicDistance theta 0 := by positivity
    rw [div_le_iff₀ htwo]
    field_simp [ne_of_gt hdpos]
    norm_num
  simp only [linearDistanceEnvelope, ne_of_gt hdpos, if_false]
  exact (min_le_right _ _).trans (hhalf.trans hinv)

/-- Multiplying a reduced rational `a/q` by six and cancelling the common
factor with `q` again gives a reduced numerator/denominator pair. -/
theorem six_mul_rational_reduction_coprime
    (a q : ℕ) (hq : 0 < q) (hac : Nat.Coprime a q) :
    Nat.Coprime ((6 * a) / Nat.gcd q 6) (q / Nat.gcd q 6) := by
  let g := Nat.gcd q 6
  let u := 6 / g
  have hgq : g ∣ q := Nat.gcd_dvd_left q 6
  have hg6 : g ∣ 6 := Nat.gcd_dvd_right q 6
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left 6 hq
  have hgle : g ≤ 6 := Nat.le_of_dvd (by decide : 0 < 6) hg6
  have hcg : Nat.Coprime u g := by
    dsimp [u]
    interval_cases g <;> norm_num [Nat.Coprime] at *
  have hu6 : u ∣ 6 := Nat.div_dvd_of_dvd hg6
  have hug : Nat.gcd u q ∣ g := by
    apply Nat.dvd_gcd (Nat.gcd_dvd_right u q)
    exact (Nat.gcd_dvd_left u q).trans hu6
  have huq : Nat.Coprime u q := by
    change Nat.gcd u q = 1
    apply Nat.dvd_one.mp
    have hdiv : Nat.gcd u q ∣ Nat.gcd u g :=
      Nat.dvd_gcd (Nat.gcd_dvd_left u q) hug
    rw [hcg.gcd_eq_one] at hdiv
    exact hdiv
  have huaq : Nat.Coprime (u * a) q := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨huq, hac⟩
  have hmain : Nat.gcd (6 * a) q = g := by
    have hnumeq : (u * a) * g = 6 * a := by
      dsimp [u]
      calc
        (6 / g * a) * g = (6 / g * g) * a := by ring
        _ = 6 * a := by rw [Nat.div_mul_cancel hg6]
    rw [← hnumeq]
    exact Nat.gcd_mul_of_coprime_of_dvd huaq hgq
  have hred := Nat.gcd_div_gcd_div_gcd_of_pos_right (m := q) (n := 6 * a) hq
  have hmain' : Nat.gcd q (6 * a) = g := by
    simpa [Nat.gcd_comm] using hmain
  simpa [Nat.Coprime, Nat.gcd_comm, hmain', g] using hred

/-- The rational part of `6a/q` is exactly its reduced center; no error is
introduced by cancelling `gcd(q,6)`. -/
theorem six_mul_rationalCenter_eq_reduced
    (a q : ℕ) (hq : 0 < q) :
    6 * rationalCenter a q =
      rationalCenter ((6 * a) / Nat.gcd q 6) (q / Nat.gcd q 6) := by
  let g := Nat.gcd q 6
  have hgq : g ∣ q := Nat.gcd_dvd_left q 6
  have hg6 : g ∣ 6 := Nat.gcd_dvd_right q 6
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left 6 hq
  have hgnum : g ∣ 6 * a := dvd_mul_of_dvd_left hg6 a
  have hnumNat : (6 * a) / g * g = 6 * a := Nat.div_mul_cancel hgnum
  have hqNat : (q / g) * g = q := Nat.div_mul_cancel hgq
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hgpos)
  have hnumR : (6 * a : ℝ) = (g : ℝ) * (((6 * a) / g : ℕ) : ℝ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using hnumNat.symm)
  have hqR : (q : ℝ) = (g : ℝ) * (q / g : ℕ) := by
    exact_mod_cast (by simpa [Nat.mul_comm] using hqNat.symm)
  simp only [CookMagyarArcs.rationalCenter]
  rw [Nat.cast_div_charZero hgnum, Nat.cast_div_charZero hgq]
  have hqRne : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  field_simp [hgR, hqRne]
  calc
    _ = (g : ℝ) * (((6 * a) / g : ℕ) : ℝ) := hnumR
    _ = ((6 * a : ℕ) : ℝ) := by
      have hnat : g * ((6 * a) / g) = 6 * a := by
        calc
          g * ((6 * a) / g) = ((6 * a) / g) * g := Nat.mul_comm _ _
          _ = 6 * a := Nat.div_mul_cancel hgnum
      exact_mod_cast hnat

/-- The reduced denominator after multiplying by six remains comparable
to the original denominator. -/
theorem six_mul_reduced_denominator_bounds (q : ℕ) :
    q / 6 ≤ q / Nat.gcd q 6 ∧ q / Nat.gcd q 6 ≤ q := by
  let g := Nat.gcd q 6
  have hgq : g ∣ q := Nat.gcd_dvd_left q 6
  have hg6 : g ≤ 6 := Nat.le_of_dvd (by decide : 0 < 6)
    (Nat.gcd_dvd_right q 6)
  have hfactor : q = (q / g) * g := (Nat.div_mul_cancel hgq).symm
  constructor
  · have hmul : q ≤ (q / g) * 6 := by
      calc
        q = (q / g) * g := hfactor
        _ ≤ (q / g) * 6 := Nat.mul_le_mul_left (q / g) hg6
    exact Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hmul)
  · exact Nat.div_le_self q g

/-- The rational approximation data for `α` induces reduced rational
approximation data for the differenced frequency `6α`. -/
theorem six_mul_approximation_eq_reduced
    (a q : ℕ) (alpha beta : ℝ) (hq : 0 < q)
    (halpha : alpha = rationalCenter a q + beta) :
    6 * alpha =
      rationalCenter ((6 * a) / Nat.gcd q 6) (q / Nat.gcd q 6) + 6 * beta := by
  rw [halpha]
  calc
    6 * (rationalCenter a q + beta) =
        6 * rationalCenter a q + 6 * beta := by ring
    _ = rationalCenter ((6 * a) / Nat.gcd q 6) (q / Nat.gcd q 6) +
        6 * beta := by rw [six_mul_rationalCenter_eq_reduced a q hq]

theorem periodicDistance_le_abs_sub (x y : ℝ) :
    periodicDistance x y ≤ |x - y| := by
  simpa only [periodicDistance, dist_eq_norm, ← AddCircle.coe_sub,
    Real.norm_eq_abs] using
    (QuotientAddGroup.norm_mk_le_norm
      (S := AddSubgroup.zmultiples (1 : ℝ)) (m := x - y))

theorem periodicDistance_eq_abs_sub_of_abs_le_half
    {x y : ℝ} (hxy : |x - y| ≤ 1 / 2) :
    periodicDistance x y = |x - y| := by
  unfold periodicDistance
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2
    (by simpa using hxy)

/-- Two distinct points in the first full orbit of a circle point of
order `q` are separated by at least `1/q`. -/
theorem periodicDistance_nsmul_separated
    {u : UnitAddCircle} {q j k : ℕ}
    (hq : 0 < q) (horder : addOrderOf u = q)
    (hj : j < q) (hk : k < q) (hjk : j ≠ k) :
    1 / (q : ℝ) ≤ dist (j • u) (k • u) := by
  let v : UnitAddCircle := j • u - k • u
  have hv0 : v ≠ 0 := by
    intro hv
    have heq : j • u = k • u := sub_eq_zero.mp hv
    have hinj := (nsmul_injOn_Iio_addOrderOf (x := u))
      (show j ∈ Set.Iio (addOrderOf u) by simpa [horder] using hj)
      (show k ∈ Set.Iio (addOrderOf u) by simpa [horder] using hk)
      heq
    exact hjk hinj
  have hqu : q • u = 0 := by
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero u
  have hqv : q • v = 0 := by
    dsimp [v]
    rw [nsmul_sub, smul_comm q j u, smul_comm q k u, hqu]
    simp
  have hvFinite : IsOfFinAddOrder v :=
    (isOfFinAddOrder_iff_nsmul_eq_zero).2 ⟨q, hq, hqv⟩
  have horderdvd : addOrderOf v ∣ q :=
    (addOrderOf_dvd_iff_nsmul_eq_zero).2 hqv
  have horderle : addOrderOf v ≤ q := Nat.le_of_dvd hq horderdvd
  have hnorm := AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder hvFinite hv0
  have hmul : (addOrderOf v : ℝ) * ‖v‖ ≤ (q : ℝ) * ‖v‖ := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast horderle) (norm_nonneg v)
  have hone : (1 : ℝ) ≤ (q : ℝ) * ‖v‖ := by
    have hnorm' : (1 : ℝ) ≤ (addOrderOf v : ℝ) * ‖v‖ := by
      simpa [nsmul_eq_mul] using hnorm
    exact hnorm'.trans hmul
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hdiv : 1 / (q : ℝ) ≤ ‖v‖ :=
    (div_le_iff₀ hqr).2 (by simpa [mul_comm] using hone)
  simpa only [v, dist_eq_norm] using hdiv

/-- The reduced rational `a/q` generates the full `q`-point circle grid.
This is the version used when a translated block is compared with a
rational approximation. -/
theorem rationalGrid_periodicDistance_separated
    {a q j k : ℕ} (hq : 0 < q) (hac : Nat.Coprime a q)
    (hj : j < q) (hk : k < q) (hjk : j ≠ k) :
    1 / (q : ℝ) ≤
      periodicDistance (rationalCenter (a * j) q)
        (rationalCenter (a * k) q) := by
  let u : UnitAddCircle := (rationalCenter a q : UnitAddCircle)
  have horder : addOrderOf u = q := by
    simpa only [u, rationalCenter, mul_one] using
      (AddCircle.addOrderOf_div_of_gcd_eq_one
        (p := (1 : ℝ)) (m := a) (n := q) hq hac)
  have hpoint (m : ℕ) :
      (rationalCenter (a * m) q : UnitAddCircle) = m • u := by
    rw [← AddCircle.coe_nsmul (1 : ℝ)]
    congr 1
    dsimp [u, rationalCenter]
    push_cast
    ring
  simpa only [periodicDistance, hpoint] using
    periodicDistance_nsmul_separated hq horder hj hk hjk

/-- Each point in an arbitrary translated block of `q` consecutive
integers lies within `1/q` (in circle distance) of the translated
rational grid. The translation `B` is retained explicitly. -/
theorem translatedBlock_close_to_rationalGrid
    {a q B j : ℕ} {alpha delta : ℝ}
    (hq : 0 < q) (hj : j < q)
    (halpha : alpha = rationalCenter a q + delta)
    (hdelta : |delta| ≤ 1 / (q : ℝ) ^ 2) :
    periodicDistance (alpha * (B + j : ℕ))
      (alpha * (B : ℝ) + rationalCenter (a * j) q) ≤
        1 / (q : ℝ) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hjr : (j : ℝ) ≤ q := by exact_mod_cast hj.le
  have hreal : alpha * (B + j : ℕ) =
      (alpha * (B : ℝ) + rationalCenter (a * j) q) + delta * j := by
    rw [halpha]
    dsimp [rationalCenter]
    push_cast
    ring
  have hdist : periodicDistance (alpha * (B + j : ℕ))
      (alpha * (B : ℝ) + rationalCenter (a * j) q) ≤ |delta * (j : ℝ)| := by
    rw [hreal]
    simpa using CookMagyarMajorArc.periodicDistance_add_int_le_abs
      (alpha * (B : ℝ) + rationalCenter (a * j) q) (delta * j) 0
  have hbound : |delta * (j : ℝ)| ≤ 1 / (q : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ j)]
    calc
      |delta| * (j : ℝ) ≤ (1 / (q : ℝ) ^ 2) * (q : ℝ) := by
        gcongr
      _ = 1 / (q : ℝ) := by field_simp
  exact hdist.trans hbound

/-- Fixed-multiple version of the translated-block perturbation bound.
It is used for the slope `6αhk` after reducing its rational part: the
perturbation may be several grid spacings rather than one. -/
theorem translatedBlock_close_to_rationalGrid_of_multiple
    {a q B j C : ℕ} {alpha delta : ℝ}
    (hq : 0 < q) (hj : j < q)
    (halpha : alpha = rationalCenter a q + delta)
    (hdelta : |delta| ≤ (C : ℝ) / (q : ℝ) ^ 2) :
    periodicDistance (alpha * (B + j : ℕ))
      (alpha * (B : ℝ) + rationalCenter (a * j) q) ≤
        (C : ℝ) / q := by
  have hreal : alpha * (B + j : ℕ) =
      (alpha * (B : ℝ) + rationalCenter (a * j) q) + delta * j := by
    rw [halpha]
    dsimp [rationalCenter]
    push_cast
    ring
  have hdist : periodicDistance (alpha * (B + j : ℕ))
      (alpha * (B : ℝ) + rationalCenter (a * j) q) ≤ |delta * (j : ℝ)| := by
    rw [hreal]
    simpa using CookMagyarMajorArc.periodicDistance_add_int_le_abs
      (alpha * (B : ℝ) + rationalCenter (a * j) q) (delta * j) 0
  have hjr : (j : ℝ) ≤ q := by exact_mod_cast hj.le
  have hbound : |delta * (j : ℝ)| ≤ (C : ℝ) / q := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ j)]
    calc
      |delta| * (j : ℝ) ≤ ((C : ℝ) / (q : ℝ) ^ 2) * q := by
        exact mul_le_mul hdelta hjr (by positivity) (by positivity)
      _ = (C : ℝ) / q := by field_simp
  exact hdist.trans hbound

/-- Translating the rational grid by the phase at the first index does
not change its pairwise circle spacing. -/
theorem translatedRationalGrid_periodicDistance_separated
    {a q j k : ℕ} (hq : 0 < q) (hac : Nat.Coprime a q)
    (hj : j < q) (hk : k < q) (hjk : j ≠ k) (base : ℝ) :
    1 / (q : ℝ) ≤
      periodicDistance (base + rationalCenter (a * j) q)
        (base + rationalCenter (a * k) q) := by
  have hsep := rationalGrid_periodicDistance_separated hq hac hj hk hjk
  simpa only [periodicDistance, AddCircle.coe_add, dist_add_left] using hsep

/-- A block point in a distance window puts its rational-grid partner
in the same window enlarged by exactly `1/q`. This is the reduction
needed before counting grid points in bins. -/
theorem translatedBlock_gridPoint_le_of_phase_le
    {a q B j : ℕ} {alpha delta target epsilon : ℝ}
    (hq : 0 < q) (hj : j < q)
    (halpha : alpha = rationalCenter a q + delta)
    (hdelta : |delta| ≤ 1 / (q : ℝ) ^ 2)
    (hphase : periodicDistance (alpha * (B + j : ℕ)) target ≤ epsilon) :
    periodicDistance
        (alpha * (B : ℝ) + rationalCenter (a * j) q) target ≤
      epsilon + 1 / (q : ℝ) := by
  have hclose := translatedBlock_close_to_rationalGrid
    (a := a) (q := q) (B := B) (j := j) hq hj halpha hdelta
  have htri : periodicDistance
      (alpha * (B : ℝ) + rationalCenter (a * j) q) target ≤
      periodicDistance
        (alpha * (B : ℝ) + rationalCenter (a * j) q)
        (alpha * (B + j : ℕ)) +
      periodicDistance (alpha * (B + j : ℕ)) target := by
    exact dist_triangle _ _ _
  calc
    periodicDistance
        (alpha * (B : ℝ) + rationalCenter (a * j) q) target ≤
      periodicDistance
        (alpha * (B : ℝ) + rationalCenter (a * j) q)
        (alpha * (B + j : ℕ)) +
      periodicDistance (alpha * (B + j : ℕ)) target := htri
    _ ≤ epsilon + 1 / (q : ℝ) := by
      have hclose' : periodicDistance
          (alpha * (B : ℝ) + rationalCenter (a * j) q)
          (alpha * (B + j : ℕ)) ≤ 1 / (q : ℝ) := by
        simpa [periodicDistance, dist_comm] using hclose
      linarith

/-- One-dimensional packing: points at mutual distance at least one
inside a closed interval of integer length `K` number at most `K+1`.
The proof assigns each point its translated integer floor; it is the
finite counting step used after choosing circle representatives. -/
theorem card_unitSeparated_Icc_le
    (s : Finset ℝ) (L : ℝ) (K : ℕ)
    (hbox : ∀ x ∈ s, L ≤ x ∧ x ≤ L + K)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ |x - y|) :
    s.card ≤ K + 1 := by
  let f : ℝ → ℕ := fun x => ⌊x - L⌋₊
  have hmap : s.image f ⊆ Finset.range (K + 1) := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    have hxbox := hbox x hx
    have hx0 : 0 ≤ x - L := by linarith
    have hxlt : x - L < (K + 1 : ℕ) := by exact_mod_cast (show x - L < (K : ℝ) + 1 by linarith)
    exact Finset.mem_range.mpr ((Nat.floor_lt hx0).2 hxlt)
  have hinj : Set.InjOn f ↑s := by
    intro x hx y hy hfloor
    by_contra hxy
    have hxysep := hsep x hx y hy hxy
    have hxbox := hbox x hx
    have hybox := hbox y hy
    have hx0 : 0 ≤ x - L := by linarith
    have hy0 : 0 ≤ y - L := by linarith
    have hxlo : (f x : ℝ) ≤ x - L := Nat.floor_le hx0
    have hylo : (f y : ℝ) ≤ y - L := Nat.floor_le hy0
    have hxhi : x - L < (f x : ℝ) + 1 := Nat.lt_floor_add_one _
    have hyhi : y - L < (f y : ℝ) + 1 := Nat.lt_floor_add_one _
    have heq : (f x : ℝ) = (f y : ℝ) := by exact_mod_cast hfloor
    have habs : |x - y| < 1 := by
      apply abs_lt.mpr
      constructor <;> linarith
    exact (not_le_of_gt habs) hxysep
  have hcard : (s.image f).card = s.card := Finset.card_image_iff.mpr hinj
  rw [← hcard]
  exact (Finset.card_le_card hmap).trans_eq (by simp)

/-- Scaled real-interval packing. This is the form used with separation
`1/q` and a bin enlarged by a fixed number of grid spacings. -/
theorem card_separated_Icc_le
    (s : Finset ℝ) (L epsilon : ℝ) (K : ℕ) (hepsilon : 0 < epsilon)
    (hbox : ∀ x ∈ s, L ≤ x ∧ x ≤ L + K * epsilon)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → epsilon ≤ |x - y|) :
    s.card ≤ K + 1 := by
  let t : Finset ℝ := s.image (fun x => x / epsilon)
  have hinj : Function.Injective (fun x : ℝ => x / epsilon) := by
    intro x y hxy
    have h := congrArg (fun z : ℝ => z * epsilon) hxy
    simpa [hepsilon.ne'] using h
  have hcard : t.card = s.card := Finset.card_image_of_injective s hinj
  have htbox : ∀ x ∈ t, L / epsilon ≤ x ∧
      x ≤ L / epsilon + K := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    have h := hbox x hx
    constructor
    · exact div_le_div_of_nonneg_right h.1 hepsilon.le
    · calc
        x / epsilon ≤ (L + K * epsilon) / epsilon :=
          div_le_div_of_nonneg_right h.2 hepsilon.le
        _ = L / epsilon + K := by field_simp
  have htsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → 1 ≤ |x - y| := by
    intro v hv w hw hvw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    have hxy : x ≠ y := by
      intro he
      exact hvw (by simp [he])
    have h := hsep x hx y hy hxy
    have heq : |x / epsilon - y / epsilon| = |x - y| / epsilon := by
      rw [← sub_div, abs_div, abs_of_pos hepsilon]
    rw [heq]
    exact (le_div_iff₀ hepsilon).2 (by simpa using h)
  rw [← hcard]
  exact card_unitSeparated_Icc_le t (L / epsilon) K htbox htsep

/-- A globally `1/q`-separated finite subset of the unit circle has at
most `q+1` points. The slightly loose endpoint count is convenient for
the large-radius branch of the local packing bound. -/
theorem card_periodicSeparated_le_q_add_one
    (s : Finset UnitAddCircle) (q : ℕ) (hq : 0 < q)
    (hsep : ∀ u ∈ s, ∀ v ∈ s, u ≠ v →
      1 / (q : ℝ) ≤ dist u v) :
    s.card ≤ q + 1 := by
  let f : UnitAddCircle → ℝ :=
    fun u => (AddCircle.equivIco (1 : ℝ) 0 u).val
  let t : Finset ℝ := s.image f
  have hf : Function.Injective f := by
    intro u v huv
    exact (AddCircle.equivIco (1 : ℝ) 0).injective
      (Subtype.ext huv)
  have hcard : t.card = s.card := Finset.card_image_of_injective s hf
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have htbox : ∀ x ∈ t, (0 : ℝ) ≤ x ∧ x ≤ 0 + q * (1 / (q : ℝ)) := by
    intro x hx
    obtain ⟨u, _hu, rfl⟩ := Finset.mem_image.mp hx
    have hu := (AddCircle.equivIco (1 : ℝ) 0 u).property
    simp only [Set.mem_Ico, zero_add] at hu
    constructor
    · exact hu.1
    · have hqinv : (q : ℝ) * (1 / (q : ℝ)) = 1 := by field_simp
      rw [zero_add, hqinv]
      exact hu.2.le
  have htsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y →
      1 / (q : ℝ) ≤ |x - y| := by
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have huv : u ≠ v := fun he => hxy (by simp [he])
    have hdist := hsep u hu v hv huv
    have hcoe_u : ((f u : ℝ) : UnitAddCircle) = u := by
      simpa only [f] using (AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := u))
    have hcoe_v : ((f v : ℝ) : UnitAddCircle) = v := by
      simpa only [f] using (AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := v))
    have hle := periodicDistance_le_abs_sub (f u) (f v)
    unfold periodicDistance at hle
    rw [hcoe_u, hcoe_v] at hle
    exact hdist.trans hle
  rw [← hcard]
  exact card_separated_Icc_le t 0 (1 / (q : ℝ)) q
    (by positivity) htbox htsep

/-- A `1/q`-separated finite set in a circle ball of radius `R/q` has
at most `2R+1` points. Centering the fundamental interval at the ball
center removes the seam case entirely. -/
theorem card_periodicSeparated_ball_le
    (s : Finset UnitAddCircle) (center : UnitAddCircle)
    (q R : ℕ) (hq : 0 < q)
    (hsep : ∀ u ∈ s, ∀ v ∈ s, u ≠ v →
      1 / (q : ℝ) ≤ dist u v)
    (hball : ∀ u ∈ s, dist u center ≤ (R : ℝ) / q) :
    s.card ≤ 2 * R + 1 := by
  let c : ℝ := (AddCircle.equivIco (1 : ℝ) 0 center).val
  let left : ℝ := c - 1 / 2
  let f : UnitAddCircle → ℝ :=
    fun u => (AddCircle.equivIco (1 : ℝ) left u).val
  let t : Finset ℝ := s.image f
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : ((c : ℝ) : UnitAddCircle) = center := by
    simpa only [c] using
      (AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := center))
  have hcmem : c ∈ Set.Ico left (left + 1) := by
    dsimp [left]
    constructor
    · linarith
    · linarith
  have hf : Function.Injective f := by
    intro u v huv
    exact (AddCircle.equivIco (1 : ℝ) left).injective (Subtype.ext huv)
  have hcard : t.card = s.card := Finset.card_image_of_injective s hf
  have hcenter : f center = c := by
    dsimp [f]
    rw [← hc, AddCircle.equivIco_coe_eq hcmem]
  have hcoord (u : UnitAddCircle) :
      |f u - c| ≤ 1 / 2 := by
    have hu := (AddCircle.equivIco (1 : ℝ) left u).property
    simp only [Set.mem_Ico] at hu
    dsimp [f, left] at *
    apply abs_le.mpr
    constructor <;> linarith [hu.1, hu.2]
  have hcoe (u : UnitAddCircle) : ((f u : ℝ) : UnitAddCircle) = u := by
    simpa only [f] using
      (AddCircle.coe_equivIco (p := (1 : ℝ)) (a := left) (y := u))
  have htbox : ∀ x ∈ t,
      c - (R : ℝ) / q ≤ x ∧
        x ≤ (c - (R : ℝ) / q) + (2 * R : ℕ) * (1 / (q : ℝ)) := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    have hdist : dist u center = |f u - c| := by
      have h := periodicDistance_eq_abs_sub_of_abs_le_half (hcoord u)
      unfold periodicDistance at h
      rw [hcoe u, hc] at h
      exact h
    have hb := hball u hu
    rw [hdist] at hb
    have hbound := abs_le.mp hb
    constructor
    · linarith [hbound.1]
    · have hid : (c - (R : ℝ) / q) +
          ((2 * R : ℕ) : ℝ) * (1 / (q : ℝ)) = c + (R : ℝ) / q := by
        push_cast
        ring
      rw [hid]
      linarith [hbound.2]
  have htsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y →
      1 / (q : ℝ) ≤ |x - y| := by
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have huv : u ≠ v := fun he => hxy (by simp [he])
    have hdist := hsep u hu v hv huv
    have hle := periodicDistance_le_abs_sub (f u) (f v)
    unfold periodicDistance at hle
    rw [hcoe u, hcoe v] at hle
    exact hdist.trans hle
  rw [← hcard]
  exact card_separated_Icc_le t (c - (R : ℝ) / q)
    (1 / (q : ℝ)) (2 * R) (by positivity) htbox htsep

/-- A circle annulus of width `K/q` contains at most `2(K+1)` points of a
`1/q`-separated set. The proof lifts the circle to a fundamental interval
centered at its target, then packs the positive and negative sides
separately. -/
theorem card_periodicSeparated_shell_le
    (s : Finset UnitAddCircle) (center : UnitAddCircle)
    (q K : ℕ) (hq : 0 < q) (lo hi : ℝ)
    (hwidth : hi ≤ lo + (K : ℝ) / q)
    (hsep : ∀ u ∈ s, ∀ v ∈ s, u ≠ v →
      1 / (q : ℝ) ≤ dist u v) :
    ((s.filter fun u => lo ≤ dist u center ∧ dist u center ≤ hi).card) ≤
      2 * (K + 1) := by
  classical
  let J : Finset UnitAddCircle := s.filter fun u =>
    lo ≤ dist u center ∧ dist u center ≤ hi
  let c : ℝ := (AddCircle.equivIco (1 : ℝ) 0 center).val
  let left : ℝ := c - 1 / 2
  let f : UnitAddCircle → ℝ :=
    fun u => (AddCircle.equivIco (1 : ℝ) left u).val
  let JP : Finset UnitAddCircle := J.filter fun u => c ≤ f u
  let JN : Finset UnitAddCircle := J.filter fun u => ¬ c ≤ f u
  let tP : Finset ℝ := JP.image f
  let tN : Finset ℝ := JN.image f
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : ((c : ℝ) : UnitAddCircle) = center := by
    simpa only [c] using
      (AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := center))
  have hcmem : c ∈ Set.Ico left (left + 1) := by
    dsimp [left]
    constructor <;> linarith
  have hf : Function.Injective f := by
    intro u v huv
    exact (AddCircle.equivIco (1 : ℝ) left).injective (Subtype.ext huv)
  have hcoe (u : UnitAddCircle) : ((f u : ℝ) : UnitAddCircle) = u := by
    simpa only [f] using
      (AddCircle.coe_equivIco (p := (1 : ℝ)) (a := left) (y := u))
  have hcoord (u : UnitAddCircle) : |f u - c| ≤ 1 / 2 := by
    have hu := (AddCircle.equivIco (1 : ℝ) left u).property
    simp only [Set.mem_Ico] at hu
    dsimp [f, left] at *
    apply abs_le.mpr
    constructor <;> linarith [hu.1, hu.2]
  have hdist (u : UnitAddCircle) : dist u center = |f u - c| := by
    have h := periodicDistance_eq_abs_sub_of_abs_le_half (hcoord u)
    unfold periodicDistance at h
    rw [hcoe u, hc] at h
    exact h
  have hcardP : tP.card = JP.card := Finset.card_image_iff.mpr (by
    intro u hu v hv huv
    exact hf huv)
  have hcardN : tN.card = JN.card := Finset.card_image_iff.mpr (by
    intro u hu v hv huv
    exact hf huv)
  have hsepP : ∀ x ∈ tP, ∀ y ∈ tP, x ≠ y →
      1 / (q : ℝ) ≤ |x - y| := by
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have huv : u ≠ v := fun he => hxy (by simp [he])
    have h := hsep u (s.filter_subset _ (J.filter_subset _ hu))
      v (s.filter_subset _ (J.filter_subset _ hv)) huv
    have hle := periodicDistance_le_abs_sub (f u) (f v)
    unfold periodicDistance at hle
    rw [hcoe u, hcoe v] at hle
    exact h.trans hle
  have hsepN : ∀ x ∈ tN, ∀ y ∈ tN, x ≠ y →
      1 / (q : ℝ) ≤ |x - y| := by
    intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have huv : u ≠ v := fun he => hxy (by simp [he])
    have h := hsep u (s.filter_subset _ (J.filter_subset _ hu))
      v (s.filter_subset _ (J.filter_subset _ hv)) huv
    have hle := periodicDistance_le_abs_sub (f u) (f v)
    unfold periodicDistance at hle
    rw [hcoe u, hcoe v] at hle
    exact h.trans hle
  have hboxP : ∀ x ∈ tP, c + lo ≤ x ∧
      x ≤ (c + lo) + (K : ℝ) / q := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    have huJ := (Finset.mem_filter.mp hu).1
    have hsign := (Finset.mem_filter.mp hu).2
    have hwindow := (Finset.mem_filter.mp huJ).2
    rw [hdist u] at hwindow
    have habs := abs_of_nonneg (sub_nonneg.mpr hsign)
    rw [habs] at hwindow
    constructor <;> linarith
  have hboxN : ∀ x ∈ tN, c - hi ≤ x ∧
      x ≤ (c - hi) + (K : ℝ) / q := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    have huJ := (Finset.mem_filter.mp hu).1
    have hsign := (Finset.mem_filter.mp hu).2
    have hwindow := (Finset.mem_filter.mp huJ).2
    rw [hdist u] at hwindow
    have hlt : f u < c := lt_of_not_ge hsign
    have habs := abs_of_neg (sub_neg.mpr hlt)
    rw [habs] at hwindow
    constructor <;> linarith
  have hK : (K : ℝ) / q = (K : ℝ) * (1 / (q : ℝ)) := by ring
  have hP : tP.card ≤ K + 1 := by
    have hb : ∀ x ∈ tP, c + lo ≤ x ∧
        x ≤ (c + lo) + (K : ℝ) * (1 / (q : ℝ)) := by
      simpa only [hK] using hboxP
    exact card_separated_Icc_le tP (c + lo) (1 / (q : ℝ)) K
      (by positivity) hb hsepP
  have hN : tN.card ≤ K + 1 := by
    have hb : ∀ x ∈ tN, c - hi ≤ x ∧
        x ≤ (c - hi) + (K : ℝ) * (1 / (q : ℝ)) := by
      simpa only [hK] using hboxN
    exact card_separated_Icc_le tN (c - hi) (1 / (q : ℝ)) K
      (by positivity) hb hsepN
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := J) (p := fun u => c ≤ f u)
  have hJcards : J.card = JP.card + JN.card := by
    dsimp [JP, JN]
    omega
  have hres : J.card ≤ 2 * (K + 1) := by
    rw [hJcards]
    omega
  simpa only [J] using hres

/-- A translated reduced rational grid has uniformly bounded occupancy
in a circle annulus of width `K/q`, independently of its distance from
the target. -/
theorem card_translatedRationalGrid_shell_le
    (a q K : ℕ) (hq : 0 < q) (hac : Nat.Coprime a q)
    (base target lo hi : ℝ)
    (hwidth : hi ≤ lo + (K : ℝ) / q) :
    ((Finset.range q).filter fun j =>
      lo ≤ periodicDistance (base + rationalCenter (a * j) q) target ∧
      periodicDistance (base + rationalCenter (a * j) q) target ≤ hi).card ≤
        2 * (K + 1) := by
  classical
  let J : Finset ℕ := (Finset.range q).filter fun j =>
    lo ≤ periodicDistance (base + rationalCenter (a * j) q) target ∧
    periodicDistance (base + rationalCenter (a * j) q) target ≤ hi
  let f : ℕ → UnitAddCircle := fun j =>
    ((base + rationalCenter (a * j) q : ℝ) : UnitAddCircle)
  let S : Finset UnitAddCircle := J.image f
  have hJ (j : ℕ) (hj : j ∈ J) : j < q := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hsepJ (j k : ℕ) (hj : j ∈ J) (hk : k ∈ J)
      (hjk : j ≠ k) : 1 / (q : ℝ) ≤ dist (f j) (f k) := by
    simpa only [f, periodicDistance] using
      translatedRationalGrid_periodicDistance_separated hq hac
        (hJ j hj) (hJ k hk) hjk base
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hfinj : Set.InjOn f ↑J := by
    intro j hj k hk heq
    by_contra hne
    have hsep := hsepJ j k hj hk hne
    rw [heq, dist_self] at hsep
    have hpos : (0 : ℝ) < 1 / (q : ℝ) := by positivity
    linarith
  have hcard : S.card = J.card := Finset.card_image_iff.mpr hfinj
  have hsepS : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      1 / (q : ℝ) ≤ dist u v := by
    intro u hu v hv huv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    have hjk : j ≠ k := by
      intro he
      exact huv (by simp [he])
    exact hsepJ j k hj hk hjk
  have hSfilter : S.filter (fun u =>
      lo ≤ dist u (target : UnitAddCircle) ∧
      dist u (target : UnitAddCircle) ≤ hi) = S := by
    apply Finset.filter_eq_self.mpr
    intro u hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    simpa [f, periodicDistance] using (Finset.mem_filter.mp hj).2
  have hbound := card_periodicSeparated_shell_le S
    (target : UnitAddCircle) q K hq lo hi hwidth hsepS
  rw [hSfilter] at hbound
  change J.card ≤ 2 * (K + 1)
  calc
    J.card = S.card := hcard.symm
    _ ≤ 2 * (K + 1) := hbound

/-- A phase shell in any translated block has constant occupancy when its
frequency is within `C/q²` of a reduced rational. The shell is enlarged by
`C/q` on both sides before applying grid packing. -/
theorem card_translatedBlock_shell_le_of_multiple
    {a q B C : ℕ} {alpha delta target : ℝ}
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + delta)
    (hdelta : |delta| ≤ (C : ℝ) / (q : ℝ) ^ 2)
    (k : ℕ) :
    ((Finset.range q).filter fun j =>
      (k : ℝ) / q ≤ periodicDistance (alpha * (B + j : ℕ)) target ∧
      periodicDistance (alpha * (B + j : ℕ)) target ≤
        ((k + 1 : ℕ) : ℝ) / q).card ≤ 2 * (2 * C + 2) := by
  classical
  let lo : ℝ := (k : ℝ) / q - (C : ℝ) / q
  let hi : ℝ := (k : ℝ) / q + ((1 + C : ℕ) : ℝ) / q
  let K : ℕ := 1 + 2 * C
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hwidthEq : hi = lo + (K : ℝ) / q := by
    dsimp [hi, lo, K]
    push_cast
    field_simp [ne_of_gt hqR]
    ring
  have hwidth : hi ≤ lo + (K : ℝ) / q := hwidthEq.le
  have hsubset :
      ((Finset.range q).filter fun j =>
        (k : ℝ) / q ≤ periodicDistance (alpha * (B + j : ℕ)) target ∧
        periodicDistance (alpha * (B + j : ℕ)) target ≤
          ((k + 1 : ℕ) : ℝ) / q) ⊆
        ((Finset.range q).filter fun j =>
          lo ≤ periodicDistance
            (alpha * (B : ℝ) + rationalCenter (a * j) q) target ∧
          periodicDistance
            (alpha * (B : ℝ) + rationalCenter (a * j) q) target ≤ hi) := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨hj'.1, ?_⟩
    have hclose := translatedBlock_close_to_rationalGrid_of_multiple
      (a := a) (q := q) (B := B) (j := j) (C := C)
      hq (Finset.mem_range.mp hj'.1) halpha hdelta
    have hclose' : periodicDistance
        (alpha * (B + j : ℕ))
        (alpha * (B : ℝ) + rationalCenter (a * j) q) ≤ (C : ℝ) / q := by
      exact hclose
    have htri₁ : periodicDistance
        (alpha * (B : ℝ) + rationalCenter (a * j) q) target ≤
        (C : ℝ) / q + periodicDistance (alpha * (B + j : ℕ)) target := by
      calc
        _ ≤ periodicDistance
            (alpha * (B : ℝ) + rationalCenter (a * j) q)
            (alpha * (B + j : ℕ)) +
            periodicDistance (alpha * (B + j : ℕ)) target := dist_triangle _ _ _
        _ ≤ _ := by
          have hc : periodicDistance
              (alpha * (B : ℝ) + rationalCenter (a * j) q)
              (alpha * (B + j : ℕ)) ≤ (C : ℝ) / q := by
            simpa [periodicDistance, dist_comm] using hclose'
          linarith
    have htri₂ : periodicDistance (alpha * (B + j : ℕ)) target ≤
        (C : ℝ) / q + periodicDistance
          (alpha * (B : ℝ) + rationalCenter (a * j) q) target := by
      calc
        _ ≤ periodicDistance (alpha * (B + j : ℕ))
            (alpha * (B : ℝ) + rationalCenter (a * j) q) +
            periodicDistance
              (alpha * (B : ℝ) + rationalCenter (a * j) q) target := dist_triangle _ _ _
        _ ≤ _ := by linarith [hclose']
    have hkadd : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hkadd] at hj'
    constructor
    · dsimp [lo]
      linarith [hj'.2.1, htri₂]
    · dsimp [hi]
      push_cast
      have hupper : (C : ℝ) / q + ((k : ℝ) + 1) / q =
          (k : ℝ) / q + (1 + (C : ℝ)) / q := by
        field_simp [ne_of_gt hqR]
        ring
      linarith [hj'.2.2, htri₁]
  have hgrid := card_translatedRationalGrid_shell_le a q K hq hac
    (alpha * (B : ℝ)) target lo hi hwidth
  have hcard := Finset.card_le_card hsubset
  dsimp [K] at hgrid
  omega

/-- Summing the zero-safe linear-character envelope over one thin shell
costs at most its occupancy times `Y` for the zero shell, or the reciprocal
of the shell's lower endpoint for every other shell. -/
theorem sum_translatedBlock_linearDistanceEnvelope_shell_le
    {a q B C : ℕ} {alpha delta : ℝ} (Y : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + delta)
    (hdelta : |delta| ≤ (C : ℝ) / (q : ℝ) ^ 2)
    (hY : 0 ≤ Y) (k : ℕ) :
    (∑ j ∈ ((Finset.range q).filter fun j =>
      (k : ℝ) / q ≤ periodicDistance (alpha * (B + j : ℕ)) 0 ∧
      periodicDistance (alpha * (B + j : ℕ)) 0 ≤
        ((k + 1 : ℕ) : ℝ) / q),
      linearDistanceEnvelope Y (alpha * (B + j : ℕ))) ≤
      ((2 * (2 * C + 2) : ℕ) : ℝ) *
        (if k = 0 then Y else (q : ℝ) / k) := by
  classical
  let J : Finset ℕ := (Finset.range q).filter fun j =>
    (k : ℝ) / q ≤ periodicDistance (alpha * (B + j : ℕ)) 0 ∧
    periodicDistance (alpha * (B + j : ℕ)) 0 ≤
      ((k + 1 : ℕ) : ℝ) / q
  let M : ℝ := if k = 0 then Y else (q : ℝ) / k
  have hM : 0 ≤ M := by
    dsimp [M]
    split_ifs with hk <;> positivity
  have hterm : ∀ j ∈ J,
      linearDistanceEnvelope Y (alpha * (B + j : ℕ)) ≤ M := by
    intro j hj
    have hshell := (Finset.mem_filter.mp hj).2.1
    by_cases hk : k = 0
    · subst k
      simpa [M] using linearDistanceEnvelope_le Y (alpha * (B + j : ℕ))
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have hrec := linearDistanceEnvelope_le_reciprocal_of_shell
        (Y := Y) (q := (q : ℝ)) (k := k)
        (theta := alpha * (B + j : ℕ)) hqR hkpos hshell
      simpa [M, hk] using hrec
  have hcount := card_translatedBlock_shell_le_of_multiple
    (a := a) (q := q) (B := B) (C := C)
    (alpha := alpha) (delta := delta) (target := 0)
    hq hac halpha hdelta k
  have hcountR : (J.card : ℝ) ≤ (2 * (2 * C + 2) : ℝ) := by
    exact_mod_cast hcount
  calc
    (∑ j ∈ J, linearDistanceEnvelope Y (alpha * (B + j : ℕ))) ≤
        ∑ j ∈ J, M := Finset.sum_le_sum hterm
    _ = (J.card : ℝ) * M := by simp
    _ ≤ (2 * (2 * C + 2) : ℝ) * M :=
      mul_le_mul_of_nonneg_right hcountR hM
    _ = ((2 * (2 * C + 2) : ℕ) : ℝ) *
        (if k = 0 then Y else (q : ℝ) / k) := by simp [M]

/-- Summing all shells of a translated block gives the corresponding
finite harmonic sum. The zero-distance shell is kept separate, so no
inverse at zero is used. -/
theorem sum_translatedBlock_linearDistanceEnvelope_le_harmonic
    {a q B C : ℕ} {alpha delta : ℝ} (Y : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + delta)
    (hdelta : |delta| ≤ (C : ℝ) / (q : ℝ) ^ 2)
    (hY : 0 ≤ Y) :
    (∑ j ∈ Finset.range q,
      linearDistanceEnvelope Y (alpha * (B + j : ℕ))) ≤
      ((2 * (2 * C + 2) : ℕ) : ℝ) *
        (∑ k ∈ Finset.range q, if k = 0 then Y else (q : ℝ) / k) := by
  classical
  let d : ℕ → ℝ := fun j => periodicDistance (alpha * (B + j : ℕ)) 0
  let bin : ℕ → ℕ := fun j => ⌊(q : ℝ) * d j⌋₊
  let J (k : ℕ) : Finset ℕ := Finset.filter (fun j => bin j = k) (Finset.range q)
  let S (k : ℕ) : Finset ℕ := (Finset.range q).filter fun j =>
    (k : ℝ) / q ≤ d j ∧ d j ≤ ((k + 1 : ℕ) : ℝ) / q
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdle (j : ℕ) : d j ≤ 1 / 2 := by
    dsimp [d]
    rw [periodicDistance_eq_abs_sub_round]
    simpa using abs_sub_round (alpha * (B + j : ℕ))
  have hscaled0 (j : ℕ) : 0 ≤ (q : ℝ) * d j := by
    exact mul_nonneg (by positivity) (dist_nonneg)
  have hscaledlt (j : ℕ) : (q : ℝ) * d j < q := by
    have h := mul_le_mul_of_nonneg_left (hdle j) (by positivity : (0 : ℝ) ≤ q)
    nlinarith [hqR]
  have hbin_lt (j : ℕ) : bin j < q := by
    apply Nat.floor_lt (hscaled0 j) |>.2
    exact_mod_cast hscaledlt j
  have hbin_shell (j : ℕ) :
      (bin j : ℝ) / q ≤ d j ∧
        d j ≤ ((bin j + 1 : ℕ) : ℝ) / q := by
    have hfloorlo : (bin j : ℝ) ≤ (q : ℝ) * d j := Nat.floor_le (hscaled0 j)
    have hfloorhi : (q : ℝ) * d j < (bin j : ℝ) + 1 := Nat.lt_floor_add_one _
    constructor
    · exact (div_le_iff₀ hqR).2 (by nlinarith [hfloorlo])
    · push_cast
      apply (le_div_iff₀ hqR).2
      nlinarith [hfloorhi]
  have hmaps : ∀ j ∈ Finset.range q, bin j ∈ Finset.range q := by
    intro j hj
    exact Finset.mem_range.mpr (hbin_lt j)
  have hnonneg (j : ℕ) :
      0 ≤ linearDistanceEnvelope Y (alpha * (B + j : ℕ)) :=
    linearDistanceEnvelope_nonneg (Y := Y) (theta := alpha * (B + j : ℕ)) hY
  have hfiber_subset (k : ℕ) : J k ⊆ S k := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    have hs := hbin_shell j
    have hs' : (k : ℝ) / q ≤ d j ∧
        d j ≤ ((k + 1 : ℕ) : ℝ) / q := by
      simpa only [hj'.2] using hs
    exact Finset.mem_filter.mpr ⟨hj'.1, hs'⟩
  have hsumFiberwise := Finset.sum_fiberwise_of_maps_to hmaps
    (fun j => linearDistanceEnvelope Y (alpha * (B + j : ℕ)))
  calc
    (∑ j ∈ Finset.range q,
        linearDistanceEnvelope Y (alpha * (B + j : ℕ))) =
      ∑ k ∈ Finset.range q,
        ∑ j ∈ J k, linearDistanceEnvelope Y (alpha * (B + j : ℕ)) := by
          simpa only [J] using hsumFiberwise.symm
    _ ≤ ∑ k ∈ Finset.range q,
        ((2 * (2 * C + 2) : ℕ) : ℝ) *
          (if k = 0 then Y else (q : ℝ) / k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg (hfiber_subset k)
        (by intro j hj hnot; exact hnonneg j)
      have hshell := sum_translatedBlock_linearDistanceEnvelope_shell_le
        (a := a) (q := q) (B := B) (C := C) (alpha := alpha)
        (delta := delta) Y hq hac halpha hdelta hY k
      exact hsub.trans (by simpa only [S] using hshell)
    _ = ((2 * (2 * C + 2) : ℕ) : ℝ) *
        (∑ k ∈ Finset.range q, if k = 0 then Y else (q : ℝ) / k) := by
      rw [Finset.mul_sum]

/-- The integral comparison for the harmonic series, in the one-step form
used to telescope the finite reciprocal sum. -/
theorem one_div_natCast_le_log_sub_pred {n : ℕ} (hn : 2 ≤ n) :
    1 / (n : ℝ) ≤
      Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    simp
  have hpredpos : 0 < (n : ℝ) - 1 := by rw [← hcast]; exact_mod_cast (by omega : 0 < n - 1)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hpredpos hnpos)
  rw [Real.log_div (ne_of_gt hpredpos) (ne_of_gt hnpos)] at hlog
  have hratio : ((n : ℝ) - 1) / n - 1 = -(1 / (n : ℝ)) := by
    field_simp
    ring
  rw [hratio] at hlog
  rw [hcast]
  linarith

/-- The finite harmonic sum up to `q-1` is at most `1 + log (q-1)`. -/
theorem sum_range_reciprocal_le_one_add_log_pred {q : ℕ} (hq : 2 ≤ q) :
    (∑ k ∈ Finset.range q, if k = 0 then (0 : ℝ) else 1 / k) ≤
      1 + Real.log ((q - 1 : ℕ) : ℝ) := by
  classical
  induction q using Nat.strong_induction_on with
  | h q ih =>
      by_cases hq2 : q = 2
      · subst q
        norm_num [Finset.sum_range_succ]
      have hq3 : 3 ≤ q := by omega
      have hrec :
          (∑ k ∈ Finset.range q, if k = 0 then (0 : ℝ) else 1 / k) =
            (∑ k ∈ Finset.range (q - 1), if k = 0 then (0 : ℝ) else 1 / k) +
              1 / ((q - 1 : ℕ) : ℝ) := by
        rw [show q = (q - 1) + 1 by omega, Finset.sum_range_succ]
        simp [show q - 1 ≠ 0 by omega]
      have hprev := ih (q - 1) (by omega) (by omega)
      have hstep := one_div_natCast_le_log_sub_pred (n := q - 1) (by omega)
      have hcombine :
          (1 + Real.log (((q - 1) - 1 : ℕ) : ℝ)) +
            1 / ((q - 1 : ℕ) : ℝ) ≤
              1 + Real.log ((q - 1 : ℕ) : ℝ) := by
        linarith [hstep]
      rw [hrec]
      linarith [hprev, hcombine]

/-- The finite reciprocal sum, including its zero term, is bounded by a
logarithm. The `q=1` case is empty and is handled separately. -/
theorem sum_range_reciprocal_le_one_add_log {q : ℕ} (hq : 0 < q) :
    (∑ k ∈ Finset.range q, if k = 0 then (0 : ℝ) else 1 / k) ≤
      1 + Real.log (q : ℝ) := by
  by_cases hq1 : q = 1
  · subst q
    norm_num
  have hq2 : 2 ≤ q := by omega
  have h := sum_range_reciprocal_le_one_add_log_pred hq2
  have hmono : Real.log ((q - 1 : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by exact_mod_cast (by omega : 0 < q - 1))
    · exact Set.mem_Ioi.mpr (by exact_mod_cast hq)
    · exact_mod_cast (by omega : q - 1 ≤ q)
  linarith

/-- Bounding the finite bin weights by the harmonic estimate gives a
logarithmic per-block cost. -/
theorem sum_zeroThenReciprocal_range_le
    {q : ℕ} {Y : ℝ} (hq : 0 < q) :
    (∑ k ∈ Finset.range q, if k = 0 then Y else (q : ℝ) / k) ≤
      Y + (q : ℝ) * (1 + Real.log (q : ℝ)) := by
  have hrecip :
      (∑ k ∈ Finset.range q, if k = 0 then (0 : ℝ) else 1 / k) ≤
        1 + Real.log (q : ℝ) := sum_range_reciprocal_le_one_add_log hq
  have hsplit :
      (∑ k ∈ Finset.range q, if k = 0 then Y else (q : ℝ) / k) =
        Y + (q : ℝ) *
          (∑ k ∈ Finset.range q, if k = 0 then (0 : ℝ) else 1 / k) := by
    calc
      _ = ∑ k ∈ Finset.range q,
          ((if k = 0 then Y else 0) +
            (q : ℝ) * (if k = 0 then (0 : ℝ) else 1 / k)) := by
              apply Finset.sum_congr rfl
              intro k hk
              by_cases hk0 : k = 0
              · simp [hk0]
              · simp [hk0, div_eq_mul_inv]
      _ = Y + (q : ℝ) *
          (∑ k ∈ Finset.range q, if k = 0 then (0 : ℝ) else 1 / k) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            have hfirst :
                (∑ k ∈ Finset.range q, if k = 0 then Y else (0 : ℝ)) = Y := by
              simp [Finset.sum_ite_eq', hq]
            rw [hfirst]
  rw [hsplit]
  have hm := mul_le_mul_of_nonneg_left hrecip (by positivity : (0 : ℝ) ≤ q)
  linarith [hm]

/-- One translated denominator block costs at most its trivial contribution
plus a logarithmic harmonic factor. -/
theorem sum_translatedBlock_linearDistanceEnvelope_le_log
    {a q B C : ℕ} {alpha delta : ℝ} (Y : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + delta)
    (hdelta : |delta| ≤ (C : ℝ) / (q : ℝ) ^ 2)
    (hY : 0 ≤ Y) :
    (∑ j ∈ Finset.range q,
      linearDistanceEnvelope Y (alpha * (B + j : ℕ))) ≤
      ((2 * (2 * C + 2) : ℕ) : ℝ) *
        (Y + (q : ℝ) * (1 + Real.log (q : ℝ))) := by
  calc
    _ ≤ ((2 * (2 * C + 2) : ℕ) : ℝ) *
        (∑ k ∈ Finset.range q, if k = 0 then Y else (q : ℝ) / k) :=
      sum_translatedBlock_linearDistanceEnvelope_le_harmonic
        Y hq hac halpha hdelta hY
    _ ≤ ((2 * (2 * C + 2) : ℕ) : ℝ) *
        (Y + (q : ℝ) * (1 + Real.log (q : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
      · exact sum_zeroThenReciprocal_range_le hq
      · positivity

/-- The block bound applies directly to the differenced frequency `6α` by
reducing its rational denominator to `q / gcd(q,6)`. -/
theorem sum_sixMul_translatedBlock_linearDistanceEnvelope_le_log
    {a q B : ℕ} {alpha beta : ℝ} (Y : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) (hY : 0 ≤ Y) :
    (∑ j ∈ Finset.range (q / Nat.gcd q 6),
      linearDistanceEnvelope Y ((6 * alpha) * (B + j : ℕ))) ≤
      28 * (Y + ((q / Nat.gcd q 6 : ℕ) : ℝ) *
        (1 + Real.log ((q / Nat.gcd q 6 : ℕ) : ℝ))) := by
  let q₀ := q / Nat.gcd q 6
  let a₀ := (6 * a) / Nat.gcd q 6
  have hgq : Nat.gcd q 6 ∣ q := Nat.gcd_dvd_left q 6
  have hfactor : q = q₀ * Nat.gcd q 6 := by
    dsimp [q₀]
    exact (Nat.div_mul_cancel hgq).symm
  have hq₀ne : q₀ ≠ 0 := by
    intro hzero
    rw [hzero] at hfactor
    simp at hfactor
    exact (Nat.ne_of_gt hq) hfactor
  have hq₀pos : 0 < q₀ := Nat.pos_of_ne_zero hq₀ne
  have hq₀le : q₀ ≤ q := by
    dsimp [q₀]
    exact Nat.div_le_self q (Nat.gcd q 6)
  have hq₀leR : (q₀ : ℝ) ≤ q := by exact_mod_cast hq₀le
  have hden : 1 / (q : ℝ) ^ 2 ≤ 1 / (q₀ : ℝ) ^ 2 := by
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  have hbeta₀ : |6 * beta| ≤ (6 : ℝ) / (q₀ : ℝ) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    calc
      6 * |beta| ≤ 6 * (1 / (q : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hbeta (by norm_num)
      _ ≤ 6 * (1 / (q₀ : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hden (by norm_num)
      _ = (6 : ℝ) / (q₀ : ℝ) ^ 2 := by ring
  have ha₀cop : Nat.Coprime a₀ q₀ := by
    dsimp [a₀, q₀]
    exact six_mul_rational_reduction_coprime a q hq hac
  have halpha₀ : (6 * alpha : ℝ) = rationalCenter a₀ q₀ + 6 * beta := by
    dsimp [a₀, q₀]
    exact six_mul_approximation_eq_reduced a q alpha beta hq halpha
  have hblock := sum_translatedBlock_linearDistanceEnvelope_le_log
    (a := a₀) (q := q₀) (B := B) (C := 6)
    (alpha := 6 * alpha) (delta := 6 * beta) Y
    hq₀pos ha₀cop halpha₀ hbeta₀ hY
  simpa [q₀, a₀] using hblock

/-- The `6α` translated-block estimate with a general approximation error
constant `K`: if `|β|≤K/q²`, the shell occupancy grows linearly with `K`. -/
theorem sum_sixMul_translatedBlock_linearDistanceEnvelope_le_log_of_error_constant
    {a q B K : ℕ} {alpha beta : ℝ} (Y : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + beta)
    (hbeta : |beta| ≤ (K : ℝ) / (q : ℝ) ^ 2) (hY : 0 ≤ Y) :
    (∑ j ∈ Finset.range (q / Nat.gcd q 6),
      linearDistanceEnvelope Y ((6 * alpha) * (B + j : ℕ))) ≤
      ((2 * (2 * (6 * K) + 2) : ℕ) : ℝ) *
        (Y + ((q / Nat.gcd q 6 : ℕ) : ℝ) *
          (1 + Real.log ((q / Nat.gcd q 6 : ℕ) : ℝ))) := by
  let q₀ := q / Nat.gcd q 6
  let a₀ := (6 * a) / Nat.gcd q 6
  have hgq : Nat.gcd q 6 ∣ q := Nat.gcd_dvd_left q 6
  have hfactor : q = q₀ * Nat.gcd q 6 := by
    dsimp [q₀]
    exact (Nat.div_mul_cancel hgq).symm
  have hq₀ne : q₀ ≠ 0 := by
    intro hzero
    rw [hzero] at hfactor
    simp at hfactor
    exact (Nat.ne_of_gt hq) hfactor
  have hq₀pos : 0 < q₀ := Nat.pos_of_ne_zero hq₀ne
  have hq₀le : q₀ ≤ q := by
    dsimp [q₀]
    exact Nat.div_le_self q (Nat.gcd q 6)
  have hq₀leR : (q₀ : ℝ) ≤ q := by exact_mod_cast hq₀le
  have hden : 1 / (q : ℝ) ^ 2 ≤ 1 / (q₀ : ℝ) ^ 2 := by
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  have hbeta₀ : |6 * beta| ≤ ((6 * K : ℕ) : ℝ) / (q₀ : ℝ) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    calc
      6 * |beta| ≤ 6 * ((K : ℝ) / (q : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hbeta (by norm_num)
      _ = (6 * (K : ℝ)) * (1 / (q : ℝ) ^ 2) := by ring
      _ ≤ (6 * (K : ℝ)) * (1 / (q₀ : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
      _ = ((6 * K : ℕ) : ℝ) / (q₀ : ℝ) ^ 2 := by
        push_cast
        ring
  have ha₀cop : Nat.Coprime a₀ q₀ := by
    dsimp [a₀, q₀]
    exact six_mul_rational_reduction_coprime a q hq hac
  have halpha₀ : (6 * alpha : ℝ) =
      rationalCenter a₀ q₀ + 6 * beta := by
    dsimp [a₀, q₀]
    exact six_mul_approximation_eq_reduced a q alpha beta hq halpha
  have hblock := sum_translatedBlock_linearDistanceEnvelope_le_log
    (a := a₀) (q := q₀) (B := B) (C := 6 * K)
    (alpha := 6 * alpha) (delta := 6 * beta) Y
    hq₀pos ha₀cop halpha₀ hbeta₀ hY
  simpa [q₀, a₀] using hblock

/-- Reindex a natural interval whose length is a multiple of `q` by its
consecutive `q`-blocks. -/
theorem sum_range_mul_eq_sum_blocks {m q : ℕ} (f : ℕ → ℝ) :
    (∑ r ∈ Finset.range (m * q), f r) =
      ∑ k ∈ Finset.range m, ∑ j ∈ Finset.range q, f (j + q * k) := by
  classical
  conv_lhs => rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ i : Fin (m * q), f i) =
        ∑ p : Fin m × Fin q, f (p.2.val + q * p.1.val) := by
      symm
      exact Fintype.sum_equiv finProdFinEquiv
        (fun p : Fin m × Fin q => f (p.2.val + q * p.1.val))
        (fun i : Fin (m * q) => f i.val) (by intro p; simp [finProdFinEquiv])
    _ = ∑ k : Fin m, ∑ j : Fin q, f (j.val + q * k.val) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ k : Fin m, ∑ j ∈ Finset.range q, f (j + q * k.val) := by
      apply Fintype.sum_congr
      intro k
      exact Fin.sum_univ_eq_sum_range
        (fun j : ℕ => f (j + q * k.val)) q
    _ = ∑ k ∈ Finset.range m, ∑ j ∈ Finset.range q, f (j + q * k) := by
      exact Fin.sum_univ_eq_sum_range
        (fun k : ℕ => ∑ j ∈ Finset.range q, f (j + q * k)) m

/-- Summing the `6α` envelope over an interval made of full reduced-
denominator blocks costs the number of blocks times the one-block bound. -/
theorem sum_sixMul_linearDistanceEnvelope_range_mul_le
    {a q B m : ℕ} {alpha beta : ℝ} (Y : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) (hY : 0 ≤ Y) :
    (∑ r ∈ Finset.range (m * (q / Nat.gcd q 6)),
      linearDistanceEnvelope Y ((6 * alpha) * (B + r : ℕ))) ≤
      (m : ℝ) *
        (28 * (Y + ((q / Nat.gcd q 6 : ℕ) : ℝ) *
          (1 + Real.log ((q / Nat.gcd q 6 : ℕ) : ℝ)))) := by
  let q₀ := q / Nat.gcd q 6
  have hq₀pos : 0 < q₀ := by
    have hgq : Nat.gcd q 6 ∣ q := Nat.gcd_dvd_left q 6
    have hfactor : q = q₀ * Nat.gcd q 6 := by
      dsimp [q₀]
      exact (Nat.div_mul_cancel hgq).symm
    have hq₀ne : q₀ ≠ 0 := by
      intro hz
      rw [hz] at hfactor
      simp at hfactor
      exact (Nat.ne_of_gt hq) hfactor
    exact Nat.pos_of_ne_zero hq₀ne
  have hblock (k : ℕ) :
      (∑ j ∈ Finset.range q₀,
        linearDistanceEnvelope Y ((6 * alpha) * (B + (j + q₀ * k) : ℕ))) ≤
        28 * (Y + (q₀ : ℝ) * (1 + Real.log (q₀ : ℝ))) := by
    have h := sum_sixMul_translatedBlock_linearDistanceEnvelope_le_log
      (a := a) (q := q) (B := B + q₀ * k) (alpha := alpha) (beta := beta) Y
      hq hac halpha hbeta hY
    have hshift :
        (∑ j ∈ Finset.range q₀,
          linearDistanceEnvelope Y ((6 * alpha) *
            (B + (j + q₀ * k) : ℕ))) =
          ∑ j ∈ Finset.range q₀,
            linearDistanceEnvelope Y ((6 * alpha) *
              (B + q₀ * k + j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show B + (j + q₀ * k) = B + q₀ * k + j by omega]
    calc
      _ = ∑ j ∈ Finset.range q₀,
          linearDistanceEnvelope Y ((6 * alpha) * (B + q₀ * k + j : ℕ)) := hshift
      _ ≤ 28 * (Y + (q₀ : ℝ) * (1 + Real.log (q₀ : ℝ))) := by
        simpa [q₀] using h
  calc
    _ = ∑ k ∈ Finset.range m, ∑ j ∈ Finset.range q₀,
        linearDistanceEnvelope Y ((6 * alpha) * (B + (j + q₀ * k) : ℕ)) := by
      exact sum_range_mul_eq_sum_blocks
        (m := m) (q := q₀)
        (fun r => linearDistanceEnvelope Y ((6 * alpha) * (B + r : ℕ)))
    _ ≤ ∑ k ∈ Finset.range m,
        28 * (Y + (q₀ : ℝ) * (1 + Real.log (q₀ : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hblock k
    _ = (m : ℝ) *
        (28 * (Y + (q₀ : ℝ) * (1 + Real.log (q₀ : ℝ)))) := by
      simp

/-- An arbitrary initial interval is bounded by extending it to the next
whole number of reduced-denominator blocks; nonnegativity makes the added
tail harmless. -/
theorem sum_sixMul_linearDistanceEnvelope_range_le
    {a q B R : ℕ} {alpha beta : ℝ} (Y : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) (hY : 0 ≤ Y) :
    (∑ r ∈ Finset.range R,
      linearDistanceEnvelope Y ((6 * alpha) * (B + r : ℕ))) ≤
      ((R / (q / Nat.gcd q 6) + 1 : ℕ) : ℝ) *
        (28 * (Y + ((q / Nat.gcd q 6 : ℕ) : ℝ) *
          (1 + Real.log ((q / Nat.gcd q 6 : ℕ) : ℝ)))) := by
  let q₀ := q / Nat.gcd q 6
  let m := R / q₀ + 1
  have hq₀pos : 0 < q₀ := by
    have hgq : Nat.gcd q 6 ∣ q := Nat.gcd_dvd_left q 6
    have hfactor : q = q₀ * Nat.gcd q 6 := by
      dsimp [q₀]
      exact (Nat.div_mul_cancel hgq).symm
    have hq₀ne : q₀ ≠ 0 := by
      intro hz
      rw [hz] at hfactor
      simp at hfactor
      exact (Nat.ne_of_gt hq) hfactor
    exact Nat.pos_of_ne_zero hq₀ne
  have hRle : R ≤ m * q₀ := by
    have hdecomp : R % q₀ + q₀ * (R / q₀) = R := Nat.mod_add_div _ _
    have hmod : R % q₀ < q₀ := Nat.mod_lt _ hq₀pos
    have hdecomp' : R % q₀ + (R / q₀) * q₀ = R := by
      simpa [Nat.mul_comm] using hdecomp
    dsimp [m]
    rw [Nat.add_mul, one_mul]
    omega
  have hnonneg (r : ℕ) :
      0 ≤ linearDistanceEnvelope Y ((6 * alpha) * (B + r : ℕ)) :=
    linearDistanceEnvelope_nonneg (Y := Y)
      (theta := (6 * alpha) * (B + r : ℕ)) hY
  have hsubset : Finset.range R ⊆ Finset.range (m * q₀) :=
    Finset.range_mono hRle
  calc
    _ ≤ ∑ r ∈ Finset.range (m * q₀),
        linearDistanceEnvelope Y ((6 * alpha) * (B + r : ℕ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (by intro r hr hnot; exact hnonneg r)
    _ ≤ (m : ℝ) *
        (28 * (Y + (q₀ : ℝ) * (1 + Real.log (q₀ : ℝ)))) := by
      exact sum_sixMul_linearDistanceEnvelope_range_mul_le
        (a := a) (q := q) (B := B) (m := m) Y
        hq hac halpha hbeta hY

/-- Arbitrary translated intervals with a scale-dependent rational error.
The occupancy cost is explicit in `K`, with no assumption that `K=1`. -/
theorem sum_sixMul_linearDistanceEnvelope_range_le_of_error_constant
    {a q B R K : ℕ} {alpha beta : ℝ} (Y : ℝ)
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + beta)
    (hbeta : |beta| ≤ (K : ℝ) / (q : ℝ) ^ 2) (hY : 0 ≤ Y) :
    (∑ r ∈ Finset.range R,
      linearDistanceEnvelope Y ((6 * alpha) * (B + r : ℕ))) ≤
      ((R / (q / Nat.gcd q 6) + 1 : ℕ) : ℝ) *
        ((2 * (2 * (6 * K) + 2) : ℕ) : ℝ) *
          (Y + ((q / Nat.gcd q 6 : ℕ) : ℝ) *
            (1 + Real.log ((q / Nat.gcd q 6 : ℕ) : ℝ))) := by
  let q₀ := q / Nat.gcd q 6
  let m := R / q₀ + 1
  have hq₀pos : 0 < q₀ := by
    have hgq : Nat.gcd q 6 ∣ q := Nat.gcd_dvd_left q 6
    have hfactor : q = q₀ * Nat.gcd q 6 := by
      dsimp [q₀]
      exact (Nat.div_mul_cancel hgq).symm
    have hq₀ne : q₀ ≠ 0 := by
      intro hz
      rw [hz] at hfactor
      simp at hfactor
      exact (Nat.ne_of_gt hq) hfactor
    exact Nat.pos_of_ne_zero hq₀ne
  have hRle : R ≤ m * q₀ := by
    have hdecomp : R % q₀ + q₀ * (R / q₀) = R := Nat.mod_add_div _ _
    have hmod : R % q₀ < q₀ := Nat.mod_lt _ hq₀pos
    have hdecomp' : R % q₀ + (R / q₀) * q₀ = R := by
      simpa [Nat.mul_comm] using hdecomp
    dsimp [m]
    rw [Nat.add_mul, one_mul]
    omega
  have hnonneg (r : ℕ) :
      0 ≤ linearDistanceEnvelope Y ((6 * alpha) * (B + r : ℕ)) :=
    linearDistanceEnvelope_nonneg (Y := Y)
      (theta := (6 * alpha) * (B + r : ℕ)) hY
  have hsubset : Finset.range R ⊆ Finset.range (m * q₀) :=
    Finset.range_mono hRle
  have hblock (k : ℕ) :
      (∑ j ∈ Finset.range q₀,
        linearDistanceEnvelope Y ((6 * alpha) * ((B + (j + q₀ * k)) : ℕ))) ≤
        ((2 * (2 * (6 * K) + 2) : ℕ) : ℝ) *
          (Y + (q₀ : ℝ) * (1 + Real.log (q₀ : ℝ))) := by
    have h := sum_sixMul_translatedBlock_linearDistanceEnvelope_le_log_of_error_constant
      (a := a) (q := q) (B := B + q₀ * k) (K := K)
      (alpha := alpha) (beta := beta) Y hq hac halpha hbeta hY
    have hshift :
        (∑ j ∈ Finset.range q₀,
          linearDistanceEnvelope Y ((6 * alpha) * ((B + (j + q₀ * k)) : ℕ))) =
        ∑ j ∈ Finset.range q₀,
          linearDistanceEnvelope Y ((6 * alpha) * ((B + q₀ * k + j) : ℕ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show B + (j + q₀ * k) = B + q₀ * k + j by omega]
    calc
      _ = ∑ j ∈ Finset.range q₀,
          linearDistanceEnvelope Y ((6 * alpha) * ((B + q₀ * k + j) : ℕ)) := hshift
      _ ≤ ((2 * (2 * (6 * K) + 2) : ℕ) : ℝ) *
          (Y + (q₀ : ℝ) * (1 + Real.log (q₀ : ℝ))) := by
        simpa [q₀] using h
  calc
    _ ≤ ∑ r ∈ Finset.range (m * q₀),
        linearDistanceEnvelope Y ((6 * alpha) * (B + r : ℕ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (by intro r hr hnot; exact hnonneg r)
    _ = ∑ k ∈ Finset.range m, ∑ j ∈ Finset.range q₀,
        linearDistanceEnvelope Y ((6 * alpha) * ((B + (j + q₀ * k)) : ℕ)) := by
      exact sum_range_mul_eq_sum_blocks
        (m := m) (q := q₀)
        (fun r => linearDistanceEnvelope Y ((6 * alpha) * ((B + r) : ℕ)))
    _ ≤ ∑ k ∈ Finset.range m,
        ((2 * (2 * (6 * K) + 2) : ℕ) : ℝ) *
          (Y + (q₀ : ℝ) * (1 + Real.log (q₀ : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hblock k
    _ = (m : ℝ) * ((2 * (2 * (6 * K) + 2) : ℕ) : ℝ) *
        (Y + (q₀ : ℝ) * (1 + Real.log (q₀ : ℝ))) := by simp; ring
    _ ≤ ((R / q₀ + 1 : ℕ) : ℝ) *
        ((2 * (2 * (6 * K) + 2) : ℕ) : ℝ) *
          (Y + (q₀ : ℝ) * (1 + Real.log (q₀ : ℝ))) := by rfl
/-- The actual differenced frequency `6α` has a uniformly bounded
thin-shell count on translated blocks, with the reduced denominator
`q/gcd(q,6)`. -/
theorem card_six_mul_translatedBlock_shell_le
    {a q B : ℕ} {alpha beta target : ℝ}
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) (k : ℕ) :
    ((Finset.range (q / Nat.gcd q 6)).filter fun j =>
      (k : ℝ) / (q / Nat.gcd q 6 : ℕ) ≤
        periodicDistance ((6 * alpha) * (B + j : ℕ)) target ∧
      periodicDistance ((6 * alpha) * (B + j : ℕ)) target ≤
        ((k + 1 : ℕ) : ℝ) / (q / Nat.gcd q 6 : ℕ)).card ≤ 28 := by
  let q₀ := q / Nat.gcd q 6
  let a₀ := (6 * a) / Nat.gcd q 6
  have hgq : Nat.gcd q 6 ∣ q := Nat.gcd_dvd_left q 6
  have hfactor : q = q₀ * Nat.gcd q 6 := by
    dsimp [q₀]
    exact (Nat.div_mul_cancel hgq).symm
  have hq₀ne : q₀ ≠ 0 := by
    intro hzero
    rw [hzero] at hfactor
    simp at hfactor
    exact (Nat.ne_of_gt hq) hfactor
  have hq₀pos : 0 < q₀ := Nat.pos_of_ne_zero hq₀ne
  have hq₀le : q₀ ≤ q := by
    dsimp [q₀]
    exact Nat.div_le_self q (Nat.gcd q 6)
  have hq₀leR : (q₀ : ℝ) ≤ q := by exact_mod_cast hq₀le
  have hq₀posR : (0 : ℝ) < q₀ := by exact_mod_cast hq₀pos
  have hden : 1 / (q : ℝ) ^ 2 ≤ 1 / (q₀ : ℝ) ^ 2 := by
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  have hbeta₀ : |6 * beta| ≤ (6 : ℝ) / (q₀ : ℝ) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    calc
      6 * |beta| ≤ 6 * (1 / (q : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hbeta (by norm_num)
      _ ≤ 6 * (1 / (q₀ : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hden (by norm_num)
      _ = (6 : ℝ) / (q₀ : ℝ) ^ 2 := by ring
  have ha₀cop : Nat.Coprime a₀ q₀ := by
    dsimp [a₀, q₀]
    exact six_mul_rational_reduction_coprime a q hq hac
  have halpha₀ : (6 * alpha : ℝ) = rationalCenter a₀ q₀ + 6 * beta := by
    dsimp [a₀, q₀]
    exact six_mul_approximation_eq_reduced a q alpha beta hq halpha
  have hbound := card_translatedBlock_shell_le_of_multiple
    (a := a₀) (q := q₀) (B := B) (C := 6)
    (alpha := 6 * alpha) (delta := 6 * beta) (target := target)
    hq₀pos ha₀cop halpha₀ hbeta₀ k
  simpa [q₀] using hbound

/-- A translated reduced rational grid has uniformly bounded occupancy
in a circle ball whose radius is a fixed number of grid spacings. -/
theorem card_translatedRationalGrid_ball_le
    (a q R : ℕ) (hq : 0 < q) (hac : Nat.Coprime a q)
    (base target : ℝ) :
    ((Finset.range q).filter fun j =>
      periodicDistance (base + rationalCenter (a * j) q) target ≤
        (R : ℝ) / q).card ≤ 2 * R + 1 := by
  classical
  let J : Finset ℕ := (Finset.range q).filter fun j =>
    periodicDistance (base + rationalCenter (a * j) q) target ≤
      (R : ℝ) / q
  let f : ℕ → UnitAddCircle := fun j =>
    ((base + rationalCenter (a * j) q : ℝ) : UnitAddCircle)
  let S : Finset UnitAddCircle := J.image f
  have hJ (j : ℕ) (hj : j ∈ J) :
      j < q ∧ periodicDistance
        (base + rationalCenter (a * j) q) target ≤ (R : ℝ) / q := by
    simpa only [J, Finset.mem_filter, Finset.mem_range] using hj
  have hsepJ (j k : ℕ) (hj : j ∈ J) (hk : k ∈ J)
      (hjk : j ≠ k) : 1 / (q : ℝ) ≤ dist (f j) (f k) := by
    simpa only [f, periodicDistance] using
      translatedRationalGrid_periodicDistance_separated hq hac
        (hJ j hj).1 (hJ k hk).1 hjk base
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hfinj : Set.InjOn f ↑J := by
    intro j hj k hk heq
    by_contra hne
    have hsep := hsepJ j k hj hk hne
    rw [heq, dist_self] at hsep
    have hpos : (0 : ℝ) < 1 / (q : ℝ) := by positivity
    linarith
  have hcard : S.card = J.card := Finset.card_image_iff.mpr hfinj
  have hsepS : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      1 / (q : ℝ) ≤ dist u v := by
    intro u hu v hv huv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    have hjk : j ≠ k := by
      intro he
      exact huv (by simp [he])
    exact hsepJ j k hj hk hjk
  have hballS : ∀ u ∈ S, dist u (target : UnitAddCircle) ≤
      (R : ℝ) / q := by
    intro u hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    exact (hJ j hj).2
  have hbound := card_periodicSeparated_ball_le S
    (target : UnitAddCircle) q R hq hsepS hballS
  simpa only [J, hcard] using hbound

/-- The same fixed-radius occupancy bound for the perturbed phase on
any translated `q`-block. The extra one-grid-spacing enlargement costs
exactly two possible points in this coarse ball count. -/
theorem card_translatedBlock_ball_le
    {a q B R : ℕ} {alpha delta target : ℝ}
    (hq : 0 < q) (hac : Nat.Coprime a q)
    (halpha : alpha = rationalCenter a q + delta)
    (hdelta : |delta| ≤ 1 / (q : ℝ) ^ 2) :
    ((Finset.range q).filter fun j =>
      periodicDistance (alpha * (B + j : ℕ)) target ≤
        (R : ℝ) / q).card ≤ 2 * R + 3 := by
  classical
  have hsubset :
      ((Finset.range q).filter fun j =>
        periodicDistance (alpha * (B + j : ℕ)) target ≤
          (R : ℝ) / q) ⊆
        ((Finset.range q).filter fun j =>
          periodicDistance
            (alpha * (B : ℝ) + rationalCenter (a * j) q) target ≤
              ((R + 1 : ℕ) : ℝ) / q) := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨hj'.1, ?_⟩
    have hclose := translatedBlock_gridPoint_le_of_phase_le
      (a := a) (q := q) (B := B) (j := j)
      hq (Finset.mem_range.mp hj'.1) halpha hdelta hj'.2
    simpa only [Nat.cast_add, Nat.cast_one, add_div] using hclose
  have hgrid := card_translatedRationalGrid_ball_le a q (R + 1)
    hq hac (alpha * (B : ℝ)) target
  have hcard := Finset.card_le_card hsubset
  omega

end CookMagyarCircle
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarCircle.card_periodicSeparated_shell_le
#print axioms SystolicGrowth.CookMagyarCircle.card_translatedRationalGrid_shell_le
#print axioms SystolicGrowth.CookMagyarCircle.translatedBlock_close_to_rationalGrid_of_multiple
#print axioms SystolicGrowth.CookMagyarCircle.card_translatedBlock_shell_le_of_multiple
#print axioms SystolicGrowth.CookMagyarCircle.six_mul_rational_reduction_coprime
#print axioms SystolicGrowth.CookMagyarCircle.six_mul_rationalCenter_eq_reduced
#print axioms SystolicGrowth.CookMagyarCircle.six_mul_reduced_denominator_bounds
#print axioms SystolicGrowth.CookMagyarCircle.six_mul_approximation_eq_reduced
#print axioms SystolicGrowth.CookMagyarCircle.card_six_mul_translatedBlock_shell_le
#print axioms SystolicGrowth.CookMagyarCircle.linearDistanceEnvelope_le
#print axioms SystolicGrowth.CookMagyarCircle.linearDistanceEnvelope_nonneg
#print axioms SystolicGrowth.CookMagyarCircle.linearDistanceEnvelope_le_reciprocal_of_shell
#print axioms SystolicGrowth.CookMagyarCircle.sum_translatedBlock_linearDistanceEnvelope_shell_le
#print axioms SystolicGrowth.CookMagyarCircle.sum_translatedBlock_linearDistanceEnvelope_le_harmonic
#print axioms SystolicGrowth.CookMagyarCircle.one_div_natCast_le_log_sub_pred
#print axioms SystolicGrowth.CookMagyarCircle.sum_range_reciprocal_le_one_add_log_pred
#print axioms SystolicGrowth.CookMagyarCircle.sum_range_reciprocal_le_one_add_log
#print axioms SystolicGrowth.CookMagyarCircle.sum_zeroThenReciprocal_range_le
#print axioms SystolicGrowth.CookMagyarCircle.sum_translatedBlock_linearDistanceEnvelope_le_log
#print axioms SystolicGrowth.CookMagyarCircle.sum_sixMul_translatedBlock_linearDistanceEnvelope_le_log
#print axioms SystolicGrowth.CookMagyarCircle.sum_range_mul_eq_sum_blocks
#print axioms SystolicGrowth.CookMagyarCircle.sum_sixMul_linearDistanceEnvelope_range_mul_le
#print axioms SystolicGrowth.CookMagyarCircle.sum_sixMul_linearDistanceEnvelope_range_le
#print axioms SystolicGrowth.CookMagyarCircle.sum_sixMul_translatedBlock_linearDistanceEnvelope_le_log_of_error_constant
#print axioms SystolicGrowth.CookMagyarCircle.sum_sixMul_linearDistanceEnvelope_range_le_of_error_constant

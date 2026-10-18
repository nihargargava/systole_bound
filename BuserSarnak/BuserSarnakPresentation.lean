module

public import BuserSarnak.BuserSarnakMarking

@[expose] public section

namespace SystolicGrowth

abbrev BSUnit23 := BuserSarnakQuaternionUnit 2 3

def octagonSign : Bool → ℤ
  | false => -1
  | true => 1

inductive OctagonGenerator where
  | center
  | A (s : Bool)
  | C (s : Bool)
  | B (s t : Bool)
  deriving DecidableEq, Fintype

def octagonUnit : OctagonGenerator → BSUnit23
  | .center => ⟨-1, 0, 0, 0, by norm_num⟩
  | .A s => ⟨3, 2 * octagonSign s, 0, 0, by cases s <;> norm_num [octagonSign]⟩
  | .C s => ⟨2, 0, octagonSign s, 0, by cases s <;> norm_num [octagonSign]⟩
  | .B s t => ⟨0, octagonSign s, octagonSign t, 1,
      by cases s <;> cases t <;> norm_num [octagonSign]⟩

def octagonHeight (q : BSUnit23) : ℤ :=
  1 + 4 * q.x1 ^ 2 + 6 * q.x2 ^ 2

def octagonA (q : BSUnit23) : ℤ := q.x0 * q.x1 + 3 * q.x2 * q.x3

def octagonC (q : BSUnit23) : ℤ := q.x0 * q.x2 - 2 * q.x1 * q.x3

@[simp] lemma octagonUnit_A_mul_x1 (s : Bool) (q : BSUnit23) :
    (octagonUnit (.A s) * q).x1 =
      3 * q.x1 + 2 * octagonSign s * q.x0 := by
  change 3 * q.x1 + (2 * octagonSign s) * q.x0 - 3 * 0 * q.x3 +
    3 * 0 * q.x2 = _
  ring

@[simp] lemma octagonUnit_A_mul_x2 (s : Bool) (q : BSUnit23) :
    (octagonUnit (.A s) * q).x2 =
      3 * q.x2 + 4 * octagonSign s * q.x3 := by
  change 3 * q.x2 + 0 * q.x0 + 2 * (2 * octagonSign s) * q.x3 -
    2 * 0 * q.x1 = _
  ring

@[simp] lemma octagonUnit_C_mul_x1 (s : Bool) (q : BSUnit23) :
    (octagonUnit (.C s) * q).x1 =
      2 * q.x1 - 3 * octagonSign s * q.x3 := by
  change 2 * q.x1 + 0 * q.x0 - 3 * octagonSign s * q.x3 +
    3 * 0 * q.x2 = _
  ring

@[simp] lemma octagonUnit_C_mul_x2 (s : Bool) (q : BSUnit23) :
    (octagonUnit (.C s) * q).x2 =
      2 * q.x2 + octagonSign s * q.x0 := by
  change 2 * q.x2 + octagonSign s * q.x0 + 2 * 0 * q.x3 -
    2 * 0 * q.x1 = _
  ring

@[simp] lemma octagonUnit_B_mul_x1 (s t : Bool) (q : BSUnit23) :
    (octagonUnit (.B s t) * q).x1 =
      octagonSign s * q.x0 - 3 * octagonSign t * q.x3 + 3 * q.x2 := by
  change 0 * q.x1 + octagonSign s * q.x0 - 3 * octagonSign t * q.x3 +
    3 * 1 * q.x2 = _
  ring

@[simp] lemma octagonUnit_B_mul_x2 (s t : Bool) (q : BSUnit23) :
    (octagonUnit (.B s t) * q).x2 =
      octagonSign t * q.x0 + 2 * octagonSign s * q.x3 - 2 * q.x1 := by
  change 0 * q.x2 + octagonSign t * q.x0 + 2 * octagonSign s * q.x3 -
    2 * 1 * q.x1 = _
  ring

lemma octagonHeight_pos (q : BSUnit23) : 0 < octagonHeight q := by
  dsimp [octagonHeight]
  positivity

lemma octagon_quadrant_bound {H U V : ℤ}
    (hH : 0 ≤ H) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hUmax : 3 * U ≤ H) (hVmax : 4 * V ≤ H)
    (hsum : 24 * (U + V) ≤ 10 * H) :
    144 * (2 * U ^ 2 + 3 * V ^ 2) ≤ 35 * H ^ 2 := by
  by_cases hsplit : 6 * U ≤ H
  · have hUsq : 0 ≤ (H - 6 * U) * (H + 6 * U) :=
      mul_nonneg (sub_nonneg.mpr hsplit) (by positivity)
    have hVsq : 0 ≤ (H - 4 * V) * (H + 4 * V) :=
      mul_nonneg (sub_nonneg.mpr hVmax) (by positivity)
    nlinarith
  · have hUlow : H ≤ 6 * U := by omega
    have hD : 12 * V ≤ 5 * H - 12 * U := by omega
    have hDnonneg : 0 ≤ 5 * H - 12 * U := by omega
    have hVsq : 0 ≤ (5 * H - 12 * U - 12 * V) *
        (5 * H - 12 * U + 12 * V) :=
      mul_nonneg (sub_nonneg.mpr hD) (by positivity)
    have hinterval : (6 * U - H) * (3 * U - H) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hUlow)
        (sub_nonpos.mpr hUmax)
    nlinarith

lemma octagon_quadratic_bound {H A C : ℤ}
    (hH : 0 ≤ H)
    (hAp : 0 ≤ H + 3 * A) (hAm : 0 ≤ H - 3 * A)
    (hCp : 0 ≤ H + 4 * C) (hCm : 0 ≤ H - 4 * C)
    (hBpp : 0 ≤ 10 * H + 24 * C - 24 * A)
    (hBpm : 0 ≤ 10 * H + 24 * C + 24 * A)
    (hBmp : 0 ≤ 10 * H - 24 * C - 24 * A)
    (hBmm : 0 ≤ 10 * H - 24 * C + 24 * A) :
    144 * (2 * A ^ 2 + 3 * C ^ 2) ≤ 35 * H ^ 2 := by
  by_cases ha : 0 ≤ A
  · by_cases hc : 0 ≤ C
    · exact octagon_quadrant_bound hH ha hc (by omega) (by omega) (by omega)
    · have h := octagon_quadrant_bound hH ha (show 0 ≤ -C by omega)
        (by omega) (by omega) (by omega)
      simpa using h
  · by_cases hc : 0 ≤ C
    · have h := octagon_quadrant_bound hH (show 0 ≤ -A by omega) hc
        (by omega) (by omega) (by omega)
      simpa using h
    · have h := octagon_quadrant_bound hH (show 0 ≤ -A by omega)
        (show 0 ≤ -C by omega) (by omega) (by omega) (by omega)
      simpa using h

lemma octagon_height_le_six_of_no_descent (q : BSUnit23)
    (hdesc : ∀ i, octagonHeight q ≤ octagonHeight (octagonUnit i * q)) :
    octagonHeight q ≤ 6 := by
  let H := octagonHeight q
  let A := octagonA q
  let C := octagonC q
  have hAp := hdesc (.A true)
  have hAm := hdesc (.A false)
  have hCp := hdesc (.C true)
  have hCm := hdesc (.C false)
  have hBpp := hdesc (.B true true)
  have hBpm := hdesc (.B true false)
  have hBmp := hdesc (.B false true)
  have hBmm := hdesc (.B false false)
  have hnorm := q.norm_one
  have hAp' : 0 ≤ H + 3 * A := by
    simp only [octagonHeight, octagonUnit_A_mul_x1, octagonUnit_A_mul_x2] at hAp
    norm_num [octagonSign] at hAp
    dsimp [H, A, octagonHeight, octagonA]
    nlinarith [hnorm]
  have hAm' : 0 ≤ H - 3 * A := by
    simp only [octagonHeight, octagonUnit_A_mul_x1, octagonUnit_A_mul_x2] at hAm
    norm_num [octagonSign] at hAm
    dsimp [H, A, octagonHeight, octagonA]
    nlinarith [hnorm]
  have hCp' : 0 ≤ H + 4 * C := by
    simp only [octagonHeight, octagonUnit_C_mul_x1, octagonUnit_C_mul_x2] at hCp
    norm_num [octagonSign] at hCp
    dsimp [H, C, octagonHeight, octagonC]
    nlinarith [hnorm]
  have hCm' : 0 ≤ H - 4 * C := by
    simp only [octagonHeight, octagonUnit_C_mul_x1, octagonUnit_C_mul_x2] at hCm
    norm_num [octagonSign] at hCm
    dsimp [H, C, octagonHeight, octagonC]
    nlinarith [hnorm]
  have hBpp' : 0 ≤ 10 * H + 24 * C - 24 * A := by
    simp only [octagonHeight, octagonUnit_B_mul_x1, octagonUnit_B_mul_x2] at hBpp
    norm_num [octagonSign] at hBpp
    dsimp [H, A, C, octagonHeight, octagonA, octagonC]
    nlinarith [hnorm]
  have hBpm' : 0 ≤ 10 * H + 24 * C + 24 * A := by
    simp only [octagonHeight, octagonUnit_B_mul_x1, octagonUnit_B_mul_x2] at hBpm
    norm_num [octagonSign] at hBpm
    dsimp [H, A, C, octagonHeight, octagonA, octagonC]
    nlinarith [hnorm]
  have hBmp' : 0 ≤ 10 * H - 24 * C - 24 * A := by
    simp only [octagonHeight, octagonUnit_B_mul_x1, octagonUnit_B_mul_x2] at hBmp
    norm_num [octagonSign] at hBmp
    dsimp [H, A, C, octagonHeight, octagonA, octagonC]
    nlinarith [hnorm]
  have hBmm' : 0 ≤ 10 * H - 24 * C + 24 * A := by
    simp only [octagonHeight, octagonUnit_B_mul_x1, octagonUnit_B_mul_x2] at hBmm
    norm_num [octagonSign] at hBmm
    dsimp [H, A, C, octagonHeight, octagonA, octagonC]
    nlinarith [hnorm]
  have hquad := octagon_quadratic_bound (show 0 ≤ H by
      exact (octagonHeight_pos q).le) hAp' hAm' hCp' hCm'
      hBpp' hBpm' hBmp' hBmm'
  let S : ℤ := 2 * q.x1 ^ 2 + 3 * q.x2 ^ 2
  have hAC : 2 * A ^ 2 + 3 * C ^ 2 = S * (S + 1) := by
    have hnorm := q.norm_one
    have hnorm' : q.x0 ^ 2 + 6 * q.x3 ^ 2 = S + 1 := by
      dsimp [S]
      nlinarith
    dsimp [A, C, octagonA, octagonC]
    rw [show 2 * (q.x0 * q.x1 + 3 * q.x2 * q.x3) ^ 2 +
        3 * (q.x0 * q.x2 - 2 * q.x1 * q.x3) ^ 2 =
        (2 * q.x1 ^ 2 + 3 * q.x2 ^ 2) *
          (q.x0 ^ 2 + 6 * q.x3 ^ 2) by ring]
    rw [hnorm']
  have hH : H = 1 + 2 * S := by
    dsimp [H, S, octagonHeight]
    ring
  rw [hAC, hH] at hquad
  have hsquare : (1 + 2 * S) ^ 2 ≤ 36 := by nlinarith
  have hnonneg : 0 ≤ 1 + 2 * S := by
    rw [← hH]
    exact (octagonHeight_pos q).le
  change H ≤ 6
  rw [hH]
  nlinarith

lemma int_eq_zero_of_sq_lt_one (x : ℤ) (h : x ^ 2 < 1) : x = 0 := by
  have hxlow : -1 < x := by
    by_contra hn
    have hx : x ≤ -1 := by omega
    nlinarith [sq_nonneg (x + 1)]
  have hxhigh : x < 1 := by
    by_contra hn
    have hx : 1 ≤ x := by omega
    nlinarith [sq_nonneg (x - 1)]
  omega

lemma int_sq_ne_three (x : ℤ) : x ^ 2 ≠ 3 := by
  intro h
  have hxlow : -2 < x := by
    by_contra hn
    have hx : x ≤ -2 := by omega
    nlinarith [sq_nonneg (x + 2)]
  have hxhigh : x < 2 := by
    by_contra hn
    have hx : 2 ≤ x := by omega
    nlinarith [sq_nonneg (x - 2)]
  interval_cases x <;> norm_num at h

lemma octagon_eq_one_or_center_of_height_le_six (q : BSUnit23)
    (hheight : octagonHeight q ≤ 6) :
    q = 1 ∨ q = octagonUnit .center := by
  have hvSq : q.x2 ^ 2 < 1 := by
    dsimp [octagonHeight] at hheight
    nlinarith [sq_nonneg q.x1]
  have hv : q.x2 = 0 := int_eq_zero_of_sq_lt_one q.x2 hvSq
  have huSqLt : q.x1 ^ 2 < 2 := by
    dsimp [octagonHeight] at hheight
    rw [hv] at hheight
    norm_num at hheight
    nlinarith
  have huCases : q.x1 ^ 2 = 0 ∨ q.x1 ^ 2 = 1 := by
    have huNonneg := sq_nonneg q.x1
    omega
  rcases huCases with huSq | huSq
  · have hu : q.x1 = 0 := by nlinarith
    have htSq : q.x3 ^ 2 < 1 := by
      have hnorm := q.norm_one
      rw [hu, hv] at hnorm
      norm_num at hnorm
      nlinarith [sq_nonneg q.x0]
    have ht : q.x3 = 0 := int_eq_zero_of_sq_lt_one q.x3 htSq
    have hwSq : q.x0 ^ 2 = 1 := by
      have hnorm := q.norm_one
      rw [hu, hv, ht] at hnorm
      norm_num at hnorm ⊢
      exact hnorm
    have hw : q.x0 = 1 ∨ q.x0 = -1 := by
      exact sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa using hwSq)
    rcases hw with hw | hw
    · left
      change q = BuserSarnakQuaternionUnit.one 2 3
      ext <;> simp [BuserSarnakQuaternionUnit.one, hu, hv, ht, hw]
    · right
      ext <;> simp [octagonUnit, hu, hv, ht, hw]
  · have htSq : q.x3 ^ 2 < 1 := by
      have hnorm := q.norm_one
      rw [huSq, hv] at hnorm
      norm_num at hnorm
      nlinarith [sq_nonneg q.x0]
    have ht : q.x3 = 0 := int_eq_zero_of_sq_lt_one q.x3 htSq
    have hwSq : q.x0 ^ 2 = 3 := by
      have hnorm := q.norm_one
      rw [huSq, hv, ht] at hnorm
      norm_num at hnorm ⊢
      nlinarith
    exact (int_sq_ne_three q.x0 hwSq).elim

lemma exists_octagon_descent (q : BSUnit23)
    (hone : q ≠ 1) (hcenter : q ≠ octagonUnit .center) :
    ∃ i, octagonHeight (octagonUnit i * q) < octagonHeight q := by
  by_contra h
  push Not at h
  have hle : ∀ i, octagonHeight q ≤ octagonHeight (octagonUnit i * q) :=
    h
  rcases octagon_eq_one_or_center_of_height_le_six q
      (octagon_height_le_six_of_no_descent q hle) with hq | hq
  · exact hone hq
  · exact hcenter hq

def octagonGeneratedGroup : Subgroup BSUnit23 :=
  Subgroup.closure (Set.range octagonUnit)

lemma octagonUnit_mem_generated (i : OctagonGenerator) :
    octagonUnit i ∈ octagonGeneratedGroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

def octagonHeightNat (q : BSUnit23) : ℕ := (octagonHeight q).toNat

/-- The eight octagon side elements, together with the central `-1`, generate
the complete integral norm-one quaternion group. -/
theorem octagonGeneratedGroup_eq_top : octagonGeneratedGroup = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro q
  refine (measure octagonHeightNat).wf.induction q ?_
  intro q ih
  by_cases hone : q = 1
  · rw [hone]
    exact Subgroup.one_mem _
  by_cases hcenter : q = octagonUnit .center
  · rw [hcenter]
    exact octagonUnit_mem_generated .center
  rcases exists_octagon_descent q hone hcenter with ⟨i, hi⟩
  have hnat : octagonHeightNat (octagonUnit i * q) < octagonHeightNat q :=
    (Int.toNat_lt_toNat (octagonHeight_pos q)).2 hi
  have hsmul : octagonUnit i * q ∈ octagonGeneratedGroup :=
    ih (octagonUnit i * q) hnat
  have hs : octagonUnit i ∈ octagonGeneratedGroup := octagonUnit_mem_generated i
  have := Subgroup.mul_mem octagonGeneratedGroup (Subgroup.inv_mem _ hs) hsmul
  simpa using this

end SystolicGrowth

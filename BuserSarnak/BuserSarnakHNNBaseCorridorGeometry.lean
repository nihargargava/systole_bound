module

public import BuserSarnak.BuserSarnakHNNBaseCorridor

@[expose] public section

/-!
# Rational shells for the octagon HNN base corridors

This file encloses the four exact source and target corridor intervals in
rational projective intervals.  It also records the exact dilation of every
projective interval under an arbitrary integral power of the handle.  These
facts provide the uniform scale separation used by the corridor incidence
automaton.
-/

open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise

namespace SystolicGrowth

noncomputable section

private lemma corridorQuadratic_neg {A B C x y : ℝ}
    (hA : A < 0) (hdisc : B ^ 2 < 4 * A * C)
    (hv : x ≠ 0 ∨ y ≠ 0) : A * x ^ 2 + B * x * y + C * y ^ 2 < 0 := by
  have hC : C < 0 := by
    nlinarith [sq_nonneg B]
  by_contra h
  have hq : 0 ≤ A * x ^ 2 + B * x * y + C * y ^ 2 := le_of_not_gt h
  have hid :
      4 * A * (A * x ^ 2 + B * x * y + C * y ^ 2) =
        (2 * A * x + B * y) ^ 2 + (4 * A * C - B ^ 2) * y ^ 2 := by
    ring
  have hleft : 4 * A * (A * x ^ 2 + B * x * y + C * y ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hq
  have hright : 0 ≤
      (2 * A * x + B * y) ^ 2 + (4 * A * C - B ^ 2) * y ^ 2 :=
    add_nonneg (sq_nonneg _) (mul_nonneg (by nlinarith) (sq_nonneg _))
  have hz : y = 0 := by
    by_contra hy
    have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
    nlinarith [sq_nonneg (2 * A * x + B * y)]
  have hx : x ≠ 0 := by
    intro hx
    rcases hv with hx' | hy'
    · exact hx' hx
    · exact hy' hz
  rw [hz] at hq
  norm_num at hq
  nlinarith [sq_pos_of_ne_zero hx]

lemma octagonSourceBoundary_subset_shell :
    octagonHNNSourceBoundarySet ⊆ projectiveIntervalSet (1 / 2) 2 := by
  intro p hp
  rw [← Projectivization.mk_rep p] at hp ⊢
  rw [mem_octagonHNNSourceBoundarySet_mk_iff] at hp
  rw [mem_projectiveIntervalSet_mk_iff]
  simp only [octagonHNNSourceBoundaryForm,
    projectiveIntervalQuadratic] at hp ⊢
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3lo : (8 / 5 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hs3hi : Real.sqrt 3 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hv : p.rep 0 ≠ 0 ∨ p.rep 1 ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    apply p.rep_nonzero
    funext i
    fin_cases i <;> simp [h.1, h.2]
  have hsspos : 0 < p.rep 0 ^ 2 + p.rep 1 ^ 2 := by
    rcases hv with hx | hy
    · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg (p.rep 1)]
    · nlinarith [sq_pos_of_ne_zero hy, sq_nonneg (p.rep 0)]
  have hmul := mul_lt_mul_of_pos_right hs3lo hsspos
  ring_nf at hp ⊢
  rw [hs3] at hp
  nlinarith

lemma octagonTargetBoundary_subset_shell :
    octagonHNNTargetBoundarySet ⊆ projectiveIntervalSet (-2) (-1 / 2) := by
  intro p hp
  rw [← Projectivization.mk_rep p] at hp ⊢
  rw [mem_octagonHNNTargetBoundarySet_mk_iff] at hp
  rw [mem_projectiveIntervalSet_mk_iff]
  simp only [octagonHNNTargetBoundaryForm,
    projectiveIntervalQuadratic] at hp ⊢
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3lo : (8 / 5 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hv : p.rep 0 ≠ 0 ∨ p.rep 1 ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    apply p.rep_nonzero
    funext i
    fin_cases i <;> simp [h.1, h.2]
  have hsspos : 0 < p.rep 0 ^ 2 + p.rep 1 ^ 2 := by
    rcases hv with hx | hy
    · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg (p.rep 1)]
    · nlinarith [sq_pos_of_ne_zero hy, sq_nonneg (p.rep 0)]
  have hmul := mul_lt_mul_of_pos_right hs3lo hsspos
  ring_nf at hp ⊢
  rw [hs3] at hp
  nlinarith

lemma octagonSourceCone3Corridor_subset_shell :
    octagonHNNSourceCone3CorridorSet ⊆ projectiveIntervalSet 1 16 := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Set.mem_smul_set.mp hq
  rw [← Projectivization.mk_rep p] at hp ⊢
  rw [mem_octagonHNNSourceBoundarySet_mk_iff] at hp
  change octagonBaseToPGL23 (octagonBaseFactorElement .cone3) •
      Projectivization.mk ℝ p.rep p.rep_nonzero ∈ projectiveIntervalSet 1 16
  rw [octagonBaseToPGL23_factorElement,
    octagon_toPGL23_smul_boundary_mk,
    mem_projectiveIntervalSet_mk_iff]
  simp only [octagonHNNSourceBoundaryForm] at hp
  simp only [projectiveIntervalQuadratic,
    octagonBoundarySL_B_apply_zero,
    octagonBoundarySL_B_apply_one, octagonSign,
    Int.cast_neg, Int.cast_one, neg_mul, one_mul]
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs23 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hs2lo : (141421 / 100000 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hs2hi : Real.sqrt 2 < (141422 / 100000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hs3lo : (173205 / 100000 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hs3hi : Real.sqrt 3 < (173206 / 100000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hs6lo : (244948 / 100000 : ℝ) < Real.sqrt 6 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hs6hi : Real.sqrt 6 < (244949 / 100000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hv : p.rep 0 ≠ 0 ∨ p.rep 1 ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    apply p.rep_nonzero
    funext i
    fin_cases i <;> simp [h.1, h.2]
  let Acoef : ℝ := -96 * Real.sqrt 2 - 34 * Real.sqrt 3 +
    17 * Real.sqrt 6 + 146
  let Bcoef : ℝ := -68 * Real.sqrt 3 + 30 * Real.sqrt 6 + 85
  let Ccoef : ℝ := 6 * Real.sqrt 2 - 34 * Real.sqrt 3 -
    17 * Real.sqrt 6 + 41
  have hA : Acoef < -7 := by
    dsimp [Acoef]
    linarith
  have hB : Bcoef < 41 := by
    dsimp [Bcoef]
    linarith
  have hC : Ccoef < -51 := by
    dsimp [Ccoef]
    linarith
  have hxy : 0 < p.rep 0 * p.rep 1 := by
    ring_nf at hp
    rw [hs3] at hp
    have hss : 0 < p.rep 0 ^ 2 + p.rep 1 ^ 2 := by
      rcases hv with hx | hy
      · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg (p.rep 1)]
      · nlinarith [sq_pos_of_ne_zero hy, sq_nonneg (p.rep 0)]
    have hs3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    nlinarith [mul_pos hs3pos hss]
  have hx : p.rep 0 ≠ 0 := by
    intro hx
    rw [hx] at hxy
    simp at hxy
  have hy : p.rep 1 ≠ 0 := by
    intro hy
    rw [hy] at hxy
    simp at hxy
  have hAx := mul_lt_mul_of_pos_right hA (sq_pos_of_ne_zero hx)
  have hBxy := mul_lt_mul_of_pos_right hB hxy
  have hCy := mul_lt_mul_of_pos_right hC (sq_pos_of_ne_zero hy)
  have hquad :
      (-7 - 10 * Real.sqrt 3) * p.rep 0 ^ 2 +
          81 * p.rep 0 * p.rep 1 +
          (-51 - 10 * Real.sqrt 3) * p.rep 1 ^ 2 < 0 := by
    apply corridorQuadratic_neg
    · nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)]
    · nlinarith [hs3, hs3lo]
    · exact hv
  have hbound :
      Acoef * p.rep 0 ^ 2 + Bcoef * p.rep 0 * p.rep 1 +
          Ccoef * p.rep 1 ^ 2 < 0 := by
    ring_nf at hp
    rw [hs3] at hp
    nlinarith
  have hout :
      ((-(Real.sqrt 2) * p.rep 0 +
          Real.sqrt 3 * (1 + Real.sqrt 2) * p.rep 1) -
        (Real.sqrt 3 * (1 - Real.sqrt 2) * p.rep 0 +
          Real.sqrt 2 * p.rep 1)) *
      ((-(Real.sqrt 2) * p.rep 0 +
          Real.sqrt 3 * (1 + Real.sqrt 2) * p.rep 1) -
        16 * (Real.sqrt 3 * (1 - Real.sqrt 2) * p.rep 0 +
          Real.sqrt 2 * p.rep 1)) =
        Acoef * p.rep 0 ^ 2 + Bcoef * p.rep 0 * p.rep 1 +
          Ccoef * p.rep 1 ^ 2 := by
    dsimp [Acoef, Bcoef, Ccoef]
    rw [← hs23]
    ring_nf
    rw [hs2, hs3]
    ring
  nlinarith [hout]

lemma octagonTargetCone4Corridor_subset_shell :
    octagonHNNTargetCone4CorridorSet ⊆
      projectiveIntervalSet (-16) (-1) := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Set.mem_smul_set.mp hq
  rw [← Projectivization.mk_rep p] at hp ⊢
  rw [mem_octagonHNNTargetBoundarySet_mk_iff] at hp
  let v : Fin 2 → ℝ := ![-p.rep 0, p.rep 1]
  have hv : v ≠ 0 := by
    intro h
    apply p.rep_nonzero
    funext i
    fin_cases i
    · have h0 := congrFun h 0
      simpa [v] using neg_eq_zero.mp h0
    · simpa [v] using congrFun h 1
  let r : OctagonProjectiveBoundary := Projectivization.mk ℝ v hv
  have hrS : r ∈ octagonHNNSourceBoundarySet := by
    rw [mem_octagonHNNSourceBoundarySet_mk_iff]
    dsimp [v]
    simp only [octagonHNNSourceBoundaryForm,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [octagonHNNTargetBoundaryForm] at hp
    convert hp using 1
    all_goals ring
  have hrC : octagonBaseToPGL23 octagonBaseE3 • r ∈
      octagonHNNSourceCone3CorridorSet := by
    exact Set.smul_mem_smul_set hrS
  have hrI := octagonSourceCone3Corridor_subset_shell hrC
  change octagonBaseToPGL23 (octagonBaseFactorElement .cone3) • r ∈
      projectiveIntervalSet 1 16 at hrI
  rw [octagonBaseToPGL23_factorElement] at hrI
  change octagonBaseToPGL23 (octagonBaseFactorElement .cone4) •
      Projectivization.mk ℝ p.rep p.rep_nonzero ∈
        projectiveIntervalSet (-16) (-1)
  rw [octagonBaseToPGL23_factorElement,
    octagon_toPGL23_smul_boundary_mk,
    mem_projectiveIntervalSet_mk_iff]
  rw [show r = Projectivization.mk ℝ v hv by rfl,
    octagon_toPGL23_smul_boundary_mk,
    mem_projectiveIntervalSet_mk_iff] at hrI
  simp only [projectiveIntervalQuadratic,
    octagonBoundarySL_B_apply_zero,
    octagonBoundarySL_B_apply_one, octagonSign,
    Int.cast_neg, Int.cast_one, neg_mul, one_mul] at hrI ⊢
  dsimp [v] at hrI
  ring_nf at hrI ⊢
  exact hrI

def octagonCorridorScale : ℝ := 17 + 12 * Real.sqrt 2

lemma octagonCorridorScale_pos : 0 < octagonCorridorScale := by
  dsimp [octagonCorridorScale]
  positivity

lemma octagonCorridorScale_gt : (33 : ℝ) < octagonCorridorScale := by
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2lo : (4 / 3 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  dsimp [octagonCorridorScale]
  nlinarith

lemma octagonCorridorScale_lt : octagonCorridorScale < (34 : ℝ) := by
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2hi : Real.sqrt 2 < (17 / 12 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  dsimp [octagonCorridorScale]
  nlinarith

lemma octagon_A_mem_scaledInterval_iff (l u : ℝ) (p : OctagonProjectiveBoundary) :
    octagonBaseToPGL23 octagonBaseA • p ∈
        projectiveIntervalSet (octagonCorridorScale * l) (octagonCorridorScale * u) ↔
      p ∈ projectiveIntervalSet l u := by
  induction p using Projectivization.ind with
  | _ v hv =>
      change octagonBaseToPGL23 (octagonBaseFactorElement .handle) •
          Projectivization.mk ℝ v hv ∈
            projectiveIntervalSet (octagonCorridorScale * l) (octagonCorridorScale * u) ↔ _
      rw [octagonBaseToPGL23_factorElement,
        octagon_toPGL23_smul_boundary_mk,
        mem_projectiveIntervalSet_mk_iff,
        mem_projectiveIntervalSet_mk_iff]
      have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hs2_3 : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
        calc
          (Real.sqrt 2) ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
          _ = 2 * Real.sqrt 2 := by rw [hs2]
      have hs2_4 : (Real.sqrt 2) ^ 4 = 4 := by
        calc
          (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
          _ = 4 := by rw [hs2]; norm_num
      have hcoef : 0 < (3 + 2 * Real.sqrt 2) ^ 2 := by
        positivity
      have hid :
          projectiveIntervalQuadratic (octagonCorridorScale * l) (octagonCorridorScale * u)
              (octagonBoundarySL (octagonUnit (.A true)) • v) =
            (3 + 2 * Real.sqrt 2) ^ 2 *
              projectiveIntervalQuadratic l u v := by
        have h0 :
            (octagonBoundarySL (octagonUnit (.A true)) • v) 0 =
              (3 + 2 * Real.sqrt 2) * v 0 := by
          rw [Matrix.SpecialLinearGroup.smul_def]
          change ((BuserSarnakQuaternionUnit.matrix
            (octagonUnit (.A true))) • v) 0 = _
          simp [BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
            octagonUnit, octagonSign, Matrix.vecHead, Matrix.vecTail]
        have h1 :
            (octagonBoundarySL (octagonUnit (.A true)) • v) 1 =
              (3 - 2 * Real.sqrt 2) * v 1 := by
          rw [Matrix.SpecialLinearGroup.smul_def]
          change ((BuserSarnakQuaternionUnit.matrix
            (octagonUnit (.A true))) • v) 1 = _
          simp [BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
            octagonUnit, octagonSign, Matrix.vecHead, Matrix.vecTail]
        rw [projectiveIntervalQuadratic, h0, h1]
        simp only [octagonCorridorScale]
        ring_nf
        rw [hs2, hs2_3, hs2_4]
        simp only [projectiveIntervalQuadratic]
        ring_nf
      rw [hid]
      constructor
      · intro h
        by_contra hn
        have hnonneg : 0 ≤ projectiveIntervalQuadratic l u v :=
          le_of_not_gt hn
        exact (not_lt_of_ge (mul_nonneg hcoef.le hnonneg)) h
      · exact mul_neg_of_pos_of_neg hcoef

lemma octagon_A_smul_projectiveIntervalSet (l u : ℝ) :
    octagonBaseToPGL23 octagonBaseA • projectiveIntervalSet l u =
      projectiveIntervalSet (octagonCorridorScale * l) (octagonCorridorScale * u) := by
  ext p
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  have h := octagon_A_mem_scaledInterval_iff l u
    ((octagonBaseToPGL23 octagonBaseA)⁻¹ • p)
  simpa using h.symm

lemma octagon_A_inv_smul_projectiveIntervalSet (l u : ℝ) :
    (octagonBaseToPGL23 octagonBaseA)⁻¹ • projectiveIntervalSet l u =
      projectiveIntervalSet (octagonCorridorScale⁻¹ * l) (octagonCorridorScale⁻¹ * u) := by
  have hs : octagonCorridorScale ≠ 0 := ne_of_gt octagonCorridorScale_pos
  have hf := octagon_A_smul_projectiveIntervalSet (octagonCorridorScale⁻¹ * l)
    (octagonCorridorScale⁻¹ * u)
  have hl : octagonCorridorScale * (octagonCorridorScale⁻¹ * l) = l := by
    field_simp
  have hu : octagonCorridorScale * (octagonCorridorScale⁻¹ * u) = u := by
    field_simp
  rw [hl, hu] at hf
  rw [← hf, ← mul_smul]
  simp

private lemma octagon_A_pow_smul_projectiveIntervalSet (k : ℕ) (l u : ℝ) :
    (octagonBaseToPGL23 octagonBaseA) ^ k • projectiveIntervalSet l u =
      projectiveIntervalSet (octagonCorridorScale ^ k * l) (octagonCorridorScale ^ k * u) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_smul, ih, octagon_A_smul_projectiveIntervalSet]
      congr 1 <;> rw [pow_succ'] <;> ring

private lemma octagon_A_inv_pow_smul_projectiveIntervalSet (k : ℕ) (l u : ℝ) :
    (octagonBaseToPGL23 octagonBaseA)⁻¹ ^ k • projectiveIntervalSet l u =
      projectiveIntervalSet ((octagonCorridorScale⁻¹) ^ k * l)
        ((octagonCorridorScale⁻¹) ^ k * u) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_smul, ih, octagon_A_inv_smul_projectiveIntervalSet]
      congr 1 <;> rw [pow_succ'] <;> ring

lemma octagon_A_zpow_smul_projectiveIntervalSet (n : ℤ) (l u : ℝ) :
    (octagonBaseToPGL23 octagonBaseA) ^ n • projectiveIntervalSet l u =
      projectiveIntervalSet (octagonCorridorScale ^ n * l) (octagonCorridorScale ^ n * u) := by
  cases n with
  | ofNat k =>
      change (octagonBaseToPGL23 octagonBaseA) ^ k •
        projectiveIntervalSet l u =
          projectiveIntervalSet (octagonCorridorScale ^ k * l) (octagonCorridorScale ^ k * u)
      exact octagon_A_pow_smul_projectiveIntervalSet k l u
  | negSucc k =>
      rw [zpow_negSucc, zpow_negSucc]
      simpa only [inv_pow] using
        octagon_A_inv_pow_smul_projectiveIntervalSet (k + 1) l u

lemma projectiveIntervalSet_disjoint_of_le {a b c d : ℝ}
    (hab : a < b) (hbc : b ≤ c) (hcd : c < d) :
    Disjoint (projectiveIntervalSet a b) (projectiveIntervalSet c d) := by
  rw [Set.disjoint_left]
  intro p hp hq
  rw [← Projectivization.mk_rep p] at hp hq
  rw [mem_projectiveIntervalSet_mk_iff] at hp hq
  simp only [projectiveIntervalQuadratic] at hp hq
  rcases mul_neg_iff.mp hp with hp | hp <;>
    rcases mul_neg_iff.mp hq with hq | hq
  · have hy : 0 < p.rep 1 := by
      have hprod : 0 < (b - a) * p.rep 1 := by nlinarith
      rcases mul_pos_iff.mp hprod with h | h
      · exact h.2
      · exact (not_lt_of_ge (sub_nonneg.mpr hab.le) h.1).elim
    have hm := mul_nonneg (sub_nonneg.mpr hbc) hy.le
    nlinarith
  · have hy : 0 < p.rep 1 := by
      have hprod : 0 < (b - a) * p.rep 1 := by nlinarith
      rcases mul_pos_iff.mp hprod with h | h
      · exact h.2
      · exact (not_lt_of_ge (sub_nonneg.mpr hab.le) h.1).elim
    have hm := mul_pos (sub_pos.mpr hcd) hy
    nlinarith
  · have hy : p.rep 1 < 0 := by
      have hprod : (b - a) * p.rep 1 < 0 := by nlinarith
      rcases mul_neg_iff.mp hprod with h | h
      · exact h.2
      · exact (not_lt_of_ge (sub_nonneg.mpr hab.le) h.1).elim
    have hm := mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr hbc) hy.le
    nlinarith
  · have hy : p.rep 1 < 0 := by
      have hprod : (b - a) * p.rep 1 < 0 := by nlinarith
      rcases mul_neg_iff.mp hprod with h | h
      · exact h.2
      · exact (not_lt_of_ge (sub_nonneg.mpr hab.le) h.1).elim
    have hm := mul_neg_of_pos_of_neg (sub_pos.mpr hcd) hy
    nlinarith

end

end SystolicGrowth

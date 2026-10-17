module

public import BuserSarnak.BuserSarnakProjectivePingPong

@[expose] public section

/-!
# Cone-factor separation on the HNN boundary intervals

This file proves that each of the four order-two octagon generators sends
both HNN boundary intervals strictly outside their union.  The proof is an
exact calculation with the two homogeneous boundary forms.
-/

open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise

namespace SystolicGrowth

noncomputable section

/-- First coordinate of the boundary action of an order-two generator. -/
@[simp] lemma octagonBoundarySL_B_apply_zero (s t : Bool) (v : Fin 2 → ℝ) :
    (octagonBoundarySL (octagonUnit (.B s t)) • v) 0 =
      (octagonSign s : ℝ) * Real.sqrt 2 * v 0 +
        Real.sqrt 3 * ((octagonSign t : ℝ) + Real.sqrt 2) * v 1 := by
  rw [Matrix.SpecialLinearGroup.smul_def]
  change ((BuserSarnakQuaternionUnit.matrix (octagonUnit (.B s t))) • v) 0 = _
  simp [BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix, octagonUnit,
    Matrix.vecHead, Matrix.vecTail]

/-- Second coordinate of the boundary action of an order-two generator. -/
@[simp] lemma octagonBoundarySL_B_apply_one (s t : Bool) (v : Fin 2 → ℝ) :
    (octagonBoundarySL (octagonUnit (.B s t)) • v) 1 =
      Real.sqrt 3 * ((octagonSign t : ℝ) - Real.sqrt 2) * v 0 -
        (octagonSign s : ℝ) * Real.sqrt 2 * v 1 := by
  rw [Matrix.SpecialLinearGroup.smul_def]
  change ((BuserSarnakQuaternionUnit.matrix (octagonUnit (.B s t))) • v) 1 = _
  simp [BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix, octagonUnit,
    Matrix.vecHead, Matrix.vecTail]
  ring

private lemma quadratic_neg_of_discriminant {A B C x y : ℝ}
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

def Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![-v 0, v 1]

private lemma octagonBoundaryReflect_ne_zero {v : Fin 2 → ℝ} (hv : v ≠ 0) :
    Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect v ≠ 0 := by
  intro h
  apply hv
  funext i
  fin_cases i
  · have h0 := congrFun h 0
    simpa [Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect] using neg_eq_zero.mp h0
  · have h1 := congrFun h 1
    simpa [Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect] using h1

private lemma octagonBoundaryReflect_source (v : Fin 2 → ℝ) :
    octagonHNNSourceBoundaryForm (Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect v) =
      octagonHNNTargetBoundaryForm v := by
  simp [Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect, octagonHNNSourceBoundaryForm,
    octagonHNNTargetBoundaryForm]
  ring

private lemma octagonBoundaryReflect_target (v : Fin 2 → ℝ) :
    octagonHNNTargetBoundaryForm (Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect v) =
      octagonHNNSourceBoundaryForm v := by
  simp [Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect, octagonHNNSourceBoundaryForm,
    octagonHNNTargetBoundaryForm]
  ring

private lemma octagonHNNSourceBoundaryForm_neg (v : Fin 2 → ℝ) :
    octagonHNNSourceBoundaryForm (-v) = octagonHNNSourceBoundaryForm v := by
  simp [octagonHNNSourceBoundaryForm]
  ring

private lemma octagonHNNTargetBoundaryForm_neg (v : Fin 2 → ℝ) :
    octagonHNNTargetBoundaryForm (-v) = octagonHNNTargetBoundaryForm v := by
  simp [octagonHNNTargetBoundaryForm]
  ring

private lemma octagonBoundaryReflect_B (s t : Bool) (v : Fin 2 → ℝ) :
    Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect (octagonBoundarySL (octagonUnit (.B s t)) • v) =
      -(octagonBoundarySL (octagonUnit (.B (!s) t)) •
        Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect v) := by
  funext i
  fin_cases i <;>
    simp [Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect, octagonBoundarySL_B_apply_zero,
      octagonBoundarySL_B_apply_one]
  all_goals cases s <;> cases t <;> norm_num [octagonSign] <;> ring

set_option maxHeartbeats 800000 in
/-- On a nonzero vector in the HNN source interval, a cone generator makes
both boundary forms strictly negative. -/
lemma octagon_B_maps_sourceBoundaryForms_negative
    (s t : Bool) (v : Fin 2 → ℝ) (hv : v ≠ 0)
    (hS : 0 ≤ octagonHNNSourceBoundaryForm v) :
    octagonHNNSourceBoundaryForm
          (octagonBoundarySL (octagonUnit (.B s t)) • v) < 0 ∧
      octagonHNNTargetBoundaryForm
          (octagonBoundarySL (octagonUnit (.B s t)) • v) < 0 := by
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3_3 : (Real.sqrt 3) ^ 3 = 3 * Real.sqrt 3 := by
    calc
      (Real.sqrt 3) ^ 3 = (Real.sqrt 3) ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hs3]
  have hs3_4 : (Real.sqrt 3) ^ 4 = 9 := by
    calc
      (Real.sqrt 3) ^ 4 = ((Real.sqrt 3) ^ 2) ^ 2 := by ring
      _ = 9 := by rw [hs3]; norm_num
  have hs2p : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_cases h0 : v 0 = 0
    · right
      intro h1
      apply hv
      funext i
      fin_cases i <;> assumption
    · exact Or.inl h0
  let a := Real.sqrt 2
  let b := Real.sqrt 3
  have hq1 :
      (-b * (4 + 2 * a)) * (v 0) ^ 2 + 8 * v 0 * v 1 +
          (-b * (4 - 2 * a)) * (v 1) ^ 2 < 0 := by
    apply quadratic_neg_of_discriminant (hv := hv')
    · dsimp [a, b]; nlinarith [hs2p, hs3p, hs2]
    · dsimp [a, b]; nlinarith [hs2, hs3]
  have hq2 :
      (-b * (20 + 10 * a)) * (v 0) ^ 2 + 48 * v 0 * v 1 +
          (-b * (20 - 10 * a)) * (v 1) ^ 2 < 0 := by
    apply quadratic_neg_of_discriminant (hv := hv')
    · dsimp [a, b]; nlinarith [hs2p, hs3p, hs2]
    · dsimp [a, b]; nlinarith [hs2, hs3]
  have hq3 :
      (-b * (4 - 2 * a)) * (v 0) ^ 2 + 8 * v 0 * v 1 +
          (-b * (4 + 2 * a)) * (v 1) ^ 2 < 0 := by
    apply quadratic_neg_of_discriminant (hv := hv')
    · dsimp [a, b]; nlinarith [hs2p, hs3p, hs2]
    · dsimp [a, b]; nlinarith [hs2, hs3]
  have hq4 :
      (-b * (20 - 10 * a)) * (v 0) ^ 2 + 48 * v 0 * v 1 +
          (-b * (20 + 10 * a)) * (v 1) ^ 2 < 0 := by
    apply quadratic_neg_of_discriminant (hv := hv')
    · dsimp [a, b]; nlinarith [hs2p, hs3p, hs2]
    · dsimp [a, b]; nlinarith [hs2, hs3]
  have hq5 :
      (-b * (20 + 10 * a)) * (v 0) ^ 2 - 40 * v 0 * v 1 +
          (-b * (20 - 10 * a)) * (v 1) ^ 2 < 0 := by
    convert quadratic_neg_of_discriminant (A := -b * (20 + 10 * a)) (B := -40)
      (C := -b * (20 - 10 * a)) (x := v 0) (y := v 1)
      (by dsimp [a, b]; nlinarith [hs2p, hs3p, hs2])
      (by dsimp [a, b]; nlinarith [hs2, hs3]) hv' using 1
    ring
  have hq6 :
      (-b * (4 + 2 * a)) * (v 0) ^ 2 +
          (-b * (4 - 2 * a)) * (v 1) ^ 2 < 0 := by
    convert quadratic_neg_of_discriminant (A := -b * (4 + 2 * a)) (B := 0)
        (C := -b * (4 - 2 * a))
        (x := v 0) (y := v 1)
        (by dsimp [a, b]; nlinarith [hs2p, hs3p, hs2])
        (by dsimp [a, b]; nlinarith [hs2, hs3]) hv' using 1
    ring
  have hq7 :
      (-b * (20 - 10 * a)) * (v 0) ^ 2 - 40 * v 0 * v 1 +
          (-b * (20 + 10 * a)) * (v 1) ^ 2 < 0 := by
    convert quadratic_neg_of_discriminant (A := -b * (20 - 10 * a)) (B := -40)
      (C := -b * (20 + 10 * a)) (x := v 0) (y := v 1)
      (by dsimp [a, b]; nlinarith [hs2p, hs3p, hs2])
      (by dsimp [a, b]; nlinarith [hs2, hs3]) hv' using 1
    ring
  have hq8 :
      (-b * (4 - 2 * a)) * (v 0) ^ 2 +
          (-b * (4 + 2 * a)) * (v 1) ^ 2 < 0 := by
    convert quadratic_neg_of_discriminant (A := -b * (4 - 2 * a)) (B := 0)
        (C := -b * (4 + 2 * a))
        (x := v 0) (y := v 1)
        (by dsimp [a, b]; nlinarith [hs2p, hs3p, hs2])
        (by dsimp [a, b]; nlinarith [hs2, hs3]) hv' using 1
    ring
  simp only [octagonHNNSourceBoundaryForm, octagonHNNTargetBoundaryForm] at hS ⊢
  cases s <;> cases t <;>
    simp only [octagonBoundarySL_B_apply_zero, octagonBoundarySL_B_apply_one,
      octagonSign, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at ⊢
  all_goals constructor
  all_goals ring_nf at hS ⊢
  all_goals simp only [hs2, hs3, hs3_3, hs3_4] at hS ⊢
  all_goals ring_nf at hS ⊢
  all_goals dsimp [a, b] at hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8
  all_goals nlinarith [hq1, hq2, hq3, hq4, hq5, hq6, hq7, hq8]

set_option maxHeartbeats 800000 in
/-- On a nonzero vector in the HNN target interval, a cone generator makes
both boundary forms strictly negative. -/
lemma octagon_B_maps_targetBoundaryForms_negative
    (s t : Bool) (v : Fin 2 → ℝ) (hv : v ≠ 0)
    (hT : 0 ≤ octagonHNNTargetBoundaryForm v) :
    octagonHNNSourceBoundaryForm
          (octagonBoundarySL (octagonUnit (.B s t)) • v) < 0 ∧
      octagonHNNTargetBoundaryForm
          (octagonBoundarySL (octagonUnit (.B s t)) • v) < 0 := by
  have h := octagon_B_maps_sourceBoundaryForms_negative (!s) t
    (Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect v) (octagonBoundaryReflect_ne_zero hv)
    (by simpa only [octagonBoundaryReflect_source] using hT)
  constructor
  · calc
      octagonHNNSourceBoundaryForm
          (octagonBoundarySL (octagonUnit (.B s t)) • v) =
          octagonHNNTargetBoundaryForm
            (Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect
              (octagonBoundarySL (octagonUnit (.B s t)) • v)) := by
                rw [octagonBoundaryReflect_target]
      _ = octagonHNNTargetBoundaryForm
          (-(octagonBoundarySL (octagonUnit (.B (!s) t)) •
            Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect v)) := by
              rw [octagonBoundaryReflect_B]
      _ = octagonHNNTargetBoundaryForm
          (octagonBoundarySL (octagonUnit (.B (!s) t)) •
            Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect v) := octagonHNNTargetBoundaryForm_neg _
      _ < 0 := h.2
  · calc
      octagonHNNTargetBoundaryForm
          (octagonBoundarySL (octagonUnit (.B s t)) • v) =
          octagonHNNSourceBoundaryForm
            (Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect
              (octagonBoundarySL (octagonUnit (.B s t)) • v)) := by
                rw [octagonBoundaryReflect_source]
      _ = octagonHNNSourceBoundaryForm
          (-(octagonBoundarySL (octagonUnit (.B (!s) t)) •
            Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect v)) := by
              rw [octagonBoundaryReflect_B]
      _ = octagonHNNSourceBoundaryForm
          (octagonBoundarySL (octagonUnit (.B (!s) t)) •
            Internal.BuserSarnakConeBoundarySeparationHelpers.octagonBoundaryReflect v) := octagonHNNSourceBoundaryForm_neg _
      _ < 0 := h.1

/-- Every cone involution sends the source interval strictly outside the
union of the source and target HNN intervals. -/
lemma octagon_B_maps_sourceBoundary_outside_both (s t : Bool) :
    Set.MapsTo (fun p : OctagonProjectiveBoundary =>
      BuserSarnakQuaternionUnit.toPGL23 (octagonUnit (.B s t)) • p)
      octagonHNNSourceBoundarySet
      (octagonHNNSourceBoundarySet ∪ octagonHNNTargetBoundarySet)ᶜ := by
  intro p hp
  rw [← Projectivization.mk_rep p] at hp ⊢
  rw [mem_octagonHNNSourceBoundarySet_mk_iff] at hp
  rw [Set.mem_compl_iff]
  intro hout
  change BuserSarnakQuaternionUnit.toPGL23 (octagonUnit (.B s t)) •
      Projectivization.mk ℝ p.rep p.rep_nonzero ∈
    octagonHNNSourceBoundarySet ∪ octagonHNNTargetBoundarySet at hout
  rw [octagon_toPGL23_smul_boundary_mk] at hout
  rcases hout with hout | hout
  · rw [mem_octagonHNNSourceBoundarySet_mk_iff] at hout
    exact (not_lt_of_ge hout)
      (octagon_B_maps_sourceBoundaryForms_negative
        s t p.rep p.rep_nonzero hp).1
  · rw [mem_octagonHNNTargetBoundarySet_mk_iff] at hout
    exact (not_lt_of_ge hout)
      (octagon_B_maps_sourceBoundaryForms_negative
        s t p.rep p.rep_nonzero hp).2

/-- Every cone involution sends the target interval strictly outside the
union of the source and target HNN intervals. -/
lemma octagon_B_maps_targetBoundary_outside_both (s t : Bool) :
    Set.MapsTo (fun p : OctagonProjectiveBoundary =>
      BuserSarnakQuaternionUnit.toPGL23 (octagonUnit (.B s t)) • p)
      octagonHNNTargetBoundarySet
      (octagonHNNSourceBoundarySet ∪ octagonHNNTargetBoundarySet)ᶜ := by
  intro p hp
  rw [← Projectivization.mk_rep p] at hp ⊢
  rw [mem_octagonHNNTargetBoundarySet_mk_iff] at hp
  rw [Set.mem_compl_iff]
  intro hout
  change BuserSarnakQuaternionUnit.toPGL23 (octagonUnit (.B s t)) •
      Projectivization.mk ℝ p.rep p.rep_nonzero ∈
    octagonHNNSourceBoundarySet ∪ octagonHNNTargetBoundarySet at hout
  rw [octagon_toPGL23_smul_boundary_mk] at hout
  rcases hout with hout | hout
  · rw [mem_octagonHNNSourceBoundarySet_mk_iff] at hout
    exact (not_lt_of_ge hout)
      (octagon_B_maps_targetBoundaryForms_negative
        s t p.rep p.rep_nonzero hp).1
  · rw [mem_octagonHNNTargetBoundarySet_mk_iff] at hout
    exact (not_lt_of_ge hout)
      (octagon_B_maps_targetBoundaryForms_negative
        s t p.rep p.rep_nonzero hp).2

end

end SystolicGrowth

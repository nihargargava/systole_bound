module

public import BuserSarnak.BuserSarnakProjectiveCenter

@[expose] public section

namespace SystolicGrowth

/-!
# Height coordinates for the projective octagon action

This file records the exact change of the octagon height under the explicit
quaternion generators.  The height is unchanged by the central scalar `-1`,
so the strict half-spaces below are suitable for arguments on the projective
quaternion quotient.
-/

/-- Left multiplication by an `A`-generator changes the height by a linear
expression in `octagonHeight` and `octagonA`. -/
lemma octagonHeight_A_mul_sub (s : Bool) (q : BSUnit23) :
    octagonHeight (octagonUnit (.A s) * q) - octagonHeight q =
      16 * (octagonHeight q + 3 * octagonSign s * octagonA q) := by
  cases s <;>
    simp only [octagonHeight, octagonA, octagonUnit_A_mul_x1,
      octagonUnit_A_mul_x2, octagonSign] <;>
    nlinarith [q.norm_one]

/-- Left multiplication by a `C`-generator changes the height by a linear
expression in `octagonHeight` and `octagonC`. -/
lemma octagonHeight_C_mul_sub (s : Bool) (q : BSUnit23) :
    octagonHeight (octagonUnit (.C s) * q) - octagonHeight q =
      6 * (octagonHeight q + 4 * octagonSign s * octagonC q) := by
  cases s <;>
    simp only [octagonHeight, octagonC, octagonUnit_C_mul_x1,
      octagonUnit_C_mul_x2, octagonSign] <;>
    nlinarith [q.norm_one]

/-- Left multiplication by a `B`-generator changes the height by a linear
expression in the three integral height coordinates. -/
lemma octagonHeight_B_mul_sub (s t : Bool) (q : BSUnit23) :
    octagonHeight (octagonUnit (.B s t) * q) - octagonHeight q =
      10 * octagonHeight q + 24 * octagonSign s * octagonC q -
        24 * octagonSign t * octagonA q := by
  cases s <;> cases t <;>
    simp only [octagonHeight, octagonA, octagonC,
      octagonUnit_B_mul_x1, octagonUnit_B_mul_x2, octagonSign] <;>
    nlinarith [q.norm_one]

/-- The central quaternion `-1` preserves the height. -/
@[simp] lemma octagonUnit_center_mul_x1 (q : BSUnit23) :
    (octagonUnit .center * q).x1 = -q.x1 := by
  change (-1) * q.x1 + 0 * q.x0 - 3 * 0 * q.x3 + 3 * 0 * q.x2 = _
  ring

@[simp] lemma octagonUnit_center_mul_x2 (q : BSUnit23) :
    (octagonUnit .center * q).x2 = -q.x2 := by
  change (-1) * q.x2 + 0 * q.x0 + 2 * 0 * q.x3 - 2 * 0 * q.x1 = _
  ring

@[simp] lemma octagonHeight_center_mul (q : BSUnit23) :
    octagonHeight (octagonUnit .center * q) = octagonHeight q := by
  simp only [octagonHeight, octagonUnit_center_mul_x1,
    octagonUnit_center_mul_x2]
  ring

/-- The height of an `A`-translate is never equal to the original height.
The obstruction is the congruence `octagonHeight q ≡ 1 + q.x1^2 (mod 3)`. -/
lemma octagonHeight_A_mul_ne (s : Bool) (q : BSUnit23) :
    octagonHeight (octagonUnit (.A s) * q) ≠ octagonHeight q := by
  intro h
  have hlinear := octagonHeight_A_mul_sub s q
  rw [h, sub_self] at hlinear
  have hzero : octagonHeight q + 3 * octagonSign s * octagonA q = 0 := by
    nlinarith
  have hmod := congrArg (fun x : ℤ => (x : ZMod 3)) hzero
  simp only [octagonHeight, octagonA, Int.cast_add, Int.cast_one,
    Int.cast_mul, Int.cast_ofNat, Int.cast_pow] at hmod
  norm_num at hmod
  let x : ZMod 3 := q.x1
  have hthree : (3 : ZMod 3) = 0 := by decide
  have hfour : (4 : ZMod 3) = 1 := by decide
  have hsix : (6 : ZMod 3) = 0 := by decide
  have hx : 1 + x ^ 2 = 0 := by
    simpa [x, hthree, hfour, hsix] using hmod
  exact (by decide : ∀ x : ZMod 3, 1 + x ^ 2 ≠ 0) x hx

/-- The height of a `C`-translate is never equal to the original height. -/
lemma octagonHeight_C_mul_ne (s : Bool) (q : BSUnit23) :
    octagonHeight (octagonUnit (.C s) * q) ≠ octagonHeight q := by
  intro h
  have hlinear := octagonHeight_C_mul_sub s q
  rw [h, sub_self] at hlinear
  cases s <;>
    simp only [octagonSign, octagonHeight, octagonC] at hlinear <;>
    omega

/-- The height of a `B`-translate is never equal to the original height.
After division by two, its height difference is odd. -/
lemma octagonHeight_B_mul_ne (s t : Bool) (q : BSUnit23) :
    octagonHeight (octagonUnit (.B s t) * q) ≠ octagonHeight q := by
  intro h
  have hlinear := octagonHeight_B_mul_sub s t q
  rw [h, sub_self] at hlinear
  cases s <;> cases t <;>
    simp only [octagonSign, octagonHeight, octagonA, octagonC] at hlinear <;>
    omega

/-- The height-decreasing half-space for an order-two projective side
generator. -/
def octagonBDescentSet (s t : Bool) : Set BSUnit23 :=
  {q | octagonHeight (octagonUnit (.B s t) * q) < octagonHeight q}

/-- Coordinate description of a `B`-descent half-space. -/
lemma mem_octagonBDescentSet_iff (s t : Bool) (q : BSUnit23) :
    q ∈ octagonBDescentSet s t ↔
      10 * octagonHeight q + 24 * octagonSign s * octagonC q -
        24 * octagonSign t * octagonA q < 0 := by
  have hdiff := octagonHeight_B_mul_sub s t q
  change octagonHeight (octagonUnit (.B s t) * q) < octagonHeight q ↔ _
  omega

/-- A `B`-generator sends the complement of its decreasing half-space into
that half-space.  Projectively this is an involutive ping-pong move because
its square is the central scalar `-1`. -/
lemma octagon_B_maps_compl_descent (s t : Bool) :
    Set.MapsTo (fun q : BSUnit23 => octagonUnit (.B s t) * q)
      (octagonBDescentSet s t)ᶜ (octagonBDescentSet s t) := by
  intro q hq
  have hnot : ¬octagonHeight (octagonUnit (.B s t) * q) < octagonHeight q := hq
  have hne := octagonHeight_B_mul_ne s t q
  have hlt : octagonHeight q < octagonHeight (octagonUnit (.B s t) * q) :=
    lt_of_le_of_ne (not_lt.mp hnot) hne.symm
  change octagonHeight
      (octagonUnit (.B s t) * (octagonUnit (.B s t) * q)) <
    octagonHeight (octagonUnit (.B s t) * q)
  rw [← mul_assoc, ← pow_two, octagon_B_sq, octagonHeight_center_mul]
  exact hlt

/-- Every projective side involution has a nonempty descent half-space. -/
lemma octagonBDescentSet_nonempty (s t : Bool) :
    (octagonBDescentSet s t).Nonempty := by
  refine ⟨octagonUnit (.B s t), ?_⟩
  change octagonHeight
      (octagonUnit (.B s t) * octagonUnit (.B s t)) <
    octagonHeight (octagonUnit (.B s t))
  rw [← pow_two, octagon_B_sq]
  cases s <;> cases t <;>
    norm_num [octagonHeight, octagonUnit, octagonSign]

/-- The scalar coordinate paired with `octagonHeight` transforms linearly
under an `A`-generator. -/
@[simp] lemma octagonUnit_A_mul_x0 (s : Bool) (q : BSUnit23) :
    (octagonUnit (.A s) * q).x0 =
      3 * q.x0 + 4 * octagonSign s * q.x1 := by
  change 3 * q.x0 + 2 * (2 * octagonSign s) * q.x1 +
    3 * 0 * q.x2 - 6 * 0 * q.x3 = _
  ring

@[simp] lemma octagonUnit_A_mul_x3 (s : Bool) (q : BSUnit23) :
    (octagonUnit (.A s) * q).x3 =
      3 * q.x3 + 2 * octagonSign s * q.x2 := by
  change 3 * q.x3 + 0 * q.x0 + (2 * octagonSign s) * q.x2 - 0 * q.x1 = _
  ring

lemma octagonA_A_mul (s : Bool) (q : BSUnit23) :
    octagonA (octagonUnit (.A s) * q) =
      6 * octagonSign s * octagonHeight q + 17 * octagonA q := by
  cases s <;>
    simp only [octagonA, octagonHeight, octagonUnit_A_mul_x0,
      octagonUnit_A_mul_x1, octagonUnit_A_mul_x2,
      octagonUnit_A_mul_x3, octagonSign] <;>
    nlinarith [q.norm_one]

/-- The component of the handle ping-pong domain attracting positive powers
of `A`. -/
def octagonHandlePositiveSet : Set BSUnit23 :=
  {q | octagonHeight q - 3 * octagonA q < 0}

/-- The component of the handle ping-pong domain attracting negative powers
of `A`. -/
def octagonHandleNegativeSet : Set BSUnit23 :=
  {q | octagonHeight q + 3 * octagonA q < 0}

/-- The two-sided handle domain. -/
def octagonHandleSet : Set BSUnit23 :=
  octagonHandlePositiveSet ∪ octagonHandleNegativeSet

/-- The region between the two handle half-spaces. -/
def octagonHandleCore : Set BSUnit23 :=
  {q | 0 < octagonHeight q - 3 * octagonA q ∧
    0 < octagonHeight q + 3 * octagonA q}

/-- The positive handle component is nonempty. -/
lemma octagonHandlePositiveSet_nonempty : octagonHandlePositiveSet.Nonempty := by
  refine ⟨octagonUnit (.A true), ?_⟩
  norm_num [octagonHandlePositiveSet, octagonHeight, octagonA, octagonUnit,
    octagonSign]

/-- The negative handle component is nonempty. -/
lemma octagonHandleNegativeSet_nonempty : octagonHandleNegativeSet.Nonempty := by
  refine ⟨octagonUnit (.A false), ?_⟩
  norm_num [octagonHandleNegativeSet, octagonHeight, octagonA, octagonUnit,
    octagonSign]

/-- One positive `A` step sends the handle core into the positive component. -/
lemma octagon_A_true_maps_handleCore :
    Set.MapsTo (fun q : BSUnit23 => octagonUnit (.A true) * q)
      octagonHandleCore octagonHandlePositiveSet := by
  intro q hq
  change 0 < octagonHeight q - 3 * octagonA q ∧
    0 < octagonHeight q + 3 * octagonA q at hq
  have hH := octagonHeight_A_mul_sub true q
  have hA := octagonA_A_mul true q
  norm_num [octagonSign] at hH hA
  exact show octagonHeight (octagonUnit (.A true) * q) -
      3 * octagonA (octagonUnit (.A true) * q) < 0 by
    omega

/-- Positive powers remain in the positive handle component. -/
lemma octagon_A_true_maps_handlePositive :
    Set.MapsTo (fun q : BSUnit23 => octagonUnit (.A true) * q)
      octagonHandlePositiveSet octagonHandlePositiveSet := by
  intro q hq
  change octagonHeight q - 3 * octagonA q < 0 at hq
  have hheight := octagonHeight_pos q
  have hH := octagonHeight_A_mul_sub true q
  have hA := octagonA_A_mul true q
  norm_num [octagonSign] at hH hA
  exact show octagonHeight (octagonUnit (.A true) * q) -
      3 * octagonA (octagonUnit (.A true) * q) < 0 by
    omega

/-- One negative `A` step sends the handle core into the negative component. -/
lemma octagon_A_false_maps_handleCore :
    Set.MapsTo (fun q : BSUnit23 => octagonUnit (.A false) * q)
      octagonHandleCore octagonHandleNegativeSet := by
  intro q hq
  change 0 < octagonHeight q - 3 * octagonA q ∧
    0 < octagonHeight q + 3 * octagonA q at hq
  have hH := octagonHeight_A_mul_sub false q
  have hA := octagonA_A_mul false q
  norm_num [octagonSign] at hH hA
  exact show octagonHeight (octagonUnit (.A false) * q) +
      3 * octagonA (octagonUnit (.A false) * q) < 0 by
    omega

/-- Negative powers remain in the negative handle component. -/
lemma octagon_A_false_maps_handleNegative :
    Set.MapsTo (fun q : BSUnit23 => octagonUnit (.A false) * q)
      octagonHandleNegativeSet octagonHandleNegativeSet := by
  intro q hq
  change octagonHeight q + 3 * octagonA q < 0 at hq
  have hheight := octagonHeight_pos q
  have hH := octagonHeight_A_mul_sub false q
  have hA := octagonA_A_mul false q
  norm_num [octagonSign] at hH hA
  exact show octagonHeight (octagonUnit (.A false) * q) +
      3 * octagonA (octagonUnit (.A false) * q) < 0 by
    omega

/-- There is no integral quaternion unit on the negative handle boundary. -/
lemma octagonHeight_add_three_octagonA_ne_zero (q : BSUnit23) :
    octagonHeight q + 3 * octagonA q ≠ 0 := by
  intro hboundary
  apply octagonHeight_A_mul_ne true q
  have hdiff := octagonHeight_A_mul_sub true q
  norm_num [octagonSign] at hdiff
  omega

/-- There is no integral quaternion unit on the positive handle boundary. -/
lemma octagonHeight_sub_three_octagonA_ne_zero (q : BSUnit23) :
    octagonHeight q - 3 * octagonA q ≠ 0 := by
  intro hboundary
  apply octagonHeight_A_mul_ne false q
  have hdiff := octagonHeight_A_mul_sub false q
  norm_num [octagonSign] at hdiff
  omega

/-- The handle core is exactly the complement of the two attracting
half-spaces. -/
lemma octagon_mem_handleCore_iff_not_mem_handleSet (q : BSUnit23) :
    q ∈ octagonHandleCore ↔ q ∉ octagonHandleSet := by
  have hp := octagonHeight_sub_three_octagonA_ne_zero q
  have hn := octagonHeight_add_three_octagonA_ne_zero q
  change (0 < octagonHeight q - 3 * octagonA q ∧
      0 < octagonHeight q + 3 * octagonA q) ↔
    ¬(octagonHeight q - 3 * octagonA q < 0 ∨
      octagonHeight q + 3 * octagonA q < 0)
  omega

/-- The two attracting components of the handle domain are disjoint. -/
lemma octagonHandlePositiveSet_disjoint_negative :
    Disjoint octagonHandlePositiveSet octagonHandleNegativeSet := by
  rw [Set.disjoint_left]
  intro q hp hn
  have hheight := octagonHeight_pos q
  change octagonHeight q - 3 * octagonA q < 0 at hp
  change octagonHeight q + 3 * octagonA q < 0 at hn
  omega

/-- Every positive natural power of `A` sends the handle core into its
positive component. -/
lemma octagon_A_true_pow_succ_maps_handleCore (n : ℕ) :
    Set.MapsTo
      (fun q : BSUnit23 => octagonUnit (.A true) ^ (n + 1) * q)
      octagonHandleCore octagonHandlePositiveSet := by
  induction n with
  | zero => simpa using octagon_A_true_maps_handleCore
  | succ n ih =>
      intro q hq
      have hpos := octagon_A_true_maps_handlePositive (ih hq)
      simpa [pow_succ', mul_assoc, Nat.succ_eq_add_one, add_assoc] using hpos

/-- Every negative natural power of `A` sends the handle core into its
negative component. -/
lemma octagon_A_false_pow_succ_maps_handleCore (n : ℕ) :
    Set.MapsTo
      (fun q : BSUnit23 => octagonUnit (.A false) ^ (n + 1) * q)
      octagonHandleCore octagonHandleNegativeSet := by
  induction n with
  | zero => simpa using octagon_A_false_maps_handleCore
  | succ n ih =>
      intro q hq
      have hneg := octagon_A_false_maps_handleNegative (ih hq)
      simpa [pow_succ', mul_assoc, Nat.succ_eq_add_one, add_assoc] using hneg

/-- Every nonzero integral power of the handle generator sends the handle
core into one of its two attracting components. -/
lemma octagon_A_zpow_maps_handleCore (n : ℤ) (hn : n ≠ 0) :
    Set.MapsTo
      (fun q : BSUnit23 => octagonUnit (.A true) ^ n * q)
      octagonHandleCore octagonHandleSet := by
  intro q hq
  cases n with
  | ofNat n =>
      cases n with
      | zero => exact (hn rfl).elim
      | succ n =>
          apply Or.inl
          simpa only [Int.ofNat_eq_natCast, zpow_natCast] using
            octagon_A_true_pow_succ_maps_handleCore n hq
  | negSucc n =>
      apply Or.inr
      have hneg := octagon_A_false_pow_succ_maps_handleCore n hq
      simpa only [zpow_negSucc, ← inv_pow, ← octagon_A_false_eq_inv] using hneg

/-! ## Domains in the projectivized quaternion group -/

/-- The projective `B`-domain is the image of its height-decreasing
half-space under the quotient by the central scalar. -/
def projectiveOctagonBDescentSet (s t : Bool) :
    Set ProjectivizedQuaternionGroup :=
  QuotientGroup.mk' octagonQuaternionCenter '' octagonBDescentSet s t

/-- Every projective `B`-domain is nonempty. -/
lemma projectiveOctagonBDescentSet_nonempty (s t : Bool) :
    (projectiveOctagonBDescentSet s t).Nonempty := by
  obtain ⟨q, hq⟩ := octagonBDescentSet_nonempty s t
  exact ⟨QuotientGroup.mk' octagonQuaternionCenter q, q, hq, rfl⟩

/-- The projective class of a `B`-generator sends the complement of its
domain into its domain. -/
lemma projective_octagon_B_maps_compl_descent (s t : Bool) :
    Set.MapsTo
      (fun x : ProjectivizedQuaternionGroup =>
        QuotientGroup.mk' octagonQuaternionCenter (octagonUnit (.B s t)) * x)
      (projectiveOctagonBDescentSet s t)ᶜ
      (projectiveOctagonBDescentSet s t) := by
  intro x hx
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective octagonQuaternionCenter x
  have hq : q ∈ (octagonBDescentSet s t)ᶜ := by
    intro hdesc
    apply hx
    exact ⟨q, hdesc, rfl⟩
  have himage := octagon_B_maps_compl_descent s t hq
  refine ⟨octagonUnit (.B s t) * q, himage, ?_⟩
  simp

/-- The projective handle domain is the image of the two attracting
half-spaces. -/
def projectiveOctagonHandleSet : Set ProjectivizedQuaternionGroup :=
  QuotientGroup.mk' octagonQuaternionCenter '' octagonHandleSet

/-- The projective handle domain is nonempty. -/
lemma projectiveOctagonHandleSet_nonempty :
    projectiveOctagonHandleSet.Nonempty := by
  obtain ⟨q, hq⟩ := octagonHandlePositiveSet_nonempty
  exact ⟨QuotientGroup.mk' octagonQuaternionCenter q, q, Or.inl hq, rfl⟩

/-- Every nonzero projective handle power sends the complement of the handle
domain into the handle domain. -/
lemma projective_octagon_A_zpow_maps_compl_handle
    (n : ℤ) (hn : n ≠ 0) :
    Set.MapsTo
      (fun x : ProjectivizedQuaternionGroup =>
        (QuotientGroup.mk' octagonQuaternionCenter
          (octagonUnit (.A true))) ^ n * x)
      (projectiveOctagonHandleSet)ᶜ projectiveOctagonHandleSet := by
  intro x hx
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective octagonQuaternionCenter x
  have hq_not : q ∉ octagonHandleSet := by
    intro hhandle
    apply hx
    exact ⟨q, hhandle, rfl⟩
  have hq_core := (octagon_mem_handleCore_iff_not_mem_handleSet q).2 hq_not
  have himage := octagon_A_zpow_maps_handleCore n hn hq_core
  refine ⟨octagonUnit (.A true) ^ n * q, himage, ?_⟩
  simp

/-! The broad height domains above provide the individual ping-pong moves,
but they are not pairwise disjoint.  The following explicit integral point
records the obstruction, so a complete five-factor argument must refine the
domains rather than silently assuming disjointness. -/

/-- A concrete quaternion unit lying in both the handle domain and the
`B(true,true)` descent domain. -/
def octagonHeightDomainOverlapWitness : BSUnit23 :=
  ⟨6, 4, -1, 0, by norm_num⟩

lemma octagonHeightDomainOverlapWitness_mem_handle :
    octagonHeightDomainOverlapWitness ∈ octagonHandleSet := by
  apply Or.inl
  norm_num [octagonHeightDomainOverlapWitness, octagonHandlePositiveSet,
    octagonHeight, octagonA]

lemma octagonHeightDomainOverlapWitness_mem_B :
    octagonHeightDomainOverlapWitness ∈ octagonBDescentSet true true := by
  rw [mem_octagonBDescentSet_iff]
  norm_num [octagonHeightDomainOverlapWitness, octagonHeight,
    octagonA, octagonC, octagonSign]

/-- In particular, the naive projective handle and `B(true,true)` domains
cannot be supplied directly as the disjoint sets in the ping-pong lemma. -/
lemma projectiveOctagonHandleSet_not_disjoint_B_true_true :
    ¬Disjoint projectiveOctagonHandleSet
      (projectiveOctagonBDescentSet true true) := by
  rw [Set.not_disjoint_iff]
  refine ⟨QuotientGroup.mk' octagonQuaternionCenter
    octagonHeightDomainOverlapWitness, ?_, ?_⟩
  · exact ⟨octagonHeightDomainOverlapWitness,
      octagonHeightDomainOverlapWitness_mem_handle, rfl⟩
  · exact ⟨octagonHeightDomainOverlapWitness,
      octagonHeightDomainOverlapWitness_mem_B, rfl⟩

/-! ## Boundary domains for the HNN stable letter

The two quadratic forms below cut out the closed projective intervals with
affine endpoints `1 / √3, √3` and `-√3, -1 / √3`, respectively.  They are the
natural source and target intervals for the cyclic subgroups in the octagon
HNN decomposition. -/

open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise

noncomputable section

/-- The real projective line on which the octagon PGL representation acts. -/
abbrev OctagonProjectiveBoundary := ℙ ℝ (Fin 2 → ℝ)

/-- The determinant-one matrix representative used for boundary
calculations. -/
def octagonBoundarySL (q : BSUnit23) : SL(2, ℝ) :=
  BuserSarnakQuaternionUnit.toSL (by norm_num) (by norm_num) q

/-- The projective quaternion action on a point represented by a nonzero
column vector is ordinary matrix multiplication on that vector. -/
lemma octagon_toPGL23_smul_boundary_mk
    (q : BSUnit23) (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    BuserSarnakQuaternionUnit.toPGL23 q • Projectivization.mk ℝ v hv =
      Projectivization.mk ℝ (octagonBoundarySL q • v)
        ((smul_ne_zero_iff_ne (octagonBoundarySL q)).2 hv) := by
  rfl

/-- Homogeneous quadratic form for the HNN source interval
`[1 / √3, √3]`. -/
def octagonHNNSourceBoundaryForm (v : Fin 2 → ℝ) : ℝ :=
  (Real.sqrt 3 * v 0 - v 1) * (Real.sqrt 3 * v 1 - v 0)

/-- Homogeneous quadratic form for the HNN target interval
`[-√3, -1 / √3]`. -/
def octagonHNNTargetBoundaryForm (v : Fin 2 → ℝ) : ℝ :=
  (v 0 + Real.sqrt 3 * v 1) * (-Real.sqrt 3 * v 0 - v 1)

/-- The closed source interval in the real projective boundary. -/
def octagonHNNSourceBoundarySet : Set OctagonProjectiveBoundary :=
  {p | 0 ≤ octagonHNNSourceBoundaryForm p.rep}

/-- The closed target interval in the real projective boundary. -/
def octagonHNNTargetBoundarySet : Set OctagonProjectiveBoundary :=
  {p | 0 ≤ octagonHNNTargetBoundaryForm p.rep}

lemma octagonHNNSourceBoundaryForm_smul (a : ℝ) (v : Fin 2 → ℝ) :
    octagonHNNSourceBoundaryForm (a • v) =
      a ^ 2 * octagonHNNSourceBoundaryForm v := by
  simp only [octagonHNNSourceBoundaryForm, Pi.smul_apply, smul_eq_mul]
  ring

lemma octagonHNNTargetBoundaryForm_smul (a : ℝ) (v : Fin 2 → ℝ) :
    octagonHNNTargetBoundaryForm (a • v) =
      a ^ 2 * octagonHNNTargetBoundaryForm v := by
  simp only [octagonHNNTargetBoundaryForm, Pi.smul_apply, smul_eq_mul]
  ring

/-- Membership in the source interval can be checked on any nonzero
representative, rather than Mathlib's chosen representative. -/
lemma mem_octagonHNNSourceBoundarySet_mk_iff
    (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    Projectivization.mk ℝ v hv ∈ octagonHNNSourceBoundarySet ↔
      0 ≤ octagonHNNSourceBoundaryForm v := by
  obtain ⟨a, ha⟩ :=
    Projectivization.exists_smul_eq_mk_rep (K := ℝ) v hv
  change 0 ≤ octagonHNNSourceBoundaryForm
    (Projectivization.mk ℝ v hv).rep ↔ _
  rw [← ha]
  change 0 ≤ octagonHNNSourceBoundaryForm ((a : ℝ) • v) ↔ _
  rw [octagonHNNSourceBoundaryForm_smul]
  exact mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero a.ne_zero)

/-- Membership in the target interval can be checked on any nonzero
representative. -/
lemma mem_octagonHNNTargetBoundarySet_mk_iff
    (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    Projectivization.mk ℝ v hv ∈ octagonHNNTargetBoundarySet ↔
      0 ≤ octagonHNNTargetBoundaryForm v := by
  obtain ⟨a, ha⟩ :=
    Projectivization.exists_smul_eq_mk_rep (K := ℝ) v hv
  change 0 ≤ octagonHNNTargetBoundaryForm
    (Projectivization.mk ℝ v hv).rep ↔ _
  rw [← ha]
  change 0 ≤ octagonHNNTargetBoundaryForm ((a : ℝ) • v) ↔ _
  rw [octagonHNNTargetBoundaryForm_smul]
  exact mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero a.ne_zero)

@[simp] lemma octagonBoundarySL_C_true_apply_zero (v : Fin 2 → ℝ) :
    (octagonBoundarySL (octagonUnit (.C true)) • v) 0 =
      2 * v 0 + Real.sqrt 3 * v 1 := by
  rw [Matrix.SpecialLinearGroup.smul_def]
  change ((BuserSarnakQuaternionUnit.matrix
    (octagonUnit (.C true))) • v) 0 = _
  simp [BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
    octagonUnit, octagonSign, Matrix.vecHead, Matrix.vecTail]

@[simp] lemma octagonBoundarySL_C_true_apply_one (v : Fin 2 → ℝ) :
    (octagonBoundarySL (octagonUnit (.C true)) • v) 1 =
      Real.sqrt 3 * v 0 + 2 * v 1 := by
  rw [Matrix.SpecialLinearGroup.smul_def]
  change ((BuserSarnakQuaternionUnit.matrix
    (octagonUnit (.C true))) • v) 1 = _
  simp [BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
    octagonUnit, octagonSign, Matrix.vecHead, Matrix.vecTail]

@[simp] lemma octagonBoundarySL_C_false_apply_zero (v : Fin 2 → ℝ) :
    (octagonBoundarySL (octagonUnit (.C false)) • v) 0 =
      2 * v 0 - Real.sqrt 3 * v 1 := by
  rw [Matrix.SpecialLinearGroup.smul_def]
  change ((BuserSarnakQuaternionUnit.matrix
    (octagonUnit (.C false))) • v) 0 = _
  simp [BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
    octagonUnit, octagonSign, Matrix.vecHead, Matrix.vecTail]
  ring

@[simp] lemma octagonBoundarySL_C_false_apply_one (v : Fin 2 → ℝ) :
    (octagonBoundarySL (octagonUnit (.C false)) • v) 1 =
      -Real.sqrt 3 * v 0 + 2 * v 1 := by
  rw [Matrix.SpecialLinearGroup.smul_def]
  change ((BuserSarnakQuaternionUnit.matrix
    (octagonUnit (.C false))) • v) 1 = _
  simp [BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
    octagonUnit, octagonSign, Matrix.vecHead, Matrix.vecTail]

/-- The positive `C`-matrix exchanges the two HNN boundary forms up to
sign. -/
lemma octagonHNNSourceBoundaryForm_C_true (v : Fin 2 → ℝ) :
    octagonHNNSourceBoundaryForm
        (octagonBoundarySL (octagonUnit (.C true)) • v) =
      -octagonHNNTargetBoundaryForm v := by
  rw [octagonHNNSourceBoundaryForm, octagonBoundarySL_C_true_apply_zero,
    octagonBoundarySL_C_true_apply_one, octagonHNNTargetBoundaryForm]
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  linear_combination
    ((Real.sqrt 3) ^ 2 * v 0 * v 1 + Real.sqrt 3 * v 0 ^ 2 +
      Real.sqrt 3 * v 1 ^ 2 - v 0 * v 1) * hs

/-- The inverse `C`-matrix exchanges the two HNN boundary forms up to
sign. -/
lemma octagonHNNTargetBoundaryForm_C_false (v : Fin 2 → ℝ) :
    octagonHNNTargetBoundaryForm
        (octagonBoundarySL (octagonUnit (.C false)) • v) =
      -octagonHNNSourceBoundaryForm v := by
  rw [octagonHNNTargetBoundaryForm, octagonBoundarySL_C_false_apply_zero,
    octagonBoundarySL_C_false_apply_one, octagonHNNSourceBoundaryForm]
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  linear_combination
    (-(Real.sqrt 3) ^ 2 * v 0 * v 1 + Real.sqrt 3 * v 0 ^ 2 +
      Real.sqrt 3 * v 1 ^ 2 + v 0 * v 1) * hs

/-- `C` sends every projective point outside the target interval into the
source interval. -/
lemma octagon_C_true_maps_compl_targetBoundary :
    Set.MapsTo (fun p : OctagonProjectiveBoundary =>
      BuserSarnakQuaternionUnit.toPGL23 (octagonUnit (.C true)) • p)
      (octagonHNNTargetBoundarySet)ᶜ octagonHNNSourceBoundarySet := by
  intro p hp
  rw [← Projectivization.mk_rep p]
  change BuserSarnakQuaternionUnit.toPGL23 (octagonUnit (.C true)) •
      Projectivization.mk ℝ p.rep p.rep_nonzero ∈
    octagonHNNSourceBoundarySet
  rw [octagon_toPGL23_smul_boundary_mk,
    mem_octagonHNNSourceBoundarySet_mk_iff,
    octagonHNNSourceBoundaryForm_C_true]
  change ¬0 ≤ octagonHNNTargetBoundaryForm p.rep at hp
  exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge hp))

/-- The HNN stable letter `C⁻¹` sends every projective point outside the
source interval into the target interval. -/
lemma octagon_C_false_maps_compl_sourceBoundary :
    Set.MapsTo (fun p : OctagonProjectiveBoundary =>
      BuserSarnakQuaternionUnit.toPGL23 (octagonUnit (.C false)) • p)
      (octagonHNNSourceBoundarySet)ᶜ octagonHNNTargetBoundarySet := by
  intro p hp
  rw [← Projectivization.mk_rep p]
  change BuserSarnakQuaternionUnit.toPGL23 (octagonUnit (.C false)) •
      Projectivization.mk ℝ p.rep p.rep_nonzero ∈
    octagonHNNTargetBoundarySet
  rw [octagon_toPGL23_smul_boundary_mk,
    mem_octagonHNNTargetBoundarySet_mk_iff,
    octagonHNNTargetBoundaryForm_C_false]
  change ¬0 ≤ octagonHNNSourceBoundaryForm p.rep at hp
  exact neg_nonneg.mpr (le_of_lt (lt_of_not_ge hp))

/-- The target map's HNN stable letter has the expected boundary
ping-pong direction. -/
lemma octagonHNNToPGL23_t_maps_compl_sourceBoundary :
    Set.MapsTo (fun p : OctagonProjectiveBoundary =>
      octagonHNNToPGL23 HNNExtension.t • p)
      (octagonHNNSourceBoundarySet)ᶜ octagonHNNTargetBoundarySet := by
  simpa only [octagonHNNToPGL23_t] using
    octagon_C_false_maps_compl_sourceBoundary

/-- The inverse HNN stable letter has the reverse boundary ping-pong
direction. -/
lemma octagonHNNToPGL23_t_inv_maps_compl_targetBoundary :
    Set.MapsTo (fun p : OctagonProjectiveBoundary =>
      octagonHNNToPGL23 (HNNExtension.t : ProjectiveOctagonHNN)⁻¹ • p)
      (octagonHNNTargetBoundarySet)ᶜ octagonHNNSourceBoundarySet := by
  have htinv :
      octagonHNNToPGL23 (HNNExtension.t : ProjectiveOctagonHNN)⁻¹ =
        BuserSarnakQuaternionUnit.toPGL23 (octagonUnit (.C true)) := by
    rw [map_inv, octagonHNNToPGL23_t]
    simp [octagon_C_false_eq_inv]
  simpa only [htinv] using octagon_C_true_maps_compl_targetBoundary

/-- The two closed HNN boundary intervals are disjoint. -/
lemma octagonHNNSourceBoundarySet_disjoint_target :
    Disjoint octagonHNNSourceBoundarySet octagonHNNTargetBoundarySet := by
  rw [Set.disjoint_left]
  intro p hs ht
  change 0 ≤ octagonHNNSourceBoundaryForm p.rep at hs
  change 0 ≤ octagonHNNTargetBoundaryForm p.rep at ht
  have hr : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsum :
      octagonHNNSourceBoundaryForm p.rep +
          octagonHNNTargetBoundaryForm p.rep =
        -2 * Real.sqrt 3 * (p.rep 0 ^ 2 + p.rep 1 ^ 2) := by
    simp only [octagonHNNSourceBoundaryForm,
      octagonHNNTargetBoundaryForm]
    ring
  have hnonneg :
      0 ≤ Real.sqrt 3 * (p.rep 0 ^ 2 + p.rep 1 ^ 2) :=
    mul_nonneg hr.le (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hmul : Real.sqrt 3 * (p.rep 0 ^ 2 + p.rep 1 ^ 2) = 0 := by
    nlinarith
  have hsumsq : p.rep 0 ^ 2 + p.rep 1 ^ 2 = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hr)
  have h0 : p.rep 0 = 0 := by nlinarith [sq_nonneg (p.rep 1)]
  have h1 : p.rep 1 = 0 := by nlinarith [sq_nonneg (p.rep 0)]
  apply p.rep_nonzero
  funext i
  fin_cases i <;> simp [h0, h1]

lemma octagonHNNSourceBoundarySet_nonempty :
    octagonHNNSourceBoundarySet.Nonempty := by
  let v : Fin 2 → ℝ := ![1, 1]
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num [v] at h0
  refine ⟨Projectivization.mk ℝ v hv, ?_⟩
  rw [mem_octagonHNNSourceBoundarySet_mk_iff]
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr : 1 ≤ Real.sqrt 3 := by nlinarith [Real.sqrt_nonneg 3]
  norm_num [octagonHNNSourceBoundaryForm, v, Matrix.vecHead, Matrix.vecTail]
  nlinarith [sq_nonneg (Real.sqrt 3 - 1)]

lemma octagonHNNTargetBoundarySet_nonempty :
    octagonHNNTargetBoundarySet.Nonempty := by
  let v : Fin 2 → ℝ := ![-1, 1]
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num [v] at h0
  refine ⟨Projectivization.mk ℝ v hv, ?_⟩
  rw [mem_octagonHNNTargetBoundarySet_mk_iff]
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr : 1 ≤ Real.sqrt 3 := by nlinarith [Real.sqrt_nonneg 3]
  norm_num [octagonHNNTargetBoundaryForm, v, Matrix.vecHead, Matrix.vecTail]
  nlinarith [sq_nonneg (Real.sqrt 3 - 1)]

/-! ## The associated cyclic subgroups preserve their boundary intervals -/

/-- Quaternion representative of the HNN source subgroup generator. -/
def octagonHNNSourceQuaternionUnit : BSUnit23 :=
  ⟨3, -4, 0, 2, by norm_num⟩

/-- Quaternion representative of the HNN target subgroup generator. -/
def octagonHNNTargetQuaternionUnit : BSUnit23 :=
  ⟨3, -4, 0, -2, by norm_num⟩

lemma octagonHNNSourceQuaternionUnit_eq_product :
    octagonUnit (.B false false) * (octagonUnit (.A true))⁻¹ *
        octagonUnit (.B false true) = octagonHNNSourceQuaternionUnit := by
  decide

lemma octagonHNNTargetQuaternionUnit_eq_product :
    (octagonUnit (.B true false))⁻¹ * (octagonUnit (.A true))⁻¹ *
        (octagonUnit (.B true true))⁻¹ = octagonHNNTargetQuaternionUnit := by
  decide

@[simp] lemma octagonBoundarySL_sourceQuaternionUnit_apply_zero
    (v : Fin 2 → ℝ) :
    (octagonBoundarySL octagonHNNSourceQuaternionUnit • v) 0 =
      (3 - 4 * Real.sqrt 2) * v 0 +
        2 * Real.sqrt 3 * Real.sqrt 2 * v 1 := by
  rw [Matrix.SpecialLinearGroup.smul_def]
  change ((BuserSarnakQuaternionUnit.matrix
    octagonHNNSourceQuaternionUnit) • v) 0 = _
  simp [BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
    octagonHNNSourceQuaternionUnit, Matrix.vecHead, Matrix.vecTail]
  ring

@[simp] lemma octagonBoundarySL_sourceQuaternionUnit_apply_one
    (v : Fin 2 → ℝ) :
    (octagonBoundarySL octagonHNNSourceQuaternionUnit • v) 1 =
      -2 * Real.sqrt 3 * Real.sqrt 2 * v 0 +
        (3 + 4 * Real.sqrt 2) * v 1 := by
  rw [Matrix.SpecialLinearGroup.smul_def]
  change ((BuserSarnakQuaternionUnit.matrix
    octagonHNNSourceQuaternionUnit) • v) 1 = _
  simp [BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
    octagonHNNSourceQuaternionUnit, Matrix.vecHead, Matrix.vecTail]
  exact Or.inl (by ring)

@[simp] lemma octagonBoundarySL_targetQuaternionUnit_apply_zero
    (v : Fin 2 → ℝ) :
    (octagonBoundarySL octagonHNNTargetQuaternionUnit • v) 0 =
      (3 - 4 * Real.sqrt 2) * v 0 -
        2 * Real.sqrt 3 * Real.sqrt 2 * v 1 := by
  rw [Matrix.SpecialLinearGroup.smul_def]
  change ((BuserSarnakQuaternionUnit.matrix
    octagonHNNTargetQuaternionUnit) • v) 0 = _
  simp [BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
    octagonHNNTargetQuaternionUnit, Matrix.vecHead, Matrix.vecTail]
  ring

@[simp] lemma octagonBoundarySL_targetQuaternionUnit_apply_one
    (v : Fin 2 → ℝ) :
    (octagonBoundarySL octagonHNNTargetQuaternionUnit • v) 1 =
      2 * Real.sqrt 3 * Real.sqrt 2 * v 0 +
        (3 + 4 * Real.sqrt 2) * v 1 := by
  rw [Matrix.SpecialLinearGroup.smul_def]
  change ((BuserSarnakQuaternionUnit.matrix
    octagonHNNTargetQuaternionUnit) • v) 1 = _
  simp [BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix,
    octagonHNNTargetQuaternionUnit, Matrix.vecHead, Matrix.vecTail]
  exact Or.inl (by ring)

/-- The source subgroup generator preserves its boundary form exactly. -/
lemma octagonHNNSourceBoundaryForm_sourceQuaternionUnit
    (v : Fin 2 → ℝ) :
    octagonHNNSourceBoundaryForm
        (octagonBoundarySL octagonHNNSourceQuaternionUnit • v) =
      octagonHNNSourceBoundaryForm v := by
  unfold octagonHNNSourceBoundaryForm
  rw [octagonBoundarySL_sourceQuaternionUnit_apply_zero,
    octagonBoundarySL_sourceQuaternionUnit_apply_one]
  have hr : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination
    (-4 * (Real.sqrt 3) ^ 2 * (Real.sqrt 2) ^ 2 * v 0 * v 1 +
      4 * Real.sqrt 3 * (Real.sqrt 2) ^ 2 * v 0 ^ 2 +
      4 * Real.sqrt 3 * (Real.sqrt 2) ^ 2 * v 1 ^ 2 -
      6 * Real.sqrt 3 * Real.sqrt 2 * v 0 ^ 2 +
      6 * Real.sqrt 3 * Real.sqrt 2 * v 1 ^ 2 + 8 * v 0 * v 1) * hr +
    (4 * Real.sqrt 3 * v 0 ^ 2 + 4 * Real.sqrt 3 * v 1 ^ 2 -
      16 * v 0 * v 1) * hs

/-- The target subgroup generator preserves its boundary form exactly. -/
lemma octagonHNNTargetBoundaryForm_targetQuaternionUnit
    (v : Fin 2 → ℝ) :
    octagonHNNTargetBoundaryForm
        (octagonBoundarySL octagonHNNTargetQuaternionUnit • v) =
      octagonHNNTargetBoundaryForm v := by
  unfold octagonHNNTargetBoundaryForm
  rw [octagonBoundarySL_targetQuaternionUnit_apply_zero,
    octagonBoundarySL_targetQuaternionUnit_apply_one]
  have hr : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination
    (4 * (Real.sqrt 3) ^ 2 * (Real.sqrt 2) ^ 2 * v 0 * v 1 +
      4 * Real.sqrt 3 * (Real.sqrt 2) ^ 2 * v 0 ^ 2 +
      4 * Real.sqrt 3 * (Real.sqrt 2) ^ 2 * v 1 ^ 2 -
      6 * Real.sqrt 3 * Real.sqrt 2 * v 0 ^ 2 +
      6 * Real.sqrt 3 * Real.sqrt 2 * v 1 ^ 2 - 8 * v 0 * v 1) * hr +
    (4 * Real.sqrt 3 * v 0 ^ 2 + 4 * Real.sqrt 3 * v 1 ^ 2 +
      16 * v 0 * v 1) * hs

lemma octagonHNNSourceQuaternionUnit_mem_iff (p : OctagonProjectiveBoundary) :
    BuserSarnakQuaternionUnit.toPGL23 octagonHNNSourceQuaternionUnit • p ∈
        octagonHNNSourceBoundarySet ↔
      p ∈ octagonHNNSourceBoundarySet := by
  rw [← Projectivization.mk_rep p]
  change BuserSarnakQuaternionUnit.toPGL23
      octagonHNNSourceQuaternionUnit •
        Projectivization.mk ℝ p.rep p.rep_nonzero ∈
          octagonHNNSourceBoundarySet ↔
    Projectivization.mk ℝ p.rep p.rep_nonzero ∈
      octagonHNNSourceBoundarySet
  rw [octagon_toPGL23_smul_boundary_mk,
    mem_octagonHNNSourceBoundarySet_mk_iff,
    mem_octagonHNNSourceBoundarySet_mk_iff,
    octagonHNNSourceBoundaryForm_sourceQuaternionUnit]

lemma octagonHNNTargetQuaternionUnit_mem_iff (p : OctagonProjectiveBoundary) :
    BuserSarnakQuaternionUnit.toPGL23 octagonHNNTargetQuaternionUnit • p ∈
        octagonHNNTargetBoundarySet ↔
      p ∈ octagonHNNTargetBoundarySet := by
  rw [← Projectivization.mk_rep p]
  change BuserSarnakQuaternionUnit.toPGL23
      octagonHNNTargetQuaternionUnit •
        Projectivization.mk ℝ p.rep p.rep_nonzero ∈
          octagonHNNTargetBoundarySet ↔
    Projectivization.mk ℝ p.rep p.rep_nonzero ∈
      octagonHNNTargetBoundarySet
  rw [octagon_toPGL23_smul_boundary_mk,
    mem_octagonHNNTargetBoundarySet_mk_iff,
    mem_octagonHNNTargetBoundarySet_mk_iff,
    octagonHNNTargetBoundaryForm_targetQuaternionUnit]

/-- The explicit source generator lies in the setwise stabilizer of the
source interval. -/
lemma octagonHNNSourceQuaternionUnit_mem_stabilizer :
    BuserSarnakQuaternionUnit.toPGL23 octagonHNNSourceQuaternionUnit ∈
      MulAction.stabilizer (PGL(2, ℝ)) octagonHNNSourceBoundarySet := by
  exact MulAction.mem_stabilizer_set.mpr
    octagonHNNSourceQuaternionUnit_mem_iff

/-- The explicit target generator lies in the setwise stabilizer of the
target interval. -/
lemma octagonHNNTargetQuaternionUnit_mem_stabilizer :
    BuserSarnakQuaternionUnit.toPGL23 octagonHNNTargetQuaternionUnit ∈
      MulAction.stabilizer (PGL(2, ℝ)) octagonHNNTargetBoundarySet := by
  exact MulAction.mem_stabilizer_set.mpr
    octagonHNNTargetQuaternionUnit_mem_iff

/-- The abstract HNN source generator has the expected quaternion image. -/
lemma octagonBaseToPGL23_sourceElement :
    octagonBaseToPGL23 octagonBaseSourceElement =
      BuserSarnakQuaternionUnit.toPGL23
        octagonHNNSourceQuaternionUnit := by
  change octagonBaseToPGL23
      (octagonBaseFactorElement .cone2 *
        (octagonBaseFactorElement .handle)⁻¹ *
        octagonBaseFactorElement .cone3) = _
  rw [map_mul, map_mul, map_inv]
  rw [octagonBaseToPGL23_factorElement,
    octagonBaseToPGL23_factorElement,
    octagonBaseToPGL23_factorElement]
  rw [← map_inv, ← map_mul, ← map_mul,
    octagonHNNSourceQuaternionUnit_eq_product]

/-- The abstract HNN target generator has the expected quaternion image. -/
lemma octagonBaseToPGL23_targetElement :
    octagonBaseToPGL23 octagonBaseTargetElement =
      BuserSarnakQuaternionUnit.toPGL23
        octagonHNNTargetQuaternionUnit := by
  change octagonBaseToPGL23
      ((octagonBaseFactorElement .cone1)⁻¹ *
        (octagonBaseFactorElement .handle)⁻¹ *
        (octagonBaseFactorElement .cone4)⁻¹) = _
  rw [map_mul, map_mul, map_inv, map_inv, map_inv]
  rw [octagonBaseToPGL23_factorElement,
    octagonBaseToPGL23_factorElement,
    octagonBaseToPGL23_factorElement]
  rw [← map_inv, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
    octagonHNNTargetQuaternionUnit_eq_product]

/-- Every power of the associated source element preserves the source
boundary interval. -/
lemma octagonBaseSourceElement_zpow_mem_sourceBoundary_iff
    (n : ℤ) (p : OctagonProjectiveBoundary) :
    octagonBaseToPGL23 (octagonBaseSourceElement ^ n) • p ∈
        octagonHNNSourceBoundarySet ↔
      p ∈ octagonHNNSourceBoundarySet := by
  rw [map_zpow, octagonBaseToPGL23_sourceElement]
  apply MulAction.mem_stabilizer_set.mp
  exact (MulAction.stabilizer (PGL(2, ℝ))
    octagonHNNSourceBoundarySet).zpow_mem
      octagonHNNSourceQuaternionUnit_mem_stabilizer n

/-- Every power of the associated target element preserves the target
boundary interval. -/
lemma octagonBaseTargetElement_zpow_mem_targetBoundary_iff
    (n : ℤ) (p : OctagonProjectiveBoundary) :
    octagonBaseToPGL23 (octagonBaseTargetElement ^ n) • p ∈
        octagonHNNTargetBoundarySet ↔
      p ∈ octagonHNNTargetBoundarySet := by
  rw [map_zpow, octagonBaseToPGL23_targetElement]
  apply MulAction.mem_stabilizer_set.mp
  exact (MulAction.stabilizer (PGL(2, ℝ))
    octagonHNNTargetBoundarySet).zpow_mem
      octagonHNNTargetQuaternionUnit_mem_stabilizer n

end

end SystolicGrowth

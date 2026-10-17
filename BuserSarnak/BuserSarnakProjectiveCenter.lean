module

public import BuserSarnak.BuserSarnakOctagonFreeProduct

@[expose] public section

open scoped MatrixGroups

namespace SystolicGrowth

noncomputable section

open Cardinal

/-! ## Coordinate control of the projective quaternion target

These elementary lemmas make the scalar kernel of the quaternion matrix
realization explicit.  They are intended as the target-side input for a
ping-pong or normal-form proof of octagon faithfulness.
-/

/-- The scalar quaternion `-1` has order exactly two. -/
lemma octagonQuaternionCenter_order : orderOf (octagonUnit .center) = 2 := by
  apply orderOf_eq_prime octagon_center_sq
  intro h
  have hcoord := congrArg BuserSarnakQuaternionUnit.x0 h
  change (-1 : ℤ) = 1 at hcoord
  omega

/-- The scalar subgroup consists of exactly `1` and `-1`. -/
lemma mem_octagonQuaternionCenter_iff (q : BSUnit23) :
    q ∈ octagonQuaternionCenter ↔ q = 1 ∨ q = octagonUnit .center := by
  have hfin : IsOfFinOrder (octagonUnit .center) :=
    (isOfFinOrder_iff_pow_eq_one).2
      ⟨2, by norm_num, octagon_center_sq⟩
  constructor
  · intro hq
    have hmem := (hfin.mem_zpowers_iff_mem_range_orderOf).mp hq
    rw [octagonQuaternionCenter_order] at hmem
    rcases Finset.mem_image.mp hmem with ⟨a, ha, hpow⟩
    rw [Finset.mem_range] at ha
    subst q
    interval_cases a <;> simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

/-- A quaternion dies in the projectivized target exactly when it is scalar. -/
@[simp] lemma quotient_mk_octagonQuaternionCenter_eq_one_iff
    (q : BSUnit23) :
    (QuotientGroup.mk' octagonQuaternionCenter q :
      ProjectivizedQuaternionGroup) = 1 ↔
      q = 1 ∨ q = octagonUnit .center := by
  exact (QuotientGroup.eq_one_iff q).trans
    (mem_octagonQuaternionCenter_iff q)

/-- The evident lift of a projective presentation generator to the central
extension's generator type. -/
def projectiveOctagonGeneratorLift :
    ProjectiveOctagonGenerator → OctagonPresentationGenerator
  | .a => .a
  | .c => .c
  | .e1 => .e1
  | .e2 => .e2
  | .e3 => .e3
  | .e4 => .e4

/-- Exact quaternion image of every projective octagon generator. -/
@[simp] lemma projectiveOctagonToProjectivizedQuaternion_of
    (x : ProjectiveOctagonGenerator) :
    projectiveOctagonToProjectivizedQuaternion (PresentedGroup.of x) =
      QuotientGroup.mk' octagonQuaternionCenter
        (octagonPresentationImage (projectiveOctagonGeneratorLift x)) := by
  cases x <;>
    simp [projectiveOctagonToProjectivizedQuaternion,
      projectivizedLiftedOctagonToProjectivizedQuaternion,
      projectiveToProjectivizedLiftedOctagon,
      projectiveToLiftedOctagonQuotientGenerator,
      projectiveOctagonGeneratorLift, octagonPresentationImage]

/-- No generator of the projective octagon presentation is killed by the
quaternion realization. -/
theorem projectiveOctagonToProjectivizedQuaternion_generator_ne_one
    (x : ProjectiveOctagonGenerator) :
    projectiveOctagonToProjectivizedQuaternion (PresentedGroup.of x) ≠ 1 := by
  cases x <;>
    rw [projectiveOctagonToProjectivizedQuaternion_of, ne_eq,
      quotient_mk_octagonQuaternionCenter_eq_one_iff] <;>
    decide

/-- The remaining octagon representation, now valued in Mathlib's standard
real projective linear group. -/
def projectiveOctagonToPGL23 : ProjectiveOctagonGroup →* PGL(2, ℝ) :=
  projectivizedQuaternionToPGL23.comp
    projectiveOctagonToProjectivizedQuaternion

/-- Exact PGL image of a projective presentation generator. -/
@[simp] lemma projectiveOctagonToPGL23_of
    (x : ProjectiveOctagonGenerator) :
    projectiveOctagonToPGL23 (PresentedGroup.of x) =
      BuserSarnakQuaternionUnit.toPGL23
        (octagonPresentationImage (projectiveOctagonGeneratorLift x)) := by
  simp [projectiveOctagonToPGL23,
    projectivizedQuaternionToPGL23,
    projectiveOctagonToProjectivizedQuaternion_of]

/-- Faithfulness of the custom projective quaternion representation is
equivalent to faithfulness of its standard PGL realization. -/
theorem projectiveOctagonToProjectivizedQuaternion_injective_iff_pgl :
    Function.Injective projectiveOctagonToProjectivizedQuaternion ↔
      Function.Injective projectiveOctagonToPGL23 := by
  constructor
  · intro h
    exact projectivizedQuaternionToPGL23_injective.comp h
  · intro h x y hxy
    apply h
    exact congrArg projectivizedQuaternionToPGL23 hxy

/-! ## The infinite handle factor -/

/-- Natural powers of the positive handle generator remain in the positive
quadrant of the split quadratic subalgebra. -/
lemma octagon_A_pow_x0_pos_x1_nonneg (k : ℕ) :
    0 < (octagonUnit (.A true) ^ k).x0 ∧
      0 ≤ (octagonUnit (.A true) ^ k).x1 := by
  induction k with
  | zero =>
      change 0 < (1 : ℤ) ∧ 0 ≤ (0 : ℤ)
      omega
  | succ k ih =>
      rw [pow_succ']
      constructor
      · change 0 < (BuserSarnakQuaternionUnit.mul
          (octagonUnit (.A true)) (octagonUnit (.A true) ^ k)).x0
        change 0 < 3 * (octagonUnit (.A true) ^ k).x0 +
          2 * (2 * octagonSign true) *
              (octagonUnit (.A true) ^ k).x1 +
          3 * 0 * (octagonUnit (.A true) ^ k).x2 -
          6 * 0 * (octagonUnit (.A true) ^ k).x3
        norm_num [octagonSign]
        omega
      · rw [octagonUnit_A_mul_x1]
        norm_num [octagonSign]
        omega

/-- Every positive power of the handle generator has nonzero `x1`
coordinate. -/
lemma octagon_A_pow_succ_x1_pos (k : ℕ) :
    0 < (octagonUnit (.A true) ^ (k + 1)).x1 := by
  rw [pow_succ']
  rw [octagonUnit_A_mul_x1]
  norm_num [octagonSign]
  have h := octagon_A_pow_x0_pos_x1_nonneg k
  omega

/-- No positive power of the handle generator is scalar. -/
lemma octagon_A_pow_succ_not_mem_center (k : ℕ) :
    octagonUnit (.A true) ^ (k + 1) ∉ octagonQuaternionCenter := by
  rw [mem_octagonQuaternionCenter_iff]
  intro h
  have hx1 := octagon_A_pow_succ_x1_pos k
  rcases h with h | h
  · have hc := congrArg BuserSarnakQuaternionUnit.x1 h
    change (octagonUnit (.A true) ^ (k + 1)).x1 = 0 at hc
    omega
  · have hc := congrArg BuserSarnakQuaternionUnit.x1 h
    change (octagonUnit (.A true) ^ (k + 1)).x1 = 0 at hc
    omega

/-- An integral power of the handle generator is scalar only at exponent
zero.  In particular its projective image has infinite order. -/
lemma octagon_A_zpow_mem_center_iff (n : ℤ) :
    octagonUnit (.A true) ^ n ∈ octagonQuaternionCenter ↔ n = 0 := by
  constructor
  · intro hn
    cases n with
    | ofNat k =>
        cases k with
        | zero => rfl
        | succ k =>
            exfalso
            have hn' := hn
            change octagonUnit (.A true) ^ ((k + 1 : ℕ) : ℤ) ∈
              octagonQuaternionCenter at hn'
            rw [zpow_natCast] at hn'
            exact octagon_A_pow_succ_not_mem_center k hn'
    | negSucc k =>
        exfalso
        have hinv := octagonQuaternionCenter.inv_mem hn
        have hpos : octagonUnit (.A true) ^ (k + 1) ∈
            octagonQuaternionCenter := by
          simpa [zpow_negSucc] using hinv
        exact octagon_A_pow_succ_not_mem_center k hpos
  · rintro rfl
    simp

/-- The PGL image of the handle generator has infinite order. -/
theorem orderOf_toPGL23_octagon_A :
    orderOf (BuserSarnakQuaternionUnit.toPGL23
      (octagonUnit (.A true))) = 0 := by
  rw [orderOf_eq_zero_iff']
  intro n hn hpow
  have hker : octagonUnit (.A true) ^ n ∈
      BuserSarnakQuaternionUnit.toPGL23.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hpow
  rw [BuserSarnakQuaternionUnit.toPGL23_ker] at hker
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact octagon_A_pow_succ_not_mem_center k hker

/-- Each cone generator remains an involution after projectivization. -/
theorem orderOf_toPGL23_octagon_B (s t : Bool) :
    orderOf (BuserSarnakQuaternionUnit.toPGL23
      (octagonUnit (.B s t))) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow, octagon_B_sq]
    change BuserSarnakQuaternionUnit.toPGL23
        (octagonUnit .center) = 1
    rw [← MonoidHom.mem_ker,
      BuserSarnakQuaternionUnit.toPGL23_ker]
    exact Subgroup.mem_zpowers _
  · intro h
    have hmem : octagonUnit (.B s t) ∈ octagonQuaternionCenter := by
      rw [← BuserSarnakQuaternionUnit.toPGL23_ker,
        MonoidHom.mem_ker]
      exact h
    rw [mem_octagonQuaternionCenter_iff] at hmem
    cases s <;> cases t <;> rcases hmem with hmem | hmem <;>
      have hcoord := congrArg BuserSarnakQuaternionUnit.x3 hmem <;>
      change (1 : ℤ) = 0 at hcoord <;>
      omega

/-! ## Faithfulness on every HNN base factor -/

/-- The restriction of a homomorphism to a cyclic subgroup is injective when
it preserves the generator's order, including infinite order (`orderOf = 0`). -/
private lemma injective_zpowers_comp_of_orderOf_map_eq
    {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G)
    (horder : orderOf (f g) = orderOf g) :
    Function.Injective (f.comp (Subgroup.zpowers g).subtype) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨x, ⟨n, rfl⟩⟩ hx
  apply Subtype.ext
  change g ^ n = 1
  apply orderOf_dvd_iff_zpow_eq_one.mp
  have hdiv : (orderOf (f g) : ℤ) ∣ n :=
    orderOf_dvd_iff_zpow_eq_one.mpr (by
      simpa [map_zpow] using hx)
  simpa [horder] using hdiv

/-- Quaternion/PGL realization restricted to the HNN base presentation. -/
def octagonBaseToPGL23 : OctagonBaseGroup →* PGL(2, ℝ) :=
  projectiveOctagonToPGL23.comp octagonBaseToProjective

@[simp] lemma octagonBaseToPGL23_factorElement
    (i : OctagonBaseFactor) :
    octagonBaseToPGL23 (octagonBaseFactorElement i) =
      BuserSarnakQuaternionUnit.toPGL23
        (match i with
        | .handle => octagonUnit (.A true)
        | .cone1 => octagonUnit (.B true false)
        | .cone2 => octagonUnit (.B false false)
        | .cone3 => octagonUnit (.B false true)
        | .cone4 => octagonUnit (.B true true)) := by
  cases i <;>
    simp [octagonBaseToPGL23, octagonBaseFactorElement,
      octagonBaseA, octagonBaseE1, octagonBaseE2, octagonBaseE3,
      octagonBaseE4, octagonBaseToProjectiveGenerator,
      projectiveOctagonGeneratorLift, octagonPresentationImage]

/-- The abstract handle generator has infinite order. -/
lemma orderOf_octagonBaseA : orderOf octagonBaseA = 0 := by
  rw [orderOf_eq_zero_iff']
  intro n hn hpow
  have h := congrArg octagonBaseExponent hpow
  simp [octagonBaseA, octagonBaseExponentImage] at h
  omega

/-- Every abstract cone generator has order exactly two. -/
lemma orderOf_octagonBaseFactorElement :
    ∀ i : OctagonBaseFactor,
      orderOf (octagonBaseFactorElement i) =
        match i with
        | .handle => 0
        | .cone1 | .cone2 | .cone3 | .cone4 => 2
  | .handle => orderOf_octagonBaseA
  | .cone1 => by
      apply orderOf_eq_prime octagonBase_e1_sq
      intro h
      have hm :
          octagonBaseToPGL23 (octagonBaseFactorElement .cone1) = 1 := by
        simpa [octagonBaseFactorElement, octagonBaseE1] using
          congrArg octagonBaseToPGL23 h
      have ho := congrArg orderOf hm
      rw [octagonBaseToPGL23_factorElement,
        orderOf_toPGL23_octagon_B, orderOf_one] at ho
      omega
  | .cone2 => by
      apply orderOf_eq_prime octagonBase_e2_sq
      intro h
      have hm :
          octagonBaseToPGL23 (octagonBaseFactorElement .cone2) = 1 := by
        simpa [octagonBaseFactorElement, octagonBaseE2] using
          congrArg octagonBaseToPGL23 h
      have ho := congrArg orderOf hm
      rw [octagonBaseToPGL23_factorElement,
        orderOf_toPGL23_octagon_B, orderOf_one] at ho
      omega
  | .cone3 => by
      apply orderOf_eq_prime octagonBase_e3_sq
      intro h
      have hm :
          octagonBaseToPGL23 (octagonBaseFactorElement .cone3) = 1 := by
        simpa [octagonBaseFactorElement, octagonBaseE3] using
          congrArg octagonBaseToPGL23 h
      have ho := congrArg orderOf hm
      rw [octagonBaseToPGL23_factorElement,
        orderOf_toPGL23_octagon_B, orderOf_one] at ho
      omega
  | .cone4 => by
      apply orderOf_eq_prime octagonBase_e4_sq
      intro h
      have hm :
          octagonBaseToPGL23 (octagonBaseFactorElement .cone4) = 1 := by
        simpa [octagonBaseFactorElement, octagonBaseE4] using
          congrArg octagonBaseToPGL23 h
      have ho := congrArg orderOf hm
      rw [octagonBaseToPGL23_factorElement,
        orderOf_toPGL23_octagon_B, orderOf_one] at ho
      omega

/-- The PGL realization preserves the order of every free-product factor
generator. -/
lemma orderOf_octagonBaseToPGL23_factorElement
    (i : OctagonBaseFactor) :
    orderOf (octagonBaseToPGL23 (octagonBaseFactorElement i)) =
      orderOf (octagonBaseFactorElement i) := by
  cases i <;>
    simp [orderOf_octagonBaseFactorElement,
      orderOf_toPGL23_octagon_A, orderOf_toPGL23_octagon_B]

/-- The PGL realization is faithful on each individual cyclic factor of the
HNN base.  The remaining base-faithfulness task is therefore purely the
ping-pong separation of distinct factors. -/
theorem octagonBaseFactorToPGL23_injective (i : OctagonBaseFactor) :
    Function.Injective
      (octagonBaseToPGL23.comp (octagonBaseFactorInclusion i)) := by
  exact injective_zpowers_comp_of_orderOf_map_eq octagonBaseToPGL23
    (octagonBaseFactorElement i)
    (orderOf_octagonBaseToPGL23_factorElement i)

/-- There are enough base factors for the cardinality branch of Mathlib's
coproduct ping-pong lemma. -/
lemma three_le_card_octagonBaseFactor : 3 ≤ #(OctagonBaseFactor) := by
  let f : Fin 3 → OctagonBaseFactor
    | 0 => .handle
    | 1 => .cone1
    | 2 => .cone2
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  calc
    3 = #(Fin 3) := by simp
    _ ≤ #(OctagonBaseFactor) := Cardinal.mk_le_of_injective hf

/-- On the free-product model of the HNN base, the quaternion/PGL map is
exactly the coproduct lift of its five factor restrictions. -/
lemma octagonBaseToPGL23_comp_freeProductToBase :
    octagonBaseToPGL23.comp octagonBaseFreeProductToBase =
      Monoid.CoprodI.lift
        (fun i => octagonBaseToPGL23.comp (octagonBaseFactorInclusion i)) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  ext x
  simp [octagonBaseFreeProductToBase]

/-- Faithfulness on the HNN base is precisely faithfulness of the coproduct
lift.  Thus the remaining base-group obligation has the exact shape required
by Mathlib's coproduct ping-pong lemma. -/
theorem octagonBaseToPGL23_injective_iff_freeProductLift :
    Function.Injective octagonBaseToPGL23 ↔
      Function.Injective
        (Monoid.CoprodI.lift
          (fun i => octagonBaseToPGL23.comp
            (octagonBaseFactorInclusion i))) := by
  rw [← octagonBaseToPGL23_comp_freeProductToBase]
  constructor
  · intro h
    exact h.comp octagonBaseEquivFreeProduct.symm.injective
  · intro h x y hxy
    apply octagonBaseEquivFreeProduct.injective
    apply h
    calc
      octagonBaseToPGL23
          (octagonBaseFreeProductToBase (octagonBaseEquivFreeProduct x)) =
          octagonBaseToPGL23 x :=
        congrArg octagonBaseToPGL23
          (octagonBaseEquivFreeProduct.left_inv x)
      _ = octagonBaseToPGL23 y := hxy
      _ = octagonBaseToPGL23
          (octagonBaseFreeProductToBase (octagonBaseEquivFreeProduct y)) :=
        congrArg octagonBaseToPGL23
          (octagonBaseEquivFreeProduct.left_inv y).symm

/-! ## The target map in HNN coordinates -/

/-- The PGL realization transported to the octagon HNN normal form. -/
def octagonHNNToPGL23 : ProjectiveOctagonHNN →* PGL(2, ℝ) :=
  projectiveOctagonToPGL23.comp octagonHNNToProjective

/-- Its restriction to the HNN base is the previously defined base map. -/
@[simp] lemma octagonHNNToPGL23_of (g : OctagonBaseGroup) :
    octagonHNNToPGL23 (HNNExtension.of g) = octagonBaseToPGL23 g := by
  rfl

/-- The HNN stable letter is represented by the inverse `C` generator. -/
@[simp] lemma octagonHNNToPGL23_t :
    octagonHNNToPGL23 HNNExtension.t =
      BuserSarnakQuaternionUnit.toPGL23 (octagonUnit (.C false)) := by
  simp [octagonHNNToPGL23, octagonHNNToProjective,
    projectiveOctagonToPGL23_of, projectiveOctagonGeneratorLift,
    octagonPresentationImage, octagon_C_false_eq_inv]

/-- Projective octagon faithfulness is equivalently faithfulness of the
explicit HNN target map. -/
theorem projectiveOctagonToPGL23_injective_iff_hnn :
    Function.Injective projectiveOctagonToPGL23 ↔
      Function.Injective octagonHNNToPGL23 := by
  constructor
  · intro h
    exact h.comp projectiveOctagonEquivHNN.symm.injective
  · intro h x y hxy
    apply projectiveOctagonEquivHNN.injective
    apply h
    calc
      projectiveOctagonToPGL23
          (octagonHNNToProjective (projectiveOctagonEquivHNN x)) =
          projectiveOctagonToPGL23 x :=
        congrArg projectiveOctagonToPGL23
          (projectiveOctagonEquivHNN.left_inv x)
      _ = projectiveOctagonToPGL23 y := hxy
      _ = projectiveOctagonToPGL23
          (octagonHNNToProjective (projectiveOctagonEquivHNN y)) :=
        congrArg projectiveOctagonToPGL23
          (projectiveOctagonEquivHNN.left_inv y).symm

end

end SystolicGrowth

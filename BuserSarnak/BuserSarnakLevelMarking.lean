module

public import BuserSarnak.BuserSarnakPresentationEquiv
public import BuserSarnak.BuserSarnakCorrection
public import Vendored.ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.TargetPresentation

@[expose] public section

/-!
# Buser--Sarnak principal-level marking

This module connects the finite reduction of the lifted octagon presentation
to the cleaned finite Reidemeister--Schreier machinery.  It fixes the target
to the standard surface presentation and exposes the finite prefix-tree and
Tietze certificates still needed for a concrete marking.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

/-- Enumeration of the seven generators, used by finite certificate producers. -/
instance instFintypeOctagonPresentationGenerator :
    Fintype OctagonPresentationGenerator :=
  Fintype.ofList [.z, .a, .c, .e1, .e2, .e3, .e4] (by
    intro x
    cases x <;> simp)

/-- Enumeration of the eight defining octagon relators. -/
instance instFintypeOctagonPresentationRelator :
    Fintype OctagonPresentationRelator :=
  Fintype.ofList
    [.z_sq, .z_comm_a, .z_comm_c, .e1_sq, .e2_sq, .e3_sq, .e4_sq,
      .polygon] (by
        intro x
        cases x <;> simp)

@[simp] theorem card_octagonPresentationRelator :
    Fintype.card OctagonPresentationRelator = 8 := by
  decide

noncomputable local instance buserSarnakReductionRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakReductionRange p) :=
  Fintype.ofFinite (BuserSarnakReductionRange p)

/-- Core.Reduction of integral quaternion units onto its finite range. -/
def buserSarnakReductionRangeHom (p : ℕ) [NeZero p] :
    BSUnit23 →* BuserSarnakReductionRange p :=
  (BuserSarnakQuaternionUnit.reductionMod p).toHomUnits.rangeRestrict

/-- Core.Reduction of each lifted-octagon presentation generator. -/
def buserSarnakOctagonReductionImage (p : ℕ) [NeZero p] :
    OctagonPresentationGenerator → BuserSarnakReductionRange p :=
  fun x => buserSarnakReductionRangeHom p (octagonPresentationImage x)

/-- At every odd prime level, the central octagon generator remains a
nontrivial element of the finite reduction image. -/
theorem buserSarnakOctagonReductionImage_z_ne_one
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) :
    buserSarnakOctagonReductionImage p .z ≠ 1 := by
  intro hz
  have hzmod : BuserSarnakQuaternionUnit.reductionMod p
      (octagonPresentationImage .z) = 1 := by
    have hval := congrArg
      (fun q : BuserSarnakReductionRange p =>
        ((q.1 : Units (BuserSarnakQuaternionMod p)) :
          BuserSarnakQuaternionMod p)) hz
    simpa [buserSarnakOctagonReductionImage,
      buserSarnakReductionRangeHom] using hval
  have hdiv :=
    (BuserSarnakQuaternionUnit.reductionMod_eq_one_iff p
      (octagonPresentationImage .z)).mp hzmod
  have hpdivInt : (p : ℤ) ∣ 2 := by
    simpa [octagonPresentationImage, octagonUnit] using hdiv.1
  have hpdiv : p ∣ 2 := by exact_mod_cast hpdivInt
  exact hp2 (Nat.dvd_prime (by norm_num : Nat.Prime 2) |>.mp hpdiv |>.resolve_left hp.ne_one)

/-- The central finite-quotient image is an involution. -/
@[simp] theorem buserSarnakOctagonReductionImage_z_sq
    (p : ℕ) [NeZero p] :
    buserSarnakOctagonReductionImage p .z ^ 2 = 1 := by
  change (buserSarnakReductionRangeHom p (octagonPresentationImage .z)) ^ 2 = 1
  rw [← map_pow, octagonPresentationImage, octagon_center_sq, map_one]

/-- Each lifted cone generator squares to the nontrivial central class in
the finite quotient. -/
theorem buserSarnakOctagonReductionImage_cone_sq
    (p : ℕ) [NeZero p]
    (e : OctagonPresentationGenerator)
    (he : e = .e1 ∨ e = .e2 ∨ e = .e3 ∨ e = .e4) :
    buserSarnakOctagonReductionImage p e ^ 2 =
      buserSarnakOctagonReductionImage p .z := by
  rcases he with rfl | rfl | rfl | rfl <;>
    change (buserSarnakReductionRangeHom p
      (octagonPresentationImage _)) ^ 2 =
        buserSarnakReductionRangeHom p (octagonPresentationImage .z) <;>
    rw [← map_pow] <;>
    simp only [octagonPresentationImage, octagon_B_sq]

/-- Consequently every lifted cone generator has exact order four at an odd
prime level. -/
theorem orderOf_buserSarnakOctagonReductionImage_cone
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (e : OctagonPresentationGenerator)
    (he : e = .e1 ∨ e = .e2 ∨ e = .e3 ∨ e = .e4) :
    orderOf (buserSarnakOctagonReductionImage p e) = 4 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · simpa [buserSarnakOctagonReductionImage_cone_sq p e he] using
      buserSarnakOctagonReductionImage_z_ne_one p hp hp2
  · norm_num
    rw [show buserSarnakOctagonReductionImage p e ^ 4 =
        (buserSarnakOctagonReductionImage p e ^ 2) ^ 2 by group,
      buserSarnakOctagonReductionImage_cone_sq p e he,
      buserSarnakOctagonReductionImage_z_sq]

/-- Pair a quotient state with its translate by the nontrivial central
involution.  These pairs are the natural cells for eliminating the lifted
orbifold torsion relations. -/
def buserSarnakCentralPartner (p : ℕ) [NeZero p]
    (q : BuserSarnakReductionRange p) : BuserSarnakReductionRange p :=
  q * buserSarnakOctagonReductionImage p .z

@[simp] theorem buserSarnakCentralPartner_partner
    (p : ℕ) [NeZero p] (q : BuserSarnakReductionRange p) :
    buserSarnakCentralPartner p (buserSarnakCentralPartner p q) = q := by
  unfold buserSarnakCentralPartner
  rw [mul_assoc, ← pow_two,
    buserSarnakOctagonReductionImage_z_sq, mul_one]

theorem buserSarnakCentralPartner_ne
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakReductionRange p) :
    buserSarnakCentralPartner p q ≠ q := by
  intro hq
  apply buserSarnakOctagonReductionImage_z_ne_one p hp hp2
  apply mul_left_cancel (a := q)
  simpa [buserSarnakCentralPartner] using hq

/-- The central pairing is a fixed-point-free involutive permutation of the
finite quotient states. -/
def buserSarnakCentralPartnerEquiv (p : ℕ) [NeZero p] :
    BuserSarnakReductionRange p ≃ BuserSarnakReductionRange p where
  toFun := buserSarnakCentralPartner p
  invFun := buserSarnakCentralPartner p
  left_inv := buserSarnakCentralPartner_partner p
  right_inv := buserSarnakCentralPartner_partner p

/-- Traversing any lifted cone edge twice reaches the central partner of the
starting quotient state. -/
theorem buserSarnak_mul_cone_mul_cone
    (p : ℕ) [NeZero p] (q : BuserSarnakReductionRange p)
    (e : OctagonPresentationGenerator)
    (he : e = .e1 ∨ e = .e2 ∨ e = .e3 ∨ e = .e4) :
    (q * buserSarnakOctagonReductionImage p e) *
        buserSarnakOctagonReductionImage p e =
      buserSarnakCentralPartner p q := by
  rw [mul_assoc, ← pow_two,
    buserSarnakOctagonReductionImage_cone_sq p e he]
  rfl

/-- The free-group map induced by the reduced octagon generators. -/
def buserSarnakOctagonReductionMap (p : ℕ) [NeZero p] :
    FreeGroup OctagonPresentationGenerator →* BuserSarnakReductionRange p :=
  FreeGroup.lift (buserSarnakOctagonReductionImage p)

/-- The free reduction map factors through the quaternion realization. -/
lemma buserSarnakOctagonReductionMap_eq_comp (p : ℕ) [NeZero p] :
    buserSarnakOctagonReductionMap p =
      (buserSarnakReductionRangeHom p).comp
        (FreeGroup.lift octagonPresentationImage) := by
  apply FreeGroup.ext_hom
  intro x
  simp [buserSarnakOctagonReductionMap,
    buserSarnakOctagonReductionImage]

private lemma octagonFreeLift_eq_lifted_mk
    (w : FreeGroup OctagonPresentationGenerator) :
    FreeGroup.lift octagonPresentationImage w =
      liftedOctagonToQuaternion (PresentedGroup.mk octagonPresentationRelators w) := by
  rfl

theorem buserSarnakOctagonReductionMap_surjective (p : ℕ) [NeZero p] :
    Function.Surjective (buserSarnakOctagonReductionMap p) := by
  intro q
  obtain ⟨u, hu⟩ := MonoidHom.rangeRestrict_surjective
      (BuserSarnakQuaternionUnit.reductionMod p).toHomUnits q
  obtain ⟨z, hz⟩ := liftedOctagonToQuaternion_surjective u
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective octagonPresentationRelators z
  refine ⟨w, ?_⟩
  rw [← hu]
  rw [buserSarnakOctagonReductionMap_eq_comp]
  apply Subtype.ext
  change (BuserSarnakQuaternionUnit.reductionMod p).toHomUnits
      (FreeGroup.lift octagonPresentationImage w) =
    (BuserSarnakQuaternionUnit.reductionMod p).toHomUnits u
  rw [octagonFreeLift_eq_lifted_mk, hz]

/-- Every octagon relator vanishes under finite reduction. -/
lemma buserSarnakOctagonReductionImage_relations (p : ℕ) [NeZero p] :
    ∀ r ∈ octagonPresentationRelators,
      FreeGroup.lift (buserSarnakOctagonReductionImage p) r = 1 := by
  intro r hr
  change buserSarnakOctagonReductionMap p r = 1
  rw [buserSarnakOctagonReductionMap_eq_comp]
  change buserSarnakReductionRangeHom p
      (FreeGroup.lift octagonPresentationImage r) = 1
  rw [octagonPresentationImage_relations r hr, map_one]

/-- The induced finite quotient of the lifted octagon group. -/
def buserSarnakOctagonReductionPresentedHom (p : ℕ) [NeZero p] :
    LiftedOctagonGroup →* BuserSarnakReductionRange p :=
  PresentedGroup.toGroup (buserSarnakOctagonReductionImage_relations p)

/-- The presented quotient is reduction after quaternion realization. -/
lemma buserSarnakOctagonReductionPresentedHom_eq_comp (p : ℕ) [NeZero p] :
    buserSarnakOctagonReductionPresentedHom p =
      (buserSarnakReductionRangeHom p).comp liftedOctagonToQuaternion := by
  apply PresentedGroup.ext
  intro x
  simp [buserSarnakOctagonReductionPresentedHom,
    buserSarnakOctagonReductionImage]

/-- The presented octagon reduction reaches its full finite range. -/
theorem buserSarnakOctagonReductionPresentedHom_surjective
    (p : ℕ) [NeZero p] :
    Function.Surjective (buserSarnakOctagonReductionPresentedHom p) := by
  rw [buserSarnakOctagonReductionPresentedHom_eq_comp]
  exact (MonoidHom.rangeRestrict_surjective
    (BuserSarnakQuaternionUnit.reductionMod p).toHomUnits).comp
      liftedOctagonToQuaternion_surjective

/-- Its kernel is the pullback of the principal congruence subgroup. -/
theorem buserSarnakOctagonReductionPresentedHom_ker (p : ℕ) [NeZero p] :
    (buserSarnakOctagonReductionPresentedHom p).ker =
      (BuserSarnakQuaternionUnit.principalCongruenceSubgroup
        (a := 2) (b := 3) (p : ℤ)).comap liftedOctagonToQuaternion := by
  rw [BuserSarnakQuaternionUnit.principalCongruenceSubgroup23_eq_ker_reductionUnits]
  ext z
  simp only [MonoidHom.mem_ker, Subgroup.mem_comap]
  rw [buserSarnakOctagonReductionPresentedHom_eq_comp]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- Mapping the presented kernel to quaternions gives the principal subgroup. -/
theorem buserSarnakOctagonReductionPresentedHom_ker_map (p : ℕ) [NeZero p] :
    (buserSarnakOctagonReductionPresentedHom p).ker.map
        liftedOctagonToQuaternion =
      BuserSarnakQuaternionUnit.principalCongruenceSubgroup
        (a := 2) (b := 3) (p : ℤ) := by
  rw [buserSarnakOctagonReductionPresentedHom_ker]
  exact Subgroup.map_comap_eq_self_of_surjective
    liftedOctagonToQuaternion_surjective _

/-- The `(2,3)` quaternion matrix realization is injective. -/
theorem buserSarnakToSLHom23_injective :
    Function.Injective
      (BuserSarnakQuaternionUnit.toSLHom
        (a := 2) (b := 3) (by norm_num) (by norm_num)) := by
  intro x y hxy
  have hm : x.matrix = y.matrix := congrArg Subtype.val hxy
  have h00 := congrFun (congrFun hm (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun hm (0 : Fin 2)) (1 : Fin 2)
  have h10 := congrFun (congrFun hm (1 : Fin 2)) (0 : Fin 2)
  have h11 := congrFun (congrFun hm (1 : Fin 2)) (1 : Fin 2)
  norm_num [BuserSarnakQuaternionUnit.matrix, buserSarnakMatrix] at h00 h01 h10 h11
  have hsqrt2 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt3 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  apply BuserSarnakQuaternionUnit.ext
  · exact_mod_cast (show (x.x0 : ℝ) = y.x0 by nlinarith)
  · exact_mod_cast (show (x.x1 : ℝ) = y.x1 by nlinarith)
  · exact_mod_cast (show (x.x2 : ℝ) = y.x2 by nlinarith)
  · exact_mod_cast (show (x.x3 : ℝ) = y.x3 by nlinarith)

/-- The integral principal subgroup and its concrete matrix image are isomorphic. -/
noncomputable def buserSarnakPrincipalEquivLevelGroup23 (p : ℕ) :
    BuserSarnakQuaternionUnit.principalCongruenceSubgroup
        (a := 2) (b := 3) (p : ℤ) ≃*
      buserSarnakLevelGroup23 p :=
  Subgroup.equivMapOfInjective
    (BuserSarnakQuaternionUnit.principalCongruenceSubgroup
      (a := 2) (b := 3) (p : ℤ))
    (BuserSarnakQuaternionUnit.toSLHom
      (a := 2) (b := 3) (by norm_num) (by norm_num))
    buserSarnakToSLHom23_injective

/-- Once the octagon presentation is faithful, its reduction kernel is the
concrete principal-level matrix group. -/
noncomputable def buserSarnakOctagonPresentedKernelEquivLevelGroup23
    (p : ℕ) [NeZero p]
    (hfaith : Function.Injective liftedOctagonToQuaternion) :
    (buserSarnakOctagonReductionPresentedHom p).ker ≃*
      buserSarnakLevelGroup23 p :=
  ((buserSarnakOctagonReductionPresentedHom p).ker.equivMapOfInjective
      liftedOctagonToQuaternion hfaith).trans
    ((MulEquiv.subgroupCongr
      (buserSarnakOctagonReductionPresentedHom_ker_map p)).trans
        (buserSarnakPrincipalEquivLevelGroup23 p))

/-- A computation-facing prefix tree for the finite octagon reduction
quotient.  A breadth-first search in the finite Cayley graph can populate
these four fields. -/
structure BuserSarnakOctagonQuotientSectionData (p : ℕ) [NeZero p] where
  quotientSectionWord : BuserSarnakReductionRange p →
    List (OctagonPresentationGenerator × Bool)
  quotientMap_mk_quotientSectionWord :
    ∀ q : BuserSarnakReductionRange p,
      buserSarnakOctagonReductionMap p
          (FreeGroup.mk (quotientSectionWord q)) = q
  quotientSectionWord_positive :
    ∀ q : BuserSarnakReductionRange p,
      ∀ xb ∈ quotientSectionWord q, xb.2 = true
  prefixState :
    ∀ q : BuserSarnakReductionRange p,
      ∀ acc rest : List (OctagonPresentationGenerator × Bool),
        acc ++ rest = quotientSectionWord q →
          quotientSectionWord
              (buserSarnakOctagonReductionMap p (FreeGroup.mk acc)) = acc

namespace BuserSarnakOctagonQuotientSectionData

/-- Forget the specialized quotient section to the generic positive certificate. -/
def toPositiveCertificate {p : ℕ} [NeZero p]
    (S : BuserSarnakOctagonQuotientSectionData p) :
    PositivePrefixClosedQuotientSectionWordCertificate
      OctagonPresentationGenerator (BuserSarnakReductionRange p) where
  quotientMap := buserSarnakOctagonReductionMap p
  quotientSectionWord := S.quotientSectionWord
  quotientMap_mk_quotientSectionWord :=
    S.quotientMap_mk_quotientSectionWord
  quotientSectionWord_positive := S.quotientSectionWord_positive
  prefixState := S.prefixState

/-- Prefix-closed Schreier data determined by the specialized quotient tree. -/
def schreierData {p : ℕ} [NeZero p]
    (S : BuserSarnakOctagonQuotientSectionData p) :
    PrefixClosedFiniteQuotientSchreierData
      OctagonPresentationGenerator (BuserSarnakReductionRange p) :=
  S.toPositiveCertificate.toPrefixClosedFiniteQuotientSchreierData

@[simp] lemma schreierData_quotientMap {p : ℕ} [NeZero p]
    (S : BuserSarnakOctagonQuotientSectionData p) :
    S.schreierData.toFiniteQuotientSchreierData.quotientMap =
      buserSarnakOctagonReductionMap p := rfl

end BuserSarnakOctagonQuotientSectionData

/-! ## A canonical finite quotient section

The quotient section below is chosen uniformly from a shortest-word predecessor
tree. Negative free-group letters first become positive powers using finiteness;
well-founded recursion on shortest positive length then makes every prefix the
chosen word for its endpoint.
-/

def positiveOctagonEval (p : ℕ) [NeZero p]
    (xs : List OctagonPresentationGenerator) : BuserSarnakReductionRange p :=
  (xs.map (buserSarnakOctagonReductionImage p)).prod

@[simp] lemma positiveOctagonEval_nil (p : ℕ) [NeZero p] :
    positiveOctagonEval p [] = 1 := rfl

lemma positiveOctagonEval_append (p : ℕ) [NeZero p]
    (xs ys : List OctagonPresentationGenerator) :
    positiveOctagonEval p (xs ++ ys) =
      positiveOctagonEval p xs * positiveOctagonEval p ys := by
  simp [positiveOctagonEval]

@[simp] lemma positiveOctagonEval_singleton (p : ℕ) [NeZero p]
    (x : OctagonPresentationGenerator) :
    positiveOctagonEval p [x] = buserSarnakOctagonReductionImage p x := by
  simp [positiveOctagonEval]

private lemma pow_natCard_sub_one_eq_inv_of_finite {G : Type*} [Group G] [Finite G] (x : G) :
    x ^ (Nat.card G - 1) = x⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  have hcard : 0 < Nat.card G := Nat.card_pos
  rw [Nat.sub_add_cancel hcard]
  exact orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard x)

def positiveOctagonExpansion (p : ℕ) [NeZero p]
    (w : List (OctagonPresentationGenerator × Bool)) :
    List OctagonPresentationGenerator :=
  w.flatMap fun xb =>
    if xb.2 then [xb.1]
    else List.replicate (Nat.card (BuserSarnakReductionRange p) - 1) xb.1

lemma positiveOctagonEval_positiveOctagonExpansion (p : ℕ) [NeZero p]
    (w : List (OctagonPresentationGenerator × Bool)) :
    positiveOctagonEval p (positiveOctagonExpansion p w) =
      FreeGroup.lift (buserSarnakOctagonReductionImage p) (FreeGroup.mk w) := by
  induction w with
  | nil => simp [positiveOctagonExpansion, positiveOctagonEval]
  | cons xb w ih =>
      rcases xb with ⟨x, b⟩
      cases b
      · rw [show positiveOctagonExpansion p ((x, false) :: w) =
          List.replicate (Nat.card (BuserSarnakReductionRange p) - 1) x ++
            positiveOctagonExpansion p w by simp [positiveOctagonExpansion]]
        rw [positiveOctagonEval_append, ih]
        rw [ReidemeisterSchreier.Discrete.SchreierRewriting.mk_cons_false,
          map_mul, map_inv, FreeGroup.lift_apply_of]
        simp [positiveOctagonEval]
        exact pow_natCard_sub_one_eq_inv_of_finite _
      · rw [show positiveOctagonExpansion p ((x, true) :: w) =
          [x] ++ positiveOctagonExpansion p w by simp [positiveOctagonExpansion]]
        rw [positiveOctagonEval_append, positiveOctagonEval_singleton, ih]
        rw [ReidemeisterSchreier.Discrete.SchreierRewriting.mk_cons_true,
          map_mul, FreeGroup.lift_apply_of]

theorem exists_positiveOctagonWord (p : ℕ) [NeZero p] (q : BuserSarnakReductionRange p) :
    ∃ xs : List OctagonPresentationGenerator,
      positiveOctagonEval p xs = q := by
  obtain ⟨w, hw⟩ := buserSarnakOctagonReductionMap_surjective p q
  refine ⟨positiveOctagonExpansion p w.toWord, ?_⟩
  rw [positiveOctagonEval_positiveOctagonExpansion]
  rw [FreeGroup.mk_toWord]
  exact hw

def HasPositiveOctagonWordLength (p : ℕ) [NeZero p]
    (q : BuserSarnakReductionRange p) (n : ℕ) : Prop :=
  ∃ xs : List OctagonPresentationGenerator,
    xs.length = n ∧ positiveOctagonEval p xs = q

noncomputable local instance hasPositiveOctagonWordLengthDecidable
    (p : ℕ) [NeZero p] (q : BuserSarnakReductionRange p) :
    DecidablePred (HasPositiveOctagonWordLength p q) :=
  Classical.decPred _

theorem exists_positiveOctagonWordLength (p : ℕ) [NeZero p]
    (q : BuserSarnakReductionRange p) :
    ∃ n, HasPositiveOctagonWordLength p q n := by
  obtain ⟨xs, hxs⟩ := exists_positiveOctagonWord p q
  exact ⟨xs.length, xs, rfl, hxs⟩

noncomputable def positiveOctagonDistance (p : ℕ) [NeZero p]
    (q : BuserSarnakReductionRange p) : ℕ :=
  Nat.find (exists_positiveOctagonWordLength p q)

theorem positiveOctagonDistance_spec (p : ℕ) [NeZero p]
    (q : BuserSarnakReductionRange p) :
    HasPositiveOctagonWordLength p q (positiveOctagonDistance p q) :=
  Nat.find_spec (exists_positiveOctagonWordLength p q)

theorem positiveOctagonDistance_le_length (p : ℕ) [NeZero p]
    {q : BuserSarnakReductionRange p} {xs : List OctagonPresentationGenerator}
    (hxs : positiveOctagonEval p xs = q) :
    positiveOctagonDistance p q ≤ xs.length :=
  Nat.find_min' (exists_positiveOctagonWordLength p q)
    ⟨xs, rfl, hxs⟩

@[simp] theorem positiveOctagonDistance_one (p : ℕ) [NeZero p] :
    positiveOctagonDistance p (1 : BuserSarnakReductionRange p) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact positiveOctagonDistance_le_length p
    (xs := []) (q := 1) (by simp)

theorem positiveOctagonDistance_pos_of_ne_one (p : ℕ) [NeZero p]
    {q : BuserSarnakReductionRange p} (hq : q ≠ 1) :
    0 < positiveOctagonDistance p q := by
  apply Nat.pos_of_ne_zero
  intro hzero
  obtain ⟨xs, hlen, heval⟩ := positiveOctagonDistance_spec p q
  rw [hzero] at hlen
  have : xs = [] := List.eq_nil_of_length_eq_zero hlen
  subst xs
  exact hq (by simpa using heval.symm)

theorem exists_positiveOctagonPredecessor (p : ℕ) [NeZero p]
    {q : BuserSarnakReductionRange p} (hq : q ≠ 1) :
    ∃ r : BuserSarnakReductionRange p, ∃ x : OctagonPresentationGenerator,
      r * buserSarnakOctagonReductionImage p x = q ∧
        positiveOctagonDistance p r < positiveOctagonDistance p q := by
  obtain ⟨xs, hlen, heval⟩ := positiveOctagonDistance_spec p q
  have hxs : xs ≠ [] := by
    intro hnil
    subst xs
    exact hq (by simpa using heval.symm)
  let ys := xs.dropLast
  let x := xs.getLast hxs
  let r := positiveOctagonEval p ys
  refine ⟨r, x, ?_, ?_⟩
  · calc
      r * buserSarnakOctagonReductionImage p x =
          positiveOctagonEval p (ys ++ [x]) := by
            rw [positiveOctagonEval_append,
              positiveOctagonEval_singleton]
      _ = positiveOctagonEval p xs := by
        rw [List.dropLast_append_getLast hxs]
      _ = q := heval
  · calc
      positiveOctagonDistance p r ≤ ys.length :=
        positiveOctagonDistance_le_length p rfl
      _ = positiveOctagonDistance p q - 1 := by
        simp only [ys, List.length_dropLast, hlen]
      _ < positiveOctagonDistance p q := by
        exact Nat.sub_lt (positiveOctagonDistance_pos_of_ne_one p hq)
          (by omega)

noncomputable def positiveOctagonPredecessor (p : ℕ) [NeZero p]
    (q : BuserSarnakReductionRange p) (hq : q ≠ 1) :
    BuserSarnakReductionRange p × OctagonPresentationGenerator :=
  let h := exists_positiveOctagonPredecessor p hq
  ⟨h.choose, h.choose_spec.choose⟩

theorem positiveOctagonPredecessor_mul (p : ℕ) [NeZero p]
    (q : BuserSarnakReductionRange p) (hq : q ≠ 1) :
    (positiveOctagonPredecessor p q hq).1 *
        buserSarnakOctagonReductionImage p
          (positiveOctagonPredecessor p q hq).2 = q :=
  (exists_positiveOctagonPredecessor p hq).choose_spec.choose_spec.1

theorem positiveOctagonPredecessor_distance_lt (p : ℕ) [NeZero p]
    (q : BuserSarnakReductionRange p) (hq : q ≠ 1) :
    positiveOctagonDistance p (positiveOctagonPredecessor p q hq).1 <
      positiveOctagonDistance p q :=
  (exists_positiveOctagonPredecessor p hq).choose_spec.choose_spec.2

noncomputable def canonicalPositiveOctagonWord (p : ℕ) [NeZero p]
    (q : BuserSarnakReductionRange p) : List OctagonPresentationGenerator :=
  if hq : q = 1 then []
  else
    canonicalPositiveOctagonWord p (positiveOctagonPredecessor p q hq).1 ++
      [(positiveOctagonPredecessor p q hq).2]
termination_by positiveOctagonDistance p q
decreasing_by exact positiveOctagonPredecessor_distance_lt p q hq

theorem positiveOctagonEval_canonicalPositiveOctagonWord
    (p : ℕ) [NeZero p] (q : BuserSarnakReductionRange p) :
    positiveOctagonEval p (canonicalPositiveOctagonWord p q) = q := by
  induction q using (measure (positiveOctagonDistance p)).wf.induction with
  | h q ih =>
      rw [canonicalPositiveOctagonWord]
      split_ifs with hq
      · simp [hq]
      · rw [positiveOctagonEval_append, positiveOctagonEval_singleton,
          ih (positiveOctagonPredecessor p q hq).1
            (positiveOctagonPredecessor_distance_lt p q hq),
          positiveOctagonPredecessor_mul]

theorem canonicalPositiveOctagonWord_prefixState
    (p : ℕ) [NeZero p] (q : BuserSarnakReductionRange p)
    (acc rest : List OctagonPresentationGenerator)
    (hcat : acc ++ rest = canonicalPositiveOctagonWord p q) :
    canonicalPositiveOctagonWord p (positiveOctagonEval p acc) = acc := by
  induction q using (measure (positiveOctagonDistance p)).wf.induction generalizing acc rest with
  | h q ih =>
      rw [canonicalPositiveOctagonWord] at hcat
      split_ifs at hcat with hq
      · have hacc : acc = [] := (List.append_eq_nil_iff.mp hcat).1
        subst acc
        simp [canonicalPositiveOctagonWord]
      · let r := (positiveOctagonPredecessor p q hq).1
        let x := (positiveOctagonPredecessor p q hq).2
        have hpref : acc <+: canonicalPositiveOctagonWord p r ++ [x] :=
          ⟨rest, hcat⟩
        rw [List.prefix_concat_iff] at hpref
        rcases hpref with hfull | hpre
        · subst acc
          have heval : positiveOctagonEval p
              (canonicalPositiveOctagonWord p r ++ [x]) = q := by
            rw [positiveOctagonEval_append, positiveOctagonEval_singleton,
              positiveOctagonEval_canonicalPositiveOctagonWord,
              positiveOctagonPredecessor_mul]
          rw [heval, canonicalPositiveOctagonWord]
          simp [hq, r, x]
        · rcases hpre with ⟨tail, htail⟩
          exact ih r (positiveOctagonPredecessor_distance_lt p q hq)
            acc tail htail

def positiveSignedOctagonWord
    (xs : List OctagonPresentationGenerator) :
    List (OctagonPresentationGenerator × Bool) :=
  xs.map fun x => (x, true)

lemma buserSarnakOctagonReductionMap_mk_positiveSignedOctagonWord
    (p : ℕ) [NeZero p] (xs : List OctagonPresentationGenerator) :
    buserSarnakOctagonReductionMap p
        (FreeGroup.mk (positiveSignedOctagonWord xs)) =
      positiveOctagonEval p xs := by
  rw [buserSarnakOctagonReductionMap]
  rw [FreeGroup.lift_mk]
  simp only [positiveSignedOctagonWord, List.map_map]
  change (xs.map (buserSarnakOctagonReductionImage p)).prod =
    positiveOctagonEval p xs
  rfl

/-- The canonical shortest-predecessor tree supplies the prefix-closed
positive quotient section uniformly at every nonzero level. -/
noncomputable def canonicalBuserSarnakOctagonQuotientSectionData
    (p : ℕ) [NeZero p] :
    BuserSarnakOctagonQuotientSectionData p where
  quotientSectionWord q :=
    positiveSignedOctagonWord (canonicalPositiveOctagonWord p q)
  quotientMap_mk_quotientSectionWord q := by
    rw [buserSarnakOctagonReductionMap_mk_positiveSignedOctagonWord,
      positiveOctagonEval_canonicalPositiveOctagonWord]
  quotientSectionWord_positive := by
    intro q xb hxb
    rcases List.mem_map.mp hxb with ⟨x, _, rfl⟩
    rfl
  prefixState := by
    intro q acc rest hcat
    let word := canonicalPositiveOctagonWord p q
    let n := acc.length
    let accX := word.take n
    have hacc : acc = positiveSignedOctagonWord accX := by
      calc
        acc = (acc ++ rest).take n := by simp [n]
        _ = (positiveSignedOctagonWord word).take n := by rw [hcat]
        _ = positiveSignedOctagonWord accX := by
          simp [positiveSignedOctagonWord, accX, n]
    have hprefix : accX ++ word.drop n = word := by
      exact List.take_append_drop n word
    have hcanonical :
        canonicalPositiveOctagonWord p (positiveOctagonEval p accX) = accX :=
      canonicalPositiveOctagonWord_prefixState p q accX (word.drop n) hprefix
    have heval :
        buserSarnakOctagonReductionMap p (FreeGroup.mk acc) =
          positiveOctagonEval p accX := by
      rw [hacc, buserSarnakOctagonReductionMap_mk_positiveSignedOctagonWord]
    rw [heval, hcanonical, ← hacc]

noncomputable local instance buserSarnakDegenerateSchreierSymbolDecidable
    {p : ℕ} [NeZero p]
    {S : BuserSarnakOctagonQuotientSectionData p} :
    DecidablePred
      S.schreierData.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol :=
  Classical.decPred _

/-! ## Size of the canonical cleaned presentation -/

abbrev Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakSection (p : ℕ) [NeZero p] :=
  canonicalBuserSarnakOctagonQuotientSectionData p

abbrev Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData
    (p : ℕ) [NeZero p] :=
  (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakSection p).schreierData.toFiniteQuotientSchreierData

/-- In the canonical Schreier graph, an edge is right multiplication by the
corresponding reduced octagon generator. -/
@[simp] lemma canonicalBuserSarnak_transition_eq_mul
    (p : ℕ) [NeZero p] (q : BuserSarnakReductionRange p)
    (x : OctagonPresentationGenerator) :
    (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).transition q x =
      q * buserSarnakOctagonReductionImage p x := by
  rw [FiniteQuotientSchreierData.transition_eq]
  rw [BuserSarnakOctagonQuotientSectionData.schreierData_quotientMap]
  exact congrArg (q * ·) FreeGroup.lift_apply_of

/-- A central Schreier edge flips to the paired quotient state. -/
@[simp] theorem canonicalBuserSarnak_transition_z
    (p : ℕ) [NeZero p] (q : BuserSarnakReductionRange p) :
    (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).transition q .z =
      buserSarnakCentralPartner p q := by
  rw [canonicalBuserSarnak_transition_eq_mul]
  rfl

/-- Two consecutive edges with the same cone label connect a state to its
central partner.  Thus every cone relation runs across one quotient-state
pair, uniformly in the prime. -/
theorem canonicalBuserSarnak_transition_cone_twice
    (p : ℕ) [NeZero p] (q : BuserSarnakReductionRange p)
    (e : OctagonPresentationGenerator)
    (he : e = .e1 ∨ e = .e2 ∨ e = .e3 ∨ e = .e4) :
    (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).transition
        ((Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).transition q e) e =
      buserSarnakCentralPartner p q := by
  rw [canonicalBuserSarnak_transition_eq_mul,
    canonicalBuserSarnak_transition_eq_mul]
  exact buserSarnak_mul_cone_mul_cone p q e he

/-- A degenerate symbol in the canonical tree appends exactly one positive
letter to the representative of its source state. -/
lemma canonicalBuserSarnak_isDegenerate_word
    {p : ℕ} [NeZero p]
    {q : BuserSarnakReductionRange p}
    {x : OctagonPresentationGenerator}
    (h : (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p)
      |>.IsDegenerateSchreierSymbol (q, x)) :
    positiveSignedOctagonWord
        (canonicalPositiveOctagonWord p
          ((Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).transition q x)) =
      positiveSignedOctagonWord (canonicalPositiveOctagonWord p q) ++
        [(x, true)] := by
  have h' :
      FreeGroup.mk (positiveSignedOctagonWord
          (canonicalPositiveOctagonWord p
            ((Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).transition q x))) =
        FreeGroup.mk
          (positiveSignedOctagonWord (canonicalPositiveOctagonWord p q) ++
            [(x, true)]) := by
    rw [← FreeGroup.mul_mk]
    exact h
  have hw := congrArg FreeGroup.toWord h'
  have hl : FreeGroup.reduce
      (positiveSignedOctagonWord
        (canonicalPositiveOctagonWord p
          ((Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).transition q x))) =
      positiveSignedOctagonWord
        (canonicalPositiveOctagonWord p
          ((Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).transition q x)) := by
    apply FiniteQuotientSchreierData.reduce_eq_of_forall_snd_eq_true
    intro xb hxb
    rcases List.mem_map.mp hxb with ⟨y, _, rfl⟩
    rfl
  have hr : FreeGroup.reduce
      (positiveSignedOctagonWord (canonicalPositiveOctagonWord p q) ++
        [(x, true)]) =
      positiveSignedOctagonWord (canonicalPositiveOctagonWord p q) ++
        [(x, true)] := by
    apply FiniteQuotientSchreierData.reduce_eq_of_forall_snd_eq_true
    intro xb hxb
    rcases List.mem_append.mp hxb with hxb | hxb
    · rcases List.mem_map.mp hxb with ⟨y, _, rfl⟩
      rfl
    · simp only [List.mem_singleton] at hxb
      subst xb
      rfl
  rw [FreeGroup.toWord_mk, FreeGroup.toWord_mk, hl, hr] at hw
  exact hw

/-- Every degenerate tree edge has a nonidentity endpoint. -/
lemma canonicalBuserSarnak_transition_ne_one_of_isDegenerate
    {p : ℕ} [NeZero p]
    {q : BuserSarnakReductionRange p}
    {x : OctagonPresentationGenerator}
    (h : (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p)
      |>.IsDegenerateSchreierSymbol (q, x)) :
    (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).transition q x ≠ 1 := by
  intro htransition
  have hw := canonicalBuserSarnak_isDegenerate_word h
  rw [htransition] at hw
  have hone : canonicalPositiveOctagonWord p
      (1 : BuserSarnakReductionRange p) = [] := by
    rw [canonicalPositiveOctagonWord]
    simp
  rw [hone] at hw
  simp [positiveSignedOctagonWord] at hw

/-- The degenerate symbols deleted from the canonical Schreier presentation. -/
abbrev CanonicalBuserSarnakDegenerateSymbol
    (p : ℕ) [NeZero p] :=
  {z : FiniteQuotientSchreierData.FiniteSchreierSymbol
      OctagonPresentationGenerator (BuserSarnakReductionRange p) //
    (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p)
      |>.IsDegenerateSchreierSymbol z}

/-- Send a canonical tree edge to its endpoint. -/
def canonicalBuserSarnakDegenerateTarget (p : ℕ) [NeZero p]
    (z : CanonicalBuserSarnakDegenerateSymbol p) :
    {q : BuserSarnakReductionRange p // q ≠ 1} :=
  ⟨(Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).transition z.1.1 z.1.2,
    canonicalBuserSarnak_transition_ne_one_of_isDegenerate z.2⟩

lemma canonicalBuserSarnak_transition_predecessor
    (p : ℕ) [NeZero p] (q : BuserSarnakReductionRange p) (hq : q ≠ 1) :
    (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).transition
        (positiveOctagonPredecessor p q hq).1
        (positiveOctagonPredecessor p q hq).2 = q := by
  rw [FiniteQuotientSchreierData.transition_eq]
  rw [BuserSarnakOctagonQuotientSectionData.schreierData_quotientMap]
  change
    (positiveOctagonPredecessor p q hq).1 *
        buserSarnakOctagonReductionMap p
          (FreeGroup.of (positiveOctagonPredecessor p q hq).2) = q
  rw [show buserSarnakOctagonReductionMap p
      (FreeGroup.of (positiveOctagonPredecessor p q hq).2) =
        buserSarnakOctagonReductionImage p
          (positiveOctagonPredecessor p q hq).2 by
    exact FreeGroup.lift_apply_of]
  exact positiveOctagonPredecessor_mul p q hq

lemma canonicalBuserSarnak_predecessor_isDegenerate
    (p : ℕ) [NeZero p] (q : BuserSarnakReductionRange p) (hq : q ≠ 1) :
    (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p)
      |>.IsDegenerateSchreierSymbol
        ((positiveOctagonPredecessor p q hq).1,
          (positiveOctagonPredecessor p q hq).2) := by
  rw [FiniteQuotientSchreierData.IsDegenerateSchreierSymbol,
    canonicalBuserSarnak_transition_predecessor p q hq]
  change
    FreeGroup.mk (positiveSignedOctagonWord
        (canonicalPositiveOctagonWord p q)) =
      FreeGroup.mk (positiveSignedOctagonWord
          (canonicalPositiveOctagonWord p
            (positiveOctagonPredecessor p q hq).1)) *
        FreeGroup.of (positiveOctagonPredecessor p q hq).2
  rw [canonicalPositiveOctagonWord]
  simp only [hq, ↓reduceDIte, positiveSignedOctagonWord, List.map_append,
    List.map_singleton]
  rw [← FreeGroup.mul_mk]
  change
    FreeGroup.mk
        (List.map (fun x : OctagonPresentationGenerator => (x, true))
          (canonicalPositiveOctagonWord p
            (positiveOctagonPredecessor p q hq).1)) *
          FreeGroup.mk [((positiveOctagonPredecessor p q hq).2, true)] =
      FreeGroup.mk
          (List.map (fun x : OctagonPresentationGenerator => (x, true))
            (canonicalPositiveOctagonWord p
              (positiveOctagonPredecessor p q hq).1)) *
        FreeGroup.mk [((positiveOctagonPredecessor p q hq).2, true)]
  rfl

/-- The last edge in the canonical word for a nonidentity state. -/
def canonicalBuserSarnakDegenerateSource (p : ℕ) [NeZero p]
    (q : {q : BuserSarnakReductionRange p // q ≠ 1}) :
    CanonicalBuserSarnakDegenerateSymbol p :=
  ⟨((positiveOctagonPredecessor p q.1 q.2).1,
      (positiveOctagonPredecessor p q.1 q.2).2),
    canonicalBuserSarnak_predecessor_isDegenerate p q.1 q.2⟩

@[simp] lemma canonicalBuserSarnakDegenerateTarget_source
    (p : ℕ) [NeZero p]
    (q : {q : BuserSarnakReductionRange p // q ≠ 1}) :
    canonicalBuserSarnakDegenerateTarget p
        (canonicalBuserSarnakDegenerateSource p q) = q := by
  apply Subtype.ext
  exact canonicalBuserSarnak_transition_predecessor p q.1 q.2

/-- Distinct canonical tree edges have distinct endpoints. -/
lemma canonicalBuserSarnakDegenerateTarget_injective
    (p : ℕ) [NeZero p] :
    Function.Injective (canonicalBuserSarnakDegenerateTarget p) := by
  intro z w htarget
  have htransition :
      (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).transition z.1.1 z.1.2 =
        (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).transition w.1.1 w.1.2 :=
    congrArg Subtype.val htarget
  have hz := canonicalBuserSarnak_isDegenerate_word z.2
  have hw := canonicalBuserSarnak_isDegenerate_word w.2
  rw [htransition] at hz
  have hfull := hz.symm.trans hw
  have hlen :
      (positiveSignedOctagonWord
        (canonicalPositiveOctagonWord p z.1.1)).length =
      (positiveSignedOctagonWord
        (canonicalPositiveOctagonWord p w.1.1)).length := by
    have hlenPlus :
        (positiveSignedOctagonWord
          (canonicalPositiveOctagonWord p z.1.1)).length + 1 =
        (positiveSignedOctagonWord
          (canonicalPositiveOctagonWord p w.1.1)).length + 1 := by
      simpa only [List.length_append, List.length_singleton] using
        congrArg List.length hfull
    exact Nat.add_right_cancel hlenPlus
  have hparts := List.append_inj hfull hlen
  have hword : canonicalPositiveOctagonWord p z.1.1 =
      canonicalPositiveOctagonWord p w.1.1 := by
    have hpair : Function.Injective
        (fun x : OctagonPresentationGenerator => (x, true)) := by
      intro x y hxy
      exact congrArg Prod.fst hxy
    exact hpair.list_map hparts.1
  have hstate : z.1.1 = w.1.1 := by
    have heval := congrArg (positiveOctagonEval p) hword
    simpa [positiveOctagonEval_canonicalPositiveOctagonWord] using heval
  have hgenerator : z.1.2 = w.1.2 :=
    congrArg Prod.fst (List.singleton_injective hparts.2)
  apply Subtype.ext
  exact Prod.ext hstate hgenerator

/-- Canonical degenerate symbols are exactly the nonroot edges of the
shortest-predecessor tree. -/
def canonicalBuserSarnakDegenerateEquivNonidentity
    (p : ℕ) [NeZero p] :
    CanonicalBuserSarnakDegenerateSymbol p ≃
      {q : BuserSarnakReductionRange p // q ≠ 1} :=
  Equiv.ofBijective (canonicalBuserSarnakDegenerateTarget p)
    ⟨canonicalBuserSarnakDegenerateTarget_injective p,
      fun q => ⟨canonicalBuserSarnakDegenerateSource p q,
        canonicalBuserSarnakDegenerateTarget_source p q⟩⟩

/-- A finite rooted tree on the reduction range has one deleted Schreier
symbol for every nonidentity quotient state. -/
theorem card_canonicalBuserSarnakDegenerateSymbol
    (p : ℕ) [NeZero p] :
    Fintype.card (CanonicalBuserSarnakDegenerateSymbol p) =
      Fintype.card (BuserSarnakReductionRange p) - 1 := by
  rw [Fintype.card_congr
    (canonicalBuserSarnakDegenerateEquivNonidentity p)]
  calc
    Fintype.card {q : BuserSarnakReductionRange p // q ≠ 1} =
        Fintype.card (BuserSarnakReductionRange p) -
          Fintype.card {q : BuserSarnakReductionRange p // q = 1} := by
      exact Fintype.card_subtype_compl
        (fun q : BuserSarnakReductionRange p => q = 1)
    _ = Fintype.card (BuserSarnakReductionRange p) - 1 := by
      rw [Fintype.card_subtype_eq]

/-- The nondegenerate generator type in the canonical cleaned presentation. -/
abbrev CanonicalBuserSarnakNondegenerateSymbol
    (p : ℕ) [NeZero p] :=
  (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakSection p).schreierData.nondegenerateSchreierSymbol

noncomputable local instance canonicalBuserSarnakNondegenerateFinite
    (p : ℕ) [NeZero p] :
    Finite (CanonicalBuserSarnakNondegenerateSymbol p) :=
  Finite.of_injective
    (fun z : CanonicalBuserSarnakNondegenerateSymbol p => z.1)
    Subtype.val_injective

noncomputable local instance canonicalBuserSarnakNondegenerateFintype
    (p : ℕ) [NeZero p] :
    Fintype (CanonicalBuserSarnakNondegenerateSymbol p) :=
  Fintype.ofFinite _

noncomputable local instance canonicalBuserSarnakNondegenerateDecidableEq
    (p : ℕ) [NeZero p] :
    DecidableEq (CanonicalBuserSarnakNondegenerateSymbol p) :=
  Classical.decEq _

/-- After deleting the tree edges, the canonical octagon Schreier
presentation has exactly `12 * halfImageIndex + 1` generators. -/
theorem card_canonicalBuserSarnakNondegenerateSymbol
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p) :
    Fintype.card (CanonicalBuserSarnakNondegenerateSymbol p) =
      12 * data.halfImageIndex + 1 := by
  have hqcard : Fintype.card (BuserSarnakReductionRange p) =
      2 * data.halfImageIndex := by
    have himage := data.image_card_eq
    rw [Nat.card_eq_fintype_card] at himage
    exact himage
  have hxcard : Fintype.card OctagonPresentationGenerator = 7 := by
    decide
  have htotal :
      Fintype.card
          (FiniteQuotientSchreierData.FiniteSchreierSymbol
            OctagonPresentationGenerator (BuserSarnakReductionRange p)) =
        14 * data.halfImageIndex := by
    simp only [FiniteQuotientSchreierData.FiniteSchreierSymbol,
      Fintype.card_prod, hqcard, hxcard]
    ring
  have hdeg := card_canonicalBuserSarnakDegenerateSymbol p
  have hsplit :
      Fintype.card (CanonicalBuserSarnakNondegenerateSymbol p) =
        Fintype.card
            (FiniteQuotientSchreierData.FiniteSchreierSymbol
              OctagonPresentationGenerator (BuserSarnakReductionRange p)) -
          Fintype.card (CanonicalBuserSarnakDegenerateSymbol p) := by
    have hsplitNat :
        Nat.card (CanonicalBuserSarnakNondegenerateSymbol p) =
          Nat.card
              (FiniteQuotientSchreierData.FiniteSchreierSymbol
                OctagonPresentationGenerator (BuserSarnakReductionRange p)) -
            Nat.card (CanonicalBuserSarnakDegenerateSymbol p) := by
      change
        Nat.card {z : FiniteQuotientSchreierData.FiniteSchreierSymbol
            OctagonPresentationGenerator (BuserSarnakReductionRange p) //
          ¬((Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p)
            |>.IsDegenerateSchreierSymbol z)} =
        Nat.card
            (FiniteQuotientSchreierData.FiniteSchreierSymbol
              OctagonPresentationGenerator (BuserSarnakReductionRange p)) -
          Nat.card {z : FiniteQuotientSchreierData.FiniteSchreierSymbol
              OctagonPresentationGenerator (BuserSarnakReductionRange p) //
            (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p)
              |>.IsDegenerateSchreierSymbol z}
      simpa only [← Nat.card_eq_fintype_card] using
        Fintype.card_subtype_compl
          ((Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p)
            |>.IsDegenerateSchreierSymbol)
    simpa only [Nat.card_eq_fintype_card] using hsplitNat
  rw [hsplit, htotal, hdeg, hqcard]
  have hqpos : 0 < Fintype.card (BuserSarnakReductionRange p) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  omega

/-- The cleaned octagon presentation has enough generators to contain a
literal copy of the standard surface-generator type. -/
theorem card_surfaceGenerator_le_canonicalBuserSarnakNondegenerate
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p) :
    Fintype.card (SurfaceGenerator (data.halfImageIndex + 1)) ≤
      Fintype.card (CanonicalBuserSarnakNondegenerateSymbol p) := by
  rw [card_canonicalBuserSarnakNondegenerateSymbol data]
  simp only [SurfaceGenerator, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  have hqcard : Fintype.card (BuserSarnakReductionRange p) =
      2 * data.halfImageIndex := by
    have himage := data.image_card_eq
    rw [Nat.card_eq_fintype_card] at himage
    exact himage
  have hqpos : 0 < Fintype.card (BuserSarnakReductionRange p) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  omega

/-- There is room to choose distinct cleaned Schreier representatives for all
standard surface generators. This is only an embedding: the remaining
Schreier symbols still require genuine word-level Tietze eliminations. -/
theorem nonempty_surfaceGenerator_embedding_canonicalBuserSarnakNondegenerate
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p) :
    Nonempty
      (SurfaceGenerator (data.halfImageIndex + 1) ↪
        CanonicalBuserSarnakNondegenerateSymbol p) :=
  Function.Embedding.nonempty_of_card_le
    (card_surfaceGenerator_le_canonicalBuserSarnakNondegenerate data)

/-- Passing from cleaned Schreier generators to standard surface generators
must eliminate exactly `10 * halfImageIndex - 1` additional generators. -/
theorem card_canonicalBuserSarnakNondegenerate_eq_surface_add_excess
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p) :
    Fintype.card (CanonicalBuserSarnakNondegenerateSymbol p) =
      Fintype.card (SurfaceGenerator (data.halfImageIndex + 1)) +
        (10 * data.halfImageIndex - 1) := by
  rw [card_canonicalBuserSarnakNondegenerateSymbol data]
  simp only [SurfaceGenerator, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  have hqcard : Fintype.card (BuserSarnakReductionRange p) =
      2 * data.halfImageIndex := by
    have himage := data.image_card_eq
    rw [Nat.card_eq_fintype_card] at himage
    exact himage
  have hqpos : 0 < Fintype.card (BuserSarnakReductionRange p) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  omega

/-- The cleaned and surface generator types cannot be related by a direct
relabeling. Any target-presentation map must perform nontrivial word
substitutions eliminating the extra Schreier generators. -/
theorem no_direct_canonicalBuserSarnak_surfaceGenerator_relabeling
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p) :
    ¬ Nonempty
      (CanonicalBuserSarnakNondegenerateSymbol p ≃
        SurfaceGenerator (data.halfImageIndex + 1)) := by
  rintro ⟨e⟩
  have hcard := Fintype.card_congr e
  rw [card_canonicalBuserSarnakNondegenerateSymbol data] at hcard
  simp only [SurfaceGenerator, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool] at hcard
  have hqcard : Fintype.card (BuserSarnakReductionRange p) =
      2 * data.halfImageIndex := by
    have himage := data.image_card_eq
    rw [Nat.card_eq_fintype_card] at himage
    exact himage
  have hqpos : 0 < Fintype.card (BuserSarnakReductionRange p) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  omega

/-- The exact Tietze data still required to identify the cleaned octagon
kernel presentation with the standard surface presentation.  The target
relator is fixed, so no arbitrary presentation can be smuggled into the
certificate. -/
structure BuserSarnakLevelTargetPresentationData
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p)
    (S : BuserSarnakOctagonQuotientSectionData p) where
  toTargetGenerator :
    S.schreierData.nondegenerateSchreierSymbol →
      FreeGroup (SurfaceGenerator (data.halfImageIndex + 1))
  fromTargetGenerator :
    SurfaceGenerator (data.halfImageIndex + 1) →
      FreeGroup S.schreierData.nondegenerateSchreierSymbol
  mapsCleanedRelators :
    ∀ q : BuserSarnakReductionRange p,
      ∀ r : OctagonPresentationRelator,
        RelatorEquivalent
          ({surfaceRelator (data.halfImageIndex + 1)} :
            Set (FreeGroup
              (SurfaceGenerator (data.halfImageIndex + 1))))
          (FreeGroup.lift toTargetGenerator
            (S.schreierData.cleanedTau q
              (octagonPresentationRelator r))) 1
  mapsSurfaceRelator :
    RelatorEquivalent
      (S.schreierData.cleanedSchreierRelators
        octagonPresentationRelators)
      (FreeGroup.lift fromTargetGenerator
        (surfaceRelator (data.halfImageIndex + 1))) 1
  from_toTargetGenerator :
    ∀ z : S.schreierData.nondegenerateSchreierSymbol,
      RelatorEquivalent
        (S.schreierData.cleanedSchreierRelators
          octagonPresentationRelators)
        (FreeGroup.lift fromTargetGenerator (toTargetGenerator z))
        (FreeGroup.of z)
  to_fromTargetGenerator :
    ∀ y : SurfaceGenerator (data.halfImageIndex + 1),
      RelatorEquivalent
        ({surfaceRelator (data.halfImageIndex + 1)} :
          Set (FreeGroup
            (SurfaceGenerator (data.halfImageIndex + 1))))
        (FreeGroup.lift toTargetGenerator (fromTargetGenerator y))
        (FreeGroup.of y)

/-- There are exactly `16 * halfImageIndex` constructor-indexed cleaned
relator obligations: eight base relators for each of the `2 * halfImageIndex`
finite quotient states. -/
theorem card_buserSarnakLevelCleanedRelatorIndex
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p) :
    Nat.card (BuserSarnakReductionRange p × OctagonPresentationRelator) =
      16 * data.halfImageIndex := by
  rw [Nat.card_prod, data.image_card_eq]
  have hrel : Nat.card OctagonPresentationRelator = 8 := by
    rw [Nat.card_eq_fintype_card]
    exact card_octagonPresentationRelator
  rw [hrel]
  ring

/-! ## A finite normal-word table for Tietze elimination

The next definitions expose the cleaned presentation as concrete reduced
words.  Thus a prospective sequence of generator pivots can inspect a finite
table rather than reason about membership in an existentially defined set.
-/

/-- The finite index type for all canonical cleaned relator words. -/
abbrev CanonicalBuserSarnakCleanedRelatorIndex
    (p : ℕ) [NeZero p] :=
  BuserSarnakReductionRange p × OctagonPresentationRelator

/-- The reduced word of the cleaned rewrite attached to a quotient state and
one of the eight octagon relators. -/
noncomputable def canonicalBuserSarnakCleanedRelatorNormalWord
    (p : ℕ) [NeZero p]
    (i : CanonicalBuserSarnakCleanedRelatorIndex p) :
    List (CanonicalBuserSarnakNondegenerateSymbol p × Bool) :=
  (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).cleanedTauNormalWord
    i.1 (octagonPresentationRelator i.2)

/-- Each entry of the finite normal-word table reconstructs its canonical
cleaned Reidemeister--Schreier relator. -/
theorem mk_canonicalBuserSarnakCleanedRelatorNormalWord
    (p : ℕ) [NeZero p]
    (i : CanonicalBuserSarnakCleanedRelatorIndex p) :
    FreeGroup.mk (canonicalBuserSarnakCleanedRelatorNormalWord p i) =
      (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).cleanedTau i.1
        (octagonPresentationRelator i.2) := by
  exact (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).mk_cleanedTauNormalWord
    i.1 (octagonPresentationRelator i.2)

private lemma norm_cleanedSchreierSymbolWord_le_one
    {X Q : Type*} [Group Q] [Fintype Q]
    (D : FiniteQuotientSchreierData X Q)
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    (z : FiniteQuotientSchreierData.FiniteSchreierSymbol X Q) :
    FreeGroup.norm (D.cleanedSchreierSymbolWord z) ≤ 1 := by
  by_cases hz : D.IsDegenerateSchreierSymbol z
  · rw [D.cleanedSchreierSymbolWord_of_degenerate hz]
    simp
  · unfold FiniteQuotientSchreierData.cleanedSchreierSymbolWord
    simp only [hz, dite_false]
    exact le_rfl

private lemma norm_cleanedTauList_le_length
    {X Q : Type*} [Group Q] [Fintype Q] [DecidableEq X]
    (D : FiniteQuotientSchreierData X Q)
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool)) :
    FreeGroup.norm (D.cleanedTauList q xs) ≤ xs.length := by
  induction xs generalizing q with
  | nil => simp
  | cons xb xs ih =>
      rcases xb with ⟨x, b⟩
      cases b
      · rw [D.cleanedTauList_cons_false]
        calc
          FreeGroup.norm
              ((D.cleanedSchreierSymbolWord (D.inverseTransition q x, x))⁻¹ *
                D.cleanedTauList (D.inverseTransition q x) xs) ≤
              FreeGroup.norm
                  (D.cleanedSchreierSymbolWord (D.inverseTransition q x, x))⁻¹ +
                FreeGroup.norm (D.cleanedTauList (D.inverseTransition q x) xs) :=
            FreeGroup.norm_mul_le _ _
          _ ≤ 1 + xs.length := Nat.add_le_add
            (by
              rw [FreeGroup.norm_inv_eq]
              exact norm_cleanedSchreierSymbolWord_le_one D _)
            (ih _)
          _ = ((x, false) :: xs).length := by
            change 1 + xs.length = xs.length + 1
            exact Nat.add_comm _ _
      · rw [D.cleanedTauList_cons_true]
        calc
          FreeGroup.norm
              (D.cleanedSchreierSymbolWord (q, x) *
                D.cleanedTauList (D.transition q x) xs) ≤
              FreeGroup.norm (D.cleanedSchreierSymbolWord (q, x)) +
                FreeGroup.norm (D.cleanedTauList (D.transition q x) xs) :=
            FreeGroup.norm_mul_le _ _
          _ ≤ 1 + xs.length := Nat.add_le_add
            (norm_cleanedSchreierSymbolWord_le_one D _)
            (ih _)
          _ = ((x, true) :: xs).length := by
            change 1 + xs.length = xs.length + 1
            exact Nat.add_comm _ _

private lemma cleanedTauNormalWord_length_le_toWord
    {X Q : Type*} [Group Q] [Fintype Q] [DecidableEq X]
    (D : FiniteQuotientSchreierData X Q)
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    (D.cleanedTauNormalWord q w).length ≤ w.toWord.length := by
  change FreeGroup.norm (D.cleanedTau q w) ≤ w.toWord.length
  rw [D.cleanedTau_eq_cleanedTauList_toWord]
  exact norm_cleanedTauList_le_length D q w.toWord

private lemma octagonPresentationRelator_toWord_length_le_eight
    (r : OctagonPresentationRelator) :
    (octagonPresentationRelator r).toWord.length ≤ 8 := by
  cases r <;> decide

/-- Every canonical cleaned relator is represented by a reduced word of
length at most eight.  Cleaning can delete letters and free reduction can
cancel them, but Schreier rewriting introduces at most one symbol per base
relator letter. -/
theorem canonicalBuserSarnakCleanedRelatorNormalWord_length_le_eight
    (p : ℕ) [NeZero p]
    (i : CanonicalBuserSarnakCleanedRelatorIndex p) :
    (canonicalBuserSarnakCleanedRelatorNormalWord p i).length ≤ 8 := by
  calc
    (canonicalBuserSarnakCleanedRelatorNormalWord p i).length ≤
        (octagonPresentationRelator i.2).toWord.length :=
      cleanedTauNormalWord_length_le_toWord
        (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p)
        i.1 (octagonPresentationRelator i.2)
    _ ≤ 8 := octagonPresentationRelator_toWord_length_le_eight i.2

/-- The finite set of distinct relators represented by the canonical
normal-word table. -/
noncomputable def canonicalBuserSarnakCleanedRelatorFinset
    (p : ℕ) [NeZero p] :
    Finset (FreeGroup (CanonicalBuserSarnakNondegenerateSymbol p)) :=
  Finset.univ.image fun i : CanonicalBuserSarnakCleanedRelatorIndex p =>
    FreeGroup.mk (canonicalBuserSarnakCleanedRelatorNormalWord p i)

/-- The finite normal-word table is exhaustive: its range is exactly the
canonical cleaned relator set. -/
@[simp] theorem mem_canonicalBuserSarnakCleanedRelatorFinset
    (p : ℕ) [NeZero p]
    {w : FreeGroup (CanonicalBuserSarnakNondegenerateSymbol p)} :
    w ∈ canonicalBuserSarnakCleanedRelatorFinset p ↔
      w ∈ (Internal.BuserSarnakLevelMarkingHelpers.canonicalBuserSarnakFiniteSchreierData p).cleanedSchreierRelators
        octagonPresentationRelators := by
  simp only [canonicalBuserSarnakCleanedRelatorFinset,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    rw [mk_canonicalBuserSarnakCleanedRelatorNormalWord]
    exact ⟨i.1, octagonPresentationRelator i.2, ⟨i.2, rfl⟩, rfl⟩
  · rintro ⟨q, r, ⟨j, rfl⟩, rfl⟩
    exact ⟨(q, j), mk_canonicalBuserSarnakCleanedRelatorNormalWord p (q, j)⟩

/-- There are at most `16 * halfImageIndex` distinct cleaned relators.  Any
uniform elimination certificate can therefore be checked by a finite scan of
the displayed normal-word table. -/
theorem card_canonicalBuserSarnakCleanedRelatorFinset_le
    {p : ℕ} [NeZero p] (data : BuserSarnakCorrectionData p) :
    (canonicalBuserSarnakCleanedRelatorFinset p).card ≤
      16 * data.halfImageIndex := by
  calc
    (canonicalBuserSarnakCleanedRelatorFinset p).card ≤
        (Finset.univ : Finset
          (CanonicalBuserSarnakCleanedRelatorIndex p)).card :=
      Finset.card_image_le
    _ = Nat.card (CanonicalBuserSarnakCleanedRelatorIndex p) := by
      rw [Nat.card_eq_fintype_card]
      rfl
    _ = 16 * data.halfImageIndex :=
      card_buserSarnakLevelCleanedRelatorIndex data

namespace BuserSarnakLevelTargetPresentationData

/-- Forget the fixed-surface certificate to the generic cleaned target data. -/
def toCleanedTargetPresentationData
    {p : ℕ} [NeZero p] {data : BuserSarnakCorrectionData p}
    {S : BuserSarnakOctagonQuotientSectionData p}
    (C : BuserSarnakLevelTargetPresentationData data S) :
    S.schreierData.CleanedReidemeisterSchreierTargetPresentationData
      octagonPresentationRelators
      (SurfaceGenerator (data.halfImageIndex + 1)) where
  targetRelators :=
    {surfaceRelator (data.halfImageIndex + 1)}
  toTargetGenerator := C.toTargetGenerator
  fromTargetGenerator := C.fromTargetGenerator
  mapsCleanedRelators := by
    intro q r hr
    rcases hr with ⟨i, rfl⟩
    exact C.mapsCleanedRelators q i
  mapsTargetRelators := by
    intro s hs
    rw [Set.mem_singleton_iff.mp hs]
    exact C.mapsSurfaceRelator
  from_toTargetGenerator := C.from_toTargetGenerator
  to_fromTargetGenerator := C.to_fromTargetGenerator

/-- The original octagon relators lie in the specialized free quotient kernel. -/
lemma octagonRelators_le_schreierKernel
    {p : ℕ} [NeZero p]
    (S : BuserSarnakOctagonQuotientSectionData p) :
    Subgroup.normalClosure octagonPresentationRelators ≤
      S.schreierData.kernel := by
  change Subgroup.normalClosure octagonPresentationRelators ≤
    (buserSarnakOctagonReductionMap p).ker
  exact PresentedGroup.closure_rels_subset_ker
    (buserSarnakOctagonReductionImage_relations p)

/-- A completed target-presentation certificate identifies the surface group
with the kernel inside the lifted octagon presentation. -/
noncomputable def surfaceEquivOctagonPresentedKernel
    {p : ℕ} [NeZero p] {data : BuserSarnakCorrectionData p}
    {S : BuserSarnakOctagonQuotientSectionData p}
    (C : BuserSarnakLevelTargetPresentationData data S) :
    SurfaceGroup (data.halfImageIndex + 1) ≃*
      (buserSarnakOctagonReductionPresentedHom p).ker :=
  (C.toCleanedTargetPresentationData.targetPresentedGroupEquivKernel
      (octagonRelators_le_schreierKernel S)).trans
    (presentedFreeKernelRelatorQuotientEquivPresentedKernel
      (buserSarnakOctagonReductionImage_relations p))

/-- Combining a cleaned Reidemeister--Schreier certificate with faithfulness
of the base octagon presentation gives the required principal-level marking. -/
noncomputable def levelGroupMarking
    {p : ℕ} [NeZero p] {data : BuserSarnakCorrectionData p}
    {S : BuserSarnakOctagonQuotientSectionData p}
    (C : BuserSarnakLevelTargetPresentationData data S)
    (hfaith : Function.Injective liftedOctagonToQuaternion) :
    buserSarnakLevelGroup23 p ≃*
      SurfaceGroup (data.halfImageIndex + 1) :=
  (buserSarnakOctagonPresentedKernelEquivLevelGroup23 p hfaith).symm.trans
    C.surfaceEquivOctagonPresentedKernel.symm

end BuserSarnakLevelTargetPresentationData

end
end SystolicGrowth

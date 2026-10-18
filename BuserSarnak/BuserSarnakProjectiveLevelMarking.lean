module

public import BuserSarnak.BuserSarnakProjectiveLevelKernel

@[expose] public section

/-!
# Projective finite level marking data

This is the smaller Reidemeister--Schreier route for the Buser--Sarnak level
kernel.  The projective orbifold has six generators and four order-two cone
generators; its finite quotient has `halfImageIndex` states rather than twice
as many lifted states.
-/

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

/-- Enumeration of the six projective octagon generators. -/
instance instFintypeProjectiveOctagonGenerator :
    Fintype ProjectiveOctagonGenerator :=
  Fintype.ofList [.a, .c, .e1, .e2, .e3, .e4] (by
    intro x
    cases x <;> simp)

/-- Enumeration of the five projective octagon relators. -/
instance instFintypeProjectiveOctagonRelator :
    Fintype ProjectiveOctagonRelator :=
  Fintype.ofList [.e1_sq, .e2_sq, .e3_sq, .e4_sq, .polygon] (by
    intro x
    cases x <;> simp)

@[simp] theorem card_projectiveOctagonGenerator :
    Fintype.card ProjectiveOctagonGenerator = 6 := by
  decide

@[simp] theorem card_projectiveOctagonRelator :
    Fintype.card ProjectiveOctagonRelator = 5 := by
  decide

noncomputable local instance buserSarnakProjectiveReductionRangeFintype
    (p : ℕ) [NeZero p] : Fintype (BuserSarnakProjectiveReductionRange p) :=
  Fintype.ofFinite _

/-- The free projective-generator reduction map. -/
def buserSarnakProjectiveReductionMap (p : ℕ) [NeZero p] :
    FreeGroup ProjectiveOctagonGenerator →*
      BuserSarnakProjectiveReductionRange p :=
  FreeGroup.lift (buserSarnakProjectiveReductionImage p)

/-- The free projective reduction reaches every finite projective state. -/
theorem buserSarnakProjectiveReductionMap_surjective
    (p : ℕ) [NeZero p] :
    Function.Surjective (buserSarnakProjectiveReductionMap p) := by
  intro q
  obtain ⟨x, hx⟩ := buserSarnakProjectiveReductionPresentedHom_surjective p q
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective projectiveOctagonRelators x
  exact ⟨w, hx⟩

/-! ## Canonical positive projective quotient section -/

/-- Evaluate a positive word in the finite projective quotient. -/
def positiveProjectiveEval (p : ℕ) [NeZero p]
    (xs : List ProjectiveOctagonGenerator) :
    BuserSarnakProjectiveReductionRange p :=
  (xs.map (buserSarnakProjectiveReductionImage p)).prod

@[simp] lemma positiveProjectiveEval_nil (p : ℕ) [NeZero p] :
    positiveProjectiveEval p [] = 1 := rfl

lemma positiveProjectiveEval_append (p : ℕ) [NeZero p]
    (xs ys : List ProjectiveOctagonGenerator) :
    positiveProjectiveEval p (xs ++ ys) =
      positiveProjectiveEval p xs * positiveProjectiveEval p ys := by
  simp [positiveProjectiveEval]

@[simp] lemma positiveProjectiveEval_singleton (p : ℕ) [NeZero p]
    (x : ProjectiveOctagonGenerator) :
    positiveProjectiveEval p [x] = buserSarnakProjectiveReductionImage p x := by
  simp [positiveProjectiveEval]

private lemma projective_pow_natCard_sub_one_eq_inv_of_finite
    {G : Type*} [Group G] [Finite G] (x : G) :
    x ^ (Nat.card G - 1) = x⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  have hcard : 0 < Nat.card G := Nat.card_pos
  rw [Nat.sub_add_cancel hcard]
  exact orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard x)

/-- Replace negative free letters by positive powers in the finite quotient. -/
def positiveProjectiveExpansion (p : ℕ) [NeZero p]
    (w : List (ProjectiveOctagonGenerator × Bool)) :
    List ProjectiveOctagonGenerator :=
  w.flatMap fun xb =>
    if xb.2 then [xb.1]
    else List.replicate (Nat.card (BuserSarnakProjectiveReductionRange p) - 1) xb.1

lemma positiveProjectiveEval_positiveProjectiveExpansion
    (p : ℕ) [NeZero p] (w : List (ProjectiveOctagonGenerator × Bool)) :
    positiveProjectiveEval p (positiveProjectiveExpansion p w) =
      FreeGroup.lift (buserSarnakProjectiveReductionImage p) (FreeGroup.mk w) := by
  induction w with
  | nil => simp [positiveProjectiveExpansion, positiveProjectiveEval]
  | cons xb w ih =>
      rcases xb with ⟨x, b⟩
      cases b
      · rw [show positiveProjectiveExpansion p ((x, false) :: w) =
          List.replicate (Nat.card (BuserSarnakProjectiveReductionRange p) - 1) x ++
            positiveProjectiveExpansion p w by simp [positiveProjectiveExpansion]]
        rw [positiveProjectiveEval_append, ih]
        rw [ReidemeisterSchreier.Discrete.SchreierRewriting.mk_cons_false,
          map_mul, map_inv, FreeGroup.lift_apply_of]
        simp [positiveProjectiveEval]
        simpa only [Nat.card_eq_fintype_card] using
          (projective_pow_natCard_sub_one_eq_inv_of_finite
            (buserSarnakProjectiveReductionImage p x))
      · rw [show positiveProjectiveExpansion p ((x, true) :: w) =
          [x] ++ positiveProjectiveExpansion p w by simp [positiveProjectiveExpansion]]
        rw [positiveProjectiveEval_append, positiveProjectiveEval_singleton, ih]
        rw [ReidemeisterSchreier.Discrete.SchreierRewriting.mk_cons_true,
          map_mul, FreeGroup.lift_apply_of]

theorem exists_positiveProjectiveWord (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    ∃ xs : List ProjectiveOctagonGenerator,
      positiveProjectiveEval p xs = q := by
  obtain ⟨w, hw⟩ := buserSarnakProjectiveReductionMap_surjective p q
  refine ⟨positiveProjectiveExpansion p w.toWord, ?_⟩
  rw [positiveProjectiveEval_positiveProjectiveExpansion]
  rw [FreeGroup.mk_toWord]
  exact hw

/-- A positive projective word of a specified length represents a state. -/
def HasPositiveProjectiveWordLength (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) (n : ℕ) : Prop :=
  ∃ xs : List ProjectiveOctagonGenerator,
    xs.length = n ∧ positiveProjectiveEval p xs = q

noncomputable local instance hasPositiveProjectiveWordLengthDecidable
    (p : ℕ) [NeZero p] (q : BuserSarnakProjectiveReductionRange p) :
    DecidablePred (HasPositiveProjectiveWordLength p q) :=
  Classical.decPred _

theorem exists_positiveProjectiveWordLength (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    ∃ n, HasPositiveProjectiveWordLength p q n := by
  obtain ⟨xs, hxs⟩ := exists_positiveProjectiveWord p q
  exact ⟨xs.length, xs, rfl, hxs⟩

/-- The shortest positive projective word length of a quotient state. -/
noncomputable def positiveProjectiveDistance (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) : ℕ :=
  Nat.find (exists_positiveProjectiveWordLength p q)

theorem positiveProjectiveDistance_spec (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    HasPositiveProjectiveWordLength p q (positiveProjectiveDistance p q) :=
  Nat.find_spec (exists_positiveProjectiveWordLength p q)

theorem positiveProjectiveDistance_le_length (p : ℕ) [NeZero p]
    {q : BuserSarnakProjectiveReductionRange p}
    {xs : List ProjectiveOctagonGenerator}
    (hxs : positiveProjectiveEval p xs = q) :
    positiveProjectiveDistance p q ≤ xs.length :=
  Nat.find_min' (exists_positiveProjectiveWordLength p q)
    ⟨xs, rfl, hxs⟩

@[simp] theorem positiveProjectiveDistance_one (p : ℕ) [NeZero p] :
    positiveProjectiveDistance p (1 : BuserSarnakProjectiveReductionRange p) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact positiveProjectiveDistance_le_length p
    (xs := []) (q := 1) (by simp)

theorem positiveProjectiveDistance_pos_of_ne_one (p : ℕ) [NeZero p]
    {q : BuserSarnakProjectiveReductionRange p} (hq : q ≠ 1) :
    0 < positiveProjectiveDistance p q := by
  apply Nat.pos_of_ne_zero
  intro hzero
  obtain ⟨xs, hlen, heval⟩ := positiveProjectiveDistance_spec p q
  rw [hzero] at hlen
  have : xs = [] := List.eq_nil_of_length_eq_zero hlen
  subst xs
  exact hq (by simpa using heval.symm)

/-- A nonidentity projective state has a shortest-word predecessor. -/
theorem exists_positiveProjectivePredecessor (p : ℕ) [NeZero p]
    {q : BuserSarnakProjectiveReductionRange p} (hq : q ≠ 1) :
    ∃ r : BuserSarnakProjectiveReductionRange p,
      ∃ x : ProjectiveOctagonGenerator,
        r * buserSarnakProjectiveReductionImage p x = q ∧
          positiveProjectiveDistance p r < positiveProjectiveDistance p q := by
  obtain ⟨xs, hlen, heval⟩ := positiveProjectiveDistance_spec p q
  have hxs : xs ≠ [] := by
    intro hnil
    subst xs
    exact hq (by simpa using heval.symm)
  let ys := xs.dropLast
  let x := xs.getLast hxs
  let r := positiveProjectiveEval p ys
  refine ⟨r, x, ?_, ?_⟩
  · calc
      r * buserSarnakProjectiveReductionImage p x =
          positiveProjectiveEval p (ys ++ [x]) := by
            rw [positiveProjectiveEval_append,
              positiveProjectiveEval_singleton]
      _ = positiveProjectiveEval p xs := by
        rw [List.dropLast_append_getLast hxs]
      _ = q := heval
  · calc
      positiveProjectiveDistance p r ≤ ys.length :=
        positiveProjectiveDistance_le_length p rfl
      _ = positiveProjectiveDistance p q - 1 := by
        simp only [ys, List.length_dropLast, hlen]
      _ < positiveProjectiveDistance p q := by
        exact Nat.sub_lt (positiveProjectiveDistance_pos_of_ne_one p hq)
          (by omega)

noncomputable def positiveProjectivePredecessor (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) (hq : q ≠ 1) :
    BuserSarnakProjectiveReductionRange p × ProjectiveOctagonGenerator :=
  let h := exists_positiveProjectivePredecessor p hq
  ⟨h.choose, h.choose_spec.choose⟩

theorem positiveProjectivePredecessor_mul (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) (hq : q ≠ 1) :
    (positiveProjectivePredecessor p q hq).1 *
        buserSarnakProjectiveReductionImage p
          (positiveProjectivePredecessor p q hq).2 = q :=
  (exists_positiveProjectivePredecessor p hq).choose_spec.choose_spec.1

theorem positiveProjectivePredecessor_distance_lt (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) (hq : q ≠ 1) :
    positiveProjectiveDistance p (positiveProjectivePredecessor p q hq).1 <
      positiveProjectiveDistance p q :=
  (exists_positiveProjectivePredecessor p hq).choose_spec.choose_spec.2

/-- The canonical positive word obtained by recursively following shortest
predecessors. -/
noncomputable def canonicalPositiveProjectiveWord (p : ℕ) [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p) :
    List ProjectiveOctagonGenerator :=
  if hq : q = 1 then []
  else
    canonicalPositiveProjectiveWord p
      (positiveProjectivePredecessor p q hq).1 ++
      [(positiveProjectivePredecessor p q hq).2]
termination_by positiveProjectiveDistance p q
decreasing_by exact positiveProjectivePredecessor_distance_lt p q hq

theorem positiveProjectiveEval_canonicalPositiveProjectiveWord
    (p : ℕ) [NeZero p] (q : BuserSarnakProjectiveReductionRange p) :
    positiveProjectiveEval p (canonicalPositiveProjectiveWord p q) = q := by
  induction q using (measure (positiveProjectiveDistance p)).wf.induction with
  | h q ih =>
      rw [canonicalPositiveProjectiveWord]
      split_ifs with hq
      · simp [hq]
      · rw [positiveProjectiveEval_append, positiveProjectiveEval_singleton,
          ih (positiveProjectivePredecessor p q hq).1
            (positiveProjectivePredecessor_distance_lt p q hq),
          positiveProjectivePredecessor_mul]

theorem canonicalPositiveProjectiveWord_prefixState
    (p : ℕ) [NeZero p] (q : BuserSarnakProjectiveReductionRange p)
    (acc rest : List ProjectiveOctagonGenerator)
    (hcat : acc ++ rest = canonicalPositiveProjectiveWord p q) :
    canonicalPositiveProjectiveWord p (positiveProjectiveEval p acc) = acc := by
  induction q using (measure (positiveProjectiveDistance p)).wf.induction
      generalizing acc rest with
  | h q ih =>
      rw [canonicalPositiveProjectiveWord] at hcat
      split_ifs at hcat with hq
      · have hacc : acc = [] := (List.append_eq_nil_iff.mp hcat).1
        subst acc
        simp [canonicalPositiveProjectiveWord]
      · let r := (positiveProjectivePredecessor p q hq).1
        let x := (positiveProjectivePredecessor p q hq).2
        have hpref : acc <+: canonicalPositiveProjectiveWord p r ++ [x] :=
          ⟨rest, hcat⟩
        rw [List.prefix_concat_iff] at hpref
        rcases hpref with hfull | hpre
        · subst acc
          have heval : positiveProjectiveEval p
              (canonicalPositiveProjectiveWord p r ++ [x]) = q := by
            rw [positiveProjectiveEval_append, positiveProjectiveEval_singleton,
              positiveProjectiveEval_canonicalPositiveProjectiveWord,
              positiveProjectivePredecessor_mul]
          rw [heval, canonicalPositiveProjectiveWord]
          simp [hq, r, x]
        · rcases hpre with ⟨tail, htail⟩
          exact ih r (positiveProjectivePredecessor_distance_lt p q hq)
            acc tail htail

/-- Add positive signs to a projective-generator word. -/
def positiveSignedProjectiveWord
    (xs : List ProjectiveOctagonGenerator) :
    List (ProjectiveOctagonGenerator × Bool) :=
  xs.map fun x => (x, true)

lemma buserSarnakProjectiveReductionMap_mk_positiveSignedProjectiveWord
    (p : ℕ) [NeZero p] (xs : List ProjectiveOctagonGenerator) :
    buserSarnakProjectiveReductionMap p
        (FreeGroup.mk (positiveSignedProjectiveWord xs)) =
      positiveProjectiveEval p xs := by
  rw [buserSarnakProjectiveReductionMap]
  rw [FreeGroup.lift_mk]
  simp only [positiveSignedProjectiveWord, List.map_map]
  change (xs.map (buserSarnakProjectiveReductionImage p)).prod =
    positiveProjectiveEval p xs
  rfl

/-- A projective quotient section with positive, prefix-closed representatives. -/
structure BuserSarnakProjectiveQuotientSectionData (p : ℕ) [NeZero p] where
  quotientSectionWord : BuserSarnakProjectiveReductionRange p →
    List (ProjectiveOctagonGenerator × Bool)
  quotientMap_mk_quotientSectionWord :
    ∀ q : BuserSarnakProjectiveReductionRange p,
      buserSarnakProjectiveReductionMap p
          (FreeGroup.mk (quotientSectionWord q)) = q
  quotientSectionWord_positive :
    ∀ q : BuserSarnakProjectiveReductionRange p,
      ∀ xb ∈ quotientSectionWord q, xb.2 = true
  prefixState :
    ∀ q : BuserSarnakProjectiveReductionRange p,
      ∀ acc rest : List (ProjectiveOctagonGenerator × Bool),
        acc ++ rest = quotientSectionWord q →
          quotientSectionWord
            (buserSarnakProjectiveReductionMap p (FreeGroup.mk acc)) = acc

namespace BuserSarnakProjectiveQuotientSectionData

open ReidemeisterSchreier.Discrete

/-- Forget the specialized section to the generic positive certificate. -/
def toPositiveCertificate {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    PositivePrefixClosedQuotientSectionWordCertificate
      ProjectiveOctagonGenerator (BuserSarnakProjectiveReductionRange p) where
  quotientMap := buserSarnakProjectiveReductionMap p
  quotientSectionWord := S.quotientSectionWord
  quotientMap_mk_quotientSectionWord := S.quotientMap_mk_quotientSectionWord
  quotientSectionWord_positive := S.quotientSectionWord_positive
  prefixState := S.prefixState

/-- Prefix-closed Schreier data induced by the projective quotient tree. -/
def schreierData {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    PrefixClosedFiniteQuotientSchreierData
      ProjectiveOctagonGenerator (BuserSarnakProjectiveReductionRange p) :=
  S.toPositiveCertificate.toPrefixClosedFiniteQuotientSchreierData

@[simp] lemma schreierData_quotientMap {p : ℕ} [NeZero p]
    (S : BuserSarnakProjectiveQuotientSectionData p) :
    S.schreierData.toFiniteQuotientSchreierData.quotientMap =
      buserSarnakProjectiveReductionMap p := rfl

end BuserSarnakProjectiveQuotientSectionData

/-- The canonical shortest-predecessor tree supplies positive prefix-closed
projective quotient representatives uniformly at every nonzero level. -/
noncomputable def canonicalBuserSarnakProjectiveQuotientSectionData
    (p : ℕ) [NeZero p] : BuserSarnakProjectiveQuotientSectionData p where
  quotientSectionWord q :=
    positiveSignedProjectiveWord (canonicalPositiveProjectiveWord p q)
  quotientMap_mk_quotientSectionWord q := by
    rw [buserSarnakProjectiveReductionMap_mk_positiveSignedProjectiveWord,
      positiveProjectiveEval_canonicalPositiveProjectiveWord]
  quotientSectionWord_positive := by
    intro q xb hxb
    rcases List.mem_map.mp hxb with ⟨x, _, rfl⟩
    rfl
  prefixState := by
    intro q acc rest hcat
    let word := canonicalPositiveProjectiveWord p q
    let n := acc.length
    let accX := word.take n
    have hacc : acc = positiveSignedProjectiveWord accX := by
      calc
        acc = (acc ++ rest).take n := by simp [n]
        _ = (positiveSignedProjectiveWord word).take n := by rw [hcat]
        _ = positiveSignedProjectiveWord accX := by
          simp [positiveSignedProjectiveWord, accX, n]
    have hprefix : accX ++ word.drop n = word := by
      exact List.take_append_drop n word
    have hcanonical :
        canonicalPositiveProjectiveWord p (positiveProjectiveEval p accX) = accX :=
      canonicalPositiveProjectiveWord_prefixState p q accX (word.drop n) hprefix
    have heval : buserSarnakProjectiveReductionMap p (FreeGroup.mk acc) =
        positiveProjectiveEval p accX := by
      rw [hacc,
        buserSarnakProjectiveReductionMap_mk_positiveSignedProjectiveWord]
    rw [heval, hcanonical, ← hacc]

/-- Each projective cone image is an involution. -/
theorem buserSarnakProjectiveReductionImage_cone_sq
    (p : ℕ) [NeZero p] (e : ProjectiveOctagonGenerator)
    (he : e = .e1 ∨ e = .e2 ∨ e = .e3 ∨ e = .e4) :
    buserSarnakProjectiveReductionImage p e ^ 2 = 1 := by
  rcases he with rfl | rfl | rfl | rfl
  · change (QuotientGroup.mk' (buserSarnakReductionCenterSubgroup p)
      (buserSarnakOctagonReductionImage p .e1)) ^ 2 = 1
    rw [← map_pow,
      buserSarnakOctagonReductionImage_cone_sq p .e1 (by simp)]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)
  · change (QuotientGroup.mk' (buserSarnakReductionCenterSubgroup p)
      (buserSarnakOctagonReductionImage p .e2)) ^ 2 = 1
    rw [← map_pow,
      buserSarnakOctagonReductionImage_cone_sq p .e2 (by simp)]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)
  · change (QuotientGroup.mk' (buserSarnakReductionCenterSubgroup p)
      (buserSarnakOctagonReductionImage p .e3)) ^ 2 = 1
    rw [← map_pow,
      buserSarnakOctagonReductionImage_cone_sq p .e3 (by simp)]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)
  · change (QuotientGroup.mk' (buserSarnakReductionCenterSubgroup p)
      (buserSarnakOctagonReductionImage p .e4)) ^ 2 = 1
    rw [← map_pow,
      buserSarnakOctagonReductionImage_cone_sq p .e4 (by simp)]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)

/-- At an odd prime, no projective cone image is trivial. -/
theorem buserSarnakProjectiveReductionImage_cone_ne_one
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (e : ProjectiveOctagonGenerator)
    (he : e = .e1 ∨ e = .e2 ∨ e = .e3 ∨ e = .e4) :
    buserSarnakProjectiveReductionImage p e ≠ 1 := by
  intro h
  have hmem : buserSarnakOctagonReductionImage p
      (projectiveOctagonGeneratorLift e) ∈
        buserSarnakReductionCenterSubgroup p := by
    exact (QuotientGroup.eq_one_iff _).mp h
  have hdvd := orderOf_dvd_of_mem_zpowers hmem
  rcases he with rfl | rfl | rfl | rfl <;>
    simp only [projectiveOctagonGeneratorLift] at hdvd <;>
    rw [orderOf_buserSarnakOctagonReductionImage_cone p hp hp2 _ (by simp),
      orderOf_buserSarnakOctagonReductionImage_z p hp hp2] at hdvd <;>
    norm_num at hdvd

/-- Each projective cone image has exact order two at every odd prime level. -/
theorem orderOf_buserSarnakProjectiveReductionImage_cone
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (e : ProjectiveOctagonGenerator)
    (he : e = .e1 ∨ e = .e2 ∨ e = .e3 ∨ e = .e4) :
    orderOf (buserSarnakProjectiveReductionImage p e) = 2 := by
  exact orderOf_eq_prime
    (buserSarnakProjectiveReductionImage_cone_sq p e he)
    (buserSarnakProjectiveReductionImage_cone_ne_one p hp hp2 e he)

/-- Right multiplication by a projective cone image acts without fixed points
on the finite projective quotient. -/
theorem buserSarnakProjectiveReductionImage_cone_right_fixedPointFree
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (q : BuserSarnakProjectiveReductionRange p)
    (e : ProjectiveOctagonGenerator)
    (he : e = .e1 ∨ e = .e2 ∨ e = .e3 ∨ e = .e4) :
    q * buserSarnakProjectiveReductionImage p e ≠ q := by
  intro h
  apply buserSarnakProjectiveReductionImage_cone_ne_one p hp hp2 e he
  apply mul_left_cancel (a := q)
  simpa using h

/-! ## Size of the canonical projective cleaned presentation -/

noncomputable local instance buserSarnakProjectiveDegenerateSchreierSymbolDecidable
    {p : ℕ} [NeZero p]
    {S : BuserSarnakProjectiveQuotientSectionData p} :
    DecidablePred
      S.schreierData.toFiniteQuotientSchreierData.IsDegenerateSchreierSymbol :=
  Classical.decPred _

abbrev Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveSection (p : ℕ) [NeZero p] :=
  canonicalBuserSarnakProjectiveQuotientSectionData p

abbrev Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData
    (p : ℕ) [NeZero p] :=
  ((Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveSection p).schreierData).toFiniteQuotientSchreierData

/-- In the canonical projective Schreier graph, an edge is right
multiplication by the corresponding reduced projective generator. -/
@[simp] lemma canonicalBuserSarnakProjective_transition_eq_mul
    (p : ℕ) [NeZero p] (q : BuserSarnakProjectiveReductionRange p)
    (x : ProjectiveOctagonGenerator) :
    (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).transition q x =
      q * buserSarnakProjectiveReductionImage p x := by
  rw [FiniteQuotientSchreierData.transition_eq]
  rw [BuserSarnakProjectiveQuotientSectionData.schreierData_quotientMap]
  exact congrArg (q * ·) FreeGroup.lift_apply_of

/-- A degenerate projective symbol appends exactly one positive letter to its
source representative. -/
lemma canonicalBuserSarnakProjective_isDegenerate_word
    {p : ℕ} [NeZero p]
    {q : BuserSarnakProjectiveReductionRange p}
    {x : ProjectiveOctagonGenerator}
    (h : (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p)
      |>.IsDegenerateSchreierSymbol (q, x)) :
    positiveSignedProjectiveWord
        (canonicalPositiveProjectiveWord p
          ((Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).transition q x)) =
      positiveSignedProjectiveWord (canonicalPositiveProjectiveWord p q) ++
        [(x, true)] := by
  have h' :
      FreeGroup.mk (positiveSignedProjectiveWord
          (canonicalPositiveProjectiveWord p
            ((Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).transition q x))) =
        FreeGroup.mk
          (positiveSignedProjectiveWord (canonicalPositiveProjectiveWord p q) ++
            [(x, true)]) := by
    rw [← FreeGroup.mul_mk]
    exact h
  have hw := congrArg FreeGroup.toWord h'
  have hl : FreeGroup.reduce
      (positiveSignedProjectiveWord
        (canonicalPositiveProjectiveWord p
          ((Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).transition q x))) =
      positiveSignedProjectiveWord
        (canonicalPositiveProjectiveWord p
          ((Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).transition q x)) := by
    apply FiniteQuotientSchreierData.reduce_eq_of_forall_snd_eq_true
    intro xb hxb
    rcases List.mem_map.mp hxb with ⟨y, _, rfl⟩
    rfl
  have hr : FreeGroup.reduce
      (positiveSignedProjectiveWord (canonicalPositiveProjectiveWord p q) ++
        [(x, true)]) =
      positiveSignedProjectiveWord (canonicalPositiveProjectiveWord p q) ++
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

/-- A canonical tree cannot contain both orientations of an involutive edge:
each degenerate orientation would increase the positive representative length. -/
lemma canonicalBuserSarnakProjective_not_both_isDegenerate_of_transition_involutive
    {p : ℕ} [NeZero p]
    {q : BuserSarnakProjectiveReductionRange p}
    {x : ProjectiveOctagonGenerator}
    (hinv : (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).transition
        ((Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).transition q x) x = q) :
    ¬ ((Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).IsDegenerateSchreierSymbol
          (q, x) ∧
      (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).IsDegenerateSchreierSymbol
            ((Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).transition q x, x)) := by
  rintro ⟨h, hnext⟩
  have hword := canonicalBuserSarnakProjective_isDegenerate_word h
  have hnextword := canonicalBuserSarnakProjective_isDegenerate_word hnext
  rw [hinv] at hnextword
  have hlen := congrArg List.length hword
  have hlennext := congrArg List.length hnextword
  simp only [List.length_append, List.length_singleton] at hlen hlennext
  omega

/-- Neither orientation of a canonical projective cone edge can be a tree
edge at an odd-order cone involution. -/
lemma canonicalBuserSarnakProjective_cone_not_both_isDegenerate
    {p : ℕ} [NeZero p]
    (q : BuserSarnakProjectiveReductionRange p)
    (e : ProjectiveOctagonGenerator)
    (he : e = .e1 ∨ e = .e2 ∨ e = .e3 ∨ e = .e4) :
    ¬ ((Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).IsDegenerateSchreierSymbol
          (q, e) ∧
      (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).IsDegenerateSchreierSymbol
            ((Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).transition q e, e)) := by
  apply canonicalBuserSarnakProjective_not_both_isDegenerate_of_transition_involutive
  calc
    (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).transition
        ((Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).transition q e) e =
      (q * buserSarnakProjectiveReductionImage p e) *
        buserSarnakProjectiveReductionImage p e := by
          simp only [canonicalBuserSarnakProjective_transition_eq_mul]
    _ = q * (buserSarnakProjectiveReductionImage p e ^ 2) := by
      rw [pow_two, mul_assoc]
    _ = q := by
      rw [buserSarnakProjectiveReductionImage_cone_sq p e he, mul_one]

/-- Every degenerate projective tree edge has a nonidentity endpoint. -/
lemma canonicalBuserSarnakProjective_transition_ne_one_of_isDegenerate
    {p : ℕ} [NeZero p]
    {q : BuserSarnakProjectiveReductionRange p}
    {x : ProjectiveOctagonGenerator}
    (h : (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p)
      |>.IsDegenerateSchreierSymbol (q, x)) :
    (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).transition q x ≠ 1 := by
  intro htransition
  have hw := canonicalBuserSarnakProjective_isDegenerate_word h
  rw [htransition] at hw
  have hone : canonicalPositiveProjectiveWord p
      (1 : BuserSarnakProjectiveReductionRange p) = [] := by
    rw [canonicalPositiveProjectiveWord]
    simp
  rw [hone] at hw
  simp [positiveSignedProjectiveWord] at hw

/-- The degenerate symbols deleted from the canonical projective Schreier
presentation. -/
abbrev CanonicalBuserSarnakProjectiveDegenerateSymbol
    (p : ℕ) [NeZero p] :=
  {z : FiniteQuotientSchreierData.FiniteSchreierSymbol
      ProjectiveOctagonGenerator (BuserSarnakProjectiveReductionRange p) //
    (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p)
      |>.IsDegenerateSchreierSymbol z}

/-- Send a canonical projective tree edge to its endpoint. -/
def canonicalBuserSarnakProjectiveDegenerateTarget (p : ℕ) [NeZero p]
    (z : CanonicalBuserSarnakProjectiveDegenerateSymbol p) :
    {q : BuserSarnakProjectiveReductionRange p // q ≠ 1} :=
  ⟨(Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).transition z.1.1 z.1.2,
    canonicalBuserSarnakProjective_transition_ne_one_of_isDegenerate z.2⟩

lemma canonicalBuserSarnakProjective_transition_predecessor
    (p : ℕ) [NeZero p] (q : BuserSarnakProjectiveReductionRange p) (hq : q ≠ 1) :
    (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).transition
        (positiveProjectivePredecessor p q hq).1
        (positiveProjectivePredecessor p q hq).2 = q := by
  rw [FiniteQuotientSchreierData.transition_eq]
  rw [BuserSarnakProjectiveQuotientSectionData.schreierData_quotientMap]
  rw [show buserSarnakProjectiveReductionMap p
      (FreeGroup.of (positiveProjectivePredecessor p q hq).2) =
        buserSarnakProjectiveReductionImage p
          (positiveProjectivePredecessor p q hq).2 by
    exact FreeGroup.lift_apply_of]
  exact positiveProjectivePredecessor_mul p q hq

lemma canonicalBuserSarnakProjective_predecessor_isDegenerate
    (p : ℕ) [NeZero p] (q : BuserSarnakProjectiveReductionRange p) (hq : q ≠ 1) :
    (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p)
      |>.IsDegenerateSchreierSymbol
        ((positiveProjectivePredecessor p q hq).1,
          (positiveProjectivePredecessor p q hq).2) := by
  rw [FiniteQuotientSchreierData.IsDegenerateSchreierSymbol,
    canonicalBuserSarnakProjective_transition_predecessor p q hq]
  change
    FreeGroup.mk (positiveSignedProjectiveWord
        (canonicalPositiveProjectiveWord p q)) =
      FreeGroup.mk (positiveSignedProjectiveWord
          (canonicalPositiveProjectiveWord p
            (positiveProjectivePredecessor p q hq).1)) *
        FreeGroup.of (positiveProjectivePredecessor p q hq).2
  rw [canonicalPositiveProjectiveWord]
  simp only [hq, ↓reduceDIte, positiveSignedProjectiveWord, List.map_append,
    List.map_singleton]
  rw [← FreeGroup.mul_mk]
  rfl

/-- The last edge in the canonical word for a nonidentity projective state. -/
def canonicalBuserSarnakProjectiveDegenerateSource (p : ℕ) [NeZero p]
    (q : {q : BuserSarnakProjectiveReductionRange p // q ≠ 1}) :
    CanonicalBuserSarnakProjectiveDegenerateSymbol p :=
  ⟨((positiveProjectivePredecessor p q.1 q.2).1,
      (positiveProjectivePredecessor p q.1 q.2).2),
    canonicalBuserSarnakProjective_predecessor_isDegenerate p q.1 q.2⟩

@[simp] lemma canonicalBuserSarnakProjectiveDegenerateTarget_source
    (p : ℕ) [NeZero p]
    (q : {q : BuserSarnakProjectiveReductionRange p // q ≠ 1}) :
    canonicalBuserSarnakProjectiveDegenerateTarget p
        (canonicalBuserSarnakProjectiveDegenerateSource p q) = q := by
  apply Subtype.ext
  exact canonicalBuserSarnakProjective_transition_predecessor p q.1 q.2

/-- Distinct canonical projective tree edges have distinct endpoints. -/
lemma canonicalBuserSarnakProjectiveDegenerateTarget_injective
    (p : ℕ) [NeZero p] :
    Function.Injective (canonicalBuserSarnakProjectiveDegenerateTarget p) := by
  intro z w htarget
  have htransition :
      (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).transition z.1.1 z.1.2 =
        (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).transition w.1.1 w.1.2 :=
    congrArg Subtype.val htarget
  have hz := canonicalBuserSarnakProjective_isDegenerate_word z.2
  have hw := canonicalBuserSarnakProjective_isDegenerate_word w.2
  rw [htransition] at hz
  have hfull := hz.symm.trans hw
  have hlen :
      (positiveSignedProjectiveWord
        (canonicalPositiveProjectiveWord p z.1.1)).length =
      (positiveSignedProjectiveWord
        (canonicalPositiveProjectiveWord p w.1.1)).length := by
    have hlenPlus :
        (positiveSignedProjectiveWord
          (canonicalPositiveProjectiveWord p z.1.1)).length + 1 =
        (positiveSignedProjectiveWord
          (canonicalPositiveProjectiveWord p w.1.1)).length + 1 := by
      simpa only [List.length_append, List.length_singleton] using
        congrArg List.length hfull
    exact Nat.add_right_cancel hlenPlus
  have hparts := List.append_inj hfull hlen
  have hword : canonicalPositiveProjectiveWord p z.1.1 =
      canonicalPositiveProjectiveWord p w.1.1 := by
    have hpair : Function.Injective
        (fun x : ProjectiveOctagonGenerator => (x, true)) := by
      intro x y hxy
      exact congrArg Prod.fst hxy
    exact hpair.list_map hparts.1
  have hstate : z.1.1 = w.1.1 := by
    have heval := congrArg (positiveProjectiveEval p) hword
    simpa [positiveProjectiveEval_canonicalPositiveProjectiveWord] using heval
  have hgenerator : z.1.2 = w.1.2 :=
    congrArg Prod.fst (List.singleton_injective hparts.2)
  apply Subtype.ext
  exact Prod.ext hstate hgenerator

/-- Canonical projective degenerate symbols are exactly the nonroot edges of
the shortest-predecessor tree. -/
def canonicalBuserSarnakProjectiveDegenerateEquivNonidentity
    (p : ℕ) [NeZero p] :
    CanonicalBuserSarnakProjectiveDegenerateSymbol p ≃
      {q : BuserSarnakProjectiveReductionRange p // q ≠ 1} :=
  Equiv.ofBijective (canonicalBuserSarnakProjectiveDegenerateTarget p)
    ⟨canonicalBuserSarnakProjectiveDegenerateTarget_injective p,
      fun q => ⟨canonicalBuserSarnakProjectiveDegenerateSource p q,
        canonicalBuserSarnakProjectiveDegenerateTarget_source p q⟩⟩

/-- A finite rooted projective tree has one deleted Schreier symbol for every
nonidentity quotient state. -/
theorem card_canonicalBuserSarnakProjectiveDegenerateSymbol
    (p : ℕ) [NeZero p] :
    Fintype.card (CanonicalBuserSarnakProjectiveDegenerateSymbol p) =
      Fintype.card (BuserSarnakProjectiveReductionRange p) - 1 := by
  rw [Fintype.card_congr
    (canonicalBuserSarnakProjectiveDegenerateEquivNonidentity p)]
  calc
    Fintype.card {q : BuserSarnakProjectiveReductionRange p // q ≠ 1} =
        Fintype.card (BuserSarnakProjectiveReductionRange p) -
          Fintype.card {q : BuserSarnakProjectiveReductionRange p // q = 1} := by
      exact Fintype.card_subtype_compl
        (fun q : BuserSarnakProjectiveReductionRange p => q = 1)
    _ = Fintype.card (BuserSarnakProjectiveReductionRange p) - 1 := by
      rw [Fintype.card_subtype_eq]

/-- The nondegenerate generator type in the canonical projective cleaned
presentation. -/
abbrev CanonicalBuserSarnakProjectiveNondegenerateSymbol
    (p : ℕ) [NeZero p] :=
  (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveSection p).schreierData.nondegenerateSchreierSymbol

noncomputable local instance canonicalBuserSarnakProjectiveNondegenerateFinite
    (p : ℕ) [NeZero p] :
    Finite (CanonicalBuserSarnakProjectiveNondegenerateSymbol p) :=
  Finite.of_injective
    (fun z : CanonicalBuserSarnakProjectiveNondegenerateSymbol p => z.1)
    Subtype.val_injective

noncomputable local instance canonicalBuserSarnakProjectiveNondegenerateFintype
    (p : ℕ) [NeZero p] :
    Fintype (CanonicalBuserSarnakProjectiveNondegenerateSymbol p) :=
  Fintype.ofFinite _

noncomputable local instance canonicalBuserSarnakProjectiveNondegenerateDecidableEq
    (p : ℕ) [NeZero p] :
    DecidableEq (CanonicalBuserSarnakProjectiveNondegenerateSymbol p) :=
  Classical.decEq _

/-- After deleting its tree edges, the canonical projective Schreier
presentation has exactly `5 * halfImageIndex + 1` generators. -/
theorem card_canonicalBuserSarnakProjectiveNondegenerateSymbol
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    Fintype.card (CanonicalBuserSarnakProjectiveNondegenerateSymbol p) =
      5 * data.halfImageIndex + 1 := by
  have hqcard : Fintype.card (BuserSarnakProjectiveReductionRange p) =
      data.halfImageIndex := by
    have h := natCard_buserSarnakProjectiveReductionRange hp hp2 data
    rw [Nat.card_eq_fintype_card] at h
    exact h
  have hxcard : Fintype.card ProjectiveOctagonGenerator = 6 := by
    decide
  have htotal :
      Fintype.card
          (FiniteQuotientSchreierData.FiniteSchreierSymbol
            ProjectiveOctagonGenerator (BuserSarnakProjectiveReductionRange p)) =
        6 * data.halfImageIndex := by
    simp only [FiniteQuotientSchreierData.FiniteSchreierSymbol,
      Fintype.card_prod, hqcard, hxcard]
    ring
  have hdeg := card_canonicalBuserSarnakProjectiveDegenerateSymbol p
  have hsplit :
      Fintype.card (CanonicalBuserSarnakProjectiveNondegenerateSymbol p) =
        Fintype.card
            (FiniteQuotientSchreierData.FiniteSchreierSymbol
              ProjectiveOctagonGenerator (BuserSarnakProjectiveReductionRange p)) -
          Fintype.card (CanonicalBuserSarnakProjectiveDegenerateSymbol p) := by
    have hsplitNat :
        Nat.card (CanonicalBuserSarnakProjectiveNondegenerateSymbol p) =
          Nat.card
              (FiniteQuotientSchreierData.FiniteSchreierSymbol
                ProjectiveOctagonGenerator (BuserSarnakProjectiveReductionRange p)) -
            Nat.card (CanonicalBuserSarnakProjectiveDegenerateSymbol p) := by
      change
        Nat.card {z : FiniteQuotientSchreierData.FiniteSchreierSymbol
            ProjectiveOctagonGenerator (BuserSarnakProjectiveReductionRange p) //
          ¬((Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p)
            |>.IsDegenerateSchreierSymbol z)} =
        Nat.card
            (FiniteQuotientSchreierData.FiniteSchreierSymbol
              ProjectiveOctagonGenerator (BuserSarnakProjectiveReductionRange p)) -
          Nat.card {z : FiniteQuotientSchreierData.FiniteSchreierSymbol
              ProjectiveOctagonGenerator (BuserSarnakProjectiveReductionRange p) //
            (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p)
              |>.IsDegenerateSchreierSymbol z}
      simpa only [← Nat.card_eq_fintype_card] using
        Fintype.card_subtype_compl
          ((Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p)
            |>.IsDegenerateSchreierSymbol)
    simpa only [Nat.card_eq_fintype_card] using hsplitNat
  rw [hsplit, htotal, hdeg, hqcard]
  have hqpos : 0 < Fintype.card (BuserSarnakProjectiveReductionRange p) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  omega

/-- The same nondegenerate-generator count expressed through the public
canonical quotient-section data.  This avoids exposing the implementation
aliases used to build the shortest-predecessor tree. -/
theorem card_canonicalBuserSarnakProjectiveConeSchreierData_nondegenerateSymbol
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    Fintype.card ((canonicalBuserSarnakProjectiveQuotientSectionData p).schreierData.toFiniteQuotientSchreierData.NondegenerateSchreierSymbol) =
      5 * data.halfImageIndex + 1 := by
  change Fintype.card (CanonicalBuserSarnakProjectiveNondegenerateSymbol p) = _
  exact card_canonicalBuserSarnakProjectiveNondegenerateSymbol hp hp2 data

/-- Instance-independent form of the public canonical nondegenerate-symbol
count, convenient for downstream finite-type partitions. -/
theorem natCard_canonicalBuserSarnakProjectiveConeSchreierData_nondegenerateSymbol
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    Nat.card ((canonicalBuserSarnakProjectiveQuotientSectionData p).schreierData.toFiniteQuotientSchreierData.NondegenerateSchreierSymbol) =
      5 * data.halfImageIndex + 1 := by
  simpa only [Nat.card_eq_fintype_card] using
    card_canonicalBuserSarnakProjectiveConeSchreierData_nondegenerateSymbol hp hp2 data

/-- The projective cleaned presentation contains the surface generators. -/
theorem card_surfaceGenerator_le_canonicalBuserSarnakProjectiveNondegenerate
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    Fintype.card (SurfaceGenerator (data.halfImageIndex + 1)) ≤
      Fintype.card (CanonicalBuserSarnakProjectiveNondegenerateSymbol p) := by
  rw [card_canonicalBuserSarnakProjectiveNondegenerateSymbol hp hp2 data]
  simp only [SurfaceGenerator, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  have hqcard : Fintype.card (BuserSarnakProjectiveReductionRange p) =
      data.halfImageIndex := by
    have h := natCard_buserSarnakProjectiveReductionRange hp hp2 data
    rw [Nat.card_eq_fintype_card] at h
    exact h
  have hqpos : 0 < Fintype.card (BuserSarnakProjectiveReductionRange p) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  omega

/-- Passing from the projective cleaned presentation to the standard surface
presentation requires exactly `3 * halfImageIndex - 1` generator
eliminations. -/
theorem card_canonicalBuserSarnakProjectiveNondegenerate_eq_surface_add_excess
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    Fintype.card (CanonicalBuserSarnakProjectiveNondegenerateSymbol p) =
      Fintype.card (SurfaceGenerator (data.halfImageIndex + 1)) +
        (3 * data.halfImageIndex - 1) := by
  rw [card_canonicalBuserSarnakProjectiveNondegenerateSymbol hp hp2 data]
  simp only [SurfaceGenerator, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  have hqcard : Fintype.card (BuserSarnakProjectiveReductionRange p) =
      data.halfImageIndex := by
    have h := natCard_buserSarnakProjectiveReductionRange hp hp2 data
    rw [Nat.card_eq_fintype_card] at h
    exact h
  have hqpos : 0 < Fintype.card (BuserSarnakProjectiveReductionRange p) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  omega

/-! ## A finite normal-word table for the projective certificate -/

/-- The projective cleaned presentation has five relator instances for every
finite quotient state. -/
theorem card_buserSarnakProjectiveLevelCleanedRelatorIndex
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    Nat.card (BuserSarnakProjectiveReductionRange p × ProjectiveOctagonRelator) =
      5 * data.halfImageIndex := by
  rw [Nat.card_prod, natCard_buserSarnakProjectiveReductionRange hp hp2 data]
  have hrel : Nat.card ProjectiveOctagonRelator = 5 := by
    rw [Nat.card_eq_fintype_card]
    exact card_projectiveOctagonRelator
  rw [hrel]
  ring

/-- Index type for every canonical projective cleaned relator word. -/
abbrev CanonicalBuserSarnakProjectiveCleanedRelatorIndex
    (p : ℕ) [NeZero p] :=
  BuserSarnakProjectiveReductionRange p × ProjectiveOctagonRelator

/-- The reduced word of the cleaned rewrite attached to a projective quotient
state and one projective octagon relator. -/
noncomputable def canonicalBuserSarnakProjectiveCleanedRelatorNormalWord
    (p : ℕ) [NeZero p]
    (i : CanonicalBuserSarnakProjectiveCleanedRelatorIndex p) :
    List (CanonicalBuserSarnakProjectiveNondegenerateSymbol p × Bool) :=
  (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).cleanedTauNormalWord
    i.1 (projectiveOctagonRelator i.2)

/-- Each table entry reconstructs its projective cleaned
Reidemeister--Schreier relator. -/
theorem mk_canonicalBuserSarnakProjectiveCleanedRelatorNormalWord
    (p : ℕ) [NeZero p]
    (i : CanonicalBuserSarnakProjectiveCleanedRelatorIndex p) :
    FreeGroup.mk (canonicalBuserSarnakProjectiveCleanedRelatorNormalWord p i) =
      (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).cleanedTau i.1
        (projectiveOctagonRelator i.2) := by
  exact (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).mk_cleanedTauNormalWord
    i.1 (projectiveOctagonRelator i.2)

private lemma projective_norm_cleanedSchreierSymbolWord_le_one
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

private lemma projective_norm_cleanedTauList_le_length
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
              exact projective_norm_cleanedSchreierSymbolWord_le_one D _)
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
            (projective_norm_cleanedSchreierSymbolWord_le_one D _)
            (ih _)
          _ = ((x, true) :: xs).length := by
            change 1 + xs.length = xs.length + 1
            exact Nat.add_comm _ _

private lemma projective_cleanedTauNormalWord_length_le_toWord
    {X Q : Type*} [Group Q] [Fintype Q] [DecidableEq X]
    (D : FiniteQuotientSchreierData X Q)
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    (D.cleanedTauNormalWord q w).length ≤ w.toWord.length := by
  change FreeGroup.norm (D.cleanedTau q w) ≤ w.toWord.length
  rw [D.cleanedTau_eq_cleanedTauList_toWord]
  exact projective_norm_cleanedTauList_le_length D q w.toWord

private lemma projectiveOctagonRelator_toWord_length_le_eight
    (r : ProjectiveOctagonRelator) :
    (projectiveOctagonRelator r).toWord.length ≤ 8 := by
  cases r <;> decide

/-- Every projective cleaned relator is represented by a word of length at
most eight. -/
theorem canonicalBuserSarnakProjectiveCleanedRelatorNormalWord_length_le_eight
    (p : ℕ) [NeZero p]
    (i : CanonicalBuserSarnakProjectiveCleanedRelatorIndex p) :
    (canonicalBuserSarnakProjectiveCleanedRelatorNormalWord p i).length ≤ 8 := by
  calc
    (canonicalBuserSarnakProjectiveCleanedRelatorNormalWord p i).length ≤
        (projectiveOctagonRelator i.2).toWord.length :=
      projective_cleanedTauNormalWord_length_le_toWord
        (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p)
        i.1 (projectiveOctagonRelator i.2)
    _ ≤ 8 := projectiveOctagonRelator_toWord_length_le_eight i.2

/-- The finite set of distinct relators represented by the projective normal
word table. -/
noncomputable def canonicalBuserSarnakProjectiveCleanedRelatorFinset
    (p : ℕ) [NeZero p] :
    Finset (FreeGroup (CanonicalBuserSarnakProjectiveNondegenerateSymbol p)) :=
  Finset.univ.image fun i : CanonicalBuserSarnakProjectiveCleanedRelatorIndex p =>
    FreeGroup.mk (canonicalBuserSarnakProjectiveCleanedRelatorNormalWord p i)

/-- The projective normal-word table is exhaustive. -/
@[simp] theorem mem_canonicalBuserSarnakProjectiveCleanedRelatorFinset
    (p : ℕ) [NeZero p]
    {w : FreeGroup (CanonicalBuserSarnakProjectiveNondegenerateSymbol p)} :
    w ∈ canonicalBuserSarnakProjectiveCleanedRelatorFinset p ↔
      w ∈ (Internal.BuserSarnakProjectiveLevelMarkingHelpers.canonicalBuserSarnakProjectiveFiniteSchreierData p).cleanedSchreierRelators
        projectiveOctagonRelators := by
  simp only [canonicalBuserSarnakProjectiveCleanedRelatorFinset,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    rw [mk_canonicalBuserSarnakProjectiveCleanedRelatorNormalWord]
    exact ⟨i.1, projectiveOctagonRelator i.2, ⟨i.2, rfl⟩, rfl⟩
  · rintro ⟨q, r, ⟨j, rfl⟩, rfl⟩
    exact ⟨(q, j),
      mk_canonicalBuserSarnakProjectiveCleanedRelatorNormalWord p (q, j)⟩

/-- There are at most `5 * halfImageIndex` distinct projective cleaned
relators, all exposed by the displayed finite word table. -/
theorem card_canonicalBuserSarnakProjectiveCleanedRelatorFinset_le
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : BuserSarnakCorrectionData p) :
    (canonicalBuserSarnakProjectiveCleanedRelatorFinset p).card ≤
      5 * data.halfImageIndex := by
  calc
    (canonicalBuserSarnakProjectiveCleanedRelatorFinset p).card ≤
        (Finset.univ : Finset
          (CanonicalBuserSarnakProjectiveCleanedRelatorIndex p)).card :=
      Finset.card_image_le
    _ = Nat.card (CanonicalBuserSarnakProjectiveCleanedRelatorIndex p) := by
      rw [Nat.card_eq_fintype_card]
      rfl
    _ = 5 * data.halfImageIndex :=
      card_buserSarnakProjectiveLevelCleanedRelatorIndex hp hp2 data

end

end SystolicGrowth

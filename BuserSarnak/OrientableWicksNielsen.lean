module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

/-!
# Finite orientable Wicks certificates

This module records the exact finite combinatorial data needed by the final
Buser--Sarnak root-word normalization. It does not assume a classification
theorem and it does not manufacture a Nielsen program: a concrete contour
must supply the occurrence pairing, the one-vertex rotation, and the
positive/negative occurrence certificates before the later induction can be
applied.
-/

namespace SystolicGrowth

noncomputable section

/-- A literal free-group word with an explicit orientation bit on every
occurrence. `true` is the positive occurrence and `false` the inverse one.
-/
abbrev SignedWord (X : Type*) := List (X × Bool)

/-- Number of literal occurrences of `x` with the requested orientation in a
signed word. Unlike a count computed after free reduction, this remembers
every position of the unreduced list. -/
def signedOccurrenceCount {X : Type*} [DecidableEq X]
    (x : X) (positive : Bool) (word : SignedWord X) : ℕ :=
  (word.filter fun occurrence => occurrence.1 = x ∧ occurrence.2 = positive).length

/-- Literal signed multiplicities add under concatenation. -/
theorem signedOccurrenceCount_append {X : Type*} [DecidableEq X]
    (x : X) (positive : Bool) (left right : SignedWord X) :
    signedOccurrenceCount x positive (left ++ right) =
      signedOccurrenceCount x positive left +
        signedOccurrenceCount x positive right := by
  simp [signedOccurrenceCount, List.filter_append]

/-- Signed multiplicity commutes with a proposition-selected list. This keeps
recursive splice case splits at the list level instead of rewriting a
dependent conditional inside `signedOccurrenceCount`. -/
theorem signedOccurrenceCount_ite {X : Type*} [DecidableEq X]
    (x : X) (positive : Bool) (P : Prop) [Decidable P]
    (whenTrue whenFalse : SignedWord X) :
    signedOccurrenceCount x positive (if P then whenTrue else whenFalse) =
      if P then signedOccurrenceCount x positive whenTrue
      else signedOccurrenceCount x positive whenFalse := by
  by_cases hP : P <;> simp [hP]

/-- Inverse-reversal exchanges positive and negative literal occurrences. -/
theorem signedOccurrenceCount_invRev {X : Type*} [DecidableEq X]
    (x : X) (positive : Bool) (word : SignedWord X) :
    signedOccurrenceCount x positive (FreeGroup.invRev word) =
      signedOccurrenceCount x (!positive) word := by
  induction word with
  | nil => simp [signedOccurrenceCount, FreeGroup.invRev]
  | cons head tail ih =>
      rw [FreeGroup.invRev_cons, signedOccurrenceCount_append, ih]
      cases head with
      | mk generator orientation =>
        cases orientation <;> cases positive <;>
        by_cases hgen : generator = x <;>
          simp [signedOccurrenceCount, FreeGroup.invRev, hgen]

/-- Successor around the cyclically ordered positions of a nonempty finite
word. -/
def cyclicSucc {n : ℕ} (i : Fin n) : Fin n :=
  finRotate n i

/-- Cyclic successor permutes the literal positions. -/
theorem cyclicSucc_bijective (n : ℕ) :
    Function.Bijective (@cyclicSucc n) :=
  (finRotate n).bijective

/-- Boolean addition modulo two, used to compose occurrence-orientation
changes along a tree path. -/
def boolXor (a b : Bool) : Bool :=
  if a then !b else b

/-- Parity accumulated from one orientation bit through a list of successive
orientation bits. The final term is the complement of the last bit. -/
def boolPathParityFrom (a : Bool) : List Bool → Bool
  | [] => !a
  | b :: bs => boolXor (boolXor a b) (boolPathParityFrom b bs)

/-- A path of adjacent XOR changes telescopes: starting with the complement
of the first bit and XORing every successive change gives the complement of
the final bit. -/
theorem boolPathParityFrom_eq_not (a : Bool) (bits : List Bool) :
    boolPathParityFrom a bits = !a := by
  induction bits generalizing a with
  | nil => rfl
  | cons b bits ih =>
      simp only [boolPathParityFrom]
      rw [ih b]
      cases a <;> cases b <;> rfl

/-- Along an oriented edge with distinct endpoints, exactly one endpoint is
its physical source. This generic form lets concrete graph developments use
their own coercions for vertices without weakening the endpoint argument. -/
theorem boolEndpointSource_flip {V : Type*} [DecidableEq V]
    (source target left right : V) (hne : source ≠ target)
    (hendpoints : (left = source ∧ right = target) ∨
      (left = target ∧ right = source)) :
    (if right = source then true else false) =
      !(if left = source then true else false) := by
  rcases hendpoints with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · have htarget_ne_source : target ≠ source := fun h => hne h.symm
    rw [hright, ite_eq_right htarget_ne_source, hleft, ite_eq_left rfl]
    rfl
  · have htarget_ne_source : target ≠ source := fun h => hne h.symm
    rw [hright, ite_eq_left rfl, hleft, ite_eq_right htarget_ne_source]
    rfl

/-- Position in the inverse-reversed copy of a signed word corresponding to
an occurrence in the original word. -/
def invRevPosition {X : Type*} {w : SignedWord X} (i : Fin w.length) :
    Fin (FreeGroup.invRev w).length :=
  i.rev.cast (by simp)

/-- Inverse reversal pairs literal occurrences, preserving the generator and
flipping its orientation bit. -/
theorem get_invRevPosition {X : Type*} (w : SignedWord X)
    (i : Fin w.length) :
    (FreeGroup.invRev w).get (invRevPosition i) =
      ((w.get i).1, !(w.get i).2) := by
  change ((List.map (fun g : X × Bool => (g.1, !g.2)) w).reverse)[(invRevPosition i).val] =
    (w[i].1, !w[i].2)
  have hlt : (invRevPosition i).val <
      (List.map (fun g : X × Bool => (g.1, !g.2)) w).reverse.length := by
    simpa [FreeGroup.invRev] using (invRevPosition i).isLt
  rw [List.getElem_reverse hlt]
  simp only [List.length_map, List.getElem_map]
  have hidx : w.length - 1 - (invRevPosition i).val = i.val := by
    simp [invRevPosition, Fin.val_cast, Fin.val_rev]
    omega
  simp only [hidx]
  rfl

/-- The position correspondence under inverse reversal is a bijection. -/
theorem invRevPosition_bijective {X : Type*} (w : SignedWord X) :
    Function.Bijective (@invRevPosition X w) := by
  constructor
  · intro i j h
    have h' : i.rev = j.rev := by
      apply Fin.ext
      simpa [invRevPosition] using congrArg Fin.val h
    exact Fin.rev_injective h'
  · intro i
    refine ⟨(i.cast (by simp)).rev, ?_⟩
    apply Fin.ext
    simp [invRevPosition]

/-- Equality of literal lists transports a position together with the
corresponding list element. -/
theorem get_cast_eq_of_eq {X : Type*} {u v : List X} (h : u = v)
    (i : Fin u.length) :
    v.get (Fin.cast (congrArg List.length h) i) = u.get i := by
  cases h
  rfl

/-- Finite one-face orientable chord data for a signed word.

The `positive` and `negative` maps are part of the certificate rather than
being recovered by classical choice. This makes occurrence provenance
available to the Nielsen induction and prevents a free-group equality from
silently erasing cancellations.
-/
structure OrientableWicksCertificate
    {X : Type*} [Fintype X] (w : SignedWord X) where
  positive : X → Fin w.length
  negative : X → Fin w.length
  positive_spec : ∀ x, w.get (positive x) = (x, true)
  negative_spec : ∀ x, w.get (negative x) = (x, false)
  /-- Every literal occurrence is one of the displayed signed occurrences. -/
  exhaustive : ∀ i : Fin w.length,
    i = positive (w.get i).1 ∨ i = negative (w.get i).1
  partner : Fin w.length → Fin w.length
  partner_spec : ∀ i,
    w.get (partner i) = ((w.get i).1, !(w.get i).2)
  /-- The boundary-crossing permutation of the one-face map. -/
  rotation : Fin w.length → Fin w.length
  /-- Boundary crossing is, by definition, pairing followed by cyclic
  advancement on the polygon boundary. -/
  rotation_eq : ∀ i, rotation i = cyclicSucc (partner i)
  one_orbit : ∀ i j, ∃ k : ℕ, rotation^[k] i = j

namespace OrientableWicksCertificate

variable {X : Type*} [Fintype X] {w : SignedWord X}

/-- The canonical vertex rotation of an orientable pairing. -/
def canonicalRotation (C : OrientableWicksCertificate w) :
    Fin w.length → Fin w.length :=
  fun i => cyclicSucc (C.partner i)

/-- The certificate's rotation is forced to be the canonical one. -/
theorem rotation_eq_canonical (C : OrientableWicksCertificate w) :
    C.rotation = C.canonicalRotation := by
  funext i
  exact C.rotation_eq i

/-- Positive occurrences of distinct generators have distinct positions. -/
theorem positive_injective
    (C : OrientableWicksCertificate w) : Function.Injective C.positive := by
  intro x y hxy
  have h := congrArg (fun i : Fin w.length => (w.get i).1) hxy
  calc
    x = (w.get (C.positive x)).1 :=
      (congrArg (fun z : X × Bool => z.1) (C.positive_spec x)).symm
    _ = (w.get (C.positive y)).1 := h
    _ = y := congrArg (fun z : X × Bool => z.1) (C.positive_spec y)

/-- Negative occurrences of distinct generators have distinct positions. -/
theorem negative_injective
    (C : OrientableWicksCertificate w) : Function.Injective C.negative := by
  intro x y hxy
  have h := congrArg (fun i : Fin w.length => (w.get i).1) hxy
  calc
    x = (w.get (C.negative x)).1 :=
      (congrArg (fun z : X × Bool => z.1) (C.negative_spec x)).symm
    _ = (w.get (C.negative y)).1 := h
    _ = y := congrArg (fun z : X × Bool => z.1) (C.negative_spec y)

/-- A positive occurrence cannot occupy a negative occurrence's position. -/
theorem positive_ne_negative
    (C : OrientableWicksCertificate w) (x y : X) :
    C.positive x ≠ C.negative y := by
  intro hxy
  have h' : (x, true) = (y, false) := by
    calc
      (x, true) = w.get (C.positive x) := (C.positive_spec x).symm
      _ = w.get (C.negative y) :=
        congrArg (fun i : Fin w.length => w.get i) hxy
      _ = (y, false) := C.negative_spec y
  cases h'

/-- Exhaustive positive/negative occurrence data makes the word's lookup
map injective. -/
private theorem get_injective
    (C : OrientableWicksCertificate w) :
    Function.Injective w.get := by
  intro i j hij
  rcases C.exhaustive i with hi | hi <;>
    rcases C.exhaustive j with hj | hj
  · have hx : (w.get i).1 = (w.get j).1 := congrArg Prod.fst hij
    calc
      i = C.positive (w.get i).1 := hi
      _ = C.positive (w.get j).1 := congrArg C.positive hx
      _ = j := hj.symm
  · have hs : true = false := by
      calc
        true = (w.get i).2 := by rw [hi, C.positive_spec]
        _ = (w.get j).2 := congrArg Prod.snd hij
        _ = false := by rw [hj, C.negative_spec]
    cases hs
  · have hs : false = true := by
      calc
        false = (w.get i).2 := by rw [hi, C.negative_spec]
        _ = (w.get j).2 := congrArg Prod.snd hij
        _ = true := by rw [hj, C.positive_spec]
    cases hs
  · have hx : (w.get i).1 = (w.get j).1 := congrArg Prod.fst hij
    calc
      i = C.negative (w.get i).1 := hi
      _ = C.negative (w.get j).1 := congrArg C.negative hx
      _ = j := hj.symm

/-- The signed-letter specification forces the partner to be an involution;
the certificate need not assume this separately. -/
theorem partner_involutive
    (C : OrientableWicksCertificate w) : Function.Involutive C.partner := by
  intro i
  apply C.get_injective
  rw [C.partner_spec (C.partner i), C.partner_spec i]
  cases h : w.get i with
  | mk x b => cases b <;> rfl

/-- Crossing a paired edge and advancing cyclically is a permutation of
polygon vertices. -/
theorem rotation_bijective
    (C : OrientableWicksCertificate w) :
    Function.Bijective C.rotation := by
  rw [C.rotation_eq_canonical]
  unfold canonicalRotation
  constructor
  · intro i j hij
    have hpartner : C.partner i = C.partner j :=
      (cyclicSucc_bijective w.length).injective hij
    calc
      i = C.partner (C.partner i) := (C.partner_involutive i).symm
      _ = C.partner (C.partner j) := congrArg C.partner hpartner
      _ = j := C.partner_involutive j
  · intro j
    obtain ⟨k, hk⟩ := (cyclicSucc_bijective w.length).2 j
    refine ⟨C.partner k, ?_⟩
    change cyclicSucc (C.partner (C.partner k)) = j
    rw [C.partner_involutive, hk]

/-- Opposite orientation at a partner rules out fixed occurrences, so this
property also follows from the signed-letter specification. -/
theorem partner_ne
    (C : OrientableWicksCertificate w) (i : Fin w.length) :
    C.partner i ≠ i := by
  intro h
  have hget := congrArg w.get h
  rw [C.partner_spec i] at hget
  have hsign := congrArg Prod.snd hget
  cases hb : (w.get i).2 <;> simp at hsign

/-- The two signed occurrences of each alphabet element enumerate the word. -/
noncomputable def occurrenceEquiv
    (C : OrientableWicksCertificate w) : Sum X X ≃ Fin w.length := by
  refine Equiv.ofBijective (fun s ↦ match s with
    | Sum.inl x => C.positive x
    | Sum.inr x => C.negative x) ?_
  constructor
  · intro a b hab
    cases a with
    | inl x =>
        cases b with
        | inl y =>
            exact congrArg Sum.inl (C.positive_injective hab)
        | inr y =>
            exact (C.positive_ne_negative x y hab).elim
    | inr x =>
        cases b with
        | inl y =>
            exact (C.positive_ne_negative y x hab.symm).elim
        | inr y =>
            exact congrArg Sum.inr (C.negative_injective hab)
  · intro i
    rcases C.exhaustive i with hpos | hneg
    · exact ⟨Sum.inl (w.get i).1, hpos.symm⟩
    · exact ⟨Sum.inr (w.get i).1, hneg.symm⟩

/-- The literal contour has exactly two occurrences per alphabet generator. -/
theorem length_eq_two_mul_card
    (C : OrientableWicksCertificate w) :
    w.length = 2 * Fintype.card X := by
  have hcard := Fintype.card_congr C.occurrenceEquiv
  have hcard' : w.length = Fintype.card X + Fintype.card X := by
    simpa [Fintype.card_sum, Fintype.card_fin] using hcard.symm
  omega

/-- The partner preserves labels and reverses orientation. -/
theorem partner_label_eq
    (C : OrientableWicksCertificate w) (i : Fin w.length) :
    (w.get (C.partner i)).1 = (w.get i).1 := by
  simpa using congrArg (fun z : X × Bool => z.1) (C.partner_spec i)

theorem partner_sign_eq_not
    (C : OrientableWicksCertificate w) (i : Fin w.length) :
    (w.get (C.partner i)).2 = !(w.get i).2 := by
  simpa using congrArg (fun z : X × Bool => z.2) (C.partner_spec i)

end OrientableWicksCertificate

end

end SystolicGrowth

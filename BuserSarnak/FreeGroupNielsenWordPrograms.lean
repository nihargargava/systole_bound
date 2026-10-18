module

public import BuserSarnak.FreeGroupNielsenBasicPrograms
public import BuserSarnak.OrientableWicksNielsen

@[expose] public section

/-!
# Literal-word elementary Nielsen multipliers

These compilers keep the existing shear/inversion move language. A left
multiplier executes its letters in their displayed order; a right multiplier
executes them in reverse order. Every multiplier letter must avoid the target
generator, and the resulting program fixes every other generator.
-/

namespace SystolicGrowth

noncomputable section

namespace FreeGroupNielsenProgram

variable {X : Type*}

/-- A literal signed word does not use the displayed target generator. -/
def WordAvoids (a : X) (word : SignedWord X) : Prop :=
  ∀ letter ∈ word, letter.1 ≠ a

@[simp] theorem wordAvoids_nil (a : X) : WordAvoids a [] := by
  simp [WordAvoids]

/-- Avoidance of a concatenation is exactly avoidance of both blocks. -/
@[simp] theorem wordAvoids_append (a : X) (left right : SignedWord X) :
    WordAvoids a (left ++ right) ↔ WordAvoids a left ∧ WordAvoids a right := by
  simp [WordAvoids, List.mem_append, or_imp, forall_and]

/-- Concatenating two avoiding literal blocks preserves avoidance. -/
theorem WordAvoids.append {a : X} {left right : SignedWord X}
    (hl : WordAvoids a left) (hr : WordAvoids a right) :
    WordAvoids a (left ++ right) :=
  (wordAvoids_append a left right).mpr ⟨hl, hr⟩

/-- Inverse reversal changes signs and order, but introduces no generator. -/
theorem WordAvoids.invRev {a : X} {word : SignedWord X}
    (h : WordAvoids a word) : WordAvoids a (FreeGroup.invRev word) := by
  intro letter hletter
  obtain ⟨original, horiginal, heq⟩ := List.mem_map.mp
    (List.mem_reverse.mp hletter)
  rw [← heq]
  exact h original horiginal

/-- The avoidance condition is inherited by a literal tail. -/
theorem WordAvoids.tail {a : X} {letter : X × Bool} {word : SignedWord X}
    (h : WordAvoids a (letter :: word)) : WordAvoids a word := by
  intro x hx
  exact h x (List.mem_cons_of_mem letter hx)

/-- The head of an avoiding word is distinct from its target. -/
theorem WordAvoids.head {a : X} {letter : X × Bool} {word : SignedWord X}
    (h : WordAvoids a (letter :: word)) : letter.1 ≠ a :=
  h letter (List.mem_cons_self)

private theorem mk_cons_eq (letter : X × Bool) (word : SignedWord X) :
    FreeGroup.mk (letter :: word) =
      (if letter.2 then FreeGroup.of letter.1 else (FreeGroup.of letter.1)⁻¹) *
        FreeGroup.mk word := by
  rcases letter with ⟨x, sign⟩
  cases sign <;> rfl

/-- Fixing every displayed generator fixes the evaluation of the whole
literal word, including negative occurrences. -/
theorem toEquiv_apply_mk_of_fixes_letters (moves : List (FreeGroupNielsenMove X))
    (word : SignedWord X)
    (hfix : ∀ letter ∈ word,
      toEquiv moves (FreeGroup.of letter.1) = FreeGroup.of letter.1) :
    toEquiv moves (FreeGroup.mk word) = FreeGroup.mk word := by
  induction word with
  | nil => exact map_one _
  | cons letter word ih =>
    rw [mk_cons_eq, map_mul, ih (fun x hx => hfix x (List.mem_cons_of_mem letter hx))]
    have hhead := hfix letter (List.mem_cons_self)
    cases letter.2 <;> simp [hhead]

/-- Compile left multiplication by an avoiding literal signed word. -/
def leftWord (a : X) : (word : SignedWord X) → WordAvoids a word →
    List (FreeGroupNielsenMove X)
  | [], _ => []
  | letter :: word, h =>
      leftLetter a letter h.head.symm ++ leftWord a word h.tail

/-- Compile right multiplication by an avoiding literal signed word. The
tail executes before the head, because program concatenation acts by
composition in execution order. -/
def rightWord (a : X) : (word : SignedWord X) → WordAvoids a word →
    List (FreeGroupNielsenMove X)
  | [], _ => []
  | letter :: word, h =>
      rightWord a word h.tail ++ rightLetter a letter h.head.symm

/-- Every left-word multiplier fixes generators other than its target. -/
theorem leftWord_apply_of_ne_source (a : X) (word : SignedWord X)
    (h : WordAvoids a word) (x : X) (hx : x ≠ a) :
    toEquiv (leftWord a word h) (FreeGroup.of x) = FreeGroup.of x := by
  induction word with
  | nil => rfl
  | cons letter word ih =>
    rw [leftWord, toEquiv_append]
    change toEquiv (leftWord a word h.tail)
      (toEquiv (leftLetter a letter h.head.symm) (FreeGroup.of x)) = _
    rw [leftLetter_apply_of_ne_source a letter h.head.symm x hx]
    exact ih h.tail

/-- Every right-word multiplier fixes generators other than its target. -/
theorem rightWord_apply_of_ne_source (a : X) (word : SignedWord X)
    (h : WordAvoids a word) (x : X) (hx : x ≠ a) :
    toEquiv (rightWord a word h) (FreeGroup.of x) = FreeGroup.of x := by
  induction word with
  | nil => rfl
  | cons letter word ih =>
    rw [rightWord, toEquiv_append]
    change toEquiv (rightLetter a letter h.head.symm)
      (toEquiv (rightWord a word h.tail) (FreeGroup.of x)) = _
    rw [ih h.tail]
    exact rightLetter_apply_of_ne_source a letter h.head.symm x hx

/-- An avoiding word is fixed by any compiled left-word multiplier. -/
theorem leftWord_apply_mk_of_avoids (a : X) (multiplier word : SignedWord X)
    (hm : WordAvoids a multiplier) (hw : WordAvoids a word) :
    toEquiv (leftWord a multiplier hm) (FreeGroup.mk word) = FreeGroup.mk word :=
  toEquiv_apply_mk_of_fixes_letters _ word fun letter hletter =>
    leftWord_apply_of_ne_source a multiplier hm letter.1 (hw letter hletter)

/-- An avoiding word is fixed by any compiled right-word multiplier. -/
theorem rightWord_apply_mk_of_avoids (a : X) (multiplier word : SignedWord X)
    (hm : WordAvoids a multiplier) (hw : WordAvoids a word) :
    toEquiv (rightWord a multiplier hm) (FreeGroup.mk word) = FreeGroup.mk word :=
  toEquiv_apply_mk_of_fixes_letters _ word fun letter hletter =>
    rightWord_apply_of_ne_source a multiplier hm letter.1 (hw letter hletter)

/-- The left-word compiler sends the target to exactly `word * target`. -/
theorem leftWord_apply_source (a : X) (word : SignedWord X)
    (h : WordAvoids a word) :
    toEquiv (leftWord a word h) (FreeGroup.of a) =
      FreeGroup.mk word * FreeGroup.of a := by
  induction word with
  | nil => simp [leftWord, ← FreeGroup.one_eq_mk]
  | cons letter word ih =>
    rw [leftWord, toEquiv_append]
    change toEquiv (leftWord a word h.tail)
      (toEquiv (leftLetter a letter h.head.symm) (FreeGroup.of a)) = _
    rw [leftLetter_apply_source, map_mul, ih h.tail, mk_cons_eq, mul_assoc]
    have hhead := leftWord_apply_of_ne_source a word h.tail letter.1 h.head
    cases letter.2 <;> simp [hhead]

/-- The right-word compiler sends the target to exactly `target * word`. -/
theorem rightWord_apply_source (a : X) (word : SignedWord X)
    (h : WordAvoids a word) :
    toEquiv (rightWord a word h) (FreeGroup.of a) =
      FreeGroup.of a * FreeGroup.mk word := by
  induction word with
  | nil => simp [rightWord, ← FreeGroup.one_eq_mk]
  | cons letter word ih =>
    rw [rightWord, toEquiv_append]
    change toEquiv (rightLetter a letter h.head.symm)
      (toEquiv (rightWord a word h.tail) (FreeGroup.of a)) = _
    rw [ih h.tail, map_mul, rightLetter_apply_source, mk_cons_eq, mul_assoc]
    have hfixed := toEquiv_apply_mk_of_fixes_letters
      (rightLetter a letter h.head.symm) word fun x hx =>
        rightLetter_apply_of_ne_source a letter h.head.symm x.1 (h.tail x hx)
    rw [hfixed]

/-- Compile the elementary basis change `a ↦ left * a * right`, fixing
all other generators. No additional move constructors are introduced. -/
def twoSidedWord (a : X) (left right : SignedWord X)
    (hl : WordAvoids a left) (hr : WordAvoids a right) :
    List (FreeGroupNielsenMove X) :=
  leftWord a left hl ++ rightWord a right hr

/-- Exact action of the two-sided multiplier compiler on its target. -/
theorem twoSidedWord_apply_source (a : X) (left right : SignedWord X)
    (hl : WordAvoids a left) (hr : WordAvoids a right) :
    toEquiv (twoSidedWord a left right hl hr) (FreeGroup.of a) =
      FreeGroup.mk left * FreeGroup.of a * FreeGroup.mk right := by
  rw [twoSidedWord, toEquiv_append]
  change toEquiv (rightWord a right hr)
    (toEquiv (leftWord a left hl) (FreeGroup.of a)) = _
  rw [leftWord_apply_source, map_mul, rightWord_apply_mk_of_avoids a right left hr hl,
    rightWord_apply_source, mul_assoc]

/-- Exact action on every generator distinct from the target. -/
theorem twoSidedWord_apply_of_ne_source (a : X) (left right : SignedWord X)
    (hl : WordAvoids a left) (hr : WordAvoids a right) (x : X) (hx : x ≠ a) :
    toEquiv (twoSidedWord a left right hl hr) (FreeGroup.of x) = FreeGroup.of x := by
  rw [twoSidedWord, toEquiv_append]
  change toEquiv (rightWord a right hr)
    (toEquiv (leftWord a left hl) (FreeGroup.of x)) = _
  rw [leftWord_apply_of_ne_source a left hl x hx,
    rightWord_apply_of_ne_source a right hr x hx]

/-- Avoidance is a syntactic condition; the action on every avoiding literal
word follows from the compiler, rather than being a new proof input. -/
theorem twoSidedWord_apply_mk_of_avoids (a : X) (left right word : SignedWord X)
    (hl : WordAvoids a left) (hr : WordAvoids a right) (hw : WordAvoids a word) :
    toEquiv (twoSidedWord a left right hl hr) (FreeGroup.mk word) = FreeGroup.mk word :=
  toEquiv_apply_mk_of_fixes_letters _ word fun letter hletter =>
    twoSidedWord_apply_of_ne_source a left right hl hr letter.1 (hw letter hletter)

theorem Internal.FreeGroupNielsenWordProgramsHelpers.singleton_avoids {target : X} {letter : X × Bool}
    (h : target ≠ letter.1) : WordAvoids target [letter] := by
  intro x hx
  have heq : x = letter := List.mem_singleton.mp hx
  exact heq ▸ h.symm

section InnerConjugation

variable [DecidableEq X]

/-- Conjugate precisely the generators displayed in a target list by one
signed letter. The multiplier generator itself is skipped. -/
def conjugateLetterTargets (letter : X × Bool) : List X →
    List (FreeGroupNielsenMove X)
  | [] => []
  | x :: xs =>
      if h : x = letter.1 then conjugateLetterTargets letter xs
      else twoSidedWord x [letter] (FreeGroup.invRev [letter])
        (Internal.FreeGroupNielsenWordProgramsHelpers.singleton_avoids h) (Internal.FreeGroupNielsenWordProgramsHelpers.singleton_avoids h).invRev ++
          conjugateLetterTargets letter xs

private theorem conjugateLetterTargets_apply_multiplier (letter : X × Bool)
    (targets : List X) :
    toEquiv (conjugateLetterTargets letter targets) (FreeGroup.of letter.1) =
      FreeGroup.of letter.1 := by
  induction targets with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x = letter.1
    · simpa only [conjugateLetterTargets, dif_pos hx] using ih
    · rw [conjugateLetterTargets, dif_neg hx, toEquiv_append]
      change toEquiv (conjugateLetterTargets letter xs)
        (toEquiv (twoSidedWord x [letter] _ _ _) (FreeGroup.of letter.1)) = _
      rw [twoSidedWord_apply_of_ne_source _ _ _ _ _ _ (Ne.symm hx), ih]

private theorem conjugateLetterTargets_apply_of_not_mem (letter : X × Bool)
    (targets : List X) (y : X) (hy : y ∉ targets) :
    toEquiv (conjugateLetterTargets letter targets) (FreeGroup.of y) = FreeGroup.of y := by
  induction targets with
  | nil => rfl
  | cons x xs ih =>
    have hyx : y ≠ x := fun h => hy (h ▸ List.mem_cons_self)
    have hyn : y ∉ xs := fun h => hy (List.mem_cons_of_mem x h)
    by_cases hx : x = letter.1
    · simpa only [conjugateLetterTargets, dif_pos hx] using ih hyn
    · rw [conjugateLetterTargets, dif_neg hx, toEquiv_append]
      change toEquiv (conjugateLetterTargets letter xs)
        (toEquiv (twoSidedWord x [letter] _ _ _) (FreeGroup.of y)) = _
      rw [twoSidedWord_apply_of_ne_source _ _ _ _ _ _ hyx, ih hyn]

private theorem conjugateLetterTargets_apply_of_mem (letter : X × Bool)
    (targets : List X) (hn : targets.Nodup) (y : X)
    (hy : y ∈ targets) (hya : y ≠ letter.1) :
    toEquiv (conjugateLetterTargets letter targets) (FreeGroup.of y) =
      FreeGroup.mk [letter] * FreeGroup.of y * (FreeGroup.mk [letter])⁻¹ := by
  induction targets generalizing y with
  | nil => exact (List.not_mem_nil hy).elim
  | cons x xs ih =>
    have hnodup := List.nodup_cons.mp hn
    by_cases hx : x = letter.1
    · rw [conjugateLetterTargets, dif_pos hx]
      exact ih hnodup.2 y (List.mem_of_ne_of_mem (by simpa [hx] using hya) hy) hya
    · rw [conjugateLetterTargets, dif_neg hx, toEquiv_append]
      change toEquiv (conjugateLetterTargets letter xs)
        (toEquiv (twoSidedWord x [letter] _ _ _) (FreeGroup.of y)) = _
      rcases List.mem_cons.mp hy with heq | hmem
      · subst y
        rw [twoSidedWord_apply_source, ← FreeGroup.inv_mk, map_mul, map_mul, map_inv]
        have hletter := toEquiv_apply_mk_of_fixes_letters
          (conjugateLetterTargets letter xs) [letter] (by
            intro l hl
            have hl' := List.mem_singleton.mp hl
            subst l
            exact conjugateLetterTargets_apply_multiplier letter xs)
        rw [hletter, conjugateLetterTargets_apply_of_not_mem letter xs x hnodup.1]
      · by_cases hyx : y = x
        · subst y
          exact (hnodup.1 hmem).elim
        · rw [twoSidedWord_apply_of_ne_source _ _ _ _ _ _ hyx]
          exact ih hnodup.2 y hmem hya

/-- Inner conjugation by a signed letter, compiled using the finite alphabet
enumeration and the existing elementary moves. -/
def conjugateLetter [Fintype X] (letter : X × Bool) :
    List (FreeGroupNielsenMove X) :=
  conjugateLetterTargets letter Finset.univ.toList

/-- The finite enumeration conjugates every generator exactly once. -/
theorem conjugateLetter_apply_of [Fintype X] (letter : X × Bool) (x : X) :
    toEquiv (conjugateLetter letter) (FreeGroup.of x) =
      FreeGroup.mk [letter] * FreeGroup.of x * (FreeGroup.mk [letter])⁻¹ := by
  by_cases hx : x = letter.1
  · subst x
    rw [conjugateLetter, conjugateLetterTargets_apply_multiplier]
    rcases letter with ⟨a, sign⟩
    cases sign
    · change FreeGroup.of a =
        (FreeGroup.of a)⁻¹ * FreeGroup.of a * ((FreeGroup.of a)⁻¹)⁻¹
      rw [inv_inv, inv_mul_cancel, one_mul]
    · change FreeGroup.of a = FreeGroup.of a * FreeGroup.of a * (FreeGroup.of a)⁻¹
      rw [mul_inv_cancel_right]
  · exact conjugateLetterTargets_apply_of_mem letter Finset.univ.toList
      (Finset.nodup_toList _) x (by simp) hx

/-- The generated program acts as inner conjugation on every free-group
element, not only on the alphabet generators. -/
theorem conjugateLetter_apply [Fintype X] (letter : X × Bool) (g : FreeGroup X) :
    toEquiv (conjugateLetter letter) g =
      FreeGroup.mk [letter] * g * (FreeGroup.mk [letter])⁻¹ := by
  have hhom : (toEquiv (conjugateLetter letter)).toMonoidHom =
      (MulAut.conj (FreeGroup.mk [letter])).toMonoidHom := by
    apply FreeGroup.ext_hom
    intro x
    exact conjugateLetter_apply_of letter x
  exact DFunLike.congr_fun hhom g

/-- Inner conjugation by a literal word. Signed letters execute in reverse
order so the resulting conjugating element has the displayed word order. -/
def conjugateWord [Fintype X] : SignedWord X → List (FreeGroupNielsenMove X)
  | [] => []
  | letter :: word => conjugateWord word ++ conjugateLetter letter

/-- The elementary word program has exactly the required inner action. -/
theorem conjugateWord_apply [Fintype X] (word : SignedWord X) (g : FreeGroup X) :
    toEquiv (conjugateWord word) g =
      FreeGroup.mk word * g * (FreeGroup.mk word)⁻¹ := by
  induction word with
  | nil => simp [conjugateWord, ← FreeGroup.one_eq_mk]
  | cons letter word ih =>
    rw [conjugateWord, toEquiv_append]
    change toEquiv (conjugateLetter letter) (toEquiv (conjugateWord word) g) = _
    rw [ih, conjugateLetter_apply]
    have hmk : FreeGroup.mk (letter :: word) =
        FreeGroup.mk [letter] * FreeGroup.mk word := rfl
    rw [hmk, mul_inv_rev]
    simp only [mul_assoc]

/-- The inverse-word program conjugates with the inverse on the left. -/
theorem conjugateWord_invRev_apply [Fintype X] (word : SignedWord X)
    (g : FreeGroup X) :
    toEquiv (conjugateWord (FreeGroup.invRev word)) g =
      (FreeGroup.mk word)⁻¹ * g * FreeGroup.mk word := by
  rw [conjugateWord_apply, ← FreeGroup.inv_mk, inv_inv]

/-- A literal cyclic prefix shift is implemented by an actual elementary
inner program, rather than absorbed into an arbitrary final equivalence. -/
theorem conjugateWord_invRev_apply_append [Fintype X]
    (left right : SignedWord X) :
    toEquiv (conjugateWord (FreeGroup.invRev left))
      (FreeGroup.mk (left ++ right)) = FreeGroup.mk (right ++ left) := by
  rw [conjugateWord_invRev_apply, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
  simp only [inv_mul_cancel_left]

end InnerConjugation

end FreeGroupNielsenProgram

end

end SystolicGrowth

#print axioms SystolicGrowth.FreeGroupNielsenProgram.twoSidedWord_apply_source
#print axioms SystolicGrowth.FreeGroupNielsenProgram.twoSidedWord_apply_of_ne_source
#print axioms SystolicGrowth.FreeGroupNielsenProgram.twoSidedWord_apply_mk_of_avoids
#print axioms SystolicGrowth.FreeGroupNielsenProgram.conjugateLetter_apply
#print axioms SystolicGrowth.FreeGroupNielsenProgram.conjugateWord_apply
#print axioms SystolicGrowth.FreeGroupNielsenProgram.conjugateWord_invRev_apply_append
